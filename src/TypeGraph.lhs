\chapter{Constructing Types in the Graph}
\begin{verbatim}

> module TypeGraph where
> import MyPrelude(variablename,pair,mapSnd)
> import Grammar
> import PrettyPrinter(Pretty(..),text)
> import MonadLibrary(State,StateM,(<@),liftop,(<@-),fetchST,executeST,mliftSTM,
>                     mfoldl,executeSTM,updateSTM,mfoldr,map2,mapl,
>                     ST,MutVar,newVar,writeVar,readVar, (===))
> import Env(Env,Cache,lookupEqEnv,rememberST,newEnv,lookaside,remember)
> import Folding(mmapEqn,mmapQualified,dmmapQualified,mcataType)

\end{verbatim}
\section{The types of types}
During type inference, the types will reside on the heap using mutable
variables (\verb|newVar|, \verb|writeVar|, \verb|readVar|) to allow for
efficient destructive updates.

The case \verb|HpVar| represents a type variable (if it points to
itself) or an indirection node (if it points somewhere else).
\begin{verbatim}

> data HpNode a = HpVar (NodePtr a) 
>               | HpCon ConID
>               | HpApp (NodePtr a) (NodePtr a)

> type NodePtr a = MutVar a (HpNode a)

> type HpType s  = NodePtr s
> type HpQType s = Qualified (HpType s)
> type HpKind s  = NodePtr s

\end{verbatim}

These should never be printed, but for debugging it might be
helpful. See {\tt showNodePtr} below for a more detailed printer.

\begin{verbatim}

> instance Pretty (HpNode s) where
>   pretty (HpCon c  ) = text c
>   pretty (HpApp _ _) = text "<HpApp>"
>   pretty (HpVar _  ) = text "<HpVar>"

\end{verbatim}
We need a version of \verb|lookaside| that uses pointer equality,
\verb|(===)|.
\begin{verbatim}

> lookupvar :: HpType s -> State (Env (HpType s) c) (Maybe c)
> lookupvar v = fetchST <@ (lookupEqEnv (===) v) 

\end{verbatim}
\section{Interface}
\begin{verbatim}

> mkVar   ::                           ST s (NodePtr s)
> mkCon   ::              ConID     -> ST s (NodePtr s)
> mkApp   :: NodePtr s -> NodePtr s -> ST s (NodePtr s)

> mkFun   :: NodePtr s -> NodePtr s -> ST s (NodePtr s)
> mkConApp:: ConID ->    [NodePtr s]-> ST s (NodePtr s)

> follow    :: NodePtr s -> ST s (NodePtr s)
> fetchNode :: NodePtr s -> ST s (NodePtr s, HpNode s)

> qtypeOutOfHeap :: NonGenerics s -> HpQType s -> ST s QType
> typeOutOfHeap  :: NonGenerics s -> HpType s  -> ST s Type
> kindOutOfHeap  ::                  HpKind s  -> ST s Kind

> qtypeIntoHeap :: QType -> ST s (HpQType s)
> typeIntoHeap  :: Type  -> ST s (HpType s)
> kindIntoHeap  :: Kind  -> ST s (HpKind s)
> eqnIntoHeap   :: Eqn   -> ST a (HpTEqn a)

\end{verbatim}
\section{Implementation}
\subsection{Constructors}
\begin{verbatim}

> mkVar =  newVar undefined     >>= \v -> 
>          writeVar v (HpVar v) <@- v

> mkCon conID = newVar (HpCon conID)

> mkApp f g = newVar (HpApp f g)

> mkFun a b = mkConApp functionConstructor [a, b]

> mkConApp conID args = mkCon conID >>= \con -> 
>                       mfoldl mkApp con args

> mkFOf :: ST s (HpType s)
> mkFOf    = mkCon "FunctorOf"

> mkFOfd :: HpType s -> ST s (HpType s)
> mkFOfd d = mkFOf >>= (`mkApp` d)

\end{verbatim}
The operator \verb|(==>)| makes a type variable `point to' another
type by overwriting it.
\begin{verbatim}

> (==>) :: NodePtr s -> NodePtr s -> ST s ()
> a ==> b = readVar b >>= \nb -> writeVar a nb <@- ()

\end{verbatim}
The write last line can be replaced by {\tt (writeVar a (HpVar b))}
(that means overwrite with an indirection node instead of a copy of
the other node) but tests indicate that this actually takes more
reductions.

\subsection{Selectors}
To fetch the value of a node we traverse the indirections until we
find a type variable (pointing to itself) or some other node value. We
return both the pointer and the value to allow for a quick equality
check (just compare the pointers). (We could use this opportunity to
short-out multiple indirections but preliminary tests suggests that
the reduced number of indirections does not compensate for the extra
complexity.)
\begin{verbatim}

> fetchNode ptr 
>   = follow ptr >>= \p-> 
>     readVar p  <@ (pair p)

> follow ptr
>   = readVar ptr >>= \node -> case node of
>       HpVar inst | not (inst === ptr) -> follow inst
>       _                               -> return ptr

\end{verbatim}
\subsection{Cata and flatten for heap types}
The catamorphism for \verb|HpType| gives its result in the \verb|ST
s|-monad as it uses data on the heap. One could think of the
combination \verb|NodePtr -> ST s| as being the real type of a heap
type. We have the type \verb|NodePtr -> ST s a| in the
variable-or-indirection case to allow this conversion function to
access the value the node pointer points to.
\begin{verbatim}

> cataHpType :: ( NodePtr s -> ST s a ) ->
>               ( ConID     ->      a ) ->
>               ( a -> a    ->      a ) ->
>               HpType s -> ST s a

> cataHpType var con app = c 
>  where c p = fetchNode p  >>= \(_, node) -> 
>              case node of                        
>                HpVar v     -> var v
>                HpCon co    -> return (con co)
>                HpApp pf px -> liftop app (c pf) (c px)

\end{verbatim}
To extract all type variables from a heap type we use
\verb|flattenHpType|.  This somwhat cryptic definition uses the
catamorphism to build a function that prepends a types variables to a
given list.  It then applies this function to the empty list. This
avoids the use of \verb|++| making the function linear in the size of
the type.
\begin{verbatim}

> flattenHpType :: HpType s -> ST s [HpType s]
> flattenHpType = map appnil . cataHpType var (\c l -> l) (.)
>  where var v = return (v:) 
>        appnil f = f []

\end{verbatim}
We need a spinewalk that gives us the head node and pointers to
the children (and to the apply nodes). We give this as a list of pairs
of pointers to nodes and their values. The first is the head and the
others are for the apply nodes. The children are reached through the
right pointers of the apply nodes.
\begin{verbatim}

> spineWalkHpType :: NodePtr s -> ST s [(NodePtr s,HpNode s)]
> spineWalkHpType t = s t <@ ($[])
>  where s p = fetchNode p  >>= \ pn@(ptr, node) -> 
>              case node of                        
>                HpVar v     -> return  (pn:)
>                HpCon c     -> return  (pn:)       
>                HpApp pf px -> s pf <@ (.(pn:))

> getChild :: HpNode s -> NodePtr s
> getChild (HpApp pf px) = px
> getChild _ = error "getChild: not an application node"

\end{verbatim}
\subsection{Type transformers}
In \verb|qtypeOutOfHeap'|, \verb|ngs| is assumed to be a list of type
variables. This is assured by first calling \verb|flattenNgs|.
\begin{verbatim}

> qtypeOutOfHeap ngs ptr =
>   flattenNgs ngs            >>= \allngs->
>   qtypeOutOfHeap' allngs ptr <@
>   runVarSupply

> typeOutOfHeap ngs ptr =
>   flattenNgs ngs            >>= \allngs->
>   typeOutOfHeap' allngs ptr <@
>   runVarSupply


> typesOutOfHeap :: NonGenerics s -> (HpType s,HpType s) -> 
>                               ST s (Type    ,Type)
> typesOutOfHeap ngs (a,b) =
>    mkApp a b                  >>= \hpt -> 
>    flattenNgs ngs             >>= \allngs->
>    typeOutOfHeap' allngs hpt <@
>    (unApp.runVarSupply)
>  where unApp (ta :@@: tb) = (ta,tb)
>        unApp _            = error "TypeGraph: typesOutOfHeap: impossible: no application found"

\end{verbatim}
During type inference we will use the heap representation of the types
in expressions so we define type synonyms for expressions and
equations labelled with heap types:
\begin{verbatim}

> type HpTExpr s = Expr' (HpQType s)
> type HpTEqn  s = Eqn'  (HpQType s)

\end{verbatim}
To translate a whole equation containing heap types to an equation
containing normal types the following steps are taken:
\begin{itemize}
\item From {\tt HpTEqn s} = {\tt Eqn' (HpQType s)} using a monadic map
  of {\tt type\-OutOf\-Heap' ngs}
\item from {\tt ST s (Eqn' (VarSupply s Type))} using {\tt map threadEqn}
\item from {\tt ST s (VarSupply s (Eqn' Type))} using {\tt map runVarSupply}
\item to {\tt ST s (Eqn' Type)} = {\tt ST s TEqn}
\end{itemize}
Where the {\tt ST s}-monad can be removed by \verb|runST| later.
(Maybe the \verb|ngs| argument should be removed.)
(The polytypic cases can use the same type variable names.)
\begin{verbatim}

> tEqnOutOfHeap :: NonGenerics s -> HpTEqn s -> ST s TEqn
> tEqnOutOfHeap ngs hpteqn = 
>   tEqnOutOfHeap' ngs hpteqn <@ runVarSupply

> tEqnOutOfHeap' :: NonGenerics s -> HpTEqn s -> ST s (VarSupply s TEqn)
> tEqnOutOfHeap' ngs hpteqn = 
>   mmapEqn (qtypeOutOfHeap' ngs) hpteqn <@ threadEqn 

> threadEqn :: (Functor m, Monad m) => Eqn' (m a) -> m (Eqn' a)
> threadEqn = mmapEqn id

> blockOutOfHeap :: [(HpTEqn s,(VarID,HpQType s))] -> 
>                   ST s [(TEqn,(VarID,QType))]
> blockOutOfHeap ps = mapl f ps 
>   where f (eqn,(n,t)) = tEqnOutOfHeap' [] eqn >>= \meqn ->
>                         qtypeOutOfHeap' [] t   >>= \mt   ->
>                         return (mapSnd (pair n) 
>                                  (runVarSupply (map2 pair meqn mt)) ) 

\end{verbatim}
To translate from the heap representation to the abstract syntax for
types we need a supply of suitable variablenames. For each variable
encountered we need either its already defined name or a fresh name.
\begin{verbatim}

#ifdef __HBC__
> type HpType2Int s a =         State (Cache (HpType s) Int)  a
> type VarSupply  s a = StateM (State (Cache (HpType s) Int)) Int a
#else
> type HpType2Int s   =         State (Cache (HpType s) Int)
> type VarSupply  s a = StateM (HpType2Int s                ) Int a
#endif

> runVarSupply :: VarSupply s a -> a
> runVarSupply = executeST newEnv . executeSTM (0::Int)
> rememberVar :: HpType s -> Int -> VarSupply s Int
> rememberVar v n = mliftSTM (rememberST v n) 
> freshVarNum :: VarSupply s Int
> freshVarNum = updateSTM (+1)     
> lookupVar :: HpType s -> VarSupply s (Maybe Int)
> lookupVar = mliftSTM . lookupvar 

> qtypeOutOfHeap' :: NonGenerics s -> HpQType s -> 
>                   ST s (VarSupply s QType) 
> qtypeOutOfHeap' ngs = dmmapQualified (typeOutOfHeap' ngs)

> typeOutOfHeap' :: NonGenerics s -> HpType s -> 
>                    ST s (VarSupply s Type) 
> typeOutOfHeap' ngs = cataHpType (return . var) con app
>   where 
>     var v = readAndUpdate lookupVar freshVarNum rememberVar v <@ varOf v
>     con c = return (TCon c)
>     app   = liftop (:@@:)
>     varOf v n | isGen v   = TVar (variablename n)
>               | otherwise = TVar ("_" ++ show n)
>     isGen p = null (filter (p===) ngs)  

\end{verbatim}
To translate from the abstract syntax to the heap we need a maping
from type variables to heap type variables to build a DAG (directed
acyclic graph).  An extension could be to share constructors or even
common subexpressions. 

The improved sharing will help the unifier and the type
labelling. Idea: keep a mapping from Type to HpType. At every level:
check if the type is in the environment, if so use that
pointer. Otherwise, create new structure, store this structure in the
environment.


The types are in the Interface section above.
\begin{verbatim}

> kindIntoHeap = typeIntoHeap
> typeIntoHeap = executeSTM newEnv . typeIntoHeap'
> eqnIntoHeap  = mmapEqn qtypeIntoHeap
> qtypeIntoHeap = executeSTM newEnv . mmapQualified typeIntoHeap'

> --                                  could be Type (HpType s)
> type Name2HpType s a = StateM (ST s) (Cache VarID (HpType s)) a

> typeIntoHeap' :: Type -> Name2HpType s (HpType s)
> typeIntoHeap' = mcataType (var,con,app)
>   where var = readAndUpdate lookaside (mliftSTM mkVar) remember
>         con name  = mliftSTM (mkCon name)
>         app tF tX = mliftSTM (mkApp tF tX)

> readAndUpdate :: Monad m => (a -> m (Maybe b)) -> m c -> 
>                             (a -> c -> m b) -> a -> m b 
> readAndUpdate look fresh save n =
>   look n >>= \hit -> case hit of
>     Nothing -> fresh >>= save n
>     Just p  -> return p

\end{verbatim} 
Kinds are very easily translated as all kind variables are converted
to kind $\ast$ (star).
\begin{verbatim}

> kindOutOfHeap = cataHpType var TCon (:@@:)
>   where var _ = return star
>         star  = (TCon "*")

\end{verbatim}
\subsection{Non-generic type variables}
A variable is generic iff it is not reachable from the list of
\verb|NonGenerics|. This is not a very efficient representation but
normally very few variables are non-generic at the same time.
\begin{verbatim}

> type NonGenerics s = [HpType s]

> isGeneric :: HpType s -> NonGenerics s -> ST s Bool
> isGeneric tyVar ngs = map not (occursInTypeList tyVar ngs) 

> occursInTypeList :: HpType s -> [HpType s] -> ST s Bool
> occursInTypeList tyVar
>     = mfoldr (\t b -> if b then return True
>                            else occursIn t) False
>   where occursIn = (tyVar `occursInType`)

\end{verbatim}
The second \verb|occursInType| (obtained by expanding the definition
of {\tt cata\-HpType} and short-circuiting the use of \verb-||-) is
more efficient as in the first laziness is destroyed by the
monad-plumbing in \verb|cataHpType|.
\begin{verbatim}

occursInType :: NodePtr s -> HpType s -> ST s Bool
(tyVar `occursInType`) = cataHpType var (\_->False) (||)
  where var v = return (tyVar === v)

> occursInType :: NodePtr s -> HpType s -> ST s Bool
> tyVar `occursInType` t = occursIn t
>   where 
>     occursIn p =
>       fetchNode p >>= \(ptr, node) -> 
>       case node of
>         HpVar v -> return (tyVar === v)
>         HpCon _ -> return False
>         HpApp pf px -> occursIn pf >>= \b -> 
>                        if b then return True
>                             else occursIn px

> flattenNgs :: NonGenerics s -> ST s (NonGenerics s)
> flattenNgs = mfoldr flat []
>   where flat t ngs = flattenHpType t <@ (++ngs)

\end{verbatim}

\section{Misc.}

For debugging purposes it is good to be able to see what the actual
pointer structure looks like.

\begin{verbatim}

> showNodePtr :: NodePtr s -> ST s String
> showNodePtr p = readVar p >>= \n-> case n of
>              HpVar v | v === p -> return "Var"
>                      | True    -> map ('-':) (showNodePtr v)
>              HpCon c -> return ('C':c)
>              HpApp p1 p2 -> liftop (++) (showNodePtr p1) (showNodePtr p2 <@ ('@':))

\end{verbatim}