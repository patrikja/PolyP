\chapter{Constructing Types in the Graph}
\begin{verbatim}

> module TypeGraph where
> import MyPrelude(variablename,pair,mapSnd,splitUp)
> import Grammar
> import PrettyPrinter(Pretty(..),text)
> import MonadLibrary(State,StateM,(<@),liftop,(<@-),
>                     fetchST,executeST,mliftSTM,executeSTM,updateSTM,
>                     mfoldl,mfoldr,map2,mapl,mIf,
>                     ST,MutVar,newVar,writeVar,readVar, (===))
> import MyPrelude(fMap)
> import Env(Env,Cache,lookupEqEnv,rememberST,newEnv,lookaside,remember)
> import Folding(mmapEqn,mmapQualified,dmmapQualified,mcataType)
> import StateFix-- (ST [,runST [,RunST]]) in hugs, ghc, hbc

> infixr 6 +#+

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
> checkCon  :: HpType  s -> ST s (Maybe ConID)

> qtypeOutOfHeap :: NonGenerics s -> HpQType s -> ST s QType
> typeOutOfHeap  :: NonGenerics s -> HpType s  -> ST s Type
> kindOutOfHeap  ::                  HpKind s  -> ST s Kind

> qtypeIntoHeap :: QType -> ST s (HpQType s)
> typeIntoHeap  :: Type  -> ST s (HpType s)
> kindIntoHeap  :: Kind  -> ST s (HpKind s)
> eqnIntoHeap   :: Eqn   -> ST a (HpTEqn a)

> (+#+) :: [Qualifier (HpType s)] -> [Qualifier (HpType s)] -> 
>    ST s [Qualifier (HpType s)]
> mkQFun :: HpQType s -> HpQType s -> ST s (HpQType s)

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

If the indirections form a loop other than the ``knot'' representing a
type variable, \texttt{fetchNode} will loop. The variant can be used
to detect this.

\begin{verbatim}

> fetchNode ptr 
>   = follow ptr >>= \p-> 
>     readVar p  <@ (pair p)

> follow ptr
>   = readVar ptr >>= \node -> case node of
>       HpVar inst | not (inst === ptr) -> follow inst
>       _                               -> return ptr

 follow ptr = follow' ptr 0
 follow' ptr n
   = readVar ptr >>= \node -> case maytrace (show n) $ node of
       HpVar inst | not (inst === ptr) -> follow' inst (n+1)
       _                               -> return ptr

> checkCon pc = fetchNode pc >>= \(_,n) -> case n of
>                  (HpCon c) -> return (Just c)
>                  _         -> return Nothing

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
> flattenHpType = fMap appnil . cataHpType var (\_ l -> l) (.)
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
>  where s p = fetchNode p  >>= \ pn@(_, node) -> 
>              case node of                        
>                HpVar _     -> return  (pn:)
>                HpCon _     -> return  (pn:)
>                HpApp pf _  -> s pf <@ (.(pn:))

> getChild :: HpNode s -> NodePtr s
> getChild (HpApp _ px) = px
> getChild _ = error "TypeGraph.getChild: not an application node"

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
>        unApp _            = error "TypeGraph.typesOutOfHeap: impossible: no application found"

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
>   where f (eqn,(n,t)) = tEqnOutOfHeap' allGeneric eqn >>= \meqn ->
>                         qtypeOutOfHeap' allGeneric t   >>= \mt   ->
>                         return (mapSnd (pair n) 
>                                  (runVarSupply (map2 pair meqn mt)) ) 

\end{verbatim}
To translate from the heap representation to the abstract syntax for
types we need a supply of suitable variablenames. For each variable
encountered we need either its already defined name or a fresh name.
\begin{verbatim}

These definitions (using type synonyms of higher kind) are explicitly
allowed by the Haskell 98 report, but do not (990511) work for HBC,
GHC.

type HpType2Int s   =         State (Cache (HpType s) Int)
type VarSupply  s a = StateM (HpType2Int s                ) Int a

Instead these expanded definitions are used.

> type HpType2Int s a =         State (Cache (HpType s) Int)  a
> type VarSupply  s a = StateM (State (Cache (HpType s) Int)) Int a

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
>     varOf v n | isGenericApproximation v ngs  = TVar (variablename n)
>               | otherwise                     = TVar ("_" ++ show n)

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

> newtype NonGenerics s = NGS [HpType s]

> allGeneric :: NonGenerics s
> allGeneric = NGS []

> addtoNGS :: [HpType s] -> NonGenerics s -> NonGenerics s
> addtoNGS a (NGS b) = NGS (a++b)

> isGeneric :: HpType s -> NonGenerics s -> ST s Bool
> isGeneric tyVar (NGS ngs) = fMap not (occursInTypeList tyVar ngs) 

> isGenericApproximation :: HpType s -> NonGenerics s -> Bool
> isGenericApproximation tyVar (NGS ngs) = null (filter (tyVar===) ngs)

> occursInTypeList :: HpType s -> [HpType s] -> ST s Bool
> occursInTypeList tyVar
>     = mfoldr (\t b -> if b then return True
>                            else occursIn t) False
>   where occursIn = (tyVar `occursInType`)

\end{verbatim} 

Function \texttt{isGenericApproximation} assumes that the list
contains only type variables so that the test \texttt{occursInType}
can be simplified to pointer equality.

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
>       fetchNode p >>= \(_, node) -> 
>       case node of
>         HpVar v -> return (tyVar === v)
>         HpCon _ -> return False
>         HpApp pf px -> occursIn pf >>= \b -> 
>                        if b then return True
>                             else occursIn px

> flattenNgs :: NonGenerics s -> ST s (NonGenerics s)
> flattenNgs (NGS ngs) = mfoldr flat allGeneric ngs
>   where flat t ngs' = flattenHpType t <@ (`addtoNGS` ngs')

\end{verbatim}

\section{Misc.}

For debugging purposes it is good to be able to see what the actual
pointer structure looks like.

\begin{verbatim}

> showNodePtr :: NodePtr s -> ST s String
> showNodePtr p = readVar p >>= \n-> case n of
>              HpVar v | v === p -> return "Var"
>                      | True    -> fMap ('-':) (showNodePtr v)
>              HpCon c -> return ('C':c)
>              HpApp p1 p2 -> liftop (++) (showNodePtr p1) (showNodePtr p2 <@ ('@':))

\end{verbatim}
\subsection{Simplification of contexts}
% 
Constant {\tt Poly} contexts must be retained (they are to guide the 
instance generation phase) but other constant Haskell contexts should 
be eliminated.
%
(Strictly speaking, this should only be done after checking an instance 
 environment, but throwing them away will not worsen the current status.)
%
\begin{verbatim}

> mkQFun (ps:=>tA) (qs:=>tB) =
>   ps +#+ qs    >>= \pqs->
>   mkFun tA tB >>= \tA2B->
>   return (pqs:=>tA2B)

> ps +#+ qs = simplifyHpQualifiers (ps ++ qs)

\end{verbatim}
%
The {\tt Poly} qualifiers are brought to the front and the rest simplified.
%
Function {\tt simpQual} assumes that {\tt Poly} qualifiers are handled 
elsewhere.
%
\begin{verbatim}

> simplifyContext :: QType -> QType
> simplifyContext qt = __RUNST__ mqt
>   where mqt :: ST s QType
>         mqt = qtypeIntoHeap qt >>= simplifyHpContext >>= qtypeOutOfHeap allGeneric


> simplifyHpContext :: HpQType s -> ST s (HpQType s)
> simplifyHpContext (ps:=>t) = simplifyHpQualifiers ps <@ (:=> t)

> simplifyHpQualifiers :: [Qualifier (HpType s)] -> 
>                    ST s [Qualifier (HpType s)]
> simplifyHpQualifiers ps = fMap concat (mapl simpQual others) <@ (polys ++)
>   where [polys,others] = splitUp [isPoly] ps

> isPoly :: Qualifier a -> Bool
> isPoly ("Poly",_) = True
> isPoly _          = False

> simpQual :: Qualifier (HpType s) -> ST s [Qualifier (HpType s)]
> simpQual q = mIf (isConstantQualifier q) (return []) (return [q])

> isConstantQualifier :: Qualifier (HpType s) -> ST s Bool
> isConstantQualifier (_,ts) = mapl flattenHpType ts <@ (null . concat)

\end{verbatim}
A qualifier is constant if the list of all variables in it is empty.


