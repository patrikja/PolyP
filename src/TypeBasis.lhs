\chapter{Type basis}
\begin{verbatim}

> module TypeBasis where
> import Grammar(QType,Kind,VarID)
> import Folding(dmmapQualified)
> import MyPrelude(pair)
> import MonadLibrary((<@),StateM,executeSTM,fetchSTM,mliftSTM,
>                     STErr,mliftErr,ErrorMonad(failEM),mapl,
>                     ST,(===))
> import Env(Env,Cache,newEnv,lookupEqEnv,lookupEnv,
>            extendsEnv,assocsEnv,remember,extendsAfterEnv)
> import TypeGraph(HpType,HpKind,HpQType,NonGenerics,NodePtr,
>                  mkVar,mkCon,mkApp,cataHpType,
>                  qtypeOutOfHeap,kindOutOfHeap,typeIntoHeap,kindIntoHeap,
>                  flattenNgs)

\end{verbatim}
\section{The definition of the basis}
The basis consists of four subenvironments:
\begin{itemize}
\item {\tt TypeEnv} contains the types of variables and constructors.
\item {\tt KindEnv} contains the kinds of type constructors.
\item {\tt HpTypeEnv} contains types under construction.
\item {\tt NonGenerics} is a list of non-generic type variables.
\end{itemize}
\begin{verbatim}

> type Basis s     = (TBasis,HpTBasis s)
> type TBasis      = (TypeEnv, KindEnv)
> type HpTBasis s  = (HpTypeEnv s, NonGenerics s)

> type TypeEnv     = Env String QType
> type KindEnv     = Env String Kind
> type HpTypeEnv s = Env String (HpQType s)

\end{verbatim}
There is no need for a {\tt TypeEnv} or {\tt NonGenerics} in the kind
environment.
\begin{verbatim}

> type KindBasis s = (KindEnv,HpKindEnv s)
> type HpKindEnv s = Env String (HpType s)

\end{verbatim}

\section{Interface}
The function {\tt lookupType} looks up a name in the type environment
and returns the pointer to a copy of the type in the heap. Notice,
however, that non-generic variables are not copied, but shared.
{\tt lookupKind} looks up a kind; no copies are made as polymorphic
kinds are not allowed.
\begin{verbatim}

> lookupType :: String -> Basis s -> STErr s (HpQType s)
> lookupKind :: String -> KindBasis s -> STErr s (HpKind s)

\end{verbatim}
Using {\tt extendTypeEnv} and {\tt extendKindEnv} you can extend the
type- and kind environments respectively.
\begin{verbatim}

> extendTypeEnv :: [(String, HpQType s)] -> Basis s -> Basis s
> extendKindEnv :: [(String, HpKind s)] -> KindBasis s -> KindBasis s

\end{verbatim}
{\tt makeNonGeneric} marks the types it receives as it first argument
as non-generic in the type basis.
\begin{verbatim}

> makeNonGeneric :: [HpType s]  -> Basis s -> Basis s
> getNonGenerics :: Basis s -> NonGenerics s
 
\end{verbatim}
\section{Implementation}
\begin{verbatim}

> lookupType name (rom,ram) =
>   maybe (failEM ("lookupType: can't find type of [" ++ name ++ "]"))
>         mliftErr 
>     (lookinram name ram  ++
>      lookinrom name (getTypeEnv rom) )

> lookinram ::String -> HpTBasis s -> Maybe (ST s (HpQType s))
> lookinram name (hptypeEnv, ngs) = 
>   lookupEnv name hptypeEnv <@ instantiate ngs

> lookinrom :: String -> TypeEnv   -> Maybe (ST s (HpQType s))
> lookinrom name typeEnv =
>   lookupEnv name typeEnv   <@ typeIntoHeap

\end{verbatim}
When looking up a kind variable no copies are made as all kind
variables are non-generic.
\begin{verbatim}

> lookupKindinram :: String -> HpKindEnv s -> Maybe (HpType s)
> lookupKindinram name hpkindEnv = 
>   lookupEnv name hpkindEnv 

> lookupKindinrom name kindEnv = 
>   lookupEnv name kindEnv <@ kindIntoHeap

> lookupKind name (rom,ram) =
>   maybe (failEM ("lookupKind: can't find kind of [" ++ name ++ "]"))
>         mliftErr
>     (lookupKindinram name ram <@ return ++
>      lookupKindinrom name rom )

> getTypeEnv :: TBasis -> TypeEnv
> getTypeEnv = fst               
> getKindEnv :: TBasis -> KindEnv
> getKindEnv = snd               

> extendTypeEnv bindings (rom,(typeEnv, ngs))
>   = (rom,(extendsEnv bindings typeEnv, ngs))

> extendKindEnv bindings (rom,kindEnv)
>   = (rom,extendsEnv bindings kindEnv)

> extendTypeTBasis :: [(VarID,QType)] -> TBasis -> TBasis
> extendTypeTBasis      l (ts,ks) = (extendsEnv l ts     ,ks)
> extendTypeAfterTBasis l (ts,ks) = (extendsAfterEnv l ts,ks)

> extendKindTBasis :: [(VarID,Kind)] -> TBasis -> TBasis
> extendKindTBasis      l (ts,ks) = (ts,extendsEnv      l ks)
> extendkindAfterTBasis l (ts,ks) = (ts,extendsAfterEnv l ks)

> makeNonGeneric extraNgs (rom,(typeEnv, ngs))
>   = (rom,(typeEnv, extraNgs ++ ngs))

> getNonGenerics (_,(_, ngs)) = ngs

> instantiate :: NonGenerics s -> HpQType s -> ST s (HpQType s)
> instantiate ngs hpqt = 
>    flattenNgs ngs   >>= \allngs ->
>    dmmapQualified (fresh allngs) hpqt >>= \freshen->
>    executeSTM newEnv freshen

\end{verbatim}
The result type of {\tt fresh} contains three monadic constructions:
\begin{itemize}
\item The outer {\tt ST s}-monad provides (reading) access to the
  heap during the reading phase. The catamorphism guides the type tree
  traversal.
\item The {\tt StateM}-monad transformer provides access to an
  environment of type variable associations from the old to the fresh
  type. (This could be extended to sharing of constructors.)
\item The inner {\tt ST s}-monad provides (writing) access to the
  heap during the writing phase.
\end{itemize}
\begin{verbatim}

> type Old2Fresh s m a = StateM m (Cache (NodePtr s) (HpType s)) a
> fresh :: NonGenerics s -> HpType s -> 
>          ST s ( Old2Fresh s (ST s) (HpType s) )
> fresh ngs = cataHpType (return.var) con app
>   where 
>     var v = 
>         lookupVar v >>= maybe
>           (if isGen v then  freshvar >>= remember v
>            else return v) -- don't copy non-generics
>           return -- use the remembered variable
>     freshvar = mliftSTM mkVar
>     con = mliftSTM . mkCon 
>        -- copies constructors instead of sharing them
>     app mf mx = mf >>= \f-> mx >>= \x -> 
>                 mliftSTM (mkApp f x)
>     isGen p = null (filter (===p) ngs)
>     lookupVar v = fetchSTM <@ lookupEqEnv (===) v

\end{verbatim}
We assume that all type variables are generic when taking the types
out of the heap.
\begin{verbatim}

> getRamTypes :: Basis s -> [(String,HpQType s)]
> getRamTypes (_,(env,_)) = assocsEnv env

> ramTypeToRom :: Basis s -> ST s [(String,QType)]
> ramTypeToRom (_,(env,_)) = 
>    mapl (\(n,hpt) -> qtypeOutOfHeap [] hpt <@ pair n ) (assocsEnv env)
> ramKindToRom :: KindBasis s -> ST s [(String,Kind)]
> ramKindToRom (_,env) = 
>    mapl (\(n,hpt)->kindOutOfHeap hpt <@ pair n) (assocsEnv env)

\end{verbatim}
