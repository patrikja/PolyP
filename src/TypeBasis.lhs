\chapter{Type basis}
\begin{verbatim}

> module TypeBasis where
> import Grammar(QType,Kind,VarID)
> import Folding(dmmapQualified)
> import MyPrelude(pair)
> import MonadLibrary((<@),StateM,executeSTM,fetchSTM,mliftSTM,
>                     STErr,mliftErr,ErrorMonad(failEM),foreach,
>                     ST,(===),(+++))
> import Env(Env,Cache,newEnv,lookupEqEnv,lookupEnv,
>            extendsEnv,assocsEnv,remember,extendsAfterEnv)
> import TypeGraph(HpType,HpKind,HpQType,NonGenerics,NodePtr,
>                  mkVar,mkCon,mkApp,cataHpType,
>                  qtypeOutOfHeap,kindOutOfHeap,qtypeIntoHeap,kindIntoHeap,
>                  flattenNgs,allGeneric,isGenericApproximation,addtoNGS)
#ifdef __HBC__
> import Monad() -- hbc does not import instance declarations correctly
#endif

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

> newtype Basis s  = Basis (TBasis,HpTBasis s)
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
\begin{verbatim}

> tBasis2Basis :: TBasis -> Basis s
> tBasis2Basis tbasis = Basis (tbasis,(newEnv,allGeneric))

\end{verbatim}


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
Invent fresh types for the supplied type variables.
\begin{verbatim}

> makeNonGeneric :: [HpType s]  -> Basis s -> Basis s
> getNonGenerics :: Basis s -> NonGenerics s
> inventTypes :: [VarID] -> STErr s [HpType s]

\end{verbatim}

Maybe inventTypes should give QTypes instead. (If so makeNonGeneric
must also be changed.)

\section{Implementation}
\begin{verbatim}

> lookupType name (Basis (rom,ram)) =
>   maybe (failEM ("lookupType: can't find type of [" ++ name ++ "]"))
>         mliftErr 
>     (lookinram name ram  +++
>      lookinrom name (getTypeEnv rom) )

> lookinram ::String -> HpTBasis s -> Maybe (ST s (HpQType s))
> lookinram name (hptypeEnv, ngs) = 
>   lookupEnv name hptypeEnv <@ instantiate ngs

> lookinrom :: String -> TypeEnv   -> Maybe (ST s (HpQType s))
> lookinrom name typeEnv =
>   lookupEnv name typeEnv   <@ qtypeIntoHeap

\end{verbatim}
When looking up a kind variable no copies are made as all kind
variables are non-generic.
\begin{verbatim}

> lookupKindinram :: String -> HpKindEnv s -> Maybe (HpType s)
> lookupKindinram name hpkindEnv = 
>   lookupEnv name hpkindEnv 

> lookupKindinrom :: String -> KindEnv -> Maybe (ST s (HpKind s))
> lookupKindinrom name kindEnv = 
>   lookupEnv name kindEnv <@ kindIntoHeap

> lookupKind name (rom,ram) =
>   maybe (failEM ("lookupKind: can't find kind of [" ++ name ++ "]"))
>         mliftErr
>     (lookupKindinram name ram <@ return +++
>      lookupKindinrom name rom )

> getTypeEnv :: TBasis -> TypeEnv
> getTypeEnv = fst               
> getKindEnv :: TBasis -> KindEnv
> getKindEnv = snd               

> extendTypeEnv bindings (Basis (rom,(typeEnv, ngs)))
>   = Basis (rom,(extendsEnv bindings typeEnv, ngs))

> extendKindEnv bindings (rom,kindEnv)
>   = (rom,extendsEnv bindings kindEnv)

> extendTypeTBasis :: [(VarID,QType)] -> TBasis -> TBasis
> extendTypeTBasis      l (ts,ks) = (extendsEnv l ts     ,ks)
> extendTypeAfterTBasis :: [(VarID,QType)] -> TBasis -> TBasis
> extendTypeAfterTBasis l (ts,ks) = (extendsAfterEnv l ts,ks)

> extendKindTBasis :: [(VarID,Kind)] -> TBasis -> TBasis
> extendKindTBasis      l (ts,ks) = (ts,extendsEnv      l ks)
> extendKindAfterTBasis :: [(VarID,Kind)] -> TBasis -> TBasis
> extendKindAfterTBasis l (ts,ks) = (ts,extendsAfterEnv l ks)

> makeNonGeneric extraNgs (Basis (rom,(typeEnv, ngs)))
>   = Basis (rom,(typeEnv, addtoNGS extraNgs ngs))

> getNonGenerics (Basis (_,(_, ngs))) = ngs

> inventTypes vars = mliftErr (foreach vars (\_ -> mkVar))

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
>     isGen p = isGenericApproximation p ngs
>     lookupVar v = fetchSTM <@ lookupEqEnv (===) v

\end{verbatim}
We assume that all type variables are generic when taking the types
out of the heap.
\begin{verbatim}

> getRamTypes :: Basis s -> [(String,HpQType s)]
> getRamTypes (Basis (_,(env,_))) = assocsEnv env

> ramTypeToRom :: Basis s -> ST s [(String,QType)]
> ramTypeToRom (Basis (_,(env,_))) = foreach (assocsEnv env) 
>    (\(n,hpt) -> qtypeOutOfHeap allGeneric hpt <@ pair n) 
> ramKindToRom :: KindBasis s -> ST s [(String,Kind)]
> ramKindToRom (_,env) = foreach (assocsEnv env) 
>    (\(n,hpt) -> kindOutOfHeap     hpt <@ pair n)

\end{verbatim}
