> module Functorise(makeFunctor,makeFunctorStruct,Struct) where
> import Grammar(ConID,VarID,Eqn,Eqn'(DataDef),Func,
>		 Type(..),spineWalkType,isTupleCon)
> import MyPrelude(mapSnd)
> import Folding(cataType)

\section{Extracting functors from {\tt data}-definitions} 
For every regular datatype we need the functor that represents its
recursive structure: {\tt D} == {\tt Mu fD}.

Preliminary version: Works for exactly one type parameter and not with
any structure on the right hand side.

The type {\tt Struct} represents the top level structure of the
datatype definition: 
\begin{verbatim}

> makeFunctor :: Eqn -> Func
> makeFunctor = snd . makeFunctorStruct

> type PList a = (a,[a])
> type Struct = PList (ConID,Int)

\end{verbatim}

*** Triples and beyond should probably be translated to nested pairs
in inn, out, or forbidden below.

\begin{verbatim}

> makeFunctorStruct :: Eqn -> (Struct,Func)
> makeFunctorStruct (DataDef def [_] alts _)
>   = ( ((def,1),map (mapSnd length) alts) , convAlts def alts)
> makeFunctorStruct _ = error "BuiltinInstances.makeFunctorStruct: impossible: not a DataDef"

> convAlts :: ConID -> [(ConID, [Type])] -> Func
> convAlts def alts = foldr1 plus (map (convProd def . snd) alts)
>   where x `plus` y = TCon "+" :@@: x :@@: y

> convProd :: ConID -> [Type] -> Func
> convProd _   [] = TCon "Empty" 
> convProd def ts = foldr1 prodFunctor (map (convType def) ts)

> prodFunctor :: Func -> Func -> Func
> prodFunctor f g = TCon "*" :@@: f :@@: g

> convType :: ConID -> Type -> Func
> convType _   (TVar _) = TCon "Par" -- indexed if multiple params
> convType _   t | isConstantType t = TCon "Const" :@@: t
> convType def (TCon con :@@: TVar _)
>   | con == def = TCon "Rec"
> convType def t | isTupleCon tup   = convProd def ts
>      where (TCon tup:ts) = spineWalkType t
> convType def (TCon con :@@: t)    = 
>    TCon "@" :@@: TCon con :@@: convType def t
> convType def _ = error ("BuiltinInstances.convType: Can't calculate FunctorOf "++ def ++" as the type is not regular enough.")

> isConstantType :: Type -> Bool
> isConstantType = null . typeVars

> typeVars :: Type -> [VarID]
> typeVars = cataType ((:[]),const [],(++))

\end{verbatim}
Far too many bad functors get through this a the moment.

