> module Functorise(makeFunctorStruct,makeFunctorStruct',Struct) where
> import Grammar(ConID,VarID,Eqn,Eqn'(DataDef),Func,
>		 Type(..),spineWalkType,isTupleCon)
> import MyPrelude(mapSnd,pair)
> import Folding(cataType)
> import MonadLibrary(foreach,(<@),Error,handleError,ErrorMonad(..))

\section{Extracting functors from {\tt data}-definitions} 
For every regular datatype we need the functor that represents its
recursive structure: {\tt D} == {\tt Mu fD}.

Preliminary version: Works for exactly one type parameter and not with
any structure on the right hand side.

The type {\tt Struct} represents the top level structure of the
datatype definition: 
\begin{verbatim}

#if 0
> makeFunctor :: Eqn -> Func
> makeFunctor = snd . makeFunctorStruct
#endif

> type PList a = (a,[a])
> type Struct = PList (ConID,Int)

\end{verbatim}

*** Triples and beyond should probably be translated to nested pairs
in inn, out, or forbidden below.

\begin{verbatim}

> makeFunctorStruct :: Eqn -> (Struct,Func)
> makeFunctorStruct = handleError err . makeFunctorStruct'
>   where err s = error ("Functorise.makeFunctorStruct: not a regular datatype:\n  "++s)

> makeFunctorStruct' :: Eqn -> Error (Struct,Func)
> makeFunctorStruct' (DataDef def args alts _) | arity == 1
>   = convAlts def alts <@ pair ((def,arity),map (mapSnd length) alts)
>					       | otherwise
>   = failEM (def++" is not Regular as only 1-parameter datatypes are Regular")
>   where arity = length args
> makeFunctorStruct' _ = error "Functorise.makeFunctorStruct: impossible: not a DataDef"

> convAlts :: ConID -> [(ConID, [Type])] -> Error Func
> convAlts def []   = failEM "An empty sum type is illegal"
> convAlts def alts = foreach alts (convProd def . snd) <@ foldr1 sumFunctor

> convProd :: ConID -> [Type] -> Error Func
> convProd _   [] = return (TCon "Empty")
> convProd def ts = foreach ts (convType def) <@ foldr1 prodFunctor

> convType :: ConID -> Type -> Error Func
> convType _   (TVar _)          = return parFunctor -- indexed if multiple params
> convType _   t 
>   | isConstantType t		 = return (constFunctor t)
> convType def (TCon con :@@: TVar _)
>   | con == def		 = return recFunctor
> convType def t 
>   | isTupleCon tup             = convProd def ts
>      where (TCon tup:ts) = spineWalkType t
> convType def (TCon con :@@: t) = convType def t <@ applyFunctor con
>   
> convType def _ = failEM ("Can't calculate FunctorOf "++ def ++" as the type is not regular enough.")

> parFunctor, recFunctor :: Func
> parFunctor = TCon "Par"
> recFunctor = TCon "Rec"

> constFunctor :: Type -> Func
> constFunctor t = TCon "Const" :@@: t

> sumFunctor :: Func -> Func -> Func
> sumFunctor x y = TCon "+" :@@: x :@@: y

> applyFunctor :: ConID -> Func -> Func
> applyFunctor d f = TCon "@" :@@: TCon d :@@: f

> prodFunctor :: Func -> Func -> Func
> prodFunctor f g = TCon "*" :@@: f :@@: g

> isConstantType :: Type -> Bool
> isConstantType = null . typeVars

> typeVars :: Type -> [VarID]
> typeVars = cataType ((:[]),const [],(++))

\end{verbatim}
Far too many bad functors get through this a the moment.

