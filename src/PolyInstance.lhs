\chapter{Generating Haskell code} 

Instead of generating instances of each polytypic call as was done in the
original design, we generate the following:

\begin{itemize}
	\item A FunctorOf instance for each datatype, defining inn and out.
	\item A class P\_{\em poly} for each {\tt polytypic} definition {\em poly}.
	\item Instances to P\_{\em poly} for each functor in the polytypic case expression.
\end{itemize}

Calls to polytypic functions does not change, however the type of polytypic functions
is transformed to match the new set of classes as illustrated below.

cata :: Regular d => (FunctorOf d a b -> b) -> d a -> b
cata f = f . fmap2 id (cata f) . out

becomes

cata :: (FunctorOf f d, P_fmap2 f) => (f a b -> b) -> d a -> b
cata f = f . fmap2 id (cata f) . out

\begin{verbatim}

> module PolyInstance(instantiateProgram) where
> import Env(Env,lookupEnv)
> import Grammar(Eqn'(..),Expr'(..),Type(..),Qualified(..),
>                Literal(..),Eqn,TEqn,Expr,Func,QType,VarID,ConID,
>                PrgTEqns, Context, Qualifier)
> import Folding(cataType,stripTEqn,mapEqn)
> import Functorise(Struct)
> import TypeGraph(simplifyContext)
> import TypeBasis(FuncEnv)
> import InferType(qTypeEval)
> import MyPrelude(mapFst,mapSnd,unique,fMap)
> import PrettyPrinter(pshow,Typelike(..))
> import TypeBasis(TBasis,FuncEnv,TypeEnv,getFuncEnv,getTypeEnv)
> import List(union,(\\),mapAccumL)
> import Monad(mplus)

\end{verbatim} 

The function instantiateProgram takes the parsed PolyP program and generates the
corresponding Haskell program. The name is inherited from the original PolyP code.

\begin{verbatim}

> instantiateProgram :: (TBasis,PrgTEqns) -> [Eqn]

\end{verbatim}
Implementation:
\begin{verbatim}

> instantiateProgram (tbasis,(datadefs,eqnss)) = 
>		datadefs
>		++ functorOfInstances datadefs (getFuncEnv tbasis)
>		++ rewritePolytypicConstructs (getTypeEnv tbasis) (getFuncEnv tbasis) eqnss

\end{verbatim}

For each datatype {\tt functorOfInstances} generates a FunctorOf instance for
the datatype and its functor.

\begin{verbatim}

> functorOfInstances :: [Eqn] -> FuncEnv -> [Eqn]
> functorOfInstances datadefs funcenv = map functorOfInstance datadefs
>	where
>		findFunc conid = maybe err snd $ lookupEnv conid funcenv
>			where err = error $ "PolyInstance.functorOfInstances: No functor for datatype " ++ conid
>		functorOfInstance (DataDef name _ cons _) =
>			Instance [] ("FunctorOf", [func, TCon name]) (innEqn func cons ++ outEqn func cons)
>			where
>				func = realFuncNames (findFunc name)

>				-- Change to real functor names
>				realFuncNames t = case t of
>					TCon "+"			-> TCon "SumF"
>					TCon "*"			-> TCon "ProdF"
>					TCon "Empty"	-> TCon "EmptyF"
>					TCon "Par"		-> TCon "ParF"
>					TCon "Rec"		-> TCon "RecF"
>					TCon "@"			-> TCon "CompF"
>					TCon "Const"	-> TCon "ConstF"
>					f :@@: g			-> realFuncNames f :@@: realFuncNames g
>					_					-> t

>				-- Compute equations for inn and out
>				innEqn f c = map (\(p,e) -> VarBind "inn" Nothing [p] e) $ inn f c
>				outEqn f c = map (\(p,e) -> VarBind "out" Nothing [p] e) $ out f c

>				-- Pattern/result pairs for inn
>				inn _ []				= []
>				inn func (c:cs)	= case func of
>					TCon "SumF" :@@: f :@@: g	-> mapFst inLeft (inn' (prodSpineWalk f) c) : map (mapFst inRight) (inn g cs)
>					_									-> [inn' (prodSpineWalk func) c]

>				-- Pattern and result for one constructor case
>				inn' fs (con, _)	=	let (ps,es) = inn'' fs varNames in
>											(foldr1 (\f g -> (Con "ProdF" :@: f) :@: g) ps, foldl1 (:@:) $ Con con:es)

>				-- Takes a list of constructor arguments and computes pattern and result arguments
>				inn'' (TCon "EmptyF":fs) names	= addP (Con "EmptyF") $ inn'' fs names
>				inn'' (TCon "ParF":fs) (n:names)	= addPE (Con "ParF" :@: Var n) (Var n) $ inn'' fs names
>				inn'' (TCon "RecF":fs) (n:names)	= addPE (Con "RecF" :@: Var n) (Var n) $ inn'' fs names
>				inn'' ((TCon "CompF" :@@: d :@@: g):fs) (n:names)
>					= addPE (Con "CompF" :@: Var n) (Var "gmap" :@: unF g :@: Var n) $ inn'' fs names
>				inn'' ((TCon "ConstF" :@@: t):fs) (n:names)
>					= addPE (Con "ConstF" :@: Var n) (Var n) $ inn'' fs names
>				inn'' []	_ = ([],[])

>				-- Pattern/result pairs for out
>				out _ []				= []
>				out func (c:cs)	= case func of
>					TCon "SumF" :@@: f :@@: g	-> mapSnd inLeft (out' (prodSpineWalk f) c) : map (mapSnd inRight) (out g cs)
>					_									-> [out' (prodSpineWalk func) c]

>				-- Pattern and result for one constructor case
>				out' fs (con, _)	=	let (ps,es) = out'' fs varNames in
>											(foldl1 (:@:) $ Con con:ps, foldr1 (\f g -> (Con "ProdF" :@: f) :@: g) es)

>				-- Takes a list of constructor arguments and computes pattern and result arguments
>				out'' (TCon "EmptyF":fs) names	= addE (Con "EmptyF") $ out'' fs names
>				out'' (TCon "ParF":fs) (n:names)	= addPE (Var n) (Con "ParF" :@: Var n) $ out'' fs names
>				out'' (TCon "RecF":fs) (n:names)	= addPE (Var n) (Con "RecF" :@: Var n) $ out'' fs names
>				out'' ((TCon "CompF" :@@: d :@@: g):fs) (n:names)
>					= addPE (Var n) (Con "CompF" :@: (Var "gmap" :@: nuF g :@: Var n)) $ out'' fs names
>				out'' ((TCon "ConstF" :@@: t):fs) (n:names)
>					= addPE (Var n) (Con "ConstF" :@: Var n) $ out'' fs names
>				out'' []	_ = ([],[])

>				-- Helpers
>				unF (TCon "ParF") = Var "unParF"
>				unF (TCon "RecF") = Var "unRecF"
>				unF (TCon "ConstF") = Var "unConstF"
>				unF (TCon "CompF" :@@: d :@@: g) = Var "." :@: (Var "gmap" :@: unF g) :@: Var "unCompF"

>				nuF (TCon "ParF") = Con "ParF"
>				nuF (TCon "RecF") = Con "RecF"
>				nuF (TCon "ConstF") = Con "ConstF"
>				nuF (TCon "CompF" :@@: d :@@: g) = Var "." :@: Con "CompF" :@: (Var "gmap" :@: nuF g)

>				addP p = mapFst (p:)
>				addE e = mapSnd (e:)
>				addPE p e = (p:) -*- (e:)

>				inLeft = (Con "InL" :@:)
>				inRight = (Con "InR" :@:)

>				prodSpineWalk (TCon "ProdF" :@@: f :@@: g) = f : prodSpineWalk g
>				prodSpineWalk f = [f]

> -- Should be in this file but I didn't want to change the other files.
> (f -*- g) (a,b) = (f a, g b)

> -- Infinite list of variable names
> varNames = let names = "" : [ s ++ [c] | s <- names, c <- ['a'..'z']] in tail names

\end{verbatim}

{\tt rewritePolytypicConstructs} rewrites {\tt polytypic} definitions to
a class and instances for each branch in the polytypic case. It also calculates
the correct types and constraints for polytypic functions.

\begin{verbatim}

> type PolyEnv = Env VarID QType

> rewritePolytypicConstructs :: TypeEnv -> FuncEnv -> [[TEqn]] -> [Eqn]
> rewritePolytypicConstructs typeenv funcenv teq
>		= evalContexts funcenv $ concatMap (rewrite polyenv) (concat treqs)
>	where

>		-- Calculate the types of polytypic functions (polyenv) and a correctly
>		-- annotaded set of equations (treqs)
>		(polyenv, treqs) = mapAccumL	(curry contextify)
>												(createPolyEnv (findPolys $ concat teq) typeenv)
>												(map translateEqns teq)
>		contextify (env, eqns)
>			| env == env'	= (env', eqns')
>			| otherwise		= contextify (env', eqns')
>			where
>				(env', eqns') = mapAccumL annotate env eqns

>		-- Pick out the name of all polytypic constructs
>		findPolys (eqn:eqns) = case eqn of
>			Polytypic name _ _ _	-> name : findPolys eqns
>			_							-> findPolys eqns
>		findPolys [] = []

>		-- Equation simplification
>		simp = simplifyTEqn funcenv . stripTEqn

>		-- Rewrite an equation
>		rewrite polyenv (Polytypic name tipe@(_ :=> tipe') (_ :=> var) alts) = classdef : instances
>			where

>				-- Doesn't work if it is a polytypic operator
>				className = "P_" ++ name

>				-- The class definition
>				classdef = Class [] (className, [var]) [ExplType [name] $ removeThisClass tipe]

>				-- We don't want this class to be in the constraints (I guess it doesn't
>				-- really matter but for aestethical reasons).
>				removeThisClass (qs :=> t) = filter ((/=className).fst) qs :=> t

>				-- The instances
>				instances = map buildInstance alts

>				-- Build an instance from a polytypic case branch
>				buildInstance (c :=> t, e) = let c :=> _ = inferQType polyenv e in
>					case t of
>						TCon "+"	:@@: f :@@: g ->
>							Instance c
>										(className, [TVar "SumF" :@@: f :@@: g])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "sumEP")) :@: e]
>						TCon "*"	:@@: f :@@: g ->
>							Instance c
>										(className, [TVar "ProdF" :@@: f :@@: g])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "prodEP")) :@: e]
>						TCon "Empty" ->
>							Instance c
>										(className, [TCon "EmptyF"])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "emptyEP")) :@: e]
>						TCon "Par" ->
>							Instance c
>										(className, [TCon "ParF"])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "parEP")) :@: e]
>						TCon "Rec" ->
>							Instance c
>										(className, [TCon "RecF"])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "recEP")) :@: e]
>						TCon "@" :@@: d :@@: g ->
>							Instance c
>										(className, [TCon "CompF" :@@: d :@@: g])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "compEP")) :@: e]
>						TCon "Const" :@@: t ->
>							Instance c
>										(className, [TCon "ConstF" :@@: t])
>										[simp $ VarBind name Nothing []
>													$ (Var "to" :@: convert tipe' var (Var "constEP")) :@: e]
>						_	-> error ("PolyInstance.rewrite: " ++ pshow e ++ ":: " ++ pshow (c :=> t))

\end{verbatim}

Since functors in the case branches are only type synonyms ({\tt type Par p
r = p}) and we want to generate an instances for the actual functor (\{\tt
ParF}) we have to transform the branch body so that it gets the right type.
{\tt convert} generates this translation function (as an EP).

\begin{verbatim}

>				convert t var ep = case t of
>					TCon "->" :@@: f :@@: g
>							-> case (convert f var ep, convert g var ep) of
>									(Var "idEP", Var "idEP")	-> Var "idEP"
>									(epF, epG)						-> Var "funEP" :@: epF :@: epG
>					f :@@: _ :@@: _ | f == var
>							-> ep
>					_		-> Var "idEP"

>		rewrite _ eq = [simp eq]

\end{verbatim}

{\tt createPolyEnv} collects the polytypic functions from a type
environment in a new environment. It also uses the translateX functions to
translates the types to use the generated Haskell classes as follows:

\begin{verbatim}
fpoly :: Poly f => t
==> fpoly :: P_fpoly f => t  (when fpoly is a polytypic definition)

poly :: Poly (FunctorOf d) => t[FunctorOf d]
==> poly :: FunctorOf functorOf_d d => t[functorOf_d]
\end{verbatim}

Instead of generating a fresh variable (which of course would be best), we
generate a variable name from the type {\tt d} that is unique in every case.

\begin{verbatim}

> createPolyEnv :: [VarID] -> TypeEnv -> PolyEnv
> createPolyEnv polys = foldr contextEnv []
>	where
>		contextEnv (v,t) env
>			| isPoly t	= (v, translateQType polys v t) : env
>			| otherwise	= env
>		isPoly (c :=> _) = any ((=="Poly").fst) c

> -- Translate a qualified type
> translateQType polys v (c :=> t) = translateContext polys v c :=> translateType t

> -- Translate a type context
> translateContext polys v = concatMap (translateQ polys v)

> -- Translate a constraint
> translateQ polys v ("Poly", [f]) = case checkFOf f of
>		Just d						-> [("FunctorOf", [fOfVar d, d])]
>		Nothing	| elem v polys	-> [("P_" ++ v, [f])]
>					| otherwise		-> []
> translateQ _ v q = [q]

> -- Translate a type
> translateType t = case t of
>		TCon "FunctorOf" :@@: d	-> fOfVar d
>		a :@@: b						-> translateType a :@@: translateType b
>		_								-> t

> -- The variable name for FunctorOf d
> fOfVar d = TVar $ "functorOf_" ++ encode d

> -- Encode a type using only alpha numerics, _ and '
> encode t = case t of
>		TVar v			-> v
>		TCon "[]"		-> "List"
>		TCon ('(':xs)	-> "Tuple" ++ show (length xs)
>		TCon "->"		-> "Fun"
>		TCon c			-> c
>		f :@@: g			-> "'" ++ encode f ++ "_" ++ encode g ++ "'"

> -- Translate a list of equations
> translateEqns :: [Eqn] -> [Eqn]
> translateEqns = concatMap translateEqn
>	where

>		-- Translate an equation
>		translateEqn eqn = case eqn of
>			VarBind name mt ps e			-> [VarBind
>														name
>														(fmap (translateQType [] name) mt)
>														(map translateExpr ps)
>														(translateExpr e)]
>			Polytypic name t var alts	-> [Polytypic
>														name
>														(translateQType [] name t)
>														var
>														(map (mapSnd translateExpr) alts)]
>			ExplType vs t					-> map (\v -> ExplType [v] (translateQType [] v t)) vs
>			Class ctx cls eqns			-> [Class
>														(translateContext [] "Error" ctx)
>														cls
>														(translateEqns eqns)]
>			Instance ctx cls eqns		-> [Instance
>														(translateContext [] "Error" ctx)
>														cls
>														(translateEqns eqns)]
>			_									-> [eqn]

>		-- Translate an expression
>		translateExpr expr = case expr of
>			Typed (Var v) t		-> Typed (Var v) (translateQType [] v t)
>			f :@: e					-> translateExpr f :@: translateExpr e
>			Lambda e e'				-> Lambda (translateExpr e) (translateExpr e')
>			Case e alts				-> Case (translateExpr e) (map (translateExpr -*- translateExpr) alts)
>			Letrec eqnss e			-> Letrec (map translateEqns eqnss) (translateExpr e)
>			_							-> expr

\end{verbatim}

We use type inference (very simple since the entire program is annotated
with types) to infer the correct constraints on polytypic functions. The
core is the {\tt mergeContexts} functions that, when we find a (type
annotated) call to a polytypic function merges the given type with the type
found in the PolyEnv.

The function {\tt annotate} infers and updates the type of variable
bindings and if it is a binding of a polytypic variable, updates the
PolyEnv.

\begin{verbatim}

> -- Update types of variable bindings and PolyEnv
> annotate env eqn = case eqn of
>		VarBind v _ p e		-> let t = inferQType env $ foldr Lambda e p
>										in (update v t env, VarBind v (Just t) p e)
>		_							-> (env, eqn)
>	where
>		update v t ((v',t'):env)
>			| v == v'	= (v',t):env
>			| otherwise	= (v',t'):update v t env
>		update _ _ [] = []

> -- Infer the type of an expression
> inferQType :: PolyEnv -> Expr' QType -> QType
> inferQType env t = case t of
>		Typed (Var v) t		-> maybe t (\t' -> mergeContexts t' t) $ lookupEnv v env
>		Typed _ t				-> t
>		f :@: e					-> case (inferQType env f, inferQType env e) of
>			(c1 :=> (TCon "->" :@@: a :@@: b), c2 :=> a') -- | a == a'
>												-> union c1 c2 :=> b
>				-- | otherwise					-> error $ pshow (f:@:e) ++ pshow a ++ " != " ++ pshow a'
>		Lambda e e'				-> case (inferQType env e, inferQType env e') of
>			(_ :=> a, c :=> b)			-> c :=> TCon "->" :@@: a :@@: b
>		Literal (IntLit _)	-> [] :=> TCon "Int"
>		Literal (FloatLit _)	-> [] :=> TCon "Float"
>		Literal (BoolLit _)	-> [] :=> TCon "Bool"
>		Literal (CharLit _)	-> [] :=> TCon "Char"
>		Literal (StrLit _)	-> [] :=> TCon "String"
>		Letrec eqnss e			-> case inferQType env e of
>			c :=> t							-> union c
>													(	foldr union []
>														$ map (inferContextEqn env)
>														$ concat eqnss
>													) :=> t
>		Case e alts				-> foldr1 (\(c1 :=> t) (c2 :=> _) -> c1 `union` c2 :=> t)
>										$ map (inferQType env . snd) alts
>		-- Should be a fresh type variable
>		WildCard					-> [] :=> TVar "dummy"
>		_							-> error $ "Cannot infer type of " ++ pshow t

> -- Infer constraints arising from let bindings (not implemented)
> inferContextEqn :: PolyEnv -> Eqn' QType -> [Qualifier Type]
> inferContextEqn env eqn = case eqn of
>		_		-> []

> -- Merge the explicit type and type found in the PolyEnv for a polytypic
> -- function.
> mergeContexts :: QType -> QType -> QType
> mergeContexts g@(gc :=> gt) s@(sc :=> st) = c :=> st
>	where
>		c = union sc (map spec gc)
>		spec (cls, ts) = (cls, map lookupT ts)
>		lookupT t = maybe (fOfLookup t) id $ lookupT' gt st t
>		lookupT' gt st t
>			| t == gt	= case checkFOf st of
>				Nothing	-> Just st
>				_			-> error "Panic"
>			| otherwise	= case (gt, st) of
>				(t1 :@@: t1', t2 :@@: t2')	-> lookupT' t1 t2 t `mplus` lookupT' t1' t2' t
>				_									-> Nothing
>		fOfLookup f = maybe (error $ "Panic2:\n" ++ show g ++ show s ++ show f) id $ do
>			d	<- findFOf gc f
>			d'	<- lookupT' gt st d
>			fOfFind sc d'
>		findFOf (("FunctorOf", [f', d]):_) f
>			| f == f'		= Just d
>		findFOf (q:c) f	= findFOf c f
>		findFOf [] _		= Nothing
>		fOfFind (("FunctorOf", [f, d']):_) d
>			| d == d'		= Just f
>		fOfFind (q:c) d	= fOfFind c d
>		fOfFind [] _		= Nothing

\end{verbatim}

When a polytypic function is called on a specific datatype, the inference
above might infer constraints like {\tt FunctorOf a []}. Since the
FunctorOf class contains a functional dependency saying that the type
determines the functor, we know in this case that {\tt a} must be
{\tt SumF EmptyF (ProdF ParF RecF)}. {\tt evalContexts} makes use of this
dependency to remove unneccessary type variables from contexts.

\begin{verbatim}

> evalContexts :: FuncEnv -> [Eqn] -> [Eqn]
> evalContexts funcenv = map evalContextEqn
>	where
>		evalContextEqn eqn = case eqn of
>			VarBind name (Just t) ps e -> simplifyTEqn funcenv $ VarBind name (Just $ evalContextType t) ps e
>			_									-> eqn
>		evalContextType (c :=> t) = substQType (findSubsts c) (c :=> t)
>			where
>				findSubsts (("FunctorOf", [TVar f,TCon d]):c) = case lookupEnv d funcenv of
>					Just (_,f')	-> (f,f'):findSubsts c
>					Nothing		-> findSubsts c
>				findSubsts (q:c) = findSubsts c
>				findSubsts [] = []

\end{verbatim}

We keep simplification of equations from the original file.

\begin{verbatim}

> simplifyTEqn :: FuncEnv -> TEqn -> TEqn
> simplifyTEqn = mapEqn . simplifyQType

> simplifyQType :: FuncEnv -> QType -> QType
> simplifyQType funcenv = simplifyContext 
>                       . qTypeEval funcenv

\end{verbatim}

And substitution over type is nice to have as well.

\begin{verbatim}

> type Subst = Env VarID Type

> appSubst :: (VarID->Type) -> Type -> Type
> appSubst s = cataType (s, TCon, (:@@:)) 

> substQType :: Subst -> QType -> QType
> substQType env = fMap (appSubst s)
>   where s v = maybe (TVar v) id (lookupEnv v env)

\end{verbatim}
