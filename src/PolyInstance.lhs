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
> import List(union,(\\),mapAccumL,nub,groupBy,sortBy)
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
>     datadefs
>     ++ functorOfInstances datadefs funcenv
>     ++ rewritePolytypicConstructs (getTypeEnv tbasis) funcenv eqnss
>  where funcenv = realFuncEnv $ getFuncEnv tbasis

\end{verbatim}

We need to translate the functors in the functor environment to the real functors
from the sugared versions used in the PolyP code (+ -> SumF, * -> ProdF, ...)

\begin{verbatim}

> realFuncEnv :: FuncEnv -> FuncEnv
> realFuncEnv funcenv = map (mapSnd $ mapSnd realFuncNames) funcenv
>
> -- Change to real functor names
> realFuncNames t = case t of
>              TCon "+"       -> TCon "SumF"
>              TCon "*"       -> TCon "ProdF"
>              TCon "Empty"   -> TCon "EmptyF"
>              TCon "Par"     -> TCon "ParF"
>              TCon "Rec"     -> TCon "RecF"
>              TCon "@"       -> TCon "CompF"
>              TCon "Const"   -> TCon "ConstF"
>              TCon ">"       -> TCon "FunF"
>              f :@@: g       -> realFuncNames f :@@: realFuncNames g
>              _              -> t

\end{verbatim}

For each datatype {\tt functorOfInstances} generates a FunctorOf instance for
the datatype and its functor.

\begin{verbatim}

> functorOfInstances :: [Eqn] -> FuncEnv -> [Eqn]
> functorOfInstances datadefs funcenv = concatMap functorOfInstance datadefs
>  where
>     findFunc conid = maybe [] ((:[]).snd) $ lookupEnv conid funcenv
>        where err = error $ "PolyInstance.functorOfInstances: No functor for datatype " ++ conid
>     functorOfInstance (DataDef name _ cons _) = case findFunc name of
>        []       -> []
>        [func]   -> [ Instance [] ("FunctorOf", [func, TCon name]) (innEqn func cons
>                                               ++ outEqn func cons
>                                               ++ dataName name
>                                               ++ constrName cons
>                                )]
>        where

>           -- Compute equations for datatypeName and constructorName
>           dataName name = [VarBind "datatypeName" Nothing [] $ Var "const" :@: Literal (StrLit name)]
>           constrName cons = map conName cons
>              where
>                 conName (conid, ts) = VarBind "constructorName"
>                                               Nothing
>                                               [foldl (\p _ -> p :@: WildCard) (Con conid) ts]
>                                               $ Literal (StrLit conid)

>           -- Compute equations for inn and out
>           innEqn f c = map (\(p,e) -> VarBind "inn" Nothing [p] e) $ inn f c
>           outEqn f c = map (\(p,e) -> VarBind "out" Nothing [p] e) $ out f c

>           -- Pattern/result pairs for inn
>           inn _ []          = []
>           inn func (c:cs)   = case func of
>              TCon "SumF" :@@: f :@@: g  -> mapFst inLeft (inn' (prodSpineWalk f) c) : map (mapFst inRight) (inn g cs)
>              _                          -> [inn' (prodSpineWalk func) c]

>           -- Pattern and result for one constructor case
>           inn' fs (con, _)  =  let (ps,es) = inn'' fs varNames in
>                                (foldr1 (\f g -> (Con ":*:" :@: f) :@: g) ps, foldl1 (:@:) $ Con con:es)

>           -- Takes a list of constructor arguments and computes pattern and result arguments
>           inn'' (TCon "EmptyF":fs) names   = addP (Con "EmptyF") $ inn'' fs names
>           inn'' (c:fs) (n:names)          = addPE (Var n) (fromFunction c :@: Var n) $ inn'' fs names

           inn'' (TCon "ParF":fs) (n:names) = addPE (Con "ParF" :@: Var n) (Var n) $ inn'' fs names
           inn'' (TCon "RecF":fs) (n:names) = addPE (Con "RecF" :@: Var n) (Var n) $ inn'' fs names
           inn'' ((TCon "CompF" :@@: d :@@: g):fs) (n:names)
              = addPE (Con "CompF" :@: Var n) (Var "gmap" :@: unF g :@: Var n) $ inn'' fs names
           inn'' ((TCon "ConstF" :@@: t):fs) (n:names)
              = addPE (Con "ConstF" :@: Var n) (Var n) $ inn'' fs names
            inn'' ((TCon "FunF" :@@: f :@@: g):fs) (n:names) = addPE (Con "FunF" :@: Var n) (Var n) $ inn'' fs names

>           inn'' [] _ = ([],[])
>           inn'' (x:fs) _ = error $ "inn'' applied to " ++ show x

>           -- Pattern/result pairs for out
>           out _ []          = []
>           out func (c:cs)   = case func of
>              TCon "SumF" :@@: f :@@: g  -> mapSnd inLeft (out' (prodSpineWalk f) c) : map (mapSnd inRight) (out g cs)
>              _                          -> [out' (prodSpineWalk func) c]

>           -- Pattern and result for one constructor case
>           out' fs (con, _)  =  let (ps,es) = out'' fs varNames in
>                                (foldl1 (:@:) $ Con con:ps, foldr1 (\f g -> (Con ":*:" :@: f) :@: g) es)

>           -- Takes a list of constructor arguments and computes pattern and result arguments
>           out'' (TCon "EmptyF":fs) names   = addE (Con "EmptyF") $ out'' fs names
>           out'' (c:fs) (n:names)           = addPE (Var n) (toFunction c :@: Var n) $ out'' fs names

           out'' (TCon "ParF":fs) (n:names) = addPE (Var n) (Con "ParF" :@: Var n) $ out'' fs names
           out'' (TCon "RecF":fs) (n:names) = addPE (Var n) (Con "RecF" :@: Var n) $ out'' fs names
           out'' ((TCon "CompF" :@@: d :@@: g):fs) (n:names)
              = addPE (Var n) (Con "CompF" :@: (Var "gmap" :@: nuF g :@: Var n)) $ out'' fs names
           out'' ((TCon "ConstF" :@@: t):fs) (n:names)
              = addPE (Var n) (Con "ConstF" :@: Var n) $ out'' fs names

>           out'' [] _ = ([],[])

>           -- Remodelling

>           -- toFunction : g --> toG
>           toFunction (TCon "ParF")                = Var "toPar"
>           toFunction (TCon "RecF")                = Var "toRec"
>           toFunction (TCon "CompF" :@@: _ :@@: g) = Var "toComp" :@: toFunction g
>           toFunction (TCon "ConstF" :@@: _)       = Var "toConst"
>           toFunction (TCon "FunF" :@@: g :@@: h)  = Var "toFun" :@: fromFunction g
>                                                                 :@: toFunction h

>           -- fromFunction : g --> fromG
>           fromFunction (TCon "ParF")                  = Var "fromPar"
>           fromFunction (TCon "RecF")                  = Var "fromRec"
>           fromFunction (TCon "CompF" :@@: _ :@@: g)   = Var "fromComp" :@: fromFunction g
>           fromFunction (TCon "ConstF" :@@: _)         = Var "fromConst"
>           fromFunction (TCon "FunF" :@@: g :@@: h)    = Var "fromFun" :@: toFunction g
>                                                                       :@: fromFunction h

>           -- Helpers
>           unF (TCon "ParF") = Var "unParF"
>           unF (TCon "RecF") = Var "unRecF"
>           unF (TCon "ConstF") = Var "unConstF"
>           unF (TCon "CompF" :@@: d :@@: g) = Var "." :@: (Var "gmap" :@: unF g) :@: Var "unCompF"

>           nuF (TCon "ParF") = Con "ParF"
>           nuF (TCon "RecF") = Con "RecF"
>           nuF (TCon "ConstF") = Con "ConstF"
>           nuF (TCon "CompF" :@@: d :@@: g) = Var "." :@: Con "CompF" :@: (Var "gmap" :@: nuF g)

>           addP p = mapFst (p:)
>           addE e = mapSnd (e:)
>           addPE p e = (p:) -*- (e:)

>           inLeft = (Con "InL" :@:)
>           inRight = (Con "InR" :@:)

>           prodSpineWalk (TCon "ProdF" :@@: f :@@: g) = f : prodSpineWalk g
>           prodSpineWalk f = [f]

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
>     = evalContexts funcenv $ concatMap (rewrite polyenv) (concat treqs)
>  where

>     -- Calculate the types of polytypic functions (polyenv) and a correctly
>     -- annotaded set of equations (treqs)
>     (polyenv, treqs) = mapAccumL  (curry contextify)
>                                   (createPolyEnv funcenv (findPolys $ concat teq) typeenv)
>                                   (map (translateEqns funcenv) teq)
>     contextify (env, eqns)
>        | env == env'  = (env', eqns')
>        | otherwise    = contextify (env', eqns')
>        where
>           (env', eqns') = mapAccumL annotate env eqns

>     -- Pick out the name of all polytypic constructs
>     findPolys (eqn:eqns) = case eqn of
>        Polytypic name _ _ _ -> name : findPolys eqns
>        _                    -> findPolys eqns
>     findPolys [] = []

>     -- Equation simplification
>     simp = simplifyTEqn funcenv . stripTEqn

>     -- Rewrite an equation
>     rewrite polyenv (Polytypic name tipe@(_ :=> tipe') (_ :=> var) alts) = classdef : instances
>        where

>           -- Doesn't work if it is a polytypic operator
>           className = "P_" ++ name

>           -- The class definition
>           classdef = Class [] (className, [var]) [ExplType [name] $ removeThisClass tipe]

>           -- We don't want this class to be in the constraints (I guess it doesn't
>           -- really matter but for aestethical reasons).
>           removeThisClass (qs :=> t) = filter ((/=className).fst) qs :=> t

>           -- The instances
>           instances = map buildInstance $ expandBranches alts

>           -- Expand default alternatives (not implemented)
>           expandBranches = id

>           -- Build an instance from a polytypic case branch
>           buildInstance (c :=> t, e) = let c :=> _ = inferQType polyenv e in
>               let t' = realFuncNames t in
>                   Instance c (className, [t'])
>                       [ simp $ VarBind name Nothing [] e ]

              case t of
                 TCon "+" :@@: f :@@: g ->
                    Instance c
                             (className, [TCon "SumF" :@@: f :@@: g])
                             [simp $ VarBind name Nothing [] e]
                 TCon "*" :@@: f :@@: g ->
                    Instance c
                             (className, [TCon "ProdF" :@@: f :@@: g])
                             [simp $ VarBind name Nothing [] e]
                 TCon "Empty" ->
                    Instance c
                             (className, [TCon "EmptyF"])
                             [simp $ VarBind name Nothing [] e]
                 TCon "Par" ->
                    Instance c
                             (className, [TCon "ParF"])
                             [simp $ VarBind name Nothing [] e]
                 TCon "Rec" ->
                    Instance c
                             (className, [TCon "RecF"])
                             [simp $ VarBind name Nothing [] e]
                 TCon "@" :@@: d :@@: g ->
                    Instance c
                             (className, [TCon "CompF" :@@: d :@@: g])
                             [simp $ VarBind name Nothing [] e]
                 TCon "Const" :@@: t ->
                    Instance c
                             (className, [TCon "ConstF" :@@: t])
                             [simp $ VarBind name Nothing [] e]
                 TCon ">" :@@: f :@@: g ->
                    Instance c
                             (className, [TCon "FunF" :@@: f :@@: g])
                             [simp $ VarBind name Nothing [] e]
                 _  -> error ("PolyInstance.rewrite: " ++ pshow e ++ ":: " ++ pshow (c :=> t))

\end{verbatim}

Since functors in the case branches are only type synonyms ({\tt type Par p
r = p}) and we want to generate an instances for the actual functor (\{\tt
ParF}) we have to transform the branch body so that it gets the right type.
{\tt convert} generates this translation function (as an EP).

\begin{verbatim}

           convert t var ep = case t of
              TCon "->" :@@: f :@@: g
                    -> case (convert f var ep, convert g var ep) of
                          (Var "idEP", Var "idEP")   -> Var "idEP"
                          (epF, epG)                 -> Var "funEP" :@: epF :@: epG
              f :@@: _ :@@: _ | f == var
                    -> ep
              _     -> Var "idEP"

>     rewrite _ eq = [simp eq]

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

> createPolyEnv :: FuncEnv -> [VarID] -> TypeEnv -> PolyEnv
> createPolyEnv funcenv polys = foldr contextEnv []
>  where
>     contextEnv (v,t) env
>        | isPoly t  = (v, translateQType funcenv polys v t) : env
>        | otherwise = env
>     isPoly (c :=> _) = any ((=="Poly").fst) c

> -- Translate a qualified type
> translateQType funcenv polys v (c :=> t) = translateContext funcenv polys v c :=> translateType funcenv t

> -- Translate a type context
> translateContext funcenv polys v = map (translateQ' funcenv) . concatMap (translateQ funcenv polys v)

> -- Translate FunctorOf a => functorOf_a in contexts
> translateQ' funcenv (c, ts) = (c, map (translateType funcenv) ts)

> -- Translate a constraint
> translateQ funcenv polys v ("Poly", [f]) = case checkFOf f of
>     Just d                  -> [("FunctorOf", [fOfVar d, d])]
>     Nothing  | elem v polys -> [("P_" ++ v, [f])]
>              | otherwise    -> []
> translateQ funcenv _ v q = [q]

> -- Translate a type
> translateType funcenv t = case t of
>     TCon "FunctorOf" :@@: d@(TCon c)  -> maybe (fOfVar d) snd $ lookupEnv c funcenv
>     TCon "FunctorOf" :@@: d       -> fOfVar d
>     a :@@: b                      -> translateType funcenv a :@@: translateType funcenv b
>     _                             -> t

> -- The variable name for FunctorOf d
> fOfVar d = TVar $ "functorOf_" ++ encode d

> -- Encode a type using only alpha numerics, _ and '
> encode t = case t of
>     TVar v         -> v
>     TCon "[]"      -> "List"
>     TCon ('(':xs)  -> "Tuple" ++ show (length xs)
>     TCon "->"      -> "Fun"
>     TCon c         -> c
>     f :@@: g       -> "'" ++ encode f ++ "_" ++ encode g ++ "'"

> -- Translate a list of equations
> translateEqns :: FuncEnv -> [Eqn] -> [Eqn]
> translateEqns funcenv = concatMap (translateEqn funcenv)
>  where

>     -- Translate an equation
>     translateEqn funcenv eqn = case eqn of
>        VarBind name mt ps e       -> [VarBind
>                                         name
>                                         (fmap (translateQType funcenv [] name) mt)
>                                         (map (translateExpr funcenv) ps)
>                                         (translateExpr funcenv e)]
>        Polytypic name t var alts  -> [Polytypic
>                                         name
>                                         (translateQType funcenv [] name t)
>                                         var
>                                         (map (mapSnd $ translateExpr funcenv) alts)]
>        ExplType vs t              -> map (\v -> ExplType [v] (translateQType funcenv [] v t)) vs
>        Class ctx cls eqns         -> [Class
>                                         (translateContext funcenv [] "Error" ctx)
>                                         cls
>                                         (translateEqns funcenv eqns)]
>        Instance ctx cls eqns      -> [Instance
>                                         (translateContext funcenv [] "Error" ctx)
>                                         cls
>                                         (translateEqns funcenv eqns)]
>        _                          -> [eqn]

>     -- Translate an expression
>     translateExpr funcenv expr = case expr of
>        Typed (Var v) t      -> Typed (Var v) (translateQType funcenv [] v t)
>        f :@: e              -> translateExpr funcenv f :@: translateExpr funcenv e
>        Lambda e e'          -> Lambda (translateExpr funcenv e) (translateExpr funcenv e')
>        Case e alts          -> Case (translateExpr funcenv e) (map (translateExpr funcenv -*- translateExpr funcenv) alts)
>        Letrec eqnss e       -> Letrec (map (translateEqns funcenv) eqnss) (translateExpr funcenv e)
>        _                    -> expr

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
>     VarBind v _ p e      -> let t = inferQType env $ foldr Lambda e p
>                             in (update v t env, VarBind v (Just t) p e)
>     _                    -> (env, eqn)
>  where
>     update v t ((v',t'):env)
>        | v == v'   = (v',t):env
>        | otherwise = (v',t'):update v t env
>     update _ _ [] = []

> -- Infer the type of an expression
> inferQType :: PolyEnv -> Expr' QType -> QType
> inferQType env t = case t of
>     Typed (Var v) t      -> maybe t (\t' -> mergeContexts t' t) $ lookupEnv v env
>     Typed _ t            -> t
>     f :@: e              -> case (inferQType env f, inferQType env e) of
>        (c1 :=> (TCon "->" :@@: a :@@: b), c2 :=> a') -- | a == a'
>                                   -> union c1 c2 :=> b
>           -- | otherwise             -> error $ pshow (f:@:e) ++ pshow a ++ " != " ++ pshow a'
>     Lambda e e'          -> case (inferQType env e, inferQType env e') of
>        (_ :=> a, c :=> b)         -> c :=> TCon "->" :@@: a :@@: b
>     Literal (IntLit _)   -> [] :=> TCon "Int"
>     Literal (FloatLit _) -> [] :=> TCon "Float"
>     Literal (BoolLit _)  -> [] :=> TCon "Bool"
>     Literal (CharLit _)  -> [] :=> TCon "Char"
>     Literal (StrLit _)   -> [] :=> TCon "String"
>     Letrec eqnss e       -> case inferQType env e of
>        c :=> t                    -> union c
>                                      (  foldr union []
>                                         $ map (inferContextEqn env)
>                                         $ concat eqnss
>                                      ) :=> t
>     Case e alts          -> foldr (\(c1 :=> t) (c2 :=> _) -> c1 `union` c2 :=> t)
>                             (inferQType env e)
>                             $ map (inferQType env . snd) alts
>     -- TODO: Should be a fresh type variable
>     WildCard             -> [] :=> TVar "dummy"
>     _                    -> error $ "Cannot infer type of " ++ pshow t

> -- Infer constraints arising from let bindings TODO: Buggy?
> inferContextEqn :: PolyEnv -> Eqn' QType -> [Qualifier Type]
> inferContextEqn env eqn = case eqn of
>     VarBind name _ _ e   -> let c :=> _ = inferQType env e in c
>     _                    -> []

> -- Merge the explicit type and type found in the PolyEnv for a polytypic
> -- function.
> mergeContexts :: QType -> QType -> QType
> mergeContexts g@(gc :=> gt) s@(sc :=> st) = c :=> st
>  where
>     c = union sc (map spec gc)
>     spec (cls, ts) = (cls, map lookupT ts)
>     lookupT t = maybe (fOfLookup t) id $ lookupT' gt st t
>     lookupT' gt st t
>        | t == gt   = case checkFOf st of
>           Nothing  -> Just st
>           _        -> error "Panic"
>        | otherwise = case (gt, st) of
>           (t1 :@@: t1', t2 :@@: t2') -> lookupT' t1 t2 t `mplus` lookupT' t1' t2' t
>           _                          -> Nothing
>     fOfLookup f = maybe (error $ "Panic2:\n" ++ show g ++ "\n" ++ show s ++ "\n" ++ show f) id $ do
>        d  <- findFOf gc f
>        d' <- lookupT' gt st d
>        fOfFind sc d'
>     findFOf (("FunctorOf", [f', d]):_) f
>        | f == f'      = Just d
>     findFOf (q:c) f   = findFOf c f
>     findFOf [] _      = Nothing
>     fOfFind (("FunctorOf", [f, d']):_) d
>        | d == d'      = Just f
>     fOfFind (q:c) d   = fOfFind c d
>     fOfFind [] _      = Nothing

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
>  where
>     evalContextEqn eqn = case eqn of
>        VarBind name (Just t) ps e -> simplifyTEqn funcenv $ VarBind name (Just $ simplifyQType $ evalContextType t) ps e
>        Instance cs c eqns         -> Instance (simplifyContext $ concat $ filter (occursIn c) $ groupCtxs cs) c eqns
>        _                          -> eqn
>     evalContextType (c :=> t) = substQType (findSubsts c) (c :=> t)
>        where
>           findSubsts (("FunctorOf", [TVar f,TCon d]):c) = case lookupEnv d funcenv of
>              Just (_,f') -> (f,f'):findSubsts c
>              Nothing     -> findSubsts c
>           findSubsts (q:c) = findSubsts c
>           findSubsts [] = []
>     simplifyContext c = let c' :=> _ = simplifyQType (c :=> undefined) in c'
>     simplifyQType q@(c :=> _) = nub c' :=> t'
>       where
>           fOfs =  concatMap mkSubst
>                   $ filter (\x -> length x > 1)
>                   $ map (nub . map fOf)
>                   $ groupBy eq
>                   $ sortBy cmp
>                   $ filter isFOf c
>           mkSubst (x:xs) = map (\(TVar v) -> (v,x)) xs
>           c' :=> t' = substQType fOfs q
>           fOf ("FunctorOf", [f,_]) = f
>           cmp ("FunctorOf", [_,d1]) ("FunctorOf", [_,d2]) = d1 `compare` d2
>           eq ("FunctorOf", [_,d1]) ("FunctorOf", [_,d2]) = d1 == d2
>           isFOf ("FunctorOf", [_,_]) = True
>           isFOf _                    = False
>     groupCtxs cs   = grp $ map (:[]) cs
>     grp []         = []
>     grp (cs:css)   = case ins cs css of
>           Just css'   -> grp css'
>           Nothing     -> cs : grp css
>        where
>           ins cs [] = Nothing
>           ins cs (cs':css)
>              | any (`elem` concatMap vars cs) $ concatMap vars cs' = Just $ (cs++cs'):css
>              | otherwise = do css' <- ins cs css; return $ cs':css'
>     occursIn c cs = any (`elem` vars c) $ concatMap vars cs
>     vars (conid, ts)     = concatMap tvars ts
>     tvars (TVar v)       = [v]
>     tvars (t1 :@@: t2)   = tvars t1 ++ tvars t2
>     tvars _              = []

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
