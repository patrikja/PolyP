\chapter{Folding}
\begin{verbatim}

> module Folding where
> import Grammar -- (Eqn'(..),Expr'(..),VarID)
> import MyPrelude(pair,mapFst,mapSnd,without,flatMap,fMap)
> import MonadLibrary(mapl,foreach,(<*>),(<@),liftop,map0,map1,map2)
> import PrettyPrinter(Pretty(),pshow)

\end{verbatim}
\section{Folding expressions and types}
The function \verb|cataExpr| folds an expression to a value. As
expressions and equations are mutually recursive \verb|cataExpr| has
to know about cataing equations, too. Function \verb|cataType| does
the same for types.
\begin{verbatim}

> type ExprFuns t x q = 
>   ( VarID -> x          -- variable
>   , ConID -> x          -- constructor
>   , x -> x -> x         -- application
>   , x -> x -> x         -- lambda abstraction
>   , Literal -> x        -- literal
>   , x                   -- wildcard
>   , x -> [(x, x)] -> x  -- case
>   , [[q]] -> x -> x     -- letrec
>   , x -> t -> x         -- explicitly typed expression
>   )
> type EqnFuns t x q =  
>   ( VarID -> Maybe t -> [x] -> x -> q  -- variable binding
>   , ConID -> [VarID] -> [(ConID, [Type])] -> [ConID] -> q 
>                                        -- data type def.
>   , VarID -> t -> t -> [(t, x)] -> q   -- polytypic def.
>   , [VarID] -> t -> q
>   )

> cataExpr :: ( ExprFuns t x q , EqnFuns t x q ) -> 
>                Expr' t -> x
> cataEqn  :: ( ExprFuns t x q , EqnFuns t x q ) -> 
>                Eqn' t  -> q
>
> cataExpr t@((var,con,app,lambda,literal,
>              wildCard,case',letrec,typed), _ ) = f
>   where 
>     f (Var a     ) = var a
>     f (Con a     ) = con a
>     f (a :@: b   ) = app (f a) (f b)
>     f (Lambda a b) = lambda (f a) (f b)
>     f (Literal a ) = literal a
>     f (WildCard  ) = wildCard
>     f (Case a b  ) = case' (f a) (map (mapBoth f) b)
>     f (Letrec a b) = letrec (map (map (cataEqn t)) a) (f b)
>     f (Typed a b ) = typed (f a) b
>     mapBoth g (a,b) = (g a, g b) 
> 
> cataEqn t@( _ , (varBind, dataDef, polyTypic, explType) ) = f
>   where
>     f (VarBind a mt b c ) = varBind a mt (map fet b) (fet c)
>     f (DataDef a b c d  ) = dataDef a b c d
>     f (Polytypic a b c d) = polyTypic a b c (map (mapSnd fet) d)
>     f (ExplType vs ty)    = explType vs ty
>     f (TypeSyn  _ _ _)    = error "Folding.cataEqn: TypeSyn not allowed"
>     f (Class    _ _ _)    = error "Folding.cataEqn: Class not allowed"
>     f (Instance _ _ _)    = error "Folding.cataEqn: Instance not allowed"
>     fet = cataExpr t               

> type TypeFuns a b = (VarID -> b , ConID -> b , a -> a -> b) 
> cataType :: TypeFuns a a -> Type -> a

> cataType (var,con,app) = cT
>   where cT (TVar v)   = var v
>         cT (TCon c)   = con c
>         cT (f :@@: x) = app (cT f) (cT x)

> mcataType :: Monad m => TypeFuns a (m a) -> Type -> m a
> mcataType (var,con,app) = cataType (var,con,mapp)
>   where mapp mf mx = mf >>= \f -> mx >>= app f

\end{verbatim}
\section{Determining the free variables}
The functions \verb|freeVars...| determine the free variables in their
argument. They use \verb|freeVars| as the argument to the appropriate
\verb|cata|. \verb|freeVars| returns a 2-tuple containing the list of
variables bound in the expression and the list of free variables. This
former list is only needed in the case of a \verb|letrec|:
\verb|letrec eqns x| has as free variables the free variables in the
right hand sides of the equations plus the free variables of \verb|x|
{\em excluding} the variables that are bound by the equations.  The
explicit types are there to stop Gofer from complaining about
`Outstanding contexts'.
\begin{verbatim}

> freeVarsPat :: Pat' a -> [VarID]
> freeVarsPat = snd . cataExpr freeVars
> freeVarsEqn :: Eqn' a -> [VarID]
> freeVarsEqn = snd . cataEqn  freeVars

> freeVars :: (ExprFuns t ([VarID],[VarID]) ([VarID],[VarID]),
>              EqnFuns t ([VarID],[VarID]) ([VarID],[VarID]))

> freeVars
>   = ( (var, con, app, lambda, literal, wildCard, case', letrec, typed)
>     , (varBind, dataDef, polyTypic, explType)
>     )
>   where
>     nil = ([],[])
>     free vs = ([],vs) :: ([VarID],[VarID])
>     var name    = free [name]
>     con _       = nil
>     app x y     = free (snd x ++ snd y)
>     lambda p e  = free (snd e `without` snd p)
>     literal _   = nil
>     wildCard    = nil
>     case' (_,x) ys = free (x ++ flatMap without2 ys)
>       where without2 ((_,l),(_,r)) = r `without` l
>     letrec ys x = let (f, s) = concat' (concat ys)
>                   in  free ((snd x ++ s) `without` f)
>     typed e t   = e 
>     varBind name typ pats body = 
>       ([name],  (snd body) `without` 
>                 (concat (map snd pats)) :: [VarID])
>     dataDef _ _ _ _        = nil
>     polyTypic name _ _ alts= ([name],freelist)
>        where freelist = concat (map (snd.snd) alts)
>     explType _ _ = nil
> 
>     concat' [] = nil
>     concat' ((a,b):xs) = let (a', b') = concat' xs
>                          in  (a ++ a', b ++ b')

\end{verbatim}
A monadic map on equations taking one representation of types (in the
explicitly typed expressions) to another.
\begin{verbatim}

> mmapEqn :: (Functor m, Monad m) => (t -> m u) -> Eqn' t -> m (Eqn' u)
> mmapEqn f = cataEqn ((var,con,app,lambda,literal,
>                       wildCard,case',letrec, typed f)
>                     , (varBind f,dataDef,polytypic f, explType f)
>                     ) 
>   where
>      typed :: (Functor m, Monad m) => (t -> m u) -> m (Expr' u) -> 
>                                                t -> m (Expr' u)
>      typed g me hpt = me >>= \e -> g hpt <@ Typed e 

>      wildCard= return WildCard
>      var     = return . Var 
>      con     = return . Con
>      literal = return . Literal
>      app     = liftop (:@:)
>      lambda  = liftop Lambda
>      case' me mcases = liftop Case me 
>                          (foreach mcases (uncurry (<*>)))
>      letrec mqss me = liftop Letrec
>                         (mapl (mapl id) mqss) me 
>      varBind g v t mps me = mmapMaybe g t >>= \u-> 
>                             liftop (VarBind v u) (mapl id mps) me
>      dataDef a b c d = return (DataDef a b c d)
>      polytypic :: Monad m => (t -> m u) -> VarID -> t -> t -> 
>                   [(t,m (Expr' u))] -> m (Eqn' u)
>      polytypic g n t fun mcs = 
>         g t >>= \u-> 
>         g fun >>= \fun' -> 
>         foreach mcs polycase >>= \cs ->
>         return (Polytypic n u fun' cs)
>        where polycase (func,me) = g func <*> me
>      explType g vs t = map1 (ExplType vs) (g t)

> mmapMaybe f Nothing = map0 Nothing
> mmapMaybe f (Just t)= map1 Just (f t)

\end{verbatim}
A normal map over (typed) expressions.
\begin{verbatim}

> mapEqn :: (t -> u) -> Eqn' t -> Eqn' u
> mapEqn g = cataEqn ((Var,Con,(:@:),Lambda,Literal,
>                       WildCard,Case,Letrec,typed g)
>                     , (varBind g,DataDef,polytypic g,explType g)
>                     ) 
>    where typed f e = Typed e . f 
>          polytypic f n t fun cs =
>             Polytypic n (f t) (f fun) (map (mapFst f) cs)
>          varBind f v t ps e = VarBind v (fMap f t) ps e
>          explType f vs t = ExplType vs (f t)

\end{verbatim}
The function {\tt dmmapQualified} works through two layers of monads.
\begin{verbatim}

> mmapQualified :: (Functor m, Monad m) => (t -> m u) -> 
>                                          Qualified t -> m (Qualified u)
> mmapQualified f (qs:=>t) =
>   map2 (:=>) (mapl mmapQ qs) (f t)
>  where mmapQ (c,ts) = fMap (pair c) (mapl f ts)

> dmmapQualified :: (Functor m, Monad m, Functor n, Monad n) =>
>                   (a -> m (n b)) -> Qualified a -> m (n (Qualified b))
> dmmapQualified f = fMap (mmapQualified id) . mmapQualified f

\end{verbatim}

% ----------------------------------------------------------------
\section{Tools for handling explicitly typed expressions}

When the new definitions have been generated the explicit types are no
longer needed and can be stripped off. Retaining them would be a good
test of the type labelling, but does currently not work as types are
not instatiated along with the program.

\begin{verbatim}

> stripTEqn  :: TEqn -> Eqn
> stripTExpr :: TExpr -> Expr
> stripTEqn  = cataEqn stripFuns
> stripTExpr = cataExpr stripFuns

> stripFuns :: (ExprFuns t (Expr' a) (Eqn' a), EqnFuns QType TExpr TEqn)

> stripFuns = (exprfuns,eqnfuns)
>   where exprfuns = (Var,Con,(:@:),Lambda,Literal,WildCard,Case,Letrec,
>                     const) -- instead of Typed
>         eqnfuns  = (VarBind,DataDef,Polytypic,ExplType)

         eqnfuns  = (varBind,DataDef,Polytypic,ExplType)
         varBind v t ps e = VarBind v noType ps e

\end{verbatim}
% ----------------------------------------------------------------
\section{Misc.}

A monadic map changing the variables names in an expression given
access to the types of the variables.  We only require that the
variables are typed.  Should be rewritten to update the state \'a la
{\tt |-}. It is used in PolyInstance.

\begin{verbatim}

> mmapTExpr :: (Functor m, Monad m,Pretty t) => 
>              (String -> t -> m String) -> Expr' t -> m (Expr' t)
> mmapTExpr f = mt
>   where 
>     mt (Typed (Var v) t) = f v t <@ ((`Typed` t).Var)
>     mt (Typed e       t) = mt e   <@ (`Typed` t)
>     mt (Var v) = error "Folding.mmapTExpr: untyped variable encountered"
>     mt e = m e -- now e can't be Typed

>     m (Con c)       = map0 (Con c)
>     m (Lambda p e)  = map2 Lambda (mt p) (mt e)
>     m (Literal l)   = map0 (Literal l)
>     m WildCard      = map0 WildCard
>     m (g :@: e)     = map2 (:@:) (mt g) (mt e)
>     m (Case e cs)   = map2 Case (mt e) (mapl (uncurry (map2 pair)) 
>                                              (map mt2 cs)          )
>     m (Letrec qss e)= map2 Letrec (mapl (mapl mq) qss) (mt e)
>     m (Typed e t)   = error ("Folding: mmapTExpr: unexpected Typed expression: "++
>                              pshow e)
>     m e             = error ("Folding: mmapTExpr: unexpected expression: "++
>                              pshow e)

>     mt2 (x, y) = (mt x,mt y)
>     mq = mmapTEqn f

> mmapTEqn  :: (Functor m, Monad m, Pretty t) => 
>              (String -> t -> m String) -> Eqn' t -> m (Eqn' t)
> mmapTEqn f = mq
>   where
>     mq (VarBind v t ps e) = 
>        map2 (VarBind v t) (mapl mt ps) (mt e)
>     mq (Polytypic n t fun cs) = 
>        map1 (Polytypic n t fun) (mapl mtSnd cs)
>     mq _ = error "Folding.mmapTEqn: impossible: not a binding"
>     mtSnd (x,y) = mt y <@ (pair x)
>     mt = mmapTExpr f

typemapTEqn :: (String -> QType -> QType) -> TEqn -> TEqn
typemapTEqn f = tmq
  where 
    tmq (VarBind v t ps e) = VarBind v (f v t) ps (me e)
    tmp q                  = error "Folding.typemapTEqn: not a VarBind"
    tme :: TExpr -> TExpr
    tme = typemapTExpr f

typemapTExpr :: (String -> QType -> QType) -> TExpr -> TExpr


\end{verbatim}
