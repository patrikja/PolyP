\chapter{Generating instances} 
This chapter deals with creating specific instances of polytypic
functions.

\begin{verbatim}

> module PolyInstance(instantiateProgram) where
> import Env(Env,mapEnv,lookasideST,lookupEnv,extendsEnv,newEnv,showsEnv)
> import Grammar(Eqn'(..),Expr'(..),Type(..),Qualified(..),
>                Eqn,TEqn,Expr,TExpr,Func,QType,VarID,ConID,
>                PrgTEqns, changeNameOfBind,noType,
>                tupleConstructor,(-=>),qualify)
> import Folding(cataType,cataEqn,cataExpr,ExprFuns,EqnFuns,
>                stripTEqn,mmapTEqn,mapEqn)
> import Functorize(inn_def,out_def,either_def,fcname_def,
>                   Struct,makeFunctorStruct,Req,eqReq,codeFunctors)
> import TypeGraph(simplifyContext)
> import InferType(qTypeEval)
> import MonadLibrary(State, executeST, mapl,(<@),(@@),unDone,
>                     OutputT,output,runOutput,mliftOut,map0,map1,map2)
> import MyPrelude(maytrace,pair,mapFst,mapSnd,combineUniqueBy,fMap,maydebug)
> import PrettyPrinter(Pretty,pshow)
> import StartTBasis(preludeFuns,preludedatadefs)
> import TypeBasis(TBasis,TypeEnv)

\end{verbatim} 
Given a program with explicitly typed identifiers, an environment
mapping identifiers to their principal types and an environment
mapping datatypes to their definitions, {\tt polyInstPrg} generates
the Gofer-translation of the program.
\begin{verbatim}

> instantiateProgram :: (TBasis,PrgTEqns) -> [Eqn]
> polyInstPrg :: [Eqn] -> [[TEqn]] -> TypeEnv -> [Eqn]

\end{verbatim}
Implementation:
\begin{verbatim}

> instantiateProgram (tbasis,(datadefs,eqnss)) = 
>     datadefs ++ polyInstPrg datadefs eqnss (fst tbasis) 

 polyInstPrg datadefs prg vartypes = map id teqns

> polyInstPrg datadefs prg vartypes = 
>     map (simplifyTEqn funcenv . stripTEqn) teqns
>   where funcenv = mapEnv makeFunctorStruct datadefenv
>         teqns = polyInst funcenv defenv vartypes
>         defenv = eqnsToDefenv (concat prg)
>         datadefenv = eqnsToDefenv (preludedatadefs++datadefs)

\end{verbatim}
% ----------------------------------------------------------------
\section{Making polytypic instances}
This should be partial evaluation of the program with respect to
polytypic type information (evidence).

Overall structure: replace polytypic identifiers with (names of)
instances and generate a list of requests for instance declarations.
Every request in the list is then handled in much the same way:
generate an instance declaration and (possibly) new requests. If the
request is for a {\tt Polytypic} definition the corresponding functor
case is looked up and inserted.

To traverse the program we start by traversing the main definition
emitting requests for the traversal of all free variables. The
requests contain the names of the functions and their instantiated
types. 

The resulting program will have the same structure as the old but with
lots of instances added.  

Given a request {\tt (name, typeinfo)} the following functions will
generate an equation of the form {\tt name_suffix = expr}.

% ----------------------------------------------------------------

\section{Instantiating a polytypic variable binding}

Traverse the expression tree and replace variables by instance names.
Keep track of the environment when traversing {\tt let}-bindings.
\subsection{The variable case}
\begin{itemize}
\item Look up its type at its definition.
\item Match the actual type (after applying the current substitution)
  with the defined type to get hold of the functor part. 
\item If any of the functors is a type variable we have an error:
  can't generate instance.
\item Generate a new name given the old name and the functor(s) (and
  possibly a unique number to avoid name clashes). If there is no
  functor in the type the new name will be the same as the old name.
\item Replace the old name with the new and issue a request of the
  form (name, typeinfo).
\end{itemize}
This implies that we need:
\begin{itemize}
\item A map over the \verb|Var|-case of an explicitly typed equation
  with easy access to the types. ({\tt mmapTEqn})
\item A current substitution of functor variables for actual functors.
  (This will be needed when we take care of the requests.)
\item A function to match type expressions.
\item The types of all polytypic functions defined at every point in
  the program. (Must be updated when passing through a {\tt
    let}, $\lambda$ or {\tt case}-expression)
\item (A number supply and) a name generator.
\item An output facility for the requests.
\end{itemize}
This calls for a monadic map for a monad with an environment part
(containing information about the types of all polytypic functions), a
current substitution (, a unique number) and an output list.

The mmap should update the environment.

\begin{verbatim}

> type OutEnvM a b = OutputT a (State (Env VarID QType)) b
> traverseTEqn :: Subst -> TEqn -> OutEnvM Req TEqn
> traverseTEqn s = mmapTEqn f . mapEqn (substQType s)
>   where
>     f :: VarID -> QType -> OutEnvM Req VarID
>     f n t = 
>       lookupOut n >>= maybe (return n) (makeReq n t)
>     makeReq :: VarID -> QType -> QType -> OutEnvM Req VarID
>     makeReq n t tdef = 
>        output req >> return newname
>          where req      = (n,t)
>                newname  = n++extra
>                extra    = codeFunctors functors
>                functors = getFunctors tdef t
>     lookupOut :: VarID -> OutEnvM a (Maybe QType)
>     lookupOut = mliftOut . lookasideST

\end{verbatim}
To traverse the whole program we create a list of requests starting
with main and then run the above for all the requests appending the
generated requests.

A request for:
\begin{itemize}
\item a value defined by a polytypic construct is handled by selecting
  the right branch in the functor case and then traversing that.
\item a value defined in a normal binding is just traversed.
\item inn or out is handled by special code generators.
\item a predefined (primitive) value is ignored.
\item anything else is an error.
\end{itemize}
The data needed is: 
\begin{itemize}
\item The program
\end{itemize}

{\em Check that requests really can not give two generated equations. }
\begin{verbatim}

> polyInst :: FuncEnv -> DefEnv -> TypeEnv -> [TEqn]
> polyInst funcenv defenv typeenv = eqns 
>   where eqns = concat (generateEqns ([mreq],[mreq]))
>         mreq = mainreq typeenv
>         generateEqns (reqs,seen) = 
>            neweqns : if null newreqs then [] 
>                      else generateEqns (newreqs,newreqs++seen)
>           where (neweqns,newreqs) = handleReqs (reqs,seen)         
>         handleReqs (rs,oldrs) = (concat newqss,newrs)
>           where (newrss,newqss) = 
>                   unzip (map (handleReq funcenv defenv typeenv . tr) rs)
>                 newrs = combineUniqueBy eqReq oldrs (concat newrss)

>         tr :: Req -> Req
>         tr r@(name,ps:=>_) = ("{- Request:"
>			     ++ name++pshow (map snd ps)
>			     ++"-}\n") 
>                          `maytrace` r

\end{verbatim}

The main request should have the correct type of main. 
Currently it only uses a dummy type variable.
\begin{verbatim}

> mainreq :: TypeEnv -> Req
> mainreq typeenv = ("main", maintype)
>   where maintype :: QType
>         maintype = maybe err id (lookupEnv "main" typeenv)
>         err = error ("PolyInstance.mainreq: main is missing "++
>                      "(maybe the type checking failed)")

\end{verbatim}
Check that the type information flows properly: traverse must know
both the type at the definition and the type at the instance.  

\begin{verbatim}

> data DefTypes = PolyDef TEqn | VarDef TEqn | SpecDef | PreDef | Unknown
> type FuncEnv = Env ConID (Struct,Func)
> type DefEnv  = Env VarID TEqn

> handleReq :: FuncEnv -> DefEnv -> TypeEnv -> (VarID, QType) -> 
>              ([Req], [TEqn]) 
> handleReq funcenv defenv typeenv (name,tinst) = 
>   case classifyDef defenv name of
>     (PolyDef eqn) -> traverse typeenv (pickPolyEqn funcenv eqn tinst) tinst
>     (VarDef  eqn) -> traverse typeenv (pairType funcenv typeenv eqn tinst) tinst
>     SpecDef       -> specPolyInst funcenv name tinst
>     PreDef        -> ([],[])
>     Unknown       -> error ("PolyInstance.handleReq: unknown function requested: "++name++
>                             "\n  (Probably error in type inference)\n")

> pairType :: FuncEnv -> TypeEnv -> Eqn -> QType -> (Eqn, Subst, QType)
> pairType funcenv typeenv (VarBind name t as e) tinst = 
>      (VarBind name (Just tOK) as e,
>       subst,
>       tdef)
>    where findtdef na = maybe (err na) id (lookupEnv na typeenv)
>          tdef  = findtdef name
>          err n = error ("PolyInstance.pairType: type not in environment:"++n)
>          subst = matchfuns (maydebug $ tdef,maydebug $ tinst)
>          tOK   = substQType subst tdef
> pairType _ _ _ _ = error "PolyInstance.pairType: impossible: not a VarBind"

\end{verbatim}

In {\tt pairType} the generated type should be a simplified version 
of the original type after substitution of the functor variables 
from the request.
%
Remaining bugs:
%
  local definitions may get a context that is not used in the type
    p :: Poly (FunctorOf a) => ([Char], Int)
    p = structure_compress_f0 struct
\subsection{Inn and out}
\begin{verbatim}

> specPolyInst :: FuncEnv -> VarID -> QType -> ([Req], [TEqn]) 
> specPolyInst funcenv n tinst | n `elem` ["inn","out"] = 
>     case functors of
>       [TCon "FunctorOf" :@@: TCon d] -> 
>            setT funcenv tinst (fundefs n (struct d))
>       _ -> error ("PolyInstance.specPolyInst: inn/out can not be generated for "++
>                   concat (map pshow functors))
>   where functors = getFunctors tfusk tinst
>         tfusk = [("Poly",[TVar "f"])] :=> undefined
>         struct d = fst (maybe (err d) id (lookupEnv d funcenv))
>         err d = error ("specPolyInst: functor not found:"++d)
>         extra = codeFunctors functors
>         fundefs "inn" = inn_def ("inn"++extra)
>         fundefs "out" = out_def ("out"++extra)
>         fundefs _     = error "PolyInstance.specPolyInst: impossible: neither inn nor out"

\end{verbatim}
\subsection{Uncurry$n$}
{\tt uncurryn = uncurry . (uncurryn-1 .) }
\begin{verbatim}

> specPolyInst funcenv name tinst | isUncurry name              
>                                     = makeUncurry name n
>   where n :: Int
>         n = read rest
>         rest = drop uncurryNameLength name

\end{verbatim}
\subsection{either}
\begin{verbatim}
either f g x = case x of 
               (Left a) -> f a
               (Right b) -> g b

> specPolyInst funcenv "either" tinst = either_def

\end{verbatim}
\subsection{fconstructorName}
\begin{verbatim}
fconstructorName

> specPolyInst funcenv n@"fconstructorName" tinst = 
>     case functors of
>       [TCon "FunctorOf" :@@: TCon d] -> 
>            setT funcenv tinst (fcname_def (n++extra) (struct d))
>       _ -> error ("specPolyInst: fconstructorName can not be generated for "++
>                   concat (map pshow functors))
>   where functors = getFunctors tfusk tinst
>         tfusk = [("Poly",[TVar "f"])] :=> undefined
>         struct d = fst (maybe (err d) id (lookupEnv d funcenv))
>         err d = error ("specPolyInst: functor not found:"++d)
>         extra = codeFunctors functors

\end{verbatim}
\begin{verbatim}

> specPolyInst datadefs n _ = error ("specPolyInst: not implemented yet:"++n)

> setT :: FuncEnv -> QType -> (QType,(a,[Eqn])) -> (a,[Eqn])
> setT funcenv tinst (tdef,p) = mapSnd (map (setType tOK)) p
>   where 
>     tOK   = substQType subst tdef
>     subst = matchfuns (tdef,tinst)

> setType t (VarBind name _        pats rhs) = 
>            VarBind name (Just t) pats rhs
> setType t _ = error "PolyInstance.updateType: impossible - no VarBind"

> makeUncurry :: VarID -> Int -> ([Req], [Eqn])
> makeUncurry name m = case m of 
>      0 -> ([] ,unc 0 [f,p] (f))
>      1 -> ([] ,unc 1 [f,p] (f :@: p))
>      2 -> ([] ,unc 2 [f,p] (f :@: p1 :@: p2 ))
>      n -> ([req (n-1)],
>            unc n [f,p] (Var (uncurryn (n-1)):@: (f :@: p1) :@: p2 ))
>    where [f,p]      = map Var ["f","p"]
>          [p1,p2]    = map ((:@:p).Var) ["fst","snd"]
>          unc n ps e = [VarBind name (Just (tunc n)) ps e]
>          unit       = Con (tupleConstructor 0)
>          pairf a b  = Con  (tupleConstructor 2) :@:  a :@:  b
>          tpairf a b = TCon (tupleConstructor 2) :@@: a :@@: b
>          uncurryn k = uncurryName++show k
>          req k      = (uncurryn k,tunc k)
>          tunc n     = qualify (func n -=> righttuple n -=> var n)
>          func n     = foldr (-=>) (var n) (map var [0..n-1])
>          righttuple 0= TCon (tupleConstructor 0)
>          righttuple 1= var 0
>          righttuple n= foldr1 tpairf (map var [0..n-1])
>          var n = TVar ("a"++show n)

It is important that the matching is done lazily.

unc0 :: a -> () -> a
unc1 :: (a->b) -> (a) -> b
unc2 :: (a->b->c) -> (a,b) -> c

uncn :: (a0->a1->...->an) -> (a0,(a1,...,an-1)...) -> an
{\tt uncurryn = uncurry . (uncurryn-1 .) }

\end{verbatim}
{\em To be rewritten.}
\begin{verbatim}

> traverse :: TypeEnv -> (TEqn,Subst,QType) -> Qualified Func -> 
>             ([Req], [TEqn])
> traverse typeenv (q,subst,tdef) tinst = 
>     (mapSnd (:[]) . executeST typeenv . runOutput []) m 
>   where m = traverseTEqn (tracing subst) newq 
>         newq = changeNameOfBind (++extra) q 
>         extra = codeFunctors functors
>         functors = getFunctors tdef tinst
>	  tracing :: Subst -> Subst
>	  tracing s = maytrace ("{- Subst:"++showsEnv s "" ++"-}\n") s

> uncurryName :: String
> uncurryName = "uncurry"
> uncurryNameLength :: Int
> uncurryNameLength = length uncurryName
> isUncurry name = length name > uncurryNameLength && 
>                  take uncurryNameLength name == uncurryName

> isSpecFun :: VarID -> Bool
> specFuns :: [VarID]

> isSpecFun name = name `elem` specFuns || isUncurry name
> specFuns = ["inn","out","fconstructorName"]

\end{verbatim} 
The list {\tt preludeFuns} contains the names of the Haskell prelude
functions. (They are known not to be polytypic so no instances are
generated for them.)

{\em All names beginning with uncurry are used up here!}
\begin{verbatim}

> classifyDef :: DefEnv -> VarID -> DefTypes
> classifyDef defenv name = 
>   if      isSpecFun name       then  SpecDef
>   else if name `elem` preludeFuns  then  PreDef
>   else case lookupEnv name defenv of
>     (Just q@(Polytypic _ _ _ _)) -> PolyDef q
>     (Just q@(VarBind _ _ _ _))   -> VarDef  q
>     (Just _)                     -> error "PolyInstance.classifyDef: impossible: not a binding"
>     Nothing                      -> Unknown

\end{verbatim}
\subsection{{\tt let}-bindings in the expression}
When traversing the expression {\tt e} in {\tt let eqns in e} the
environment must be updated with information about the types of the
new definitions. If requests for instances of these functions are
issued their generated instances must either be placed at this level,
before the other bindings, or at the top level with extended names to
avoid clashes between other definitions of the same identifiers.
% ----------------------------------------------------------------
\section{Handling requests for {\tt Polytypic} instantiations}
Given a request {\tt (name, newname, functor)} this will generate an
equation of the form {\tt newname = expr} where expr comes from the
polytypic case corresponding to the top level constructor of {\tt
  functor}.
\begin{itemize}
\item Look at the top level of the functor:
\item If it is a functor (type-) variable, complain, otherwise go on.
\item Lookup the top level constructor in the polytypic definition.
\item Match the current functor with the functor pattern of this case
  alternative giving associations from the functor variables (\verb|f|
  and \verb|g| in the pattern {\tt f + g}) to actual functor
  expressions.
\item With these associations in mind (that is, do the type
  substitutions or keep them in an environment), the (explicitly
  typed) expression from the case alternative is what to proceed with.
\item Call the variable binding handler with the new equation.
\end{itemize}
This description implies that we need:
\begin{itemize}
\item An environment with all polytypic definitions.
\item A function to match functor expressions.
\item A function to lookup a matching case in a polytypic definition.
\end{itemize}
We also want to generate a correctly instantiated type.

% ----------------------------------------------------------------
\section{Implementation}
Get the correct equation out of the poly case.

\begin{verbatim}

> pickPolyEqn :: FuncEnv -> TEqn -> QType -> (TEqn, Subst, QType)
> pickPolyEqn funcenv (Polytypic n tdef (_:=>TVar fname) cs) tinst =
>     (VarBind n (Just tOK) [] e, s, tdef) 
>   where f     = getFunctor funcenv fname tdef tinst
>         mp    = functorCase f cs
>         (e,s) = maybe err id mp
>         err   = error ("PolyInstance.functorCase: no match for "++
>                        pshow f  ++ 
>                        " in polytypic " ++ n)
>         subst = matchfuns (tdef,tinst)
>         tOK   = substQType subst tdef

> pickPolyEqn _ _ _ = error "PolyInstance.pickPolyEqn: impossible: not Polytypic"

> simplifyTEqn :: FuncEnv -> TEqn -> TEqn
> simplifyTEqn = mapEqn . simplifyQType

> simplifyQType :: FuncEnv -> QType -> QType
> simplifyQType funcenv = simplifyContext 
>                       . qTypeEval 
>                       . evaluateFunInQType funcenv

> functorCase :: Func -> [(QType, e)] -> Maybe (e, Subst)
> functorCase f [] = Nothing
> functorCase f ((_:=>p,eqn):cs) = case match (p,f) of
>    (Just s) -> Just (eqn,s)
>    Nothing  -> functorCase f cs

\end{verbatim}
The VarID is the name of the functor we are looking for, the first
QType is the defined type and the second is the instance. The result
is the functor instance corresponding to the named functor.
\begin{verbatim}

> getFunctor :: FuncEnv -> VarID -> QType -> QType -> Func
> getFunctor funcenv fname (ps:=>t) (qs:=>tinst) = 
>     case [ fun | (("Poly",TVar fn:_),(_,fun:_)) <- zip ps qs, fn==fname] of
>       (fun:_) -> evaluateTopFun funcenv fun
>       _       -> error ("PolyInstance.getFunctor: "++
>                         "Poly not found in polytypic definition: "++
>                         fname) -- ++ " "++ (pshow ps)++pshow qs)

> evaluateTopFun :: FuncEnv -> Func -> Func
> evaluateTopFun funcenv (TCon "FunctorOf" :@@: TCon d) = functorOf funcenv d
> evaluateTopFun funcenv f = f

> evaluateFunInQType :: FuncEnv -> QType -> QType
> evaluateFunInQType    funcenv =  fMap (evaluateFunInType funcenv)

> evaluateFunInType :: FuncEnv -> Type -> Type
> evaluateFunInType    funcenv =  ev
>   where ev :: Type -> Type
>         ev (TCon "FunctorOf" :@@: TCon d) = functorOf funcenv d
>         ev (f :@@: x)                     = ev f :@@: ev x
>         ev y                              = y

> functorOf :: FuncEnv -> VarID -> Func
> functorOf fenv d = snd (maybe err id (lookupEnv d fenv))
>   where err = error ("PolyInstance.functorOf: unknown datatype: "++d)

\end{verbatim}
Usage chain: (functorOf needs the datatype environment)
\begin{tabular}{ll}
Function       & Used in       \\
functorOf      & evaluateTopFun\\
evaluateTopFun & getFunctor    \\
getFunctor     & pickPolyEqn   \\
pickPolyEqn    & handleReq     \\
handleReq      & polyInst      \\
polyInst       & polyInstPrg   
\end{tabular}
% ----------------------------------------------------------------
\section{An example}
As an example: (violating most rules for variable names and
eliminating some explicit types for readability)
Poly (FunctorOf List)
\begin{verbatim}
(fsum :: (Par + (Rec * Rec)) Int Int -> Int) x
\end{verbatim}
gives (use SpPrr -notation)
\begin{verbatim}
fsum(Par+(Rec*Rec)) x
fsum(Par+(Rec*Rec)) = (fsum :: Par Int Int -> Int) `either`
                          (fsum :: (Rec * Rec) Int Int -> Int)
\end{verbatim}
gives
\begin{verbatim}
fsum(Par+(Rec*Rec)) x
fsum(Par+(Rec*Rec)) = fsumPar `either` fsum(Rec*Rec)
fsumPar = id
fsum(Rec*Rec) = \(x,y) -> (fsum :: Rec Int Int -> Int) x + 
                            (fsum :: Rec Int Int -> Int) y
\end{verbatim}
gives
\begin{verbatim}
fsum(Par+(Rec*Rec)) x
fsum(Par+(Rec*Rec)) = fsumPar `either` fsum(Rec*Rec)
fsumPar = id
fsum(Rec*Rec) = \(x,y) -> fsumRec x + fsumRec y
fsumRec = id
\end{verbatim}
The whole translation can be split into two parts: first
determine what instances are needed and substitute their names
assuming that they already exist, then generate definitions for them.
(Though the generation of definitions will require more instances ...)
Thus: build a list of required functions from two parts: the demands
generated when traversing the program and the part generated when
generating instances for the list.
Rough sketch:
\begin{verbatim}
instantiatePrg :: Prg -> [Eqn]
instantiatePrg prg = eqns
  where
    (eqns,newrequired) = buildinstances required
    (prg', = traverseProgram prg ++ newrequired

buildInstances :: [Req] -> ([TEqn],[Reqs])
buildInstances = foldr buildstep ([],[])
  where buildstep req (eqns,reqs) = (eqns++neqns,reqs++nreqs)
        (neqns,nreqs) = buildinstance req

buildinstance :: Req -> ([TEqn],[Reqs])
\end{verbatim}
% ----------------------------------------------------------------
\section{Matching types}
Given a type $t$ containing a functor variable $f$ and an instance
$\tau$ of this type we want to find the functor corresponding to $f$.
This can be done by unifying the two types and extracting the part of
the substitution that refers to $f$.

Make sure match works for variables too. (insert dictionaries?)
(together with functorCase)

\begin{verbatim}

> type Subst = Env VarID Type

> getFunctors :: QType -> QType -> [Func] -- used by traverseEqn
> getFunctors (ps:=>t) (qs:=>tinst) = 
>     [ fun | (("Poly",_),(_,fun:_)) <- zip ps qs]

> matchfuns :: (QType, QType) -> [(String, Func)]
> matchfuns (ps:=>t , qs:=>tinst) = subst
>   where fts = [ f | ("Poly",[f]) <- ps] :: [Func]
>         ftis= [ f | ("Poly",[f]) <- qs] 
>         pairs= zip fts ftis
>         subst = maybe err id m
>         m :: Maybe Subst
>         m = thread (map match' pairs) []
>         thread :: Monad m => [a -> m a] -> a -> m a
>         thread = foldr (@@) return
>         err = error "PolyInstance.matchfuns: no match"

> match :: (Type, Type) -> Maybe Subst
> match p = match' p []

\end{verbatim}
Variables in the first type get bound to expressions in the second type.
\begin{verbatim}

> match' :: (Type,Type) -> ( Subst -> Maybe Subst )
> match' (TVar tv, TVar uv) | tv == uv = Just
> match' (TCon tc, TCon uc) | tc == uc = Just
> match' (tf :@@: tg,uf :@@: ug)       = match' (tf,uf) @@ match' (tg,ug)
> match' (TVar tv, u)                  = addbind tv u 
> match' _                             = const Nothing

> addbind :: a -> b -> [(a, b)] -> Maybe [(a, b)]
> addbind v t = Just . ((v,t):)

\end{verbatim}
% ----------------------------------------------------------------
\section{Substitutions}
To apply a substitution we simply fold over the abstract syntax of types:
\begin{verbatim}

> appSubst :: (VarID->Type) -> Type -> Type
> appSubst s = cataType (s, TCon, (:@@:)) 

> substQType :: Subst -> QType -> QType
> substQType env = fMap (appSubst s)
>   where s v = maybe (TVar v) id (lookupEnv v env)

\end{verbatim}
% ----------------------------------------------------------------
\section{Some unused functions}
A simple substitution of the type variable f with fi ( f \verb"|->" fi ) must
make sure that no name clashes occur in the resulting type.
\begin{verbatim}

 (f |-> fi) v | v==f      = rename fi
              | otherwise = TVar v 

 rename = appSubst (TVar.('_':))

 testex2 = appSubst ("f" |-> (functors !! 3)) testex
 testex = unDone $ parse pType1 "(a->b) -> Mu f a -> Mu f b"
 ex1 = match' (testex,testex2) []

 substEqn :: (String -> Expr' a) -> Eqn' a -> Eqn' a
 substExpr :: (String -> Expr' a) -> Expr' a -> Expr' a
 substEqn s = cataEqn (substFuns (substExpr s . s))
 substExpr s = c 
   where c = cataExpr (substFuns (c.s))
 substFuns subst = ( (subst,Con,(:@:),Lambda,
                        Literal,WildCard,Case,Letrec,Typed) ,
                     (VarBind,DataDef,Polytypic) )

\end{verbatim}

\begin{verbatim}

> eqnsToDefenv :: [Eqn] -> DefEnv
> eqnsToDefenv eqns = extendsEnv (map pairwithname eqns) newEnv
>   where pairwithname q@(VarBind n _ _ _)   = (n,q)
>         pairwithname q@(Polytypic n _ _ _) = (n,q)
>         pairwithname q@(DataDef n _ _ _)   = (n,q)
>         pairwithname _ = error "PolyInstance.eqnsToDefenv: impossible: not a binding or a DataDef"

\end{verbatim}
% ----------------------------------------------------------------
\section{Work}
Try out: {\tt match :: (Regular d, Regular (Mu (() + FunctorOf d))) =>
  (d a, Mu (() + FunctorOf d)) -> Maybe (d a)}
  
Problems: 
\begin{itemize}
 \item Make the output type the correct instance.
 \item Maybe there should be two judgement forms:
  \begin{itemize}
   \item {\tt BiFunctor f}: f is a bifunctor (a type of kind {\tt *->*->*}
     built up using +, *, @, Par, Rec, Const t and FunctorOf D for
     regular datatypes D)
   \item {\tt Regular D}: D is a datatype functor (D is a datatype (of
     kind {\tt *->*}) that has been unified with a Mu f or D is Mu
     (FunctorOf D))
  \end{itemize}
 \item Make sure the explicit types are simplified and instatiated after 
   code generation so that they can be printed in the output.
 \item Check what overloading problems we can get in the generated code. 
   (Gofer takes it, but maybe not Hugs or Haskell.)
 \item The generation of functors is not ready.
 \item either is required - should be generated
 \item Local bindings (let, lambda, case) should hide the outer one:
   the inner map in (a silly version of the identity function)
   \verb+\map->map+ should not be instantiated.
 \item The type labelling was not correct for {\tt cata}: The
   dependence on {\tt Poly f} gets into the type basis but not to the
   recursive use. Temporarily solved by brute force: infer all types
   twice.
\end{itemize}
Solved(?) problems:
\begin{itemize}
\item {\tt inn} and {\tt out} are generated.
\item The Poly context is too widespread: if {\tt test = map (+1) [1]}
  then test gets the type {\tt Poly (FunctorOf []) => Mu (FunctorOf
    []) Int} instead of just {\tt [Int]}. Possible solutions:
  \begin{itemize}
  \item This probably means that the equality between {\tt Mu
      (FunctorOf D)} and {\tt D} has to be implemented in the type
    checker so that the former is (whenever possible) rewritten to the
    latter. In doing that the corresponding part of the context must
    be removed.
  \item It may be enough to remove constant contexts from the type 
    environment. (Done)*** Where?!
  \end{itemize}
\item Sometimes a function does not get the correct instantiated name
  on the left hand side. (Probably related to the above.)
\end{itemize}
% ----------------------------------------------------------------
\section{Algorithm description}
instantiateProgram and polyInstPrg are shells around the main
functions: polyInst, handleReq, traverse, traverseTEqn

\subsection{Dependencies}
\begin{verbatim}
instantiateProgram :: (TBasis,PrgTEqn) -> [Eqn]
  polyInstPrg
polyInstPrg :: [Eqn] -> [[TEqn]] -> TypeEnv -> [Eqn]
  stripTEqn, polyInst,  eqnsToDefenv, (makeFunctorStruct)
traverseTEqn :: (Functor m, Monad m) => Subst -> TEqn -> OutEnvM Req m TEqn
  codeFunctor, (substQType)
polyInst :: FuncEnv -> DefEnv -> TypeEnv -> [TEqn]
  handleReq, mainreq
mainreq :: Req
handleReq :: FuncEnv -> DefEnv -> TypeEnv -> (VarID, QType) -> ([Req], [TEqn]) 
  classifyDef, traverse, pickPolyEqn, pairType, specPolyInst
pairType :: TypeEnv -> Eqn' t -> QType -> (Eqn' t, Subst, QType)
specPolyInst :: FuncEnv -> VarID -> QType -> ([Req], [TEqn]) 
  matchfuns, makeUncurry, (inn_def,out_def)
makeUncurry :: Int -> ([Req], [Eqn])
traverse :: TypeEnv -> (TEqn,Subst,QType) -> Qualified Func -> ([Req], [TEqn])
  traverseTEqn, matchfuns, codeFunctors, runOutput, changeName
classifyDef :: DefEnv -> VarID -> DefTypes
pickPolyEqn :: FuncEnv -> TEqn -> QType -> (TEqn, Subst, QType)
  getFunctor, functorCase


functorCase :: Type -> [(QType, a)] -> (a, Subst)
  match
getFunctor :: FuncEnv -> VarID -> QType -> QType -> Func
  evaluateTopFun
evaluateTopFun :: FuncEnv -> Type -> Type
  functorOf
type FuncEnv = Env ConID (Struct,Func)
  Env.Env Grammar.ConID Functorize.Struct Grammar.Func
functorOf :: FuncEnv -> VarID -> Func

getFunctors :: QType -> QType -> [Func] -- used by traverseEqn
matchfuns :: (QType, QType) -> [(String, Func)] -- used by traverse
match :: (Type, Type) -> Maybe Subst
  match'
match' :: (Type,Type) -> Subst -> Maybe Subst
addbind :: a -> b -> [(a, b)] -> Maybe [(a, b)]
appSubst :: (VarID->Type) -> Type -> Type
substQType :: Subst -> QType -> QType

eqnsToDefenv :: [Eqn' a] -> [(VarID, Eqn' a)]

{- In Folding.lhs
stripTEqn  :: TEqn -> Eqn
  stripFuns
stripTExpr :: TExpr -> Expr
  stripFuns
stripFuns :: (ExprFuns a (Expr' b) (Eqn' b), EqnFuns c (Expr' c) (Eqn' c))
mmapTExpr :: (Functor m, Monad m) => 
             (String -> a -> m String) -> Expr' a -> m (Expr' a)
-}

{- In Functorize.lhs
codeFunctors :: [Func] -> String
  codeFunctor
codeFunctor :: Func -> String
  codeTyCon
decodeFunctor :: String -> Func
  decodeTyCon
codeTyCon :: String -> String
decodeTyCon :: String -> (String,String)
-}

\end{verbatim}
