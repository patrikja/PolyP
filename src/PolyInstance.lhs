\chapter{Generating instances} 
This chapter deals with creating specific instances of polytypic
functions.

\begin{verbatim}

> module PolyInstance(instantiateProgram) where
> import Char(isDigit)
> import Env(Env,mapEnv,lookasideST,lookupEnv,extendsEnv,newEnv)
> import Grammar(Eqn'(..),Expr'(..),Type(..),Qualified(..),
>                Eqn,TEqn,Expr,TExpr,Func,QType,VarID,ConID,
>                PrgTEqns, changeNameOfBind,noType)
> import Folding(cataType,cataEqn,cataExpr,ExprFuns,EqnFuns)
> import Functorize(inn_def,out_def,either_def,fcname_def,
>                   makeFunctorStruct,Struct,Req,eqReq)
> import MonadLibrary(State, executeST, join,mapl,(<@),(@@),unDone,
>                     OutputT,output,runOutput,mliftOut,map0,map1,map2)
> import MyPrelude(maytrace,pair,mapFst,mapSnd,combineUniqueBy,  debug)
> import Parser(tupleConstructor)
> import PrettyPrinter(Pretty(..))
> import StartTBasis(preludeFuns,preludedatadefs)
> import TypeBasis(TBasis,TypeEnv)

#ifdef __DEBUG__
> maydebug :: Show a => a -> a
> maydebug = debug
#else
> maydebug = id
#endif

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

> polyInstPrg datadefs prg vartypes = map stripTEqn teqns
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
lots of instance declarations added.  

Given a request {\tt (name, typeinfo)} the following functions will
generate an equation of the form {\tt newname = expr}.
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
> traverseTEqn s = mmapTEqn f
>   where
>     f n t = 
>       lookupOut n >>= maybe (return n) (makeReq n (substQType s t))
>     makeReq n t tdef = 
>        output req >> return newname
>          where req     = (n,t)
>                newname = n++extra
>                extra = codeFunctors functors
>                functors = getFunctors tdef t
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
>   where eqns = concat (generateEqns ([mainreq],[mainreq]))
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
>			     ++ name++show (map (pretty.snd) ps)
>			     ++"-}\n") 
>                          `maytrace` r

\end{verbatim}

\begin{verbatim}

> mainreq :: Req
> mainreq = ("main", [] :=> TVar "v")

\end{verbatim}
Check that the type information flows properly: traverse must know
both the type at the definition and the type at the instance.  

{\em Make the output types correct. (Substitute functors and simplify
  contexts)}
\begin{verbatim}

> data DefTypes = PolyDef TEqn | VarDef TEqn | SpecDef | PreDef | Unknown
> type FuncEnv = Env ConID (Struct,Func)
> type DefEnv  = Env VarID TEqn

> handleReq :: FuncEnv -> DefEnv -> TypeEnv -> (VarID, QType) -> 
>              ([Req], [TEqn]) 
> handleReq funcenv defenv typeenv (name,tinst) = 
>   case classifyDef defenv name of
>     (PolyDef eqn) -> traverse typeenv (pickPolyEqn funcenv eqn tinst) tinst
>     (VarDef  eqn) -> traverse typeenv (pairType typeenv eqn tinst) tinst
>     SpecDef       -> specPolyInst funcenv name tinst
>     PreDef        -> ([],[])
>     Unknown       -> error ("handleReq: unknown function requested: "++name++
>                             "\n  (Probably error in type inference)\n")

> pairType :: TypeEnv -> Eqn' t -> QType -> (Eqn' t, Subst, QType)
> pairType typeenv q@(VarBind name t _ _) tinst = 
>      (q,matchfuns (maydebug $ tdef name,maydebug $ tinst),tdef name)
>    where tdef na = maybe (err na) id (lookupEnv na typeenv)
>          err n = error ("pairType: type not in environment:"++n)
> pairType _ _ _ = error "PolyInstance: pairType: impossible: nor a VarBind"

\end{verbatim}
\subsection{Inn and out}
\begin{verbatim}

> specPolyInst :: FuncEnv -> VarID -> QType -> ([Req], [TEqn]) 
> specPolyInst funcenv n tinst | n `elem` ["inn","out"] = 
>     case functors of
>       [TCon "FunctorOf" :@@: TCon d] -> fundefs n (struct d)
>       _ -> error ("specPolyInst: inn/out can not be generated for "++
>                   concat (map (show.pretty) functors))
>   where functors = getFunctors tdef tinst
>         tdef = [("Poly",[TVar "f"])] :=> undefined
>         struct d = fst (maybe (err d) id (lookupEnv d funcenv))
>         err d = error ("specPolyInst: functor not found:"++d)
>         extra = codeFunctors functors
>         fundefs "inn" = inn_def ("inn"++extra)
>         fundefs "out" = out_def ("out"++extra)
>         fundefs _     = error "PolyInstance: specPolyInst: impossible: neither inn nor out"

\end{verbatim}
\subsection{Uncurry$n$}
{\tt uncurryn = uncurry . (uncurryn-1 .) }
\begin{verbatim}

> specPolyInst funcenv name tinst 
>            | take 7 name == "uncurry"  = makeUncurry name n
>   where n = read (drop 7 name) 

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
>       [TCon "FunctorOf" :@@: TCon d] -> fcname_def (n++extra) (struct d)
>       _ -> error ("specPolyInst: fconstructorName can not be generated for "++
>                   concat (map (show.pretty) functors))
>   where functors = getFunctors tdef tinst
>         tdef = [("Poly",[TVar "f"])] :=> undefined
>         struct d = fst (maybe (err d) id (lookupEnv d funcenv))
>         err d = error ("specPolyInst: functor not found:"++d)
>         extra = codeFunctors functors

\end{verbatim}
\begin{verbatim}

> specPolyInst datadefs n _ = error ("specPolyInst: not implemented yet:"++n)

> makeUncurry :: VarID -> Int -> ([Req], [Eqn])
> makeUncurry name n = case n of 
>      0 -> ([] ,uncn [f,p] (f))
>      1 -> ([] ,uncn [f,p] (f :@: p))
>      2 -> ([] ,uncn [f,p] (f :@: p1 :@: p2 ))
>      _ -> ([r],uncn [f,p] (Var uncurryn :@: (f :@: p1) :@: p2 ))
>    where [f,p] = map Var ["f","p"]
>          [p1,p2] = map ((:@:p).Var) ["fst","snd"]
>          uncn ps e = [VarBind name (Just tuncn) ps e]
>          unit = Con (tupleConstructor 0)
>          pairf a b = Con (tupleConstructor 2) :@: a :@: b
>          uncurryn = "uncurry"++show (n-1)
>          r = (uncurryn,tuncn)
>          tuncn = []:=>TVar "a" -- should be the real type (see below)

It is important that the matching is done lazily.

unc0 :: a -> () -> a
unc1 :: (a->b) -> (a) -> b
unc2 :: (a->b->c) -> (a,b) -> c

uncn :: 
{\tt uncurryn = uncurry . (uncurryn-1 .) }


\end{verbatim}
{\em To be rewritten.}
\begin{verbatim}

> traverse :: TypeEnv -> (TEqn,Subst,QType) -> Qualified Func -> 
>             ([Req], [TEqn])
> traverse typeenv (q,subst,tdef) tinst = 
>     (mapSnd (:[]) . executeST typeenv . runOutput []) m 
>   where m = traverseTEqn (tr subst) newq 
>         newq = changeNameOfBind (++extra) q 
>         extra = codeFunctors functors
>         functors = getFunctors tdef tinst
>	  tr :: Subst -> Subst
>	  tr s = maytrace ("{- Subst:"++show s++"-}\n") s

> isSpecFun :: VarID -> Bool
> specFuns :: [VarID]

> isSpecFun name = name `elem` specFuns || isUncurry name
> isUncurry name = length name > 7 && take 7 name == "uncurry"
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
>     (Just _)                     -> error "PolyInstance: classifyDef: impossible: not a binding"
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
% ----------------------------------------------------------------
\section{Implementation}
{\em Check the tdef in VarBind n tdef ...}
Get the correct equation out of the poly case.
\begin{verbatim}

> pickPolyEqn :: FuncEnv -> TEqn -> QType -> (TEqn, Subst, QType)
> pickPolyEqn funcenv (Polytypic n tdef (_:=>TVar fname) cs) t =
>     (VarBind n (Just tdef) [] e, s, tdef) 
>   where f = getFunctor funcenv fname tdef t
>         (e,s) = functorCase f cs
> pickPolyEqn _ _ _ = error "PolyInstance: pickPolyEqn: impossible: not Polytypic"

> functorCase :: Func -> [(QType, e)] -> (e, Subst)
> functorCase f [] = error ("functorCase: no match for "++show (pretty f))
> functorCase f ((_:=>p,eqn):cs) = case match (p,f) of
>    (Just s) -> (eqn,s)
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
>       _       -> error ("getFunctor: "++
>                         "Poly not found in polytypic definition: "++
>                         fname) -- ++ " "++ (show2 ps)++show2 qs)
> --  where show2 = show . pretty

> evaluateTopFun funcenv (TCon "FunctorOf" :@@: TCon d) = functorOf d funcenv
> evaluateTopFun funcenv f = f

> functorOf :: VarID -> FuncEnv -> Func
> functorOf d fenv = snd (maybe err id (lookupEnv d fenv))
>   where err = error ("functorOf: unknown datatype:"++d)

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
\section{Functor names}
To identify a functor in a concise way, we use a coding of functors as
strings of characters. 
%
We use prefix format and translate the operators as follows: 
%
The structures {\tt f+g}, {\tt f*g} and {\tt d@g} are coded by the
first letters in Sum, Product and Application followed by the coded
versions of their children. 
%
The base cases {\tt Empty}, {\tt Par}, {\tt Rec} and {\tt Const t} are
coded by their first letter but in lower case.  
%
(This will have to be improved in the {\tt Const t} case when t is not
just a type variable.  We simply need a pair of functions {\tt
  codeType} and {\tt decodeType}.)  
%
There is one special case: {\tt FunctorOf []} is coded as {\tt F0}
instead of {\tt F[]} to make it possible to parse.
\begin{verbatim}

> codeFunctors :: [Func] -> String
> codeFunctors = concatMap (('_':).codeFunctor)

> codeFunctor :: Func -> String
> codeFunctor f = s f []
>   where 
>     s (TCon "Const" :@@: c)   = ('c':) -- . codeType c
>     s (g :@@: t)     = s g . s t
>     s (TCon "Empty") = ('e':)
>     s (TCon "Par")   = ('p':)    
>     s (TCon "Rec")   = ('r':)    
>     s (TCon "Mu")    = ('m':)
>     s (TCon "FunctorOf")= ('f':)
>     s (TCon "+")     = ('S':)
>     s (TCon "*")     = ('P':)
>     s (TCon "@")     = ('A':)
>     s (TCon d)       = ((codeStr d)++)
>     s t@(TVar v)     = error ("codeFunctor: uninstantiated functor variable " ++
>                               show (pretty t) ++ " found as part of " ++ show (pretty f) )

> decodeFunctor :: String -> Func
> decodeFunctor s = snd (p s)
>   where
>     p ('e':xs)  = (xs,TCon "Empty")
>     p ('p':xs)  = (xs,TCon "Par")
>     p ('r':xs)  = (xs,TCon "Rec")
>     p ('m':xs)  = (xs,TCon "Mu")
>     p ('f':xs)  = (xs,TCon "FunctorOf")
>     p ('c':xs)  = (xs,TCon "Const" :@@: TVar "t") -- use decodeType
>     p ('S':xs)  = mapSnd plus (popp xs)
>     p ('P':xs)  = mapSnd prod (popp xs)
>     p ('A':xs)  = mapSnd appl (popp xs)
>     p xs | isDigit (head xs) = mapSnd TCon (decodeStr xs)
>     popp = p `op` p
>     plus (t,t') = TCon "+" :@@: t :@@: t'
>     prod (t,t') = TCon "*" :@@: t :@@: t'
>     appl (t,t') = TCon "@" :@@: t :@@: t'
>     op w w' xs = (zs,(y,z))
>       where (ys,y) = w  xs
>             (zs,z) = w' ys

> codeStr :: String -> String
> codeStr "[]" = "0"
> codeStr s = show (length s) ++ s

> decodeStr :: String -> (String,String)
> decodeStr s | n > 0 = splitAt n text
>             | n ==0 = ("[]",text)
>             | True  = error "PolyInstance.decodeStr: impossible: negative length"
>    where (num,text) = span isDigit s
>          n = read num

\end{verbatim}
Just a test expression --- not used.
\begin{verbatim}

> testfunctors :: [Func]
> testfunctors = map decodeFunctor [fList,fTree,fRoseTree,
>                                   fVarTree,fVNumber,fBoolAlg]
>      where fList     = "SePpr"
>            fTree     = "SpPrr"
>            fRoseTree = "PpA"++fList++"r"
>            fVarTree  = "Sc"++fTree
>            fVNumber  = "SeSrSPrrPrr"
>            fBoolAlg  = "Se"++fVNumber

\end{verbatim}
% ----------------------------------------------------------------
\section{Matching types}
Given a type $t$ containing a functor variable $f$ and an instance
$\tau$ of this type we want to find the functor corresponding to $f$.
This can be done by unifying the two types and extracting the part of
the substitution that refers to $f$.

Make sure match works for variables too. (together with functorCase)
\begin{verbatim}

> type Subst = [(VarID,Type)]

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
>         err = error "matchfuns: no match"

> match :: (Type, Type) -> Maybe Subst
> match p = match' p []

\end{verbatim}
Variables in the first type get bound to expressions in the second type.
\begin{verbatim}

> match' :: (Type,Type) -> Subst -> Maybe Subst
> match' (TVar tv, TVar uv) = Just
> match' (TCon tc, TCon uc) | tc == uc = Just
> match' (tf :@@: tg,uf :@@: ug) = match' (tf,uf) @@ match' (tg,ug)
> match' (TVar tv, u) = addbind tv u 
> match' _ = const Nothing

> addbind :: a -> b -> [(a, b)] -> Maybe [(a, b)]
> addbind v t s = Just ((v,t):s)

\end{verbatim}
% ----------------------------------------------------------------
\section{Substitutions}
To apply a substitution we simply fold over the abstract syntax of types:
\begin{verbatim}

> appSubst :: (VarID->Type) -> Type -> Type
> appSubst s = cataType (s, TCon, (:@@:)) 

> substQType :: Subst -> QType -> QType
> substQType s = map (appSubst (f s))
>   where f s' v = maybe (TVar v) id (lookup' v)
>           where lookup' w = lookupEnv w (extendsEnv s' newEnv)

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
>         eqnfuns  = (varBind,DataDef,Polytypic,ExplType)
>         varBind v t ps e = VarBind v noType ps e

\end{verbatim}
% ----------------------------------------------------------------
\section{Misc.}
A monadic map with access to the types of the variables.  We only
require that the variables are typed.  Should be rewritten to update
the state \'a la {\tt |-}.
\begin{verbatim}

> mmapTExpr :: (Functor m, Monad m,Pretty t) => 
>              (String -> t -> m String) -> Expr' t -> m (Expr' t)
> mmapTExpr f = mt
>   where 
>     mt (Typed (Var v) t) = f v t <@ ((`Typed` t).Var)
>     mt (Typed e       t) = mt e   <@ (`Typed` t)
>     mt (Var v) = error "mmapTExpr: untyped variable encountered"
>     mt e = m e -- now e can't be Typed

>     m (Con c)       = map0 (Con c)
>     m (Lambda p e)  = map2 Lambda (mt p) (mt e)
>     m (Literal l)   = map0 (Literal l)
>     m WildCard      = map0 WildCard
>     m (g :@: e)     = map2 (:@:) (mt g) (mt e)
>     m (Case e cs)   = map2 Case (mt e) (mapl (uncurry (map2 pair)) 
>                                              (map mt2 cs)          )
>     m (Letrec qss e)= map2 Letrec (mapl (mapl mq) qss) (mt e)
>     m (Typed e t)   = error ("mmapTExpr: unexpected Typed expression: "++
>                              show (pretty e))
>     m e             = error ("mmapTExpr: unexpected expression: "++
>                              show (pretty e))

>     mt2 (x, y) = (mt x,mt y)
>     mq = mmapTEqn f

> mmapTEqn  :: (Functor m, Monad m,Pretty t) => 
>              (String -> t -> m String) -> Eqn' t -> m (Eqn' t)
> mmapTEqn f = mq
>   where
>     mq (VarBind v t ps e) = 
>        map2 (VarBind v t) (mapl mt ps) (mt e)
>     mq (Polytypic n t fun cs) = 
>        map1 (Polytypic n t fun) (mapl mtSnd cs)
>     mq _ = error "PolyInstance: mmapTEqn: impossible: not a binding"
>     mtSnd (x,y) = mt y <@ (pair x)
>     mt = mmapTExpr f

> eqnsToDefenv :: [Eqn] -> DefEnv
> eqnsToDefenv eqns = extendsEnv (map pairwithname eqns) newEnv
>   where pairwithname q@(VarBind n _ _ _)   = (n,q)
>         pairwithname q@(Polytypic n _ _ _) = (n,q)
>         pairwithname q@(DataDef n _ _ _)   = (n,q)
>         pairwithname _ = error "PolyInstance: eqnsToDefenv: impossible: not a binding or a DataDef"

\end{verbatim}
% ----------------------------------------------------------------
\section{Work}
Try out: {\tt match :: (Regular d, Regular (Mu (() + FunctorOf d))) =>
  (d a, Mu (() + FunctorOf d)) -> Maybe (d a)}
  
Problems: 
\begin{itemize}
 \item Make inn more lazy: delay the pattern match in uncurry. 
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
    environment. (Done)
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
functorOf :: VarID -> FuncEnv -> Func
codeFunctors :: [Func] -> String
  codeFunctor
codeFunctor :: Func -> String
  codeStr
decodeFunctor :: String -> Func
  decodeStr
codeStr :: String -> String
decodeStr :: String -> (String,String)
getFunctors :: QType -> QType -> [Func] -- used by traverseEqn
matchfuns :: (QType, QType) -> [(String, Func)]
match :: (Type, Type) -> Maybe Subst
  match'
match' :: (Type,Type) -> Subst -> Maybe Subst
addbind :: a -> b -> [(a, b)] -> Maybe [(a, b)]
appSubst :: (VarID->Type) -> Type -> Type
substQType :: Subst -> QType -> QType
stripTEqn  :: TEqn -> Eqn
  stripFuns
stripTExpr :: TExpr -> Expr
  stripFuns
stripFuns :: (ExprFuns a (Expr' b) (Eqn' b), EqnFuns c (Expr' c) (Eqn' c))
mmapTExpr :: (Functor m, Monad m) => 
             (String -> a -> m String) -> Expr' a -> m (Expr' a)
eqnsToDefenv :: [Eqn' a] -> [(VarID, Eqn' a)]
\end{verbatim}
