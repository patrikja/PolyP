\chapter{Kind inference}
\begin{verbatim}

> module InferKind where

> import Grammar(Kind,Type(..),Eqn,Eqn'(..),VarID,ConID,QType,
>                (-=>),qualify,getNameOfDataDef)
> import TypeGraph(HpKind,HpNode(..),fetchNode,mkVar,mkCon,mkFun,
>                  kindOutOfHeap)
> import TypeBasis(KindBasis,TBasis,lookupKind,inventTypes,
>                  extendKindEnv,ramKindToRom,getKindEnv,
>                  extendTypeTBasis,extendKindTBasis)
> import StateFix-- (ST [,runST [,RunST]]) in hugs, ghc, hbc
> import Env(newEnv,lookupEnv,extendsEnv)
> import PrettyPrinter(Pretty(),pshow)
> import UnifyTypes(unify)
> import MonadLibrary(STErr,mliftErr,convertSTErr,ErrorMonad(failEM),
>                     Error(..),LErr, foreach,(<@))

> infix 9 |*

\end{verbatim}
The kind inference is used to check that the type constructors are
used correctly in explicitly given types. (Including datatype
definitions.)  Every expression must have kind $\ast$ so
\verb|assureType| infers the kind and (effectively) unifies it with
$\ast$.  This could have been done by a call to \verb|unify| but to get
the correct error message it is done by pattern matching on the kind
directly.
\begin{verbatim}

> assureType :: KindBasis s -> Type -> STErr s ()
> assureType basis tp
>   = basis |* tp                 >>= \hpKind -> 
>     mliftErr (fetchNode hpKind) >>= \(k, node) -> 
>     case node of
>       HpCon "*" -> return ()
>       HpVar _  -> return ()
>       _       -> mliftErr (kindOutOfHeap k) >>= \kind->
>                  failEM ("Kind error: Expected * but found: "
>                          ++ pshow kind)

 assureType basis tp
   = basis |* tp                 >>= \hpKind -> 
     mliftErr (mkCon "*")        >>= \star   ->
     unify star hpKind 
\end{verbatim}
The actual kind inference algorithm.
\begin{verbatim}

> (|*) :: KindBasis s -> Type -> STErr s (HpKind s)

> basis |* (TVar name) = name `lookupKind` basis
> basis |* (TCon name) = name `lookupKind` basis 
> basis |* (f :@@: x)
>   = basis |* x               >>= \kX   -> 
>     basis |* f               >>= \kF   -> 
>     mliftErr mkVar           >>= \kApp -> 
>     mliftErr (mkFun kX kApp) >>= \kF'  -> 
>     unify kF kF'             >>
>     return kApp

\end{verbatim}
(It seems to be slightly more efficient to infer the kind of \verb|x|
before \verb|f|.)


\section{Datatype declarations}
For each datatype constructor the types of the data constructors and the kind 

\begin{verbatim}

> inferDataDef :: KindBasis s -> Eqn -> STErr s [(ConID, QType)]
> inferDataDef basis (DataDef tyCon vars alts _)
>   = inventKinds vars >>= \kindVars -> 
>     let extbasis = extendKindEnv (zip vars kindVars) basis
>     in foreach alts (checkAltKind extbasis)
>   where
>     checkAltKind extbasis (constr, args) =
>            assureType extbasis tp >>
>            return (constr, qualify tp) 
>        where tp = foldr (-=>) res args
>     res = foldl (:@@:) (TCon tyCon) (map TVar vars)
> inferDataDef _ _ = error "InferType.inferDataDef: impossible: not a DataDef"

> inferDataDefs :: TBasis -> [Eqn] -> LErr TBasis
> inferDataDefs startTBasis dataDefs = 
>         case inferDataDefs' startTBasis dataDefs of
>           Err msg -> (startTBasis,Err msg)
>           Done (tass,kass) -> 
>            let basis = (extendTypeTBasis tass . 
>                         extendKindTBasis kass) startTBasis
>            in (basis,Done ())

> inferDataDefs' :: TBasis -> [Eqn] -> 
>                   Error ([(ConID, QType)],[(ConID, Kind)])
> inferDataDefs' tbasis eqns = 
>     __RUNST__ (convertSTErr m)
>   where m :: STErr s ([(String,QType)],[(String,Kind)])
>         m = inventKinds names >>= \kinds -> 
>             let extbasis = extendKindEnv 
>                               (zip names kinds) basis
>             in foreach eqns (inferDataDef extbasis) 
>                                    <@ concat >>= \tass->
>                mliftErr (ramKindToRom extbasis) 
>                                              >>= \kass->
>                return (tass,kass)
>         names = map getNameOfDataDef eqns
>         basis = (getKindEnv tbasis,newEnv) 

> inventKinds :: [VarID] -> STErr s [HpKind s]
> inventKinds = inventTypes

\end{verbatim}


