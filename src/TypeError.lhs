\chapter{Type errors}
\begin{verbatim}

> module TypeError(mayreportTError, continueIfNoError, 
>	           TError(..),mayshowargs', failWith,
>	           handleTypeError,noErrMsg,continueIfNoErr,
>                  ErrMsg(..), LocalErrMsg(..), internalError, impossible) where
> import TypeGraph(HpType,NonGenerics,
>                  qtypeOutOfHeap,typesOutOfHeap,
>                  showNodePtr,allGeneric)
> import MonadLibrary(STErr,mliftErr,ErrorMonad(failEM),ST)
> import PrettyPrinter(Pretty(..),pshow,($$),nest,text,sep)
> import Grammar(Type(..),Qualified(..))

#ifdef __DEBUG_UNIFY__
> import MyPrelude(maytrace)
#else
> maytrace :: String -> a -> a
> maytrace _ = id
#endif

> data TError t = TOk
>               | TBad String t t

> continueIfNoError :: Monad m => m (TError t) -> TError t -> m (TError t)
> continueIfNoError mx TOk            = mx
> continueIfNoError mx e@(TBad _ _ _) = return e

> mayreportTError :: NonGenerics s -> HpType s -> HpType s -> TError (HpType s) -> STErr s ()
> mayreportTError _   _ _ TOk            = return ()
> mayreportTError ngs a b (TBad msg t u) = 
>           mliftErr (typesOutOfHeap ngs [a,b,t,u]) >>= \[tA,tB,tT,tU]->
>           failEM (show (typeerror msg tA tB tT tU))
>   where
>      typeerror mess ta tb t' u' =
>        (text "Type instantiation error when comparing")
>        $$ nest 3 (sep [pretty ta,text "with",pretty tb])
>        $$ text "or more specifically when comparing"
>        $$ nest 3 (sep [pretty t',text "with",pretty u'])
>        $$ text "The first is not an instance of the second because"
>	 $$ text mess

> failWith :: String -> HpType s -> HpType s -> STErr s b
> failWith mess a b = mliftErr (typesOutOfHeap allGeneric [a,b]) >>= \l->
>                     failEM (show (err l))
>   where err [a',b']= sep [text "can't unify:",
>                           nest 3 (sep [pretty a',text "with",pretty b'])] 
>                    $$ text ("as "++mess)

> {-
> mayshowargs :: HpType s -> HpType s -> STErr s ()
> mayshowargs a b = mliftErr (mayshowargs' allGeneric a b)
> -}

> mayshowargs' :: NonGenerics s -> HpType s -> HpType s -> ST s ()
> mayshowargs' l a b = typesOutOfHeap l [a,b] >>= mayshowtypes a b

> mayshowtypes :: HpType s -> HpType s -> [Type] -> ST s ()
> mayshowtypes a b [t,t'] = showNodePtr a >>= \sa ->
>                           showNodePtr b >>= \sb ->
>                           maytrace (concat [ "a=",sa,"=",st,
>                                              ",b=",sb,"=",st']) 
>                           (return ())
>    where st = pshow t 
>          st'= pshow t' 

> handleTypeError :: HpType s -> HpType s -> ErrMsg (HpType s) -> STErr s ()
> handleTypeError a b (ErrMsg (Nothing)) = return ()
> handleTypeError a b (ErrMsg (Just (localerr, l, r))) = 
>     mliftErr (typesOutOfHeap ngs [a,b,l,r]) >>=
>     failEM . show . typeerror (show localerr)
>   where
>      ngs = allGeneric -- *** This should be a parameter to handleTypeError
>      typeerror mess [ta,tb,tl,tr] =
>        (text "Unification error when unifying:")
>        $$ nest 3 (sep [pretty ta,text "with",pretty tb])
>        $$ text "or more specifically when unifying:"
>        $$ nest 3 (sep [pretty tl,text "with",pretty tr])
>        $$ text ("the error was: "++mess)


> newtype ErrMsg t = ErrMsg {unErrMsg :: Maybe (LocalErrMsg, t, t)}
> noErrMsg :: ErrMsg t
> noErrMsg = ErrMsg Nothing

> continueIfNoErr :: Monad m =>  m (ErrMsg t) -> ErrMsg t -> m (ErrMsg t)
> continueIfNoErr mx   (ErrMsg Nothing)  = mx
> continueIfNoErr mx e@(ErrMsg (Just _)) = return e

> data LocalErrMsg = 
>               EUnifyConstApp String 
>             | EUnifyKind     
>             | ENoMuApp       
>             | EMissedCase    
>             | EImpossible    
>             | ENoFunctorFor String
>	      | EFOfnonDT String
>	      | ECyclicType 
>	      | EDifferentConstructors

> instance Show LocalErrMsg where
>   showsPrec _ e = showString (prError e)

> prError :: LocalErrMsg -> String
> prError (EUnifyConstApp c)  = "Unify: constructor `" ++ c ++
>                               "' can not be unified with type application"
> prError EUnifyKind       = "Unify: kind error"
> prError ENoMuApp         = "Unify: Mu f can't match a type application"
> prError (ENoFunctorFor d)= "Unify: No functor defined for datatype constructor "++d
> prError (EFOfnonDT msg)  = "punifyFOf: "++ msg
> prError EMissedCase      = "Unify: missed a case"
> prError EImpossible	   = "Unify: impossible! Internal error."
> prError ECyclicType	   = "unifyVar: Cyclic types not allowed"
> prError EDifferentConstructors = "Unify: different constructors"

> internalError :: String -> a
> internalError s = error ("Internal PolyP error: " ++ s)

> {-
> unimpl :: String -> a
> unimpl s = internalError (s++" is not implemented yet")
> -}

> impossible :: String -> a
> impossible s = internalError ("impossible: "++s)

\end{verbatim}
