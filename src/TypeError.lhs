\chapter{Type errors}
\begin{verbatim}

> module TypeError(mayreportTError, TError(..),mayshowargs, failWith,
>                  ErrMsg(..), internalError, impossible) where
> import TypeGraph(HpType,NonGenerics,
>                  qtypeOutOfHeap,typesOutOfHeap,
>                  showNodePtr)
> import MonadLibrary(STErr,mliftErr,ErrorMonad(failEM),(<@),mIf,liftop,
>                     ST,(===),readVar)
> import PrettyPrinter(Pretty(..),($$),nest,text,sep,prType)
> import Grammar(Type(..),Qualified(..))

#ifdef __DEBUG_UNIFY__
> import MyPrelude(maytrace)
#else
> maytrace _ = id
#endif

> data TError t = TOk
>               | TBad String t t

> mayreportTError :: NonGenerics s -> HpType s -> TError (HpType s) -> STErr s ()
> mayreportTError ngs a TOk            = return ()
> mayreportTError ngs a (TBad msg t u) = 
>           mliftErr (outofhp (a,t) u) >>= \((tA,tT),tU)->
>           failEM (show (typeerror msg tA tT tU))
>    where 
>      outofhp p u =
>            typesOutOfHeap ngs p        >>= \tp    -> 
>            qtypeOutOfHeap  ngs ([]:=>u) >>= \([]:=>typeU) -> 
>            return (tp,typeU)
>      typeerror mess ta t u =
>        (text "Type instantiation error in:")
>        $$ nest 3 (pretty ta)
>        $$ text mess
>        $$ nest 3 (pretty t $$ pretty u)

> failWith :: String -> HpType s -> HpType s -> STErr s b
> failWith mess a b = mliftErr (typesOutOfHeap [] (a,b)) >>= \p->
>                     failEM (show (err p))
>   where err (a,b)= sep [text "can't unify:",
>                         nest 3 (sep [pretty a,text "with",pretty b])] 
>                    $$ text ("as "++mess)

> mayshowargs :: HpType s -> HpType s -> STErr s ()
> mayshowargs a b = mliftErr (typesOutOfHeap [] (a,b) >>= mayshowtypes a b)

> mayshowtypes :: HpType s -> HpType s -> (Type,Type) -> ST s ()
> mayshowtypes a b (t,t') = showNodePtr a >>= \sa ->
>                           showNodePtr b >>= \sb ->
>                           maytrace (concat [ "a=",sa,"=",st,
>                                              ",b=",sb,"=",st']) 
>                           (return ())
>    where st = show (pretty t) 
>          st'= show (pretty t') 


> data ErrMsg = EUnifyConstApp String 
>             | EUnifyKind     
>             | ENoMuApp       
>             | EMissedCase    
>             | EImpossible    
>             | ENoFunctorFor String
>	      | EFOfnonDT      

> instance Show ErrMsg where
>   showsPrec _ e = showString "ErrMsg:" . showString (prError e)


> prError :: ErrMsg -> String
> prError (EUnifyConstApp c)  = "Unify: constructor `" ++ c ++
>                               "' can not be unified with type application"
> prError EUnifyKind       = "Unify: kind error"
> prError ENoMuApp         = "Unify: Mu f can't match a typeapplication"
> prError (ENoFunctorFor d)= "Unify: No functor defined for datatype constructor "++d
> prError EFOfnonDT        = "FunctorOf <not datatype>"

-- partially applied types are not Regular

> internalError :: String -> a
> internalError s = error ("Internal PolyP error: " ++ s)

> unimpl :: String -> a
> unimpl s = internalError (s++" is not implemented yet")

> impossible :: String -> a
> impossible s = internalError ("impossible: "++s)

\end{verbatim}
