\chapter{Type errors}
\begin{verbatim}

> module TypeError(mayreportTError, TError(..),mayshowargs, failWith) where
> import TypeGraph(HpType,NonGenerics,
>                  typeOutOfHeap,typesOutOfHeap,
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
>            typeOutOfHeap  ngs ([]:=>u) >>= \([]:=>typeU) -> 
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

\end{verbatim}
