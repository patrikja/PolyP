\chapter{Environments}
\begin{verbatim}

> module Env where

> import MyPrelude(mapSnd)
> import MonadLibrary(StateM,State,updateSTM,updateST,fetchSTM,fetchST,
>                     (<@-),(<@))

\end{verbatim}
Should not export info about the implementation of Env.
\section{Interface}
\begin{verbatim}

> type Env k v = [(k, v)]

> mapEnv     :: (val->val') -> Env key val -> Env key val'
> newEnv     :: Env key val
> lookupEnv  :: Eq key => key  -> Env key val -> Maybe val
> lookupEqEnv:: (k->k->Bool) -> k -> Env k val -> Maybe val
> showsEnv   :: (Show key,Show val) => Env key val -> ShowS
> extendEnv  :: key -> val   -> Env key val -> Env key val
> extendsEnv :: [(key, val)] -> Env key val -> Env key val
> extendsAfterEnv :: [(k, val)] -> Env k val -> Env k val
> combineEnv :: Env key val  -> Env key val -> Env key val
> assocsEnv  :: Env key val  -> [(key, val)]

> type Cache a b = Env a b

\end{verbatim}

\section{Implementation}

\begin{verbatim}

> mapEnv = map . mapSnd

> newEnv = []

> lookupEnv = lookup -- from the Prelude

lookupEnv k [] = Nothing
lookupEnv key ((key', val') : env)
  = if key == key' then Just val' else lookupEnv key env

> lookupEqEnv eq = lookup' 
>   where lookup' k [] = Nothing
>         lookup' k ((k', val') : env)
>           = if k `eq` k' then Just val' else lookup' k env

> showsEnv env = shows env

> extendEnv key val env = (key, val) : env

\end{verbatim}
Maybe the show should give \texttt{\{ {\tt k1 |-> v1 , ... } \}}.
The implementation of \texttt{extendsEnv} is important when it comes to
efficiency and laziness. There are several tradeoffs:
\begin{itemize}
\item If the new entries are put in the end of the list the list can
  be lazily consumed without having to wait for the last addition to
  be made.
\item If the new entries are put in front of the old ones, the new
  ones will be found faster in subsequent lookups. (If this is good or
  bad depends on if the most requests are for newly inserted items or
  for early items (a prelude for example).)
\item When doing many successive concatenations it is more efficient
  to put the new elements in the beginning as the first list (that
  will have to be traversed in \verb|(++)|) will be shorter.
\end{itemize}
(This probably means that should not be implemented by a list of pairs
at all.)
A partial solution is to provide both forms:
\begin{verbatim}

> extendsEnv entries env = entries ++ env 
> extendsAfterEnv entries env = env ++ entries

> combineEnv = (++)
> assocsEnv env = env

\end{verbatim}
Interface functions for using an environment as a state in a state monad. 
\begin{verbatim}

> remember :: (Functor m, Monad m) => a -> b -> StateM m (Env a b) b   
> remember key val  = updateSTM (extendEnv key val) <@- val

> rememberST :: a -> b -> State (Env a b) b
> rememberST key val = updateST (extendEnv key val) <@- val

> lookaside key   = fetchSTM <@ lookupEnv key
> lookasideST key = fetchST  <@ lookupEnv key

\end{verbatim}
