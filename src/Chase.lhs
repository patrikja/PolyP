\subsection{Chasing Imports}
Chase a set of possibly recursive module imports maintaining a list of
files to try and a list of files that have been found.

980501: yet to be written

> module Chase(chaseImports)  where
> chaseImports = chaseImports

#if 0
> chaseImports :: [String] -> [String] -> [String] -> IO [String]
> chaseImports path [] seen 
>   = return seen
> 
> chaseImports path (file:files) seen 
>   | file `elem` seen
>   = chaseImports path files seen
> 
>   | otherwise
>   = do
>       imports <- getImports path file
>       --putStrLn (concat $ ["File ", file, " imports: "] ++ imports)
>       chaseImports path (imports ++ files) (file:seen)
> 
> getImports :: [String] -> String -> IO [String]
> getImports path file = do
>   decls <- map (fromMaybe []) (tryRead path file)
>   --print decls
>   return (catMaybes [mbImportName s | Haskell s <- decls])
#endif 
