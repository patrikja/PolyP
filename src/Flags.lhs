> module Flags(Flags(..),flags) where
> import CommandLine(unsafeGetArgs,unsafeGetEnvDef)

> data Flags = Flags {verbose          :: Bool, 
>		      help	       :: Bool,
>		      preludeFileNames :: [String],
>		      fileargs	       :: [String]}
>   deriving Show

> defaultPreludeFileName :: String

#ifdef __POLYPPRELUDE__
> defaultPreludeFileName = __POLYPPRELUDE__
#else
> defaultPreludeFileName = "PolyPrel.hs"
#endif

> preludeFileName :: String
> preludeFileName = unsafeGetEnvDef "POLYPPRELUDE" defaultPreludeFileName

> defaultflags :: Flags
> defaultflags = Flags {verbose		 = False, 
>		        help             = False,
>		        preludeFileNames = [preludeFileName],
>			fileargs         = []}

> flags :: Flags
> flags = analyseFlags unsafeGetArgs

> analyseFlags :: [String] -> Flags
> analyseFlags []            = defaultflags
> analyseFlags (fl:rest)     
>    | isVerboseFlag fl      = (analyseFlags rest) {verbose = True}	    
>    | isHelpFlag fl	     = (analyseFlags rest) {help    = True}	    
> analyseFlags (fl:name:rest) 
>    | isIncludeFlag fl      = mapPrFileName (name:) (analyseFlags rest)
> analyseFlags (file:rest)   = mapFileArgs   (file:) (analyseFlags rest)

> mapPrFileName :: ([String] -> [String]) -> Flags -> Flags
> mapPrFileName f x = x {preludeFileNames = f (preludeFileNames x)}

> mapFileArgs :: ([String] -> [String]) -> Flags -> Flags
> mapFileArgs f x = x {fileargs = f (fileargs x)}

> isIncludeFlag :: String -> Bool
> isIncludeFlag = ("-p"==)

> isVerboseFlag :: String -> Bool
> isVerboseFlag = ("-v"==)

> isHelpFlag :: String -> Bool
> isHelpFlag ('-':c:_) = c `elem` "h?"
> isHelpFlag _	       = False
