> module Flags(Flags(..),flags) where
> import CommandLine(unsafeGetArgs,unsafeGetEnvDef)

> data Flags = Flags {verbose          :: Bool, 
>		      version          :: Bool, 
>		      help	       :: Bool,
>		      requests         :: [String],
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
>		        version          = False,
>			help             = False,
>			requests	 = [],
>		        preludeFileNames = [preludeFileName],
>			fileargs         = []}

> flags :: Flags
> flags = analyseFlags unsafeGetArgs

> analyseFlags :: [String] -> Flags
> analyseFlags []            = defaultflags
> analyseFlags (fl:rest)     
>    | isVersionFlag fl      = (analyseFlags rest) {version = True}	    
>    | isVerboseFlag fl      = (analyseFlags rest) {verbose = True}	    
>    | isHelpFlag fl	     = (analyseFlags rest) {help    = True}	    
> analyseFlags (fl:name:rest) 
>    | isIncludeFlag fl      = mapPrFileName (name:) (analyseFlags rest)
>    | isRequestFlag fl      = mapRequests    (name:) (analyseFlags rest)
> analyseFlags (file:rest)   = mapFileArgs   (file:) (analyseFlags rest)

> mapPrFileName :: ([String] -> [String]) -> Flags -> Flags
> mapPrFileName f x = x {preludeFileNames = f (preludeFileNames x)}

> mapRequests :: ([String] -> [String]) -> Flags -> Flags
> mapRequests f x = x {requests = f (requests x)}

> mapFileArgs :: ([String] -> [String]) -> Flags -> Flags
> mapFileArgs f x = x {fileargs = f (fileargs x)}

> isIncludeFlag :: String -> Bool
> isIncludeFlag = ("-p"==)

> isVerboseFlag :: String -> Bool
> isVerboseFlag = ("-v"==)

> isVersionFlag :: String -> Bool
> isVersionFlag = ("--version"==)

> isRequestFlag :: String -> Bool
> isRequestFlag = ("-r"==)

> isHelpFlag :: String -> Bool
> isHelpFlag ('-':c:_) = c `elem` "h?"
> isHelpFlag _	       = False
