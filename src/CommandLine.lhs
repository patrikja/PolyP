Command Line arguments transformed to global variables.

> module CommandLine where
> import NonStdTrace(unsafePerformIO)
> import System(getEnv,getArgs)

> unsafeGetArgs :: [String]
> unsafeGetArgs = unsafePerformIO getArgs

> unsafeGetEnvDef :: String -> String -> String
> unsafeGetEnvDef e def = unsafePerformIO (getEnvDef e def)

> getEnvDef :: String -> String -> IO String
> getEnvDef e def = getEnv e `catch` \ _ -> return def

 maybeGetEnv :: String -> IO (Maybe String)
 maybeGetEnv e = (getEnv e <@ Just) `catch` \ _ -> return Nothing
