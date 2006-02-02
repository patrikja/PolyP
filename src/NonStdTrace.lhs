> module NonStdTrace(trace,unsafePerformIO) where

In Gofer and older hugs - this was required
  primitive trace "primTrace" :: String -> a -> a

#ifdef __HBC__
> import Trace(trace)
> import UnsafePerformIO(unsafePerformIO)
#else 
#if __GLASGOW_HASKELL__ > 600
> import Debug.Trace(trace)
> import System.IO.Unsafe(unsafePerformIO)
#else
> import IOExts(trace)
> import IOExts(unsafePerformIO)
#endif 
#endif 

ALternative definition:

trace :: String -> a -> a
trace _ y = y

