> module NonStdTrace(trace,unsafePerformIO) where

In Gofer and older hugs - this was required
  primitive trace "primTrace" :: String -> a -> a

#ifdef __HBC__
# ifdef __DEBUG__
> import Trace(trace)
# endif
> import UnsafePerformIO(unsafePerformIO)

#else 
# ifdef __DEBUG__
> import IOExts(trace)
# endif
> import IOExts(unsafePerformIO)

#endif 

#ifndef __DEBUG__
> trace :: String -> a -> a
> trace _ y = y

#endif 

