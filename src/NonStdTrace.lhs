> module NonStdTrace(trace) where

primitive trace "primTrace" :: String -> a -> a

#ifdef __DEBUG__
#ifndef __HBC__

> import IOExts(trace)

#else /* __HBC__ */

> trace x y = y  --*** replace by proper hbc-code for debugging

#endif /* __HBC__ */
#else /* not __DEBUG__ */

> trace x y = y

#endif /* __DEBUG__ */

