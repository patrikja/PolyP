module ThreadFuns(propagate,cross) where
import Thread(thread)
import PolyPTypes

cross :: Regular d => d [a] -> [d a]
cross = thread 

propagate :: Regular d => d (Maybe a) -> Maybe (d a)
propagate = thread 
