fmapM_Ppr      :: Monad m => (a->m c) -> (b->m d) -> (a,b) -> m (c,d)
fmapM_e        :: Monad m => (a->m c) -> (b->m d) -> () -> m ()
fmapM_f0       :: Monad m => (a->m c) -> (b->m d) -> Either () (a,b) -> m (Either () (c,d))
fmapM_A0r      :: Monad m => (a->m c) -> (b->m d) -> [b] -> m [d]
fmapM_f4Rose   :: Monad m => (a->m c) -> (b->m d) -> (a,[b]) -> m (c,[d])
