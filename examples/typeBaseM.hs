fmapM_Ppr      :: Monad m => (a->m c) -> (b->m d) -> (a,b) -> m (c,d)
fmapM_e        :: Monad m => (a->m c) -> (b->m d) -> () -> m ()
fmapM_f0       :: Monad m => (a->m c) -> (b->m d) -> Either () (a,b) -> m (Either () (c,d))
fmapM_A0r      :: Monad m => (a->m c) -> (b->m d) -> [b] -> m [d]
fmapM_f4Rose   :: Monad m => (a->m c) -> (b->m d) -> (a,[b]) -> m (c,[d])

fmapMr_Ppr      :: Monad m => (a->m c) -> (b->m d) -> (a,b) -> m (c,d)
fmapMr_e        :: Monad m => (a->m c) -> (b->m d) -> () -> m ()
fmapMr_f0       :: Monad m => (a->m c) -> (b->m d) -> Either () (a,b) -> m (Either () (c,d))
fmapMr_A0r      :: Monad m => (a->m c) -> (b->m d) -> [b] -> m [d]
fmapMr_f4Rose   :: Monad m => (a->m c) -> (b->m d) -> (a,[b]) -> m (c,[d])

fmapM'_Ppr      :: Monad m => Bool -> (a->m c) -> (b->m d) -> (a,b) -> m (c,d)
fmapM'_e        :: Monad m => Bool -> (a->m c) -> (b->m d) -> () -> m ()
fmapM'_f0       :: Monad m => Bool -> (a->m c) -> (b->m d) -> Either () (a,b) -> m (Either () (c,d))
fmapM'_A0r      :: Monad m => Bool -> (a->m c) -> (b->m d) -> [b] -> m [d]
fmapM'_f4Rose   :: Monad m => Bool -> (a->m c) -> (b->m d) -> (a,[b]) -> m (c,[d])
