---------------------------------------------------------------------------
Some graph algorithms based on:
  Lazy Depth-First Search and Linear Graph Algorithms in Haskell
  David King and John Launchbury
---------------------------------------------------------------------------

> module GraphLibrary where
> import MyPrelude(swap)
> import Array(Array,array,accumArray,bounds,indices,(!))
> import StateFix -- (ST [,runST [,RunST]]) for hugs, ghc, hbc

> type Vertex  = Int

Representing graphs:

> type Table a = Array Vertex a
> type Graph   = Table [Vertex]

> vertices :: Graph -> [Vertex]
> vertices  = indices

> type Edge = (Vertex,Vertex)

> edges    :: Graph -> [Edge]
> edges g   = [ (v, w) | v <- vertices g, w <- g!v ]

> mapT    :: (Vertex -> a -> b) -> Table a -> Table b
> mapT f t = array (bounds t) [ (v,f v (t!v)) | v <- indices t ]

> type Bounds = (Vertex, Vertex)

> outdegree :: Graph -> Table Int
> outdegree  = mapT numEdges
>              where numEdges v ws = length ws

> buildG :: Bounds -> [Edge] -> Graph
> buildG  = accumArray (flip (:)) []

> transposeG  :: Graph -> Graph
> transposeG g = buildG (bounds g) (reverseE g)

> reverseE :: Graph -> [Edge]
> reverseE = map swap .  edges

> indegree :: Graph -> Table Int
> indegree  = outdegree . transposeG


Depth-first search

> data Tree a   = Node a (Forest a)
> type Forest a = [Tree a]

> dff          :: Graph -> Forest Vertex
> dff g         = dfs g (vertices g)

> dfs          :: Graph -> [Vertex] -> Forest Vertex
> dfs g vs      = pruneF (bounds g) (map (generate g) vs)

> generate     :: Graph -> Vertex -> Tree Vertex
> generate g v  = Node v (map (generate g) (g!v))

> type Set s    = MutArr s Vertex Bool

> mkEmpty      :: Bounds -> ST s (Set s)
> mkEmpty bnds  = newArr bnds False

> contains     :: Set s -> Vertex -> ST s Bool
> contains m v  = readArr m v

> include      :: Set s -> Vertex -> ST s ()
> include m v   = writeArr m v True

> pruneF        :: Bounds -> Forest Vertex -> Forest Vertex

> pruneF bnds ts = __RUNST__ (mkEmpty bnds  >>= \m ->
>                             chop m ts)

> chop         :: Set s -> Forest Vertex -> ST s (Forest Vertex)
> chop m []     = return []
> chop m (Node v ts : us)
>               = contains m v >>= \visited ->
>                 if visited then
>                   chop m us
>                 else
>                   include m v >>= \_  ->
>                   chop m ts   >>= \as ->
>                   chop m us   >>= \bs ->
>                   return (Node v as : bs)

Topological sorting

> postorder :: Tree a -> [a]
> postorder (Node a ts) = postorderF ts ++ [a]

> postorderF   :: Forest a -> [a]
> postorderF ts = concat (map postorder ts)

> postOrd      :: Graph -> [Vertex]
> postOrd       = postorderF . dff

> topSort      :: Graph -> [Vertex]
> topSort       = reverse . postOrd

Strongly connected components

> scc          :: Graph -> Forest Vertex
> scc g         = dfs (transposeG g) (reverse (postOrd g))

> scc'         :: Graph -> Forest Vertex
> scc' g        = dfs g (reverse (postOrd (transposeG g)))
