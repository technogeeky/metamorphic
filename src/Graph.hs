-----------------------------------------------------------------------------
-- |
-- Module      :  Graph
-- Copyright   :  (C) 2012 Drew Day
--             :  (C) 1999 Martin Erwig
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Drew Day <drewday@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Code adapted from: 
-- <http://web.engr.oregonstate.edu/~erwig/meta/>
--
-- Documentation (and further updates in technique) forthcoming.
----------------------------------------------------------------------------


module Graph (
   -- types
   Node,Graph,                                              -- abstract
   Edge(..),Adj(..),Context(..),MContext(..),Decomp(..),    -- transparent
   -- main functions
   empty,embed,match,
   -- derived operations
   isEmpty,matchAny,matchSome,matchThe,context,(\\),
   suc,pre,neighbors,out,inn,indeg,outdeg,deg,
   suc',pre',neighbors',out',inn',indeg',outdeg',deg',node',lab',
   noNodes,nodeRange,nodes,labNodes,edges,labEdges,
   -- graph folds
   ufold,gfold,
   -- graph transformations
   undir,
   -- utilities to build graphs
   newNodes,insNode,insNodes,insEdge,insEdges,mkGraph,buildGr
   ) where

import SimpleMap
import Thread (threadMaybe,threadList)
import Data.Maybe (fromJust)
import Data.List (nub)


--
--  Graph.hs -- Inductive Graphs  (c) 1999 by Martin Erwig
--
--  The implementation is based on extensible finite maps.
--  For fixed size graphs, see StaticGraph.hs
--
--  Graph Algorithms:    GraphAlg.hs
--  Example Graphs:      GraphData.hs
--

----------------------------------------------------------------------
-- TYPES
----------------------------------------------------------------------


-- abstract
--
type Node = Int
data Graph a b = Graph (GraphRep a b)


-- transparent
--
type Edge b       = (Node,Node,b)
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) -- Context a b "=" Context' a b "+" Node
type MContext a b = Maybe (Context a b)
type Decomp a b   = (MContext a b,Graph a b)


-- local
--
type Context' a b = (Adj b,a,Adj b)
type GraphRep a b = FiniteMap Node (Context' a b)


type Dir a b      = (Context a b) -> [Node]  -- direction of fold
type Dagg a b c d = (Context a b) -> c -> d  -- depth aggregation
type Bagg a b     = (Maybe a -> b -> b,b)    -- breadth/level aggregation

updAdj :: GraphRep a b -> Adj b -> (b -> Context' a b -> Context' a b) -> GraphRep a b


addSucc   v l (pre,lab,suc) = (                   pre, lab ,             (l,v):suc)
addPred   v l (pre,lab,suc) = (           (l,v) : pre, lab ,                   suc)
clearSucc v l (pre,lab,suc) = (                   pre, lab ,filter ((/=v).snd) suc)
clearPred v l (pre,lab,suc) = (filter ((/=v).snd) pre, lab ,                   suc)

updAdj g []         f              = g
updAdj g ((l,v):vs) f | elemFM g v = updAdj (updFM g v (f l)) vs f
                      | otherwise  = error ("Edge Exception, Node: "++show v)

-- pairL x ys = map ((,) x) ys
-- pairR x ys = map (flip (,) x) ys
fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
thd4 (_,_,x,_) = x
fth4 (_,_,_,x) = x

-- projecting on context elements
--
context1 v g = fst4 (context v g)
context2 v g = snd4 (context v g)
context3 v g = thd4 (context v g)
context4 v g = fth4 (context v g)

----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------

empty ::                             Graph a b 
embed :: Context a b -> Graph a b -> Graph a b 
match ::                     Node -> Graph a b -> Decomp a b
matchAny  ::                                     Graph a b -> (Context a b,Graph a b)
isEmpty   ::  Graph a b         -> Bool
matchSome :: (Graph a b -> Node -> Bool)      -> Graph a b -> (Context a b,Graph a b)
matchThe  :: (Graph a b -> Node -> Bool)      -> Graph a b -> (Context a b,Graph a b)
context   ::                            Node  -> Graph a b ->  Context a b
(\\)      ::  Graph a b             -> [Node] -> Graph a b


empty =  Graph emptyFM

embed (pre,v,l,suc) (Graph g) | elemFM g v = error ("Node Exception, Node: "++show v)
                              | otherwise  = Graph g3
      where g1 = addToFM g v (pre,l,suc)
            g2 = updAdj g1 pre (addSucc v)
            g3 = updAdj g2 suc (addPred v)         
      
match v (Graph g) = 
      case splitFM g v of 
           Nothing -> (Nothing,Graph g)
           Just (g,(_,(pre,lab,suc))) -> (Just (pre',v,lab,suc),Graph g2)
                where suc' = filter ((/=v).snd) suc
                      pre' = filter ((/=v).snd) pre
                      g1   = updAdj g  suc' (clearPred v)
                      g2   = updAdj g1 pre' (clearSucc v)



-- derived/specialized observers
--
-- match      matches a specified node
-- matchAny   matches an arbitrary node
-- matchSome  matches any node with a specified property
-- matchThe   matches a node if it is uniquely characterized by the given property
--

isEmpty  (Graph g) = case g of {Empty -> True; _ -> False}

matchAny (Graph Empty)              = err_emp
matchAny g@(Graph (Node _ (v,_) _)) = (c,g') where (Just c,g') = match v g

matchSome _ (Graph Empty) = err_emp
matchSome p       g       = case filter (p g) (nodes g) of
                  []      ->  err_404
                  (v:vs)  ->  (c,g') where (Just c,g') = match v g

matchThe _ (Graph Empty) = err_emp
matchThe p       g       = case filter (p g) (nodes g) of
                  []   ->  err_404
                  [v]  ->  (c,g') where (Just c,g') = match v g
                  _    ->  err_300

context v (Graph g) = 
        case lookupFM g v of 
             Nothing            -> error ("Match Exception, Node: "++show v)
             Just (pre,lab,suc) -> (filter ((/=v).snd) pre,v,lab,suc)

g \\ []     = g
g \\ (v:vs) = snd (match v g) \\ vs


err_emp   = error "Match Exception: Empty Graph"
err_404   = error "Match Exception: No such node found"
err_300   = error "Match Exception: More than one node found"


suc       :: Graph a b -> Node -> [Node]
pre       :: Graph a b -> Node -> [Node]
neighbors :: Graph a b -> Node -> [Node]
nodes     :: Graph a b         -> [Node]
out       :: Graph a b -> Node -> [Edge b]
inn       :: Graph a b -> Node -> [Edge b]
labEdges  :: Graph a b         -> [Edge b]
labNodes  :: Graph a b         -> [(Node,a)]
indeg     :: Graph a b -> Node -> Int
outdeg    :: Graph a b -> Node -> Int
deg       :: Graph a b -> Node -> Int
noNodes   :: Graph a b         -> Int
nodeRange :: Graph a b         -> (Node,Node)



undir     ::                                 Graph a ()                                   -> Graph a ()
gmap      :: (Context a b -> Context a b) -> Graph a b                                    -> Graph a b
buildGr   :: [Context a b]                -> Graph a b
insNode   ::                                 Graph a b ->  (Node,a)                       -> Graph a b
insNodes  ::                                 Graph a b -> [(Node,a)]                      -> Graph a b
insEdge   ::                                 Graph a b                ->  (Node,Node,b)   -> Graph a b
insEdges  ::                                 Graph a b                -> [(Node,Node,b)]  -> Graph a b
mkGraph   ::                                              [(Node,a)]  -> [(Node,Node,b)]  -> Graph a b
newNodes  ::                          Int -> Graph a b ->  [Node]

gfold     :: (Dir a b) -> (Dagg a b c d) -> (Bagg d c) -> [Node] -> Graph a b -> c
ufold     :: ((Context a b) -> c -> c) -> c -> Graph a b -> c

-- informations derived from specific contexts
--
neighbors g v = (\(p,_,_,s) -> map snd (p++s)     )    (context  v g)
deg       g v = (\(p,_,_,s) -> length p + length s)    (context  v g)
out       g v = map (\(l,w) -> (v,w,l)            )    (context4 v g)
inn       g v = map (\(l,w) -> (w,v,l)            )    (context1 v g)
suc       g v = map snd                                (context4 v g)
pre       g v = map snd                                (context1 v g)
outdeg    g v = length                                 (context4 v g)
indeg     g v = length                                 (context1 v g)

-- above operations for already given contexts
--
neighbors' (p,_,_,s) = map snd p ++ map snd s
deg'       (p,_,_,s) =  length p +   length s

pre'       (p,_,_,_) = map snd p
suc'       (_,_,_,s) = map snd s
indeg'     (p,_,_,_) = length p
outdeg'    (_,_,_,s) = length s

out'       (p,_,_,_) = p
inn'       (_,_,_,s) = s

labNode'   (_,v,l,_) = (v,l)
node'      (_,v,_,_) =  v
lab'       (_,_,l,_) =    l





-- gobal projections/selections
--
noNodes   (Graph g)      = sizeFM g
nodeRange (Graph Empty)  = (    0       ,     -1     )
nodeRange (Graph g)      = (ix (minFM g),ix (maxFM g)) where ix = fst.fromJust
nodes     (Graph g)      = map       fst                                         (fmToList g)
labNodes  (Graph g)      = map       (\(v,(_,l,_)) -> (v,l)                    ) (fmToList g)
edges     (Graph g)      = concatMap (\(v,(_,_,s)) -> map (\(_,w) -> (v,w))   s) (fmToList g)
labEdges  (Graph g)      = concatMap (\(v,(_,_,s)) -> map (\(l,w) -> (v,w,l)) s) (fmToList g)


-- graph folds
--
ufold f u (Graph Empty) = u
ufold f u g             = f c (ufold f u g') where (c,g') = matchAny g


threadGraph f c = threadMaybe f c match

-- gfold1 f d b u = threadGraph (\c->d (labNode' c)) (\c->gfoldn f d b u (f c))
gfold1 f d b = threadGraph d (\c->gfoldn f d b (f c))
gfoldn f d b = threadList b (gfold1 f d b)

-- gfold :: ((Context a b) -> [Node]) -> ((Node,a) -> c -> d) -> 
--          (Maybe d -> c -> c) -> c -> [Node] -> Graph a b -> c
-- gfold f d b u l g = fst (gfoldn f d b u l g)


-- These are probably earler attempts at the types: -DD
--
-- type Dagg a b c = (Node,a) -> b -> c       -- depth aggregation
-- 
-- gfold :: (Dir a b) -> (Dagg a c d) -> (Bagg d c) -> [Node] -> Graph a b -> c
-- gfold f d (b,u) l g = fst (gfoldn f d b u l g)



gfold f d b l g = fst (gfoldn f d b l g)


gmap f = ufold (\c g -> embed (f c) g) empty

undir = gmap (\(p,v,l,s) -> let ps = nub (p++s) in (ps,v,l,ps))
              
newNodes i g         = [n..n+i]                           where n = 1 + foldr max 0 (nodes g)
insNode    g (v,l)   = embed ([],v,l,[]) g
insEdge    g (v,w,l) = embed (pre,v,lab,(l,w):suc) g'     where (Just (pre,_,lab,suc),g') = match v g

insNodes g vs = foldr (flip insNode) g vs 
insEdges g es = foldr (flip insEdge) g es
buildGr       = foldr    embed   empty
                  
mkGraph vs es = insEdges (insNodes empty vs) es 

-- undirBy :: (b -> b -> b) -> Graph a b -> Graph a b
-- undirBy = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))



----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------


-- pretty printing
--
showsGraph :: (Show a,Show b) => GraphRep a b -> ShowS
showsGraph Empty = id
showsGraph (Node l (v,(_,lab,suc)) r) = showsGraph l . ("\n\t "++) . 
     shows v . (" : "++) . shows lab . (" -> "++) . shows suc . showsGraph r
                
instance (Show a,Show b) => Show (Graph a b) where
  showsPrec _ (Graph g) = showsGraph g

