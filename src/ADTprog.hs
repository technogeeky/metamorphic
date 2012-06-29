--
--  ADTprog.hs -- Examples showing the use of ADTs and transformers
--
module ADTprog where

import Data.Maybe (fromJust)

import ADT
import ADTlib

import Tree
import Graph (Graph,Context,MContext,Node,
              empty,embed,isEmpty,matchAny,mkGraph)
import GraphData
import qualified Heap as H
import qualified SimpleMap as M


----------------------------------------------------------------------
-- FOLD EXAMPLES
----------------------------------------------------------------------
fac1 = fold cProd rng'

sum' :: (Eq a,Num a) => [a] -> a
sum' = fold (fromB 0 (+)) list

sumset :: (Eq a,Num a) => [a] -> a
sumset = fold (fromB 0 (+)) set


----------------------------------------------------------------------
-- nat TRANSFORMERS
----------------------------------------------------------------------

countdown = transit rng list
fac2      = transit rng prod
log2      = pred . transit halves nat
double    = transit nat evn

{- NOTE:     foo = transit evn evn    
   is not the identity function, foo computes the successor
   for odd numbers.   
-}


----------------------------------------------------------------------
-- nat x nat TRANSFORMERS
----------------------------------------------------------------------

minus = uncurry (-)
eq0  = (==0).snd
eq0' = (==0).fst
lt0' = (<0).fst

mult   = transit (nat2 eq0  (id >< pred))   summ
power  = transit (nat2 eq0  (id >< pred))   prod
fac3 n = transit (nat2 eq0  (pred >< pred)) prod (n,n)
mod'   = transit (nat2 lt0' (minus /\ snd)) final
gcd'   = transit (nat2 eq0' (imod /\ fst))  final
         where imod = (\(Just x)->x).mod'.swap
               swap (m,n) = (n,m)
        

----------------------------------------------------------------------
-- list and set TRANSFORMERS
----------------------------------------------------------------------

length1 = trans p2 list nat
          where p2 UnitB       = UnitU
                p2 (Two _ y) = One y
                -- p2 : natural transformation from Binary to Unary
length2 = trans (ntBU (\_ y->y)) list nat
length3 = transit list count          

card :: (Eq a, Num a) => [a] -> Int
card = transit set count

size a = transit a count  
-- length = size list
-- card   = size set

mapset f = trans (fmapFst f) set set

quicksort :: Ord a => [a] -> [a]
quicksort =  transit fork combine

any2 p = trans (fmapFst p) list bool      -- take set if p is expensive!

all2 p = trans (fmapFst p) list boolAnd   -- take set if p is expensive!

histogram :: Ord a => [a] -> M.FiniteMap a Int
histogram = trans once list (arr (+))
            where once = fmapFst (\n->(n,1))
 

----------------------------------------------------------------------
-- tree TRANSFORMERS
----------------------------------------------------------------------

flipTree = transit flip tree
           where flip = ADT (con tree) (toT isLeaf key right left)

preorder = trans (ntTB id (++)) tree list
-- preorder = trans klr tree list
--            where klr UnitT         = UnitB
--                  klr (Three x y z) = Two x (y++z)
--            -- klr : natural transformation from Ternary to Binary
--            -- (see length1)

tree' :: (Tree a->t) -> (Tree a->Tree a) -> ADT () (Binary t) (Tree a)
tree' f g = ADT (\_->Leaf) (toB isLeaf f g)

binSearch :: Ord a => a -> Tree a -> Bool
binSearch x = transit (tree' ((x==).key) follow) bool
              where follow t | x<key t   = left t
                             | otherwise = right t
            
-- dfs and bfs on rose tree forests
--
dfsr = trans (ntPB id concat) forest' list
bfsr = concat.transit forest list

rose1 = Nd 1 [Nd 2 [nd 5,nd 6],nd 3,Nd 4 [nd 7]]
        where nd x = Nd x []
rose2 = Nd 1 [Nd 2 [nd 5,nd 6,Nd 61 [nd 8,nd 9]],nd 3,Nd 4 [nd 7]]
        where nd x = Nd x []

-- call, eg: dfsr rose1


----------------------------------------------------------------------
-- graph TRANSFORMERS
----------------------------------------------------------------------

build :: [Context a b] -> Graph a b
build = transit list graph


-- "simple" transformers using unordered graph decomposition
--
nodes :: Graph a b -> [Node]
nodes = trans (fmapFst q2) graph list

labNodes :: Graph a b -> [(Node,a)]
labNodes = trans (fmapFst q23) graph list

member :: Node -> Graph a b -> Bool
member v = trans (fmapFst ((v==).q2)) graph bool

noEdges :: Graph a b -> Int
noEdges = trans (fmapFst noNeighbors) graph summ
          where noNeighbors (p,_,_,s) = length p+length s

edges :: Graph a b -> [(Node,Node)]
edges = concat . trans (fmapFst incident) graph list
        where incident (p,v,_,s) = [(w,v) | (_,w) <- p]++[(v,w) | (_,w) <- s] 

labEdges :: Graph a b -> [(Node,Node,b)]
labEdges = concat . trans (fmapFst incident) graph list
           where incident (p,v,_,s) = [(w,v,l) | (l,w)<-p]++[(v,w,l) | (l,w)<-s] 

gmap :: (Context a b -> Context c d) -> Graph a b -> Graph c d
gmap f = trans (fmapFst f) graph graph

mapNodes :: (a -> a') -> Graph a b -> Graph a' b
mapNodes f = gmap (label f) where label f (p,v,l,s) = (p,v,f l,s)

mapEdges :: (b -> b') -> Graph a b -> Graph a b'
mapEdges f = gmap (label f) 
             where label f (p,v,l,s) = (map (f >< id) p,v,l,fmap (f >< id) s)

grev :: Graph a b -> Graph a b
grev = gmap swap where swap (p,v,l,s) = (s,v,l,p)


-- "buffered" transformers using indexed graph decomposition
--
mlist  = maybeView list
nodeId :: Binary (MContext a b) c -> Binary (Maybe Node) c
nodeId = fmapFst (fmap q2)

sucs _ (_,_,_,s) = fmap snd s

dfsn vs g = trans nodeId (bufGraph jStack id sucs) mlist (vs,g)
dfs g = dfsn (reverse (nodes g)) g

bfs v g = trans nodeId (bufGraph jQueue id sucs) mlist ([v],g)

-- NOTE: node costs must come first in pqueue
labSucs (y,_) (_,_,_,s) = [(y+l,v) | (l,v) <- s]
sp  v g = trans nodeId (bufGraph jPqueue  snd labSucs) mlist ([(0,v)],g)
sp1 v g = trans nodeId (bufGraph jPqueueH snd labSucs) mlist (H.unit (0,v),g)


----------------------------------------------------------------------
-- ADT STREAMS
----------------------------------------------------------------------


--  on lists
--
remdup      :: (Num a, Eq a) => [a] -> [a]
rev         :: [a] -> [a]
heapsort    :: Ord a => [a] -> [a]
bucketsort' :: Ord a => [a] -> [a]
bucketsort  :: Ord a => [a] -> [a]
      
remdup      = via list set list
rev         = via list queue list
heapsort    = via list pqueueH list
bucketsort  = via list bag list
bucketsort' = fmap fst.via list (arr (\_ _->())) list . fmap (flip (,) ())      
              -- bucketsort' removes duplicates
              

--  on graphs ???
--


----------------------------------------------------------------------
-- EXAMPLE DATA
----------------------------------------------------------------------


-- list
--
l    = [3,2,4,2,3,1,4,2]
nats = [1..]
l1   = take 10 nats
l2   = take 100 nats
l3   = take 1000 nats
l4   = take 10000 nats
forceList l = last l


-- tree
--
listToTree :: [a] -> Tree a   -- converts sorted list to binary search tree
listToTree [] = Leaf
listToTree xs = Branch {key=x,left=listToTree l,right=listToTree r}
                where (l,(x:r)) = splitAt (length xs `div` 2) xs

t = Branch 5 (Branch 3 Leaf (Branch 4 Leaf Leaf)) 
             (Branch 7 Leaf (Branch 9 Leaf Leaf)) 

t1 = listToTree l1
t2 = listToTree l2
t3 = listToTree l3
t4 = listToTree l4


-- graph
--

-- some auxiliary functions
--   labnl  : generate list of labeled nodes
--   noLab  : denote unlabeled edges
labnl c i = take i (zip [1..] [c..])
noLab (i,j)   = (i,j,())
