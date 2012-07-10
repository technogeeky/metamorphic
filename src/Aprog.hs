-----------------------------------------------------------------------------
-- |
-- Module      :  Aprog
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

module Aprog where

import Data.Maybe (fromJust)

import A
import Alib

import Tree
import Graph (Graph,Context,MContext,Node,
              empty,embed,isEmpty,matchAny,mkGraph)
import GraphData
import qualified Heap as H
import qualified SimpleMap as M

-----------------------------------------------------------------------------------------------------------------------------
-- * Simple Fold Examples
-----------------------------------------------------------------------------------------------------------------------------


sum'      :: (Eq a,Num a) => [a] -> a
sumset    :: (Eq a,Num a) => [a] -> a

fac1   = fold cProd rng'
sum'   = fold (fromB 0 (+)) list
sumset = fold (fromB 0 (+)) set

-----------------------------------------------------------------------------------------------------------------------------
-- * Numeric ( Nat ) Transformers
-----------------------------------------------------------------------------------------------------------------------------

countdown :: Int -> [Int]
fac2      :: Int -> Int
log2      :: Int -> Int
double    :: Int -> Int

countdown =        transit rng list
fac2      =        transit rng prod
log2      = pred . transit halves nat
double    =        transit nat evn

{- NOTE:     foo = transit evn evn    
   is not the identity function, foo computes the successor
   for odd numbers.   
-}

-----------------------------------------------------------------------------------------------------------------------------
-- * Numeric ( N * N ) Transformers
-----------------------------------------------------------------------------------------------------------------------------

minus ::         Num c  => (c, c ) -> c
eq0   :: (Eq  b, Num b) => (a, b ) -> Bool
eq0'  :: (Eq  b, Num b) => (b, b1) -> Bool
lt0'  :: (Ord b, Num b) => (b, b1) -> Bool
mult  ::                     IxI   -> Int
power ::                     IxI   -> Int
mod'  ::                     IxI   -> Maybe Int
gcd'  ::                     IxI   -> Maybe Int
fac3  :: Int -> Int


minus = uncurry (-)
eq0  = (== 0) . snd
eq0' = (== 0) . fst
lt0' = (<  0) . fst

mult   = transit (nat2 eq0  (id    ><  pred))  summ
power  = transit (nat2 eq0  (id    ><  pred))  prod
fac3 n = transit (nat2 eq0  (pred  ><  pred))  prod (n,n)
mod'   = transit (nat2 lt0' (minus /\  snd ))  final
gcd'   = transit (nat2 eq0' (imod  /\  fst ))  final
         where imod = (\(Just x) -> x ) . mod' . swap
               swap (m,n) = (n,m)
        
-----------------------------------------------------------------------------------------------------------------------------
-- * List and Set Transformers
-----------------------------------------------------------------------------------------------------------------------------

length1   ::                  [t] -> Int
length2   ::                  [a] -> Int
length3   ::                  [a] -> Int
length4   ::                  [a] -> Int
card      :: (Eq a, Num a) => [a] -> Int
card_alt  :: (Eq a, Num a) => [a] -> Int
quicksort :: Ord a         => [a] ->            [a]
histogram :: Ord a         => [a] -> M.FiniteMap a Int

any2      :: (a -> Bool)   -> [a] -> Bool
all2      :: (a -> Bool)   -> [a] -> Bool

size      :: A s (II a) t -> t -> Int



length1 = trans p2 list nat
          where p2 (UII_U   ) = U_I_U
                p2 ( II  _ y) =  I  y
                -- ^ p2 : natural transformation from II to Unary

size    a = transit a    count  
length3   = transit list count          
card      = transit set  count
quicksort = transit fork combine

length4   = size list
card_alt  = size set

mapset :: (Eq a, Eq b, Num a, Num b) => (a -> b) -> [a] -> [b]
mapset f   = trans (fmapLI   f             ) set  set
any2     p = trans (fmapLI   p             ) list bool      -- take set if p is expensive!
all2     p = trans (fmapLI   p             ) list boolAnd   -- take set if p is expensive!
histogram  = trans (fmapLI (\n   -> (n,1)) ) list (arr (+))
length2    = trans (ntBU   (\_ y ->   y  ) ) list nat
 

-----------------------------------------------------------------------------------------------------------------------------
-- * Tree Transformers
-----------------------------------------------------------------------------------------------------------------------------
flipTree  ::  Tree a  -> Tree a
preorder  ::  Tree a  ->     [a]
dfsr      ::  Rose a  ->     [a]
bfsr      :: [Rose a] ->     [a]

binSearch :: Ord a => a -> Tree a -> Bool

flipTree    = transit flip tree
                where flip = A (con tree) (toT isLeaf key right left)

binSearch x = transit (tree' ((x==).key) follow) bool
              where                      follow t | x < key t = left t
                                                  | otherwise = right t

-- preorder = trans klr tree list
--            where klr UnitT         = UII_U
--                  klr (Three x y z) = II x (y++z)
--            -- klr : natural transformation from Ternary to II
--            -- (see length1)

preorder = trans (ntTB id (++)  ) tree    list
dfsr     = trans (ntPB id concat) forest' list
bfsr     = concat . transit       forest  list


tree' :: (Tree a->t) -> (Tree a->Tree a) -> A () (II t) (Tree a)
tree' f g = A (\_->Leaf) (toB isLeaf f g)



rose1 :: Num a => Rose a
rose2 :: Num a => Rose a

rose1 = Nd 1 [Nd 2 [nd 5,nd 6],nd 3,Nd 4 [nd 7]]
        where nd x = Nd x []
rose2 = Nd 1 [Nd 2 [nd 5,nd 6,Nd 61 [nd 8,nd 9]],nd 3,Nd 4 [nd 7]]
        where nd x = Nd x []

-----------------------------------------------------------------------------------------------------------------------------
-- * Graph Transformers
-----------------------------------------------------------------------------------------------------------------------------

build     :: [Context a b]                -> Graph a b
gmap      :: (Context a b -> Context c d) -> Graph a b -> Graph c d
nodes     ::                                 Graph a b -> [Node]
labNodes  ::                                 Graph a b -> [(Node,a)]
member    ::                         Node -> Graph a b -> Bool
noEdges   ::                                 Graph a b -> Int
edges     ::                                 Graph a b -> [(Node,Node)]
labEdges  ::                                 Graph a b -> [(Node,Node,b)]
mapNodes  ::                    (a -> a') -> Graph a b -> Graph a' b
mapEdges  ::                    (b -> b') -> Graph a b -> Graph a  b'
grev      ::                                 Graph a b -> Graph a  b

build = transit list graph

nodes      =          trans (fmapLI          q2)   graph list
labNodes   =          trans (fmapLI          q23)  graph list
member   v =          trans (fmapLI ((v==) . q2))  graph bool
noEdges    =          trans (fmapLI noLocal)       graph summ where noLocal  (p,_,_,s) = length p + length s
edges      = concat . trans (fmapLI incident)      graph list where incident (p,v,_,s) = [(w,v)   | (_,w) <- p]++[(v,w)   | (_,w) <- s] 
labEdges   = concat . trans (fmapLI incident)      graph list where incident (p,v,_,s) = [(w,v,l) | (l,w) <- p]++[(v,w,l) | (l,w) <- s] 
gmap     f =          trans (fmapLI f)             graph graph
mapNodes f =                 gmap (label f)                   where label f  (p,v,l,s) = (              p, v,f l,               s)
mapEdges f =                 gmap (label f)                   where label f  (p,v,l,s) = (map (f >< id) p, v,  l,fmap (f >< id) s)
grev       =                 gmap swap                        where swap     (p,v,l,s) = (s,v,l,p)


-- "buffered" transformers using indexed graph decomposition
--
mlist :: A (II (Maybe a) [a]) (II a) [a]
mlist  = maybeView list

nodeId :: II (MContext a b) c -> II (Maybe Node) c
nodeId = fmapLI (fmap q2)


dfsn ::                  [Node] -> Graph a b -> [Node]
bfs  ::                   Node  -> Graph a b -> [Node]
dfs  ::                            Graph a b -> [Node]
sp   :: (Num b, Ord b) => Node  -> Graph a b -> [Node]
sp1  :: (Num b, Ord b) => Node  -> Graph a b -> [Node]

dfsn vs g = trans nodeId (bufGraph jStack   id     sucs) mlist (          vs   ,g)
bfs  v  g = trans nodeId (bufGraph jQueue   id     sucs) mlist (          [v]  ,g)
sp   v  g = trans nodeId (bufGraph jPqueue  snd labSucs) mlist (       [(0,v)] ,g)
sp1  v  g = trans nodeId (bufGraph jPqueueH snd labSucs) mlist ( H.unit (0,v)  ,g)

dfs     g = dfsn (reverse (nodes g)) g

-- NOTE: node costs must come first in pqueue


-----------------------------------------------------------------------------------------------------------------------------
-- * ADT Streams
-----------------------------------------------------------------------------------------------------------------------------

remdup      :: (Num a, Eq a) => [a] -> [a]
rev         ::                  [a] -> [a]
heapsort    :: Ord a         => [a] -> [a]
bucketsort' :: Ord a         => [a] -> [a]
bucketsort  :: Ord a         => [a] -> [a]
      
remdup      =            via list set                list
rev         =            via list queue              list
heapsort    =            via list pqueueH            list
bucketsort  =            via list bag                list
bucketsort' = fmap fst . via list (arr (\_ _-> () )) list . fmap (flip (,) ())      
              -- bucketsort' removes duplicates
              

-----------------------------------------------------------------------------------------------------------------------------
-- * Example Data
-----------------------------------------------------------------------------------------------------------------------------


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

-----------------------------------------------------------------------------------------------------------------------------
-- * Auxiliary Functions
-----------------------------------------------------------------------------------------------------------------------------



sucs      :: Functor f         => t       -> (t1, t2, t3, f (a, b) )  -> f b
--labSucs   :: (Monad m, Num t4) => (t4, t) -> (t1, t2, t3, m (t4, t5)) -> m (t4, t5)

sucs       _  (_,_,_,s) = fmap snd s
labSucs (y,_) (_,_,_,s) = [ (y + l,v) | (l,v) <- s]


-- some auxiliary functions
--   labnl  : generate list of labeled nodes
--   noLab  : denote unlabeled edges

labnl :: (Enum a, Enum b, Num a) => b -> Int -> [(a, b)]
labnl c i = take i (zip [1..] [c..])

noLab :: (t, t1) -> (t, t1, ())
noLab (i,j)   = (i,j,())

