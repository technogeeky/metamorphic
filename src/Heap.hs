--
--  Pairing Heaps
--

module Heap (Heap(..),
             empty,unit,insert,merge,
             isEmpty,findMin,deleteMin,splitMin
            )
where


data Heap a = Empty | Node a [Heap a]
     deriving Eq

showsHeap :: (Show a,Ord a) => Heap a -> ShowS
showsHeap Empty       = id
showsHeap (Node x []) = shows x
showsHeap (Node x hs) = shows x . (' ':) . shows hs
                
instance (Show a,Ord a) => Show (Heap a) where
  showsPrec _ d = showsHeap d


----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------

empty     :: Ord a =>              Heap a
insert    :: Ord a =>         a -> Heap a -> Heap a
merge     :: Ord a =>              Heap a -> Heap a -> Heap a 
mergeAll  :: Ord a => [Heap a] ->  Heap a 
isEmpty   :: Ord a =>              Heap a -> Bool
findMin   :: Ord a =>              Heap a -> a
deleteMin :: Ord a =>              Heap a -> Heap a 
splitMin  :: Ord a =>              Heap a -> (a,Heap a)

empty = Empty

unit x = Node x []

insert x h = merge (unit x) h

merge h Empty = h
merge Empty h = h
merge h@(Node x hs) h'@(Node y hs') | x<y       = Node x (h':hs)
                                    | otherwise = Node y (h:hs')

mergeAll []        = Empty
mergeAll [h]       = h
mergeAll (h:h':hs) = merge (merge h h') (mergeAll hs)

isEmpty Empty = True
isEmpty _     = False
          
findMin Empty      = error "Heap.findMin: empty heap"
findMin (Node x _) = x

deleteMin Empty       = Empty
deleteMin (Node x hs) = mergeAll hs

splitMin Empty       = error "Heap.splitMin: empty heap"
splitMin (Node x hs) = (x,mergeAll hs)


----------------------------------------------------------------------
-- APPLICATION FUNCTIONS, EXAMPLES
----------------------------------------------------------------------


build     :: Ord a => [a] -> Heap a
toList    :: Ord a => Heap a -> [a]
heapsort  :: Ord a => [a] -> [a]

build = foldr insert Empty

toList Empty = []
toList h = x:toList r
           where (x,r) = (findMin h,deleteMin h)

heapsort = toList . build

l  = [6,9,2,13,6,8,14,9,10,7,5]
l' = reverse l

h1  = build l
h1' = build l'

s1  = heapsort l
s1' = heapsort l'

