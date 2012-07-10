-----------------------------------------------------------------------------
-- |
-- Module      :  Alib
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

module Alib where

import Data.Maybe (fromMaybe)

import A

import Tree
import Graph (Graph,Context,MContext,Node,
              empty,embed,isEmpty,match,matchAny)
import qualified Heap as H
import qualified SimpleMap as M

-----------------------------------------------------------------------------------------------------------------------------
-- * Constructors (Emitters) and Destructors (Absorbers) -- Functions
-----------------------------------------------------------------------------------------------------------------------------

cNat      =  fromU      0   succ
dNat      =    toU   (==0)  pred
cList     =  fromB     []        (:)
dList     =    toB    null  head     tail


cRose     = undefined
dRose     = undefined

cProd     =  fromB  (1)   (*)
dProd     =  undefined

dPqueueH  = toB' H.isEmpty H.splitMin

dPqueue xs | null xs   = UII_U
           | otherwise = II x (delFst x xs)
                         where x = foldr1 min xs
                               delFst x []                 = []
                               delFst x (y:ys) | y==x      = ys
                                               | otherwise = y:delFst x ys




-----------------------------------------------------------------------------------------------------------------------------
-- Simple (non-parametric) ADTs
-----------------------------------------------------------------------------------------------------------------------------

nat       :: SymA     I                        Int
evn       :: SymA     I                        Int
halves    :: SymA     I                        Int
nat2      ::                                           (IxI -> Bool)  -> (IxI -> IxI)  
             -> A  (            )  ( II   Int) IxI
rng       ::    A  (  I      Int)  ( II   Int) Int
rng'      ::    A  (            )  ( II   Int) Int
count     ::    A  ( II   a  Int)     I   Int
prod      ::    A  ( II  Int Int)     I   Int
summ      ::    A  ( II  Int Int)     I   Int
bool      :: BinA        Bool         Bool
boolAnd   :: BinA        Bool         Bool


nat       =  A cNat                                 dNat 
evn       =  A        (fromU 0 (succ . succ))             (toU (<=0) (pred . pred))
halves    =  A cNat                                       (toU (==0) (`div` 2)    )
rng       =  A cNat                                       (toB (==0) id pred)
rng'      =  A        (\()->   0  )                       (toB (==0) id pred)
nat2  p f =  A        (\_ -> (0,0))                       (toB   p   fst f)
count     =  A        (fromB 0 (\_ x -> succ x))    dNat
prod      =  A        (fromB 1 (*)             )    dNat
summ      =  A        (fromB 0 (+)             )    dNat
graph     =  A cGraph                                     (toB' isEmpty matchAny)
bool      =  A        (fromB False (||))                  (toB' not (\_ -> (True,False)) )
boolAnd   =  A        (fromB True  (&&))                  (toB' id  (\_ -> (True,True )) )


-----------------------------------------------------------------------------------------------------------------------------
-- * Familar Data Structures
-----------------------------------------------------------------------------------------------------------------------------

set       :: (Num a, Eq a)          =>  BinA       a               [a]
list      ::                            BinA       a               [a]
queue     ::                            BinA       a               [a]
pqueue    :: Ord a                  =>  BinA       a               [a]
pqueueH   :: Ord a                  =>  BinA       a        (H.Heap a)
jPqueueH  :: Ord a                  => JoinA       a         H.Heap
jQueue    ::                           JoinA       a               [ ]
jList     ::                           JoinA       a               [ ]
jPqueue   :: Ord a                  => JoinA       a               [ ]
bag       :: Ord a                  =>  BinA       a   (M.FiniteMap a   Int )
arr       :: Ord i => (a -> a -> a) ->  BinA   (i ,a)  (M.FiniteMap i    a  )
fork      :: Ord a                  =>     A (II        a        [a])  (IIV     [a] )         [a]
final     ::                               A (II        a  (Maybe a))  (Id          )   (Maybe a)
combine   ::                               A (IIV      [a]       [a])  (II       a  )         [a]
tree      ::                            SymA (IIV       a           )  (Tree     a  ) 
rose      ::                            SymA (Power     a           )  (Rose     a  )
graph     ::                            BinA (Context   a     b     )  (Graph    a b)
type                   LinGraph a b =   II   (Context   a     b     )  (Graph    a b)
cGraph    ::           LinGraph a b ->                                  Graph    a b




-----------------------------------------------------------------------------------------------------------------------------------
-- * 22 data structures in 22 lines
-----------------------------------------------------------------------------------------------------------------------------
list      =  A cList                                         dList
rose      =  A cRose                                         dRose
pqueue    =  A cList                                         dPqueue
set       =  A cList (toB     null  head rest)
queue     =  A cList (toB     null  last init)
pqueueH   =  A       (fromB   H.Empty   H.insert           ) dPqueueH
final     =  A       (fromB   Nothing  (Just `o` fromMaybe))          (toId id)
tree      =  A       (fromT   Leaf      Branch             )          (toT isLeaf key left right) 
fork      =  A cList                                                  (toT null (sel (==)) (sel (<)) (sel (>)))
combine   =  A       (fromT    []        append213 )          dList 
arr     f =  A       (fromB   M.emptyFM (accum f)  )                  (toB' M.isEmptyFM split_arr)
bag       =  A       (fromB   M.emptyFM  add       )                  (toB' M.isEmptyFM split_bag)
forest'   =  A       (fromP   Null Nd)                                (toP' isNull  cut                        )
forest    =  A       (fromId      id)                                 (toB  null   (map root) (concat.map kids))
cGraph =              fromB    empty                          embed


stack     =           list
jStack    =          jList
jList     =  joinView list
jQueue    =  joinView queue                   
jPqueue   =  joinView pqueue
jPqueueH  =  joinView pqueueH
               
-----------------------------------------------------------------------------------------------------------------------------
-- ** Helpers (Selectors, Appends (with swap))
-----------------------------------------------------------------------------------------------------------------------------

sel       :: (a -> a -> Bool)      -> [a] -> [a]
rest      :: (Eq a)                => [a] -> [a]
append213 ::                          [a] -> [a] -> [a] -> [a]

sel  f l@(x:_)      = filter (flip f x)  l                                                
rest     (x:xs)     = filter (/=x)      xs                                                
append213     y x z = x ++ y ++ z                                                         


-----------------------------------------------------------------------------------------------------------------------------
-- ** Helpers (Accumulation and Splitting)
-----------------------------------------------------------------------------------------------------------------------------

accum     :: (Ord o) => (a -> a -> a) -> (o, a) -> M.FiniteMap o a ->         M.FiniteMap o a
add       :: (Ord o, Num a)        =>     o     -> M.FiniteMap o a ->         M.FiniteMap o a
split_bag :: (Ord o, Eq a, Num a)  =>              M.FiniteMap o a -> ( o   , M.FiniteMap o a)
split_arr :: (Ord o)               =>              M.FiniteMap o a -> ((o,a), M.FiniteMap o a)


accum  f (i,x) a = M.accumFM  a  i  f   x                                            
add         x  b = M.accumFM  b  x (+)  1                                            

split_bag  b = 
               let                                                                   
                    Just                           (b'', (x ,c)) = M.splitMinFM b
                    b'   = if (==) c 1 then         b''      
                         else        M.addToFM      b'' x (c-1)
               in (x,b') 
split_arr a =  let  Just  (a',x) = M.splitMinFM a                                    
               in       (x,a') 



-----------------------------------------------------------------------------------------------------------------------------
-- * Constructors (Emitters) and Destructors (Absorbers) -- Type Signatures
-----------------------------------------------------------------------------------------------------------------------------


-- |                                                         construct (resp. destroy) a 'I' of Naturals using 'Int's.
cNat      ::    I       Int   -> Int
dNat      ::                     Int ->    I           Int
-- ^                                                         construct (resp. destroy) a 'I'  of Naturals using 'Int's.
-- |                                                         construct (resp. destroy) a 'II' of @a@s using Lists
cList     ::   II   a   [a]   -> [a]
dList     ::                     [a] ->   II  a        [a]
-- ^                                                         construct (resp. destroy) a 'II' of @a@s using base Lists
dPqueue   :: Ord a =>            [a] ->   II  a        [a]
-- ^                                                         destroy priority queue (a 'II' over base Lists)
dPqueueH  :: Ord a =>      H.Heap a  ->   II  a (H.Heap a)
-- ^                                                         destroy priority queue heap (a 'II' ('Bifunctor') over 'H.Heap's)
-- |                                                         construct (resp. destroy) a 'II' of two Naturals using 'Int's.
cProd     ::   II   Int Int   -> Int
dProd     ::                     Int ->   II Int       Int
-- ^                                                         construct (resp. destroy) a 'II' of two Naturals using 'Int's.

type IxI = (Int, Int) -- ^ a simple type for pairs of integers (not used yet!)



-----------------------------------------------------------------------------------------------------------------------------
-- * Rose Trees
-----------------------------------------------------------------------------------------------------------------------------

data Rose   a = Null | Nd    a   [Rose a] deriving Show
type Forest a =                  [Rose a]

forest'   ::           PowA  a   (Rose a)
forest    ::              A (Id  [Rose a] ) 
                            (II  [     a] ) 
                                 [Rose a]

-----------------------------------------------------------------------------------------------------------------------------
-- ** Rose Tree Smart Constructors
-----------------------------------------------------------------------------------------------------------------------------

isNull    :: Rose a                     -> Bool
cut       :: Rose a  -> (a,[Rose a])
root      :: Rose a  ->  a
kids      :: Rose t     -> [Rose t]

isNull Null = True
isNull ____ = False

cut  (Nd x rs) = (x,rs)   
root (Nd x __) =  x       
kids (Nd _ rs) =    rs    




-----------------------------------------------------------------------------------------------------------------------------
-- * Linear Graphs (not really complete)
-----------------------------------------------------------------------------------------------------------------------------

bufGraph ::  (JoinA  c f) 
           ->      ( c -> Node) 
           ->      ( c ->   Context a b    -> [c] ) 
           -> 
           A  ()     (II  (MContext a b))   (f c  , Graph a b)

bufGraph (A c d) f h = A (\_ -> (c UII_U,empty)) explore
         where explore (b,g) = case d b of
                 UII_U                  -> UII_U
                 II x b'    | isEmpty g -> UII_U
                            | otherwise ->  II ctx (c (II s b'), g' )
                              where          ( ctx    ,          g' ) = match (f x) g
                                             s                        = maybe [] (h x) ctx


-----------------------------------------------------------------------------------------------------------------------------
-- * Utilities
-----------------------------------------------------------------------------------------------------------------------------

q1  :: ( t, x, y, z) -> t     
q2  :: ( t, x, y, z) -> x     
q23 :: ( t, x, y, z) -> (x,y)
q4  :: ( t, x, y, z) -> z     

q1     ( t, _, _, _) = t
q2     ( _, x, _, _) = x
q23    ( _, x, y, _) = (x,y)
q4     ( _, _, _, z) = z


-- uncurrying process:
--   (\f g ->       (f .          g)  ) :: forall   a b (f :: * -> *). (Functor f) => (a -> b) -> f a -> f b
--   (\f g ->       (f . (uncurry g)) ) :: forall   a b a1 b1.                        (a -> b) -> (a1 -> b1 -> a) -> (a1,  b1) -> b
--   (\f g -> curry (f . (uncurry g)) ) :: forall c a b c1.                          (c1 -> c) -> (a  -> b -> c1) ->  a -> b   -> c

-- | curried composition
--
--o      :: forall a f g b. (b -> a) -> (f -> g -> b) -> f -> g -> a

f `o` g = curry (f . (uncurry g))

-----------------------------------------------------------------------------------------------------------------------------
-- * Extra! (perhaps not needed)
-----------------------------------------------------------------------------------------------------------------------------

-- Perhaps I'll find use for this later (to shorten Nothing)
data NoK o = No
           | OK o


infixr 8 ><
infixr 8 /\


(f >< g) (x,y) = (f x,g y)     -- never used here
(f /\ g)  x    = (f x,g x)     -- never used here

