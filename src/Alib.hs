--
--  Alib.hs -- A Library of As
--
module Alib where

import Data.Maybe (fromMaybe)

import A

import Tree
import Graph (Graph,Context,MContext,Node,
              empty,embed,isEmpty,match,matchAny)
import qualified Heap as H
import qualified SimpleMap as M
-- import Geo


----------------------------------------------------------------------
-- SOME UTILITIES
----------------------------------------------------------------------

infixr 8 ><
infixr 8 /\


-- some operations for tuples
--
(f >< g) (x,y) = (f x,g y)
(f /\ g)  x    = (f x,g x)

q1  (a,_,_,_) = a
q2  (_,b,_,_) = b
q23 (_,b,c,_) = (b,c)
q4  (_,_,_,d) = d


-- curried composition
--
f `o` g = curry (f . (uncurry g))


----------------------------------------------------------------------
-- CONSTRUCTORS AND DESTRUCTORS
----------------------------------------------------------------------

cNat ::   I   Int -> Int
cNat =  fromU 0 succ

cProd ::   II   Int Int -> Int
cProd =  fromB 1 (*)

dNat :: Int ->   I   Int
dNat =  toU (==0) pred

cList ::   II   a [a] -> [a]
cList =  fromB [] (:)

dList :: [a] ->   II   a [a]
dList =  toB null head tail

dPqueue :: Ord a => [a] ->   II   a [a]
dPqueue xs | null xs   = UII_U
           | otherwise = II x (delFst x xs)
                         where x = foldr1 min xs
                               delFst x []                 = []
                               delFst x (y:ys) | y==x      = ys
                                               | otherwise = y:delFst x ys

dPqueueH :: Ord a => H.Heap a ->   II   a (H.Heap a)
dPqueueH = toB' H.isEmpty H.splitMin

type LinGraph a b =   II   (Context a b) (Graph a b)
cGraph :: LinGraph a b -> Graph a b
cGraph = fromB empty embed


----------------------------------------------------------------------
-- EXAMPLE AS
----------------------------------------------------------------------


-- Number As: nat, count, rng, prod
--
nat   :: SymA   I   Int
nat   =  A cNat dNat 

evn   :: SymA   I   Int
evn   =  A (fromU 0 (succ . succ)) (toU (<=0) (pred . pred))

count :: A (  II   a Int)   I   Int
count =  A (fromB 0 (\_ x->succ x)) dNat

rng   :: A (  I   Int) (  II   Int) Int
rng   =  A cNat (toB (==0) id pred)

rng'  :: A () (  II   Int) Int
rng'  =  A (\()->0) (toB (==0) id pred)

prod  :: A (  II   Int Int)   I   Int
prod  =  A (fromB 1 (*)) dNat

summ  :: A (  II   Int Int)   I   Int
summ  =  A (fromB 0 (+)) dNat

halves :: SymA   I   Int
halves =  A cNat (toU (==0) (`div` 2))


-- "pair" A: nat x nat
--
type Int2 = (Int,Int)

nat2 :: (Int2->Bool) -> (Int2->Int2) -> A () (  II   Int) Int2
nat2 p f = A (\_->(0,0)) (toB p fst f)


-- Misc. simple As
--
bool  :: BinA Bool Bool
bool  =  A (fromB False (||)) (toB' not (\_->(True,False)))

boolAnd :: BinA Bool Bool
boolAnd =  A (fromB True (&&)) (toB' id (\_->(True,True)))


-- Collection As
--
--list   :: BinA a [a]
list   =  A cList dList

jList  :: JoinA a []
jList  =  joinView list

final  :: A (  II   a (Maybe a)) Id (Maybe a)
final  =  A (fromB Nothing (Just `o` fromMaybe)) (toId id)

stack  =  list
jStack =  jList

queue  :: BinA a [a]
queue  =  A cList (toB null last init)

pqueue :: Ord a => BinA a [a]
pqueue =  A cList dPqueue

pqueueH :: Ord a => BinA a (H.Heap a)
pqueueH =  A (fromB H.Empty H.insert) dPqueueH

jQueue :: JoinA a []
jQueue =  joinView queue
                   
jPqueue :: Ord a => JoinA a []
jPqueue =  joinView pqueue

jPqueueH :: Ord a => JoinA a H.Heap
jPqueueH =  joinView pqueueH
               
set :: (Num a, Eq a) => BinA a [a]
set =  A cList (toB null head rest)
       where rest (x:xs) = filter (/=x) xs

arr :: Ord i => (a -> a -> a) -> BinA (i,a) (M.FiniteMap i a)
arr f = A (fromB M.emptyFM accum) (toB' M.isEmptyFM split)
        where accum (i,x) a = M.accumFM a i f x
              split a = (x,a') where Just (a',x) = M.splitMinFM a

bag :: Ord a => BinA a (M.FiniteMap a Int)
bag =  A (fromB M.emptyFM add) (toB' M.isEmptyFM split)
          where add x b = M.accumFM b x (+) 1
                split b = (x,b') 
                  where Just (b'',(x,c)) = M.splitMinFM b
                        b' = if c==1 then b'' else M.addToFM b'' x (c-1)

tree :: SymA (IIV a) (Tree a) 
tree =  A (fromT Leaf Branch) (toT isLeaf key left right) 

fork :: Ord a => A (  II   a [a]) (IIV [a]) [a]
fork =  A cList (toT null (sel (==)) (sel (<)) (sel (>)))
        where sel f l@(x:_) = filter (flip f x) l

combine :: A (IIV [a] [a]) (  II   a) [a]
combine =  A (fromT [] append213) dList
           where append213 y x z = x ++ y ++ z


-- As for rose trees
--
data Rose a = Null | Nd a [Rose a] deriving Show
type Forest a = [Rose a]

isNull :: Rose a -> Bool
isNull Null = True
isNull _    = False

cut :: Rose a -> (a,[Rose a])
cut (Nd x rs) = (x,rs)

root (Nd x _)  = x
kids (Nd _ rs) = rs

--forest' :: PowA a (Rose a)
forest' =  A (fromP Null Nd) (toP' isNull cut)

--forest :: A (I [Rose a]) (  II   [a]) [Rose a]
forest =  A (fromId id) (toB null (map root) (concat.map kids))


-- graph As
--
graph :: BinA (Context a b) (Graph a b)
graph = A cGraph (toB' isEmpty matchAny)

bufGraph :: (JoinA c f) -> (c -> Node) -> (c -> Context a b -> [c]) ->
            A () (  II   (MContext a b)) (f c,Graph a b)
bufGraph (A c d) f h = A (\_->(c UII_U,empty)) explore
         where explore (b,g) = case d b of
                 UII_U                  -> UII_U
                 II x b' | isEmpty g -> UII_U
                            | otherwise -> II ctx (c (II s b'),g')
                              where (ctx,g') = match (f x) g
                                    s        = maybe [] (h x) ctx

{-
   generalize bufGraph to bufA:
   then we can do dfs/bfs on trees and graphs!
-}

-- Rose Trees
--
-- rose :: SymA (Power a) (Rose a)
-- rose = A cRose dRose
