--
--  ADTlib.hs -- A Library of ADTs
--
module ADTlib where

import Data.Maybe (fromMaybe)

import ADT

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
dPqueue xs | null xs   = U__U
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
-- EXAMPLE ADTS
----------------------------------------------------------------------


-- Number ADTs: nat, count, rng, prod
--
nat   :: SymADT   I   Int
nat   =  ADT cNat dNat 

evn   :: SymADT   I   Int
evn   =  ADT (fromU 0 (succ . succ)) (toU (<=0) (pred . pred))

count :: ADT (  II   a Int)   I   Int
count =  ADT (fromB 0 (\_ x->succ x)) dNat

rng   :: ADT (  I   Int) (  II   Int) Int
rng   =  ADT cNat (toB (==0) id pred)

rng'  :: ADT () (  II   Int) Int
rng'  =  ADT (\()->0) (toB (==0) id pred)

prod  :: ADT (  II   Int Int)   I   Int
prod  =  ADT (fromB 1 (*)) dNat

summ  :: ADT (  II   Int Int)   I   Int
summ  =  ADT (fromB 0 (+)) dNat

halves :: SymADT   I   Int
halves =  ADT cNat (toU (==0) (`div` 2))


-- "pair" ADT: nat x nat
--
type Int2 = (Int,Int)

nat2 :: (Int2->Bool) -> (Int2->Int2) -> ADT () (  II   Int) Int2
nat2 p f = ADT (\_->(0,0)) (toB p fst f)


-- Misc. simple ADTs
--
bool  :: BinADT Bool Bool
bool  =  ADT (fromB False (||)) (toB' not (\_->(True,False)))

boolAnd :: BinADT Bool Bool
boolAnd =  ADT (fromB True (&&)) (toB' id (\_->(True,True)))


-- Collection ADTs
--
--list   :: BinADT a [a]
list   =  ADT cList dList

jList  :: JoinADT a []
jList  =  joinView list

final  :: ADT (  II   a (Maybe a)) Id (Maybe a)
final  =  ADT (fromB Nothing (Just `o` fromMaybe)) (toId id)

stack  =  list
jStack =  jList

queue  :: BinADT a [a]
queue  =  ADT cList (toB null last init)

pqueue :: Ord a => BinADT a [a]
pqueue =  ADT cList dPqueue

pqueueH :: Ord a => BinADT a (H.Heap a)
pqueueH =  ADT (fromB H.Empty H.insert) dPqueueH

jQueue :: JoinADT a []
jQueue =  joinView queue
                   
jPqueue :: Ord a => JoinADT a []
jPqueue =  joinView pqueue

jPqueueH :: Ord a => JoinADT a H.Heap
jPqueueH =  joinView pqueueH
               
set :: (Num a, Eq a) => BinADT a [a]
set =  ADT cList (toB null head rest)
       where rest (x:xs) = filter (/=x) xs

arr :: Ord i => (a -> a -> a) -> BinADT (i,a) (M.FiniteMap i a)
arr f = ADT (fromB M.emptyFM accum) (toB' M.isEmptyFM split)
        where accum (i,x) a = M.accumFM a i f x
              split a = (x,a') where Just (a',x) = M.splitMinFM a

bag :: Ord a => BinADT a (M.FiniteMap a Int)
bag =  ADT (fromB M.emptyFM add) (toB' M.isEmptyFM split)
          where add x b = M.accumFM b x (+) 1
                split b = (x,b') 
                  where Just (b'',(x,c)) = M.splitMinFM b
                        b' = if c==1 then b'' else M.addToFM b'' x (c-1)

tree :: SymADT (IIV a) (Tree a) 
tree =  ADT (fromT Leaf Branch) (toT isLeaf key left right) 

fork :: Ord a => ADT (  II   a [a]) (IIV [a]) [a]
fork =  ADT cList (toT null (sel (==)) (sel (<)) (sel (>)))
        where sel f l@(x:_) = filter (flip f x) l

combine :: ADT (IIV [a] [a]) (  II   a) [a]
combine =  ADT (fromT [] append213) dList
           where append213 y x z = x ++ y ++ z


-- ADTs for rose trees
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

--forest' :: PowADT a (Rose a)
forest' =  ADT (fromP Null Nd) (toP' isNull cut)

--forest :: ADT (I [Rose a]) (  II   [a]) [Rose a]
forest =  ADT (fromId id) (toB null (map root) (concat.map kids))


-- graph ADTs
--
graph :: BinADT (Context a b) (Graph a b)
graph = ADT cGraph (toB' isEmpty matchAny)

bufGraph :: (JoinADT c f) -> (c -> Node) -> (c -> Context a b -> [c]) ->
            ADT () (  II   (MContext a b)) (f c,Graph a b)
bufGraph (ADT c d) f h = ADT (\_->(c U__U,empty)) explore
         where explore (b,g) = case d b of
                 U__U                  -> U__U
                 II x b' | isEmpty g -> U__U
                            | otherwise -> II ctx (c (II s b'),g')
                              where (ctx,g') = match (f x) g
                                    s        = maybe [] (h x) ctx

{-
   generalize bufGraph to bufADT:
   then we can do dfs/bfs on trees and graphs!
-}

-- Rose Trees
--
-- rose :: SymADT (Power a) (Rose a)
-- rose = ADT cRose dRose
