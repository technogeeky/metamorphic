-----------------------------------------------------------------------------
-- |
-- Module      :  SimpleMap
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

module SimpleMap (FiniteMap(..),             --transparent(not yet abstract)
                  emptyFM,addToFM,delFromFM,
                  updFM,                     -- applies function to stored entry
                  accumFM,                   -- defines or aggregates entries
                  splitFM,                   -- combines delFrom & lookup
                  isEmptyFM,sizeFM,lookupFM,elemFM,
                  rangeFM,                   -- applies lookup to an interval
                  minFM,maxFM,predFM,succFM,
                  splitMinFM,                -- combines splitFM & minFM
                  fmToList
                 ) where

import Data.Maybe (isJust)              

data FiniteMap a b = Empty 
                   | Node  (FiniteMap a b)  (a,b)  (FiniteMap a b)
                   deriving (Eq)


----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------
emptyFM    :: Ord a => FiniteMap a b
isEmptyFM  ::          FiniteMap a b      -> Bool
elemFM     :: Ord a => FiniteMap a b -> a -> Bool
sizeFM     :: Ord a => FiniteMap a b -> Int
minFM      :: Ord a => FiniteMap a b                     -> Maybe (a,b)
maxFM      :: Ord a => FiniteMap a b                     -> Maybe (a,b)
lookupFM   :: Ord a => FiniteMap a b -> a -> Maybe    b
succFM     :: Ord a => FiniteMap a b -> a -> Maybe (a,b)
predFM     :: Ord a => FiniteMap a b -> a -> Maybe (a,b)
succFM'    :: Ord a => FiniteMap a b -> a -> Maybe (a,b) -> Maybe (a,b)
predFM'    :: Ord a => FiniteMap a b -> a -> Maybe (a,b) -> Maybe (a,b)

rangeFM    :: Ord a => FiniteMap a b -> a -> a -> [b]
delFromFM  :: Ord a => FiniteMap a b -> a                             -> FiniteMap a b
addToFM    :: Ord a => FiniteMap a b -> a       -> b                  -> FiniteMap a b
updFM      :: Ord a => FiniteMap a b -> a       -> (b -> b)           -> FiniteMap a b
accumFM    :: Ord a => FiniteMap a b -> a       -> (b -> b -> b) -> b -> FiniteMap a b



fmToList   :: Ord a => FiniteMap a b -> [(a,b)]
merge      :: Ord a => FiniteMap a b -> FiniteMap a b -> FiniteMap a b

splitMax   :: Ord a => FiniteMap a b      ->       (FiniteMap a b,(a,b))
splitMinFM :: Ord a => FiniteMap a b      -> Maybe (FiniteMap a b,(a,b))
splitFM    :: Ord a => FiniteMap a b -> a -> Maybe (FiniteMap a b,(a,b))





emptyFM         = Empty
isEmptyFM Empty = True
isEmptyFM _     = False

sizeFM(Empty         )     = 0
sizeFM (Node l _ r)        = sizeFM l + 1 + sizeFM r

minFM (Empty             ) = Nothing
minFM (Node Empty x _____) = Just x
minFM (Node   l   x _____) = minFM l

maxFM (Empty             ) = Nothing
maxFM (Node _____ x Empty) = Just x
maxFM (Node _____ x   r  ) = maxFM r


predFM  m i    = predFM'       m i Nothing
succFM  m i    = succFM'       m i Nothing
rangeFM m i j  = rangeFMa      m i j []
elemFM  m i    = case lookupFM m i of {Nothing -> False; _ -> True}





addToFM   (Empty         ) i   x                  =  Node      Empty      (  i,  x)       Empty
addToFM   (Node l (j,y) r) i   x   | i < j        =  Node (addToFM l i x) (j  ,y  )          r
                                   | i > j        =  Node          l      (j  ,y  ) (addToFM r i x) 
                                   | otherwise    =  Node          l      (j  ,  x)          r

accumFM   (Empty         ) i f x                  =  Node       Empty       (i  ,  x  )   Empty
accumFM   (Node l (j,y) r) i f x   | i < j        =  Node (accumFM l i f x) (  j,    y)          r
                                   | i > j        =  Node          l        (  j,    y) (accumFM r i f x) 
                                   | otherwise    =  Node          l        (  j,f x y)          r  

updFM     (Empty         ) _ _                    =  Empty
updFM     (Node l (j,x) r) i f     | i < j        =  Node (updFM   l i f) (j,  x)        r
                                   | i > j        =  Node          l      (j,  x) (updFM r i f) 
                                   | otherwise    =  Node          l      (j,f x)        r  

delFromFM (Empty         ) _                      =  Empty
delFromFM (Node l (j,x) r) i       | i < j        =  Node (delFromFM l i) (j,x)            r
                                   | i > j        =  Node            l    (j,x) (delFromFM r i) 
                                   | otherwise    =  merge           l                     r  

lookupFM  (Empty         ) _                      =  Nothing
lookupFM  (Node l (j,x) r) i       | i < j        =  lookupFM l i
                                   | i > j        =  lookupFM r i 
                                   | otherwise    =  Just x

rangeFMa  (Empty         ) _ _ a                  = a
rangeFMa  (Node l (k,x) r) i j a   | k < i        = rangeFMa                     r i j a
                                   | k > j        = rangeFMa l i j a
                                   | otherwise    = rangeFMa l i j (x : rangeFMa r i j a)
predFM'   (Empty         ) _ p                    =  p
predFM'   (Node l (j,x) r) i p     | i < j        =  predFM' l i p
                                   | i > j        =  predFM' r i (Just (j,x))
                                   | isJust    ml =  ml 
                                   | otherwise    =  p
                                   where       ml = maxFM l
succFM'   (Empty         )  _ p                   =  p
succFM'   (Node l (j,x) r)  i p    | i < j        =  succFM' l i (Just (j,x))
                                   | i > j        =  succFM' r i p
                                   | isJust    mr =  mr 
                                   | otherwise    =  p
                                   where       mr = minFM r


fmToList m = scan m []
             where scan Empty        xs = xs
                   scan (Node l x r) xs = scan l (scan r (x:xs))


splitFM (Empty         )  _ =  Nothing
splitFM (Node l (j,x) r) i =  if i < j then  case splitFM l i of Just (l',y) -> Just (Node l' (j,x) r ,y)
                                                                 Nothing     -> Nothing
                         else
                              if i > j then  case splitFM r i of Just (r',y) -> Just (Node l  (j,x) r',y) 
                                                                 Nothing     -> Nothing  
                         else  {- i = j -}                                      Just (merge l r ,(j,x))  

splitMinFM (Empty         )   = Nothing
splitMinFM (Node Empty x r)   = Just (r,x)
splitMinFM (Node   l   x r)   = Just (Node l' x r,y) 
                          where      Just (l'    ,y) = splitMinFM l


splitMax (Node l x Empty) =      (l,x)
splitMax (Node l x r    ) = (Node l x  m , y) where 
                                      (m , y) = splitMax r

merge   l   Empty   = l
merge Empty   r     = r
merge   l     r     = Node l' x r where 
                          (l',x) = splitMax l


----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------


-- pretty printing
--
showsMap :: (Show a,Show b,Ord a) => FiniteMap a b -> ShowS
showsMap (Empty         )  = id
showsMap (Node l (i,x) r)  = showsMap l . (' ':) . 
                             shows    i . (" -> "++) . shows x . showsMap r
                
instance (Show a,Show b,Ord a) => Show (FiniteMap a b) where
  showsPrec _ m = showsMap m

                            
