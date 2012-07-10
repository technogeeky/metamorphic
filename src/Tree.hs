-----------------------------------------------------------------------------
-- |
-- Module      :  Tree
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

module Tree 
where


data Tree a = Leaf | Branch {key::a,left,right::Tree a}
     deriving Eq

showsTree :: Show a => Tree a -> ShowS
showsTree Leaf = id
showsTree t    = ('(':) . showsTree (left t) . shows (key t)
                        . showsTree (right t) . (')':)

instance Show a => Show (Tree a) where
  showsPrec _ d = showsTree d

isLeaf Leaf = True
isLeaf _    = False


-- http://blog.moertel.com/articles/2012/01/26/the-inner-beauty-of-tree-traversals
