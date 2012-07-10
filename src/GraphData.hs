-----------------------------------------------------------------------------
-- |
-- Module      :  GraphData
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

module GraphData (
   -- example graphs
   a,b,c,e,ab,loop,cyc3,dag3,dag4,
   clr479,clr486,clr489,clr528,kin248
   ) where

import Graph



----------------------------------------------------------------------
-- EXAMPLE GRAPHS
----------------------------------------------------------------------


-- some auxiliary functions
--   labnl  : generate list of labeled nodes
--   noLab  : denote unlabeled edges
labnl c i = take i (zip [1..] [c..])
noLab :: [(a,b)] -> [(a,b,())]
noLab = map (\(i,j) -> (i,j,()))
noEdges = [] :: [(Int,Int,())]


-- some small graphs
--
a    = embed ([],1,'a',[]::[((),Int)]) empty  --  just a node
b    = mkGraph (zip [1..2] "ab") noEdges      --  just two nodes
c    = mkGraph (zip [1..3] "abc") noEdges     --  just three nodes
e    = embed ([((),1)],2,'b',[]) a            --  just one edge a-->b
loop = embed ([],1,'a',[((),1)]) empty        --  loop on single node
ab   = embed ([((),1)],2,'b',[((),1)]) a      --  cycle of two nodes:  a<-->b
cyc3 = buildGr                                --  cycle of three nodes
       [([("ca",3)],1,'a',[("ab",2)]),
                ([],2,'b',[("bc",3)]),
                ([],3,'c',[])]
dag3 = mkGraph (zip [1..3] "abc") (noLab [(1,3)])
dag4 = mkGraph (labnl 1 4) (noLab [(1,2),(1,4),(2,3),(2,4),(4,3)])


-- more graphs (Book<page>)
--
-- clr : Cormen/Leiserson/Rivest
-- kin : Kingston
--
clr479 = mkGraph (labnl 'u' 6) 
         (noLab [(1,2),(1,4),(2,5),(3,5),(3,6),(4,2),(5,4),(6,6)])
clr486 = mkGraph (zip [1..9] ["shorts","socks","watch","pants","shoes",
                              "shirt","belt","tie","jacket"])
                 (noLab [(1,4),(1,5),(2,5),(4,5),(4,7),(6,7),(6,8),(7,9),(8,9)])
clr489 = mkGraph (labnl 'a' 8)
                 (noLab [(1,2),(2,3),(2,5),(2,6),(3,4),(3,7),(4,3),(4,8),
                         (5,1),(5,6),(6,7),(7,6),(7,8),(8,8)])
clr528 = mkGraph [(1,'s'),(2,'u'),(3,'v'),(4,'x'),(5,'y')]
                 [(1,2,10),(1,4,5),(2,3,1),(2,4,2),(3,5,4),
                  (4,2,3),(4,3,9),(4,5,2),(5,1,7),(5,3,6)]
kin248 = mkGraph (labnl 1 10)
                 (noLab [(1,2),(1,4),(1,7),(2,4),(2,5),(3,4),(3,10),
                         (4,5),(4,8),(5,2),(5,3),(6,7),(7,6),(7,8),
                         (8,10),(9,9),(9,10),(10,8),(10,9)])



