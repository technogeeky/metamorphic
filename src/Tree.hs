--
--  Tree.hs -- Definition of binary tree data type
--
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
