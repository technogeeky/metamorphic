data Rose a = Null | Nd a [Rose a] deriving Show
type Forest a = [Rose a]

type LinGraph a b =   II   (Context a b) (Graph a b)

type Int2 = (Int,Int)


----------------------------------------------------------------------
-- TYPES
----------------------------------------------------------------------


-- abstract
--
type Node = Int
data Graph a b = Graph (GraphRep a b)


-- transparent
--
type Edge b       = (Node,Node,b)
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) -- Context a b "=" Context' a b "+" Node
type MContext a b = Maybe (Context a b)
type Decomp a b   = (MContext a b,Graph a b)


-- local
--
type Context' a b = (Adj b,a,Adj b)
type GraphRep a b = FiniteMap Node (Context' a b)



type Dir a b      = (Context a b) -> [Node]  -- direction of fold
type Dagg a b c d = (Context a b) -> c -> d  -- depth aggregation
type Bagg a b     = (Maybe a -> b -> b,b)    -- breadth/level aggregation

data Heap a = Empty | Node a [Heap a]
     deriving Eq

