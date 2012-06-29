-- {-# LANGUAGE DatatypeContexts #-}

--
--  ADT.hs -- ADTs, ADT Fold, and ADT Transformer
--
module ADT where

import Data.Foldable (Foldable())


----------------------------------------------------------------------
-- UTILITIES: BiFunctor class
----------------------------------------------------------------------

class BiFunctor f where
  fmap2   :: (a -> b) -> (t -> u) -> f a t -> f b u
  fmapFst :: (a -> b) -> f a t -> f b t
  fmapFst f = fmap2 f id 


----------------------------------------------------------------------
-- FUNCTORS
----------------------------------------------------------------------


-- I
--
data I a = I a

fromI :: (a -> b) -> I a -> b
fromI f (I x) = f x

toI :: (b -> a) -> b -> I a
toI f x = I (f x)

instance Functor I where
  fmap f (I x) = I (f x)


-- Unary  =  1 + I    (= Maybe a)
--
data Unary a = UnitU | One a


fromU :: b -> (a -> b) -> Unary a -> b
fromU u f UnitU   = u
fromU u f (One x) = f x

toU :: (b -> Bool) -> (b -> a) -> (b -> Unary a)
toU p f x = if p x then UnitU else One (f x) 

-- Binary  =  1 + A*I
--
data Binary a b = UnitB | Two a b
-- Ternary  =  1 + A*I*I
--
data Ternary a b = UnitT | Three a b b
-- Power = Nary  =  1 + A*[I]
--
data Power a b = UnitP | Many a [b]

fromB :: t -> (a -> b -> t) -> Binary a b -> t
fromB u f UnitB     = u
fromB u f (Two x y) = f x y

toB :: (t -> Bool) -> (t -> a) -> (t -> b) -> t -> Binary a b
toB p f g x = if p x then UnitB else Two (f x) (g x) 

toB' :: (t -> Bool) -> (t -> (a,b)) -> t -> Binary a b
toB' p f x = if p x then UnitB else Two y z where (y,z) = f x

instance Functor Unary where       fmap f    UnitU          =                        UnitU
                                   fmap f    (One x)        = One (f x)
instance Functor (Binary a) where  fmap f    UnitB          =                        UnitB
                                   fmap f    (Two x y)      = Two x (f y)
instance Functor (Ternary a) where fmap f    UnitT          =                        UnitT
                                   fmap f    (Three x y z)  = Three x (f y) (f z)
instance BiFunctor Binary    where fmap2 f g UnitB          =                        UnitB
                                   fmap2 f g (Two x y)      = Two (f x) (g y)
instance BiFunctor Ternary where   fmap2 f g UnitT          =                        UnitT
                                   fmap2 f g (Three x y z)  = Three (f x) (g y) (g y)

instance BiFunctor Power where     fmap2 f g UnitP          =                        UnitP
                                   fmap2 f g (Many x ys)    = Many (f x) (map g ys)
instance Functor (Power a) where   fmap f    UnitP          =                        UnitP
                                   fmap f    (Many x ys)    = Many x (map f ys)



fromT :: t -> (a -> b -> b -> t) -> Ternary a b -> t
fromT u f UnitT         = u
fromT u f (Three x y z) = f x y z

toT :: (t -> Bool) -> (t -> a) -> (t -> b) -> (t -> b) -> t -> Ternary a b
toT p f g h x = if p x then UnitT else Three (f x) (g x) (h x) 




fromP :: t -> (a -> [b] -> t) -> Power a b -> t
fromP u f UnitP       = u
fromP u f (Many x ys) = f x ys

toP :: (t -> Bool) -> (t -> a) -> (t -> [b]) -> t -> Power a b
toP p f g x = if p x then UnitP else Many (f x) (g x)

toP' :: (t -> Bool) -> (t -> (a,[b])) -> t -> Power a b
toP' p f x = if p x then UnitP else Many y zs where (y,zs) = f x



-- natural transformations between functors:
--
ntBU :: (a -> b -> c)              -> Binary  a b -> Unary c
ntTB :: (a -> c) -> (b -> b -> d)  -> Ternary a b -> Binary c d
ntPB :: (a -> c) -> ([b] -> d)     -> Power   a b -> Binary c d

ntBU f    UnitB          = UnitU
ntBU f   (Two   x y  )   = One (f x y)
ntTB f g  UnitT          = UnitB
ntTB f g (Three x y z)   = Two (f x) (g y z)
ntPB f g  UnitP          = UnitB
ntPB f g (Many  x ys )   = Two (f x) (g ys)



----------------------------------------------------------------------
-- REPRESENTATION OF ADTS
----------------------------------------------------------------------

{-
    An ADT is given by a pair of functions (constructor,destructor)
    with
      s : argument type of constructor
      g : type constructor (functor) for destructor result type
      t : carrier type 
-}

data ADT s g t = ADT (s -> t) (t -> g t)
-- newtype Functor g => ADT s g t = ADT (s -> t,t -> g t)

con (ADT c _) = c
des (ADT _ d) = d
-- con (ADT (c,_)) = c
-- des (ADT (_,d)) = d


{-
    An ADT whose constructor and destructor map from/to the same type
    is called "symmetric". Thus, for a symmetric ADT: s = g t.
    Moreover, a symmetric ADT with Binary base functor is called 
    a linear ADT. A Join-ADT is a linear ADT with list of values
    to be inserted on the constructor side.
-}

type SymADT     g  t  = ADT    (g t)    g t
type BinADT  a     t  = SymADT (Binary a) t
type JoinADT a  g     = ADT    (Binary [a] (g a)) (Binary a) (g a)
type PowADT  a     t  = SymADT (Power a) t


----------------------------------------------------------------------
-- ADT COMBINATORS
----------------------------------------------------------------------


-- Equip an ADT having linear constructor with a join view
--
joinView :: (Functor g) => ADT (Binary a t) g t -> ADT (Binary [a] t) g t
joinView (ADT c d) = ADT c' d
         where c' UnitB        = c UnitB
               c' (Two xs y) = foldr c'' y xs
                   where c'' x y = c (Two x y)

-- Extend ADT constructors to Maybe types, make ADTs "maybeable"
--
maybeView :: (Functor g) => ADT (Binary a t) g t -> ADT (Binary (Maybe a) t) g t
maybeView (ADT c d) = ADT c' d
          where c' UnitB              = c UnitB
                c' (Two Nothing y)  = y
                c' (Two (Just x) y) = c (Two x y)


----------------------------------------------------------------------
-- FOLD, TRANSFORMER, STREAM
----------------------------------------------------------------------


-- ADT fold
--
fold :: (Functor g) => (g u -> u) -> ADT s g t -> (t -> u)
fold f a = f . fmap (fold f a) . des a
-- fold f a@(ADT _ d) = f . map (fold f a) . d

unfold :: (Functor f, Functor g) => (t -> f t) -> ADT (f u) g u -> (t -> u)
unfold f a = con a . fmap (unfold f a) . f


-- Hylomorphisms in binary and triplet form (just for completeness)
--
hylo :: (Functor f) => (f b -> b) -> (a -> f a) -> (a -> b)
hylo c d = c . fmap (hylo c d) . d


hylot :: (Functor f) => (f b -> g b) -> (g b -> b) -> (a -> f a) -> (a -> b)
hylot f c d = c . f . fmap (hylot f c d) . d


-- ADT transformer
--
trans :: (Functor g, Functor h) => (g u -> r) -> ADT s g t -> ADT r h u -> ( t -> u)
trans f a b = con b . f . fmap (trans f a b) . des a

transit :: (Functor g, Functor h) => ADT s g t -> ADT (g u) h u -> (t -> u)
transit = trans id


-- ADT streams
--
via :: (
        Functor g,
        Functor h,
        Functor i
        ) =>
       ADT s g t -> ADT (g u) h u -> ADT (h v) i v -> t -> v
via a b c = transit b c . transit a b

stream :: (Functor g) => [SymADT g t] -> t -> t
stream [a,b]    = transit a b
stream (a:b:as) = stream (b:as) . (transit a b) 

