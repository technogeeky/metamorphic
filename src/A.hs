-----------------------------------------------------------------------------
-- |
-- Module      :  A
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
module A where



-- |
-- A standard Bifunctor, but with a Roman Numeral naming scheme:
--
-- [/II/] instead of @Bi@
--
-- [/fmapII/] instead of @bimap@
--
-- [/fmapLI/] instead of @first@
--
-- [/fmapIR/] instead of @second@
--
-- This is to remind us that the other column remains intact
--   when focus on one (L or R).
--
class IIFunctor f where
  fmapII  ::  (a -> b) -> (c -> d) -> f a c -> f b d
  fmapLI  ::  (a -> b)             -> f a c -> f b c
  fmapIR  ::       (b -> c)        -> f a b -> f a c  
  fmapII f g = fmapLI f      . fmapIR g
  fmapLI f   = fmapII f  id
  fmapIR   g =                 fmapII id  g

{-
class IIIFunctor f where
  fmapIII   ::                     (d -> s -> b) -> (u -> c -> t) -> f u d -> f s c -> f b t
  fmapIIH   :: (IIFunctor f) =>         (s -> b) ->      (c -> t)          -> f s c -> f b t
--  fmapICI   ::                     (d   ->    b) -> (u   ->    t) -> f d u          -> f b t
  fmapLII   :: (IIFunctor f) =>    (d -> s)      -> (u -> c)      -> f d u -> f s c

--  fmapIII  ::  (a -> b) -> f a t -> f b t

--  fmapIII l c r = fmapLII l c . fmapIIH c r
  fmapIIH   c r = fmapII c r
--  fmapICI l c r = fmapLII l c . fmapIIH c r
  fmapLII l c   = fmapII l c
-}


----------------------------------------------------------------------
-- FUNCTORS
----------------------------------------------------------------------


-- Id
--
data Id a = Id a

fromId :: (a -> b) -> Id a -> b
fromId f (Id x) = f x

toId :: (b -> a) -> b -> Id a
toId f x = Id (f x)

instance Functor Id where
  fmap f (Id x) = Id (f x)


--   I    =  1 + Id    (= Maybe a)
--


fromU :: t -> (a -> t)           ->   I     a   -> t
fromB :: t -> (a -> b      -> t) ->   II    a b -> t
fromT :: t -> (a -> b -> b -> t) ->   IIV   a b -> t
fromP :: t -> (a -> [b]    -> t) -> Power   a b -> t



toU  :: (t -> Bool) -> (t -> a)                         -> t ->   I     a
toB  :: (t -> Bool) -> (t -> a) -> (t -> b)             -> t ->   II    a b
toT  :: (t -> Bool) -> (t -> a) -> (t -> b) -> (t -> b) -> t ->   IIV   a b
toP  :: (t -> Bool) -> (t -> a) -> (t -> [b])           -> t -> Power   a b
toP' :: (t -> Bool) -> (t -> (a,[b]))                   -> t -> Power   a b
toB' :: (t -> Bool) -> (t -> (a, b ))                   -> t ->   II    a b

fromU u f U_I_U              = u
fromU u f      (I x)         = f x
fromB u f UII_U              = u
fromB u f      (II x y)      = f x y
fromT u f UIIVU              = u
fromT u f      (IIV x y z)   = f x y z
fromP u f UnitP              = u
fromP u f      (Many x ys)   = f x ys


toU  p f     x = if p x then U_I_U   else I     (f x) 
toB  p f g   x = if p x then UII_U  else II    (f x) (g x) 
toT  p f g h x = if p x then UIIVU else IIV   (f x) (g x) (h x) 
toP  p f g   x = if p x then UnitP else Many  (f x) (g x)
toP' p f     x = if p x then UnitP else Many y zs where (y,zs) = f x
toB' p f     x = if p x then UII_U  else II  y z  where (y, z) = f x

data    I    a   = U_I_U | I     a
data   II    a b = UII_U | II    a b
data   IIV   a b = UIIVU | IIV   a b b
{-
data    IV   a b = U_IVU | IV    a b b b
data    V    a b = U_V_U | V     a b b b b
data    VI   a b = U_VIU | VI    a b b b b b
data   VII   a b = UVIIU | VII   a b b b b b b
data   IIX   a b = UIIXU | IIX   a b b b b b b b
data    IX   a b = U_IXU |  IX   a b b b b b b b b
data    X    a b = U_X_U |  X    a b b b b b b b b b
data    XI   a b = U_XIU |  XI   a b b b b b b b b b b
data   XII   a b = UXIIU |  XII  a b b b b b b b b b b b
-}
data Power   a b = UnitP | Many  a [b]


instance Functor    I        where fmap f      U_I_U           = U_I_U
                                   fmap f     (I x)          =  I      (f x)

instance Functor (  II   a)  where fmap f      UII_U          = UII_U
                                   fmap f     (II x y)       =  II   x (f y)

instance Functor (  IIV   a) where fmap f      UIIVU         = UIIVU
                                   fmap f     (IIV x y z)    =  IIV  x (f y) (f z)

{-
instance Functor (  IV    a) where fmap f      U_IVU        = U_IVU
                                   fmap f     (IV t x y z)   =   IV  t (f x) (f y) (f z)
-}
instance IIFunctor   II      where fmapII f g  UII_U          = UII_U
                                   fmapII f g (II x y)       =  II   (f x) (g y)

instance IIFunctor   IIV     where fmapII f g  UIIVU         = UIIVU
                                   fmapII f g (IIV x y z)    =  IIV  (f x) (g y) (g y)

instance IIFunctor Power     where fmapII f g  UnitP         =                       UnitP
                                   fmapII f g (Many x ys)    = Many (f x) (fmap g ys)

instance Functor (Power a)   where fmap  f     UnitP         =                       UnitP
                                   fmap  f    (Many x ys)    = Many    x  (fmap f ys)





-- natural transformations between functors:
--
ntBU :: (a -> b -> c)              ->   II    a b ->   I   c
ntTB :: (a -> c) -> (b -> b -> d)  ->   IIV   a b ->   II   c d
ntPB :: (a -> c) -> ([b] -> d)     -> Power   a b ->   II   c d

ntBU f    UII_U          = U_I_U
ntBU f   (II   x y  )   = I (f x y)

ntTB f g  UIIVU          = UII_U
ntTB f g (IIV x y z)     = II (f x) (g y z)

ntPB f g  UnitP          = UII_U
ntPB f g (Many  x ys )   = II (f x) (g ys)



----------------------------------------------------------------------
-- REPRESENTATIdON OF AS
----------------------------------------------------------------------

{-
    An A is given by a pair of functions (constructor,destructor)
    with
      s : argument type of constructor
      g : type constructor (functor) for destructor result type
      t : carrier type 
-}

data A s g t = A (s -> t) (t -> g t)
-- newtype Functor g => A s g t = A (s -> t,t -> g t)

con (A c _) = c
des (A _ d) = d
-- con (A (c,_)) = c
-- des (A (_,d)) = d


{-
    An A whose constructor and destructor map from/to the same type
    is called "symmetric". Thus, for a symmetric A: s = g t.
    Moreover, a symmetric A with   II   base functor is called 
    a linear A. A Join-A is a linear A with list of values
    to be inserted on the constructor side.
-}

type BinA  a     t  = SymA (II    a)  t
type PowA  a     t  = SymA (Power a)  t

type SymA     g  t  = A       ( g t)           g t
type JoinA a  g     = A    (II [a]  (g a) ) 
                           (II  a ) (g a)


----------------------------------------------------------------------
-- A COMBINATORS
----------------------------------------------------------------------


joinView  :: (Functor g) => A (II a t) g t -> A (II [      a]  t) g t
maybeView :: (Functor g) => A (II a t) g t -> A (II (Maybe a)  t) g t

-- | Equip an A having linear constructor with a join view
--
joinView (A c d) = A c' d     where c' UII_U           = c UII_U
                                    c' (II xs y)       = foldr c'' y xs
                                                 where         c'' x ys = c (II x ys)
maybeView (A c d) = A c' d    where c' UII_U           = c UII_U
                                    c' (II Nothing  y) = y
                                    c' (II (Just x) y) = c (II x y)


----------------------------------------------------------------------
-- FOLD, TRANSFORMER, STREAM
----------------------------------------------------------------------


-- * Fold and Unfold

fold      :: (Functor g)                       => (g u ->   u) -> A    s  g   t                                -> (t -> u)
unfold    :: (Functor f, Functor g)            => (  t -> f t) -> A (f u) g   u                                -> (t -> u)
trans     :: (Functor g, Functor h)            => (g u ->   r) -> A    s  g   t -> A    r  h u                 -> (t -> u)
transit   :: (Functor g, Functor h)            =>                 A    s  g   t -> A (g u) h u                 -> (t -> u)
via       :: (Functor g, Functor h, Functor i) =>                 A    s  g   t -> A (g u) h u  -> A (h v) i v -> (t -> v)

fold   f a     = f     .     fmap (fold   f a  ) . des a
unfold f a     =                                   con a .     fmap (unfold f a  ) . f
-- trans  f a b=                                   con b . f . fmap (trans  f a b) . des a
trans  f a b   = con b . f . fmap (trans  f a b) . des a


transit        = trans id
via      a b c = transit b c . transit a b



-- | 
--   Hylomorphisms in binary and triplet form (just for completeness)
--
hylo  :: (Functor f) => (f b ->   b)                                                 -> (a -> f a) -> (a -> b)
hylot :: (Functor f) => (f b -> g b) -> (g b ->   b)                                 -> (a -> f a) -> (a -> b)
hhh   :: (Functor f) => (f b -> i b) -> (i b -> g b) -> (g b ->   b)                 -> (a -> f a) -> (a -> b)
h     :: (Functor f) => (f b -> i b) -> (i b -> j b) -> (j b -> k b) -> (k b ->   b) -> (a -> f a) -> (a -> b)

hylo    c d = c .             fmap (hylo    c d) . d
hylot f c d = c . f .         fmap (hylot f c d) . d
hhh g f c d = c . f . g .     fmap (hhh g f c d) . d
h i g f c d = c . f . g . i . fmap (h i g f c d) . d


-- ^ A simple Stream ADT
stream :: (Functor g) => [SymA g t] -> t -> t
stream [a,b]    = transit a b
stream (a:b:as) = stream (b:as) . (transit a b) 

