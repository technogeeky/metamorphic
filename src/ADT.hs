-- {-# LANGUAGE DatatypeContexts #-}

--
--  ADT.hs -- ADTs, ADT Fold, and ADT Transformer
--
module ADT where



----------------------------------------------------------------------
-- UTIdLIdTIdES: IIFunctor class
----------------------------------------------------------------------

class IIFunctor f where
  ffmap   :: (a -> b) -> (t -> u) -> f a t -> f b u
  ffmapL ::  (a -> b) -> f a t -> f b t
  ffmapL f = ffmap f id 


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

fromU u f U_U         = u
fromU u f (I x)       = f x
fromB u f  U__U        = u
fromB u f (II x y)     = f x y
fromT u f  UIIVU        = u
fromT u f (IIV x y z) = f x y z
fromP u f  UnitP        = u
fromP u f (Many x ys)   = f x ys


toU  p f     x = if p x then U_U else I     (f x) 
toB  p f g   x = if p x then U__U else II   (f x) (g x) 
toT  p f g h x = if p x then UIIVU else IIV (f x) (g x) (h x) 
toP  p f g   x = if p x then UnitP else Many  (f x) (g x)
toP' p f     x = if p x then UnitP else Many y zs where (y,zs) = f x
toB' p f     x = if p x then U__U else II  y z  where (y, z) = f x

data   I     a   = U_U     | I     a
data   II    a b = U__U    | II    a b
data   IIV   a b = UIIVU   | IIV   a b b
data    IV   a b = U_IV_U  | IV    a b b b
data     V   a b = U__V__U | V     a b b b b
data Power   a b = UnitP   | Many  a [b]


instance Functor    I        where fmap f    U_U            =                       U_U
                                   fmap f    (I x)          = I (f x)
instance Functor (  II   a)  where fmap f    U__U           =                       U__U
                                   fmap f    (II x y)       = II x (f y)
instance Functor (  IIV   a) where fmap f    UIIVU          =                       UIIVU
                                   fmap f    (IIV x y z)    = IIV x (f y) (f z)
instance Functor (  IV    a) where fmap f    U_IV_U        =                        U_IV_U
                                   fmap f    (IV t x y z)   = IV  t (f x) (f y) (f z)
instance IIFunctor   II      where ffmap f g U__U           =                        U__U
                                   ffmap f g (II x y)       = II (f x) (g y)
instance IIFunctor   IIV     where ffmap f g UIIVU          =                        UIIVU
                                   ffmap f g (IIV x y z)    = IIV (f x) (g y) (g y)


instance IIFunctor Power     where ffmap f g  UnitP         =                        UnitP
                                   ffmap f g (Many x ys)    = Many (f x) (fmap g ys)
instance Functor (Power a)   where fmap  f    UnitP         =                        UnitP
                                   fmap  f   (Many x ys)    = Many x (fmap f ys)





-- natural transformations between functors:
--
ntBU :: (a -> b -> c)              ->   II    a b ->   I   c
ntTB :: (a -> c) -> (b -> b -> d)  ->   IIV   a b ->   II   c d
ntPB :: (a -> c) -> ([b] -> d)     -> Power   a b ->   II   c d

ntBU f    U__U          = U_U
ntBU f   (II   x y  )   = I (f x y)
ntTB f g  UIIVU          = U__U
ntTB f g (IIV x y z)   = II (f x) (g y z)
ntPB f g  UnitP          = U__U
ntPB f g (Many  x ys )   = II (f x) (g ys)



----------------------------------------------------------------------
-- REPRESENTATIdON OF ADTS
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
    Moreover, a symmetric ADT with   II   base functor is called 
    a linear ADT. A Join-ADT is a linear ADT with list of values
    to be inserted on the constructor side.
-}

type SymADT     g  t  = ADT    (g t)    g t
type BinADT  a     t  = SymADT (  II   a) t
type JoinADT a  g     = ADT    (  II   [a] (g a)) (  II   a) (g a)
type PowADT  a     t  = SymADT (Power a) t


----------------------------------------------------------------------
-- ADT COMBINATORS
----------------------------------------------------------------------


-- Equip an ADT having linear constructor with a join view
--
joinView :: (Functor g) => ADT (  II   a t) g t -> ADT (  II   [a] t) g t
joinView (ADT c d) = ADT c' d
         where c' U__U        = c U__U
               c' (II xs y) = foldr c'' y xs
                   where c'' x y = c (II x y)

-- Extend ADT constructors to Maybe types, make ADTs "maybeable"
--
maybeView :: (Functor g) => ADT (  II   a t) g t -> ADT (  II   (Maybe a) t) g t
maybeView (ADT c d) = ADT c' d
          where c' U__U              = c U__U
                c' (II Nothing y)  = y
                c' (II (Just x) y) = c (II x y)


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
hylo  :: (Functor f) => (f b ->   b)                                                 -> (a -> f a) -> (a -> b)
hylot :: (Functor f) => (f b -> g b) -> (g b ->   b)                                 -> (a -> f a) -> (a -> b)
hhh   :: (Functor f) => (f b -> i b) -> (i b -> g b) -> (g b ->   b)                 -> (a -> f a) -> (a -> b)
h     :: (Functor f) => (f b -> i b) -> (i b -> j b) -> (j b -> k b) -> (k b ->   b) -> (a -> f a) -> (a -> b)

hylo    c d = c .             fmap (hylo    c d) . d
hylot f c d = c . f .         fmap (hylot f c d) . d
hhh g f c d = c . f . g .     fmap (hhh g f c d) . d
h i g f c d = c . f . g . i . fmap (h i g f c d) . d

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

