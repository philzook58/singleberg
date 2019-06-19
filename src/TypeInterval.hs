{-# LANGUAGE TemplateHaskell
,DataKinds
,DefaultSignatures
,EmptyCase
,ExistentialQuantification
,FlexibleContexts
,FlexibleInstances
,GADTs
,InstanceSigs
,KindSignatures
,NoStarIsType
,PolyKinds
,RankNTypes
,ScopedTypeVariables
,StandaloneDeriving
,TemplateHaskell
,TypeFamilies
,TypeOperators
,UndecidableInstances
#-}
module TypeInterval where


import Data.Singletons.TH
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.List

import Data.Singletons.Prelude.Eq
-- http://hackage.haskell.org/package/lattices something to think about
-- http://hackage.haskell.org/package/heyting-algebras
-- 


-- Data.Intevral
-- why have empty and not full?


$(promote [d|
    data Interval a = I !a !a | Empty deriving (Eq, Ord)
    (...) :: Ord a => a -> a -> Interval a
    a ... b
            | a <= b = I a b
            | otherwise = Empty
    singleton :: a -> Interval a
    singleton a = I a a
    increasing :: (a -> b) -> Interval a -> Interval b
    increasing f (I a b) = I (f a) (f b)
    increasing _ Empty = Empty
    instance (Num a, Ord a) => Num (Interval a) where
        I a b + I a' b' = (a + a') ... (b + b')
        _ + _ = Empty
        {-# INLINE (+) #-}
        I a b - I a' b' = (a - b') ... (b - a')
        _ - _ = Empty
        {-# INLINE (-) #-}
        I a b * I a' b' =
            minimum [a * a', a * b', b * a', b * b']
            ...
            maximum [a * a', a * b', b * a', b * b']
        _ * _ = Empty
        {-# INLINE (*) #-}
        abs x@(I a b)
            | a >= 0    = x
            | b <= 0    = negate x
            | otherwise = 0 ... max (- a) b
        abs Empty = Empty
        {-# INLINE abs #-}
        
        signum = increasing signum
        {-# INLINE signum #-}
        
        fromInteger i = singleton (fromInteger i)
  |])

type T1 = 1 ... 3
type T2 =  3 ... 1
type T3 = (1 ... 4) + (2 ... 6)
type T4 = (1 ... 4) * (2 ... 6)
type T5 = ((0 - 1) ... 4) * (2 ... 6) -- hmm. 
-- http://hackage.haskell.org/package/type-level-integers  type level integers. This is a peano style implementation

{-
newtype TInt n = TInt Int
-- I need to reflect a. I can do that with KnownNat, but what is the sinlgeton version?
safebuild :: Int -> Maybe (TInt (I a b))
safeBuild x | x < a = Nothing
            | x > b = Nothing
            | otherwise = Just (TInt x) 

roundInto :: KnownNat => Int -> (TInt (I a b))
roundInto x | x <= a = TInt a
            | x >= b = TInt b
            | otherwise = TInt x 

-- fishy. Sounds good and all but how are you going to actually deliver these proofs?
safecast :: (Sub (Interval a b) (Interval c d) ~ 'True) => TInt (Interval a b) -> TInt (Interval c d)
safecast x = coerce x 
-- also We may want all of the operators to have this implcitly.

-- A singleton flavor. We're kind of doing GDP style interval arithmetic?
plus :: ((i1 + i2) <== i3) ~~ 'True , i1, i2 ~ Interval a b )=> TInt i1 -> TInt i2 -> TInt i3 -- with cast built in.
plus :: TInt i1 -> TInt i2 -> TInt (i1 + i2) -- Singleton style addition



-}


{-

refinement stream
I'm doing some real free association here. I'm not making any sense.
a sequence of shrinking "intervals" or domains
absrtaction refinement is having some methodology for going as deep in the stream as you need
These are data types reifying a finite lattice. The sharing is perhaps not relevant. You might want to backtrack if you feel you refined the wrong path

The model is an Interval data type. A sequence of shrinking intervals is a plausible model for real numbers. Better than an uncontrolled infinite seqeunce of rationals?
Like, you can prove stuff. You just need to refine your knowledge of the number to the appropriate point.
Or perhaps a monotonic stream over regular numbers

-- an intriniscally decreasing non empty list
data MonoTonic a t where 
    Next :: a -> (a <= b) -> MonoTonic a t -> MonoTonic b t
    Done :: a -> Monotonic a t
-- There can be a strema version without done

-- "Internal" refinement
-- This is the CatList to the above List. We're refining an inequality rather than a domain?
data RefineStream a b where
    Refine :: c -> (c <= b) -> RefineStream a c -> RefineSteam a b
    End :: a -> RefineStream a a
RefineStream Top Top


-- Domain crossing "external" refinement. Galois connections. An adjunction list
data GaloisStream
    GNext :: ((f x <= y) <-> (x <= g y)) -> GaloisStream f tx -> GaloisStream g ty
    GNext :: (f -| g ) -> GaloisStream f tx -> GaloisStream g ty
    GDone

-- an adjunction tree
data GaloisTree

-}