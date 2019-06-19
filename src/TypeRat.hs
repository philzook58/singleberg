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
module TypeRat where

-- import Data.Ratio

import Data.Singletons.TH
import Data.Singletons.Prelude.Num
-- You know we're not getting much help using the Haskell Ratio type
-- espiecally since the construcotr is :% which is going to be a nightmare of symbols
-- $(genSingletons [''Ratio])

$(promote [d|
  data Rat a = Rat a a
  plus :: Num a => Rat a -> Rat a -> Rat a
  plus (Rat x y) (Rat a b) = Rat (b*x + y*a) (y * b)
  --mul (Rat x y) (Rat a b) = Rat (a*x) (y * b)

  instance (Num a, Eq a) => Eq (Rat a) where
    (Rat x y) == (Rat a b) = (b * x) == (a * y)
  instance (Num a, Ord a) => Ord (Rat a) where
    compare (Rat x y) (Rat a b) = compare (b * x) (a * y) -- assuming both denominators are positive (or both are negative).
  instance (Num a) => Num (Rat a) where
    (Rat x y) + (Rat a b) = Rat (b*x + y*a) (y * b)
    (Rat x y) - (Rat a b) = Rat (b*x - y*a) (y * b)
    (Rat x y) * (Rat a b) = Rat (a*x) (y * b)
    abs (Rat x y) = Rat (abs x) (abs y)
    fromInteger x = Rat (fromInteger x) (fromInteger 1)
    signum (Rat x y) = Rat (signum x) (signum y)


 

  |])

-- You know, I think there is a good argument to be made for 
-- -@#@$ may be a reaosnable symbol fro integer
-- /@#@$ might be a rewasonable symbol for  

type Test1 = 1 == 1
type Test2 = ('Rat 2 4) == ('Rat 1 2) -- 'True
type Test3 = ('Rat 3 4) == ('Rat 1 2) -- 'False


-- No this isn't really what we wanted. $$$ directly translates to the type family
--type Integer' a b = a -@#@$$$ b

--type Test4 = (Integer' 4 2)

{-
$(singletons [d|
  data Nat = Zero | Succ Nat
  pred :: Nat -> Nat
  pred Zero = Zero
  pred (Succ n) = n
  |])
  -}
-- test1 :: SRatio ()