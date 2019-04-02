{-# LANGUAGE TypeOperators, DataKinds, GADTs #-}
module Single where

import  Data.Type.Equality -- has defintions of symm, others
import Data.Nat -- extra package that inlcudes unary Nat.
import Data.Singletons.Prelude
import Data.Singletons.TH

type Fred a b = a :~: b

p1 :: Int :~: Int
p1 = Refl

p2 :: (Lit 0) :~: (Lit 0)
p2 = Refl

p3 :: (Lit 2) + (Lit 2) :~: (Lit 4)
p3 = Refl

p4 :: SNat x -> (Z + x) :~: x 
p4 _ = Refl

p5 :: SNat x -> (x + Z) :~: x 
p5 SZ = Refl
p5 (SS x) | Refl <- p5 x = Refl

