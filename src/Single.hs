{-# LANGUAGE TypeOperators, DataKinds, GADTs, MultiParamTypeClasses, FlexibleInstances,  FunctionalDependencies, UndecidableInstances, EmptyCase, LambdaCase #-}
module Single where

import  Data.Type.Equality -- has defintions of symm, others
import Data.Nat -- extra package that inlcudes unary Nat.
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.Sigma
import Data.Singletons.Decide
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


-- using the ordinary inequality type of singletons. Maybe we should reflect to a oprositional inqueality

simpord :: SBool ((Lit 0) <= (Lit 1))
simpord = STrue

-- I'm having a lot of trouble with the singleton native <= operator. I'm not certain what it's definition even is
{-
lerefl :: SNat x -> (x <= x) :~: True
lerefl SZ = Refl
lerefl (SS x) | Refl <- lerefl x = 
-}

{-
my guess for how <= looks
Z <= Z = True
Z <= (S y) = True
(S x) <= (S y) = x <= y
(S x) <= Z = False


-}
{-
succle :: SNat a -> SNat b -> (a <= b) :~: True -> ((S a) <= (S b)) :~: True
succle SZ SZ _ = Refl
succle SZ (SS b) _ = Refl
succle (SS a) (SS b) Refl | Refl <- succle a b _ = _
-}
{-
succle :: SNat a -> SNat b -> (a <= b) :~: True -> (a <= (S b)) :~: True
succle SZ SZ _ = Refl
succle SZ (SS b) _ = Refl
succle (SS a) (SS b) Refl = _
-}

succinj :: a :~: b -> (S a) :~: (S b)
succinj Refl = Refl

-- basically isomorphic to the Nat of the difference
data NatLE a b where
    LERefl :: NatLE a a
    LESucc :: NatLE a b -> NatLE a (S b)

transle :: NatLE a b -> NatLE b c -> NatLE a c
transle p LERefl = p
-- transle LERefl p = p
transle p (LESucc p') | p'' <- transle p p' = LESucc p''

zerole :: SNat a -> NatLE Z a
zerole SZ = LERefl
zerole (SS x) = LESucc (zerole x)


data Even n where
   EZero :: Even Z
   ETwo :: Even n -> Even (S (S n))

oneisnoteven :: Refuted (Even (Lit 1))
oneisnoteven = \case {}

evenorodd :: SNat a -> Decision (Even a)
evenorodd SZ = Proved EZero
evenorodd (SS SZ) = Disproved oneisnoteven
evenorodd (SS (SS x)) = case (evenorodd x) of
                        Proved p -> Proved (ETwo p)
                        Disproved f -> Disproved (\case (ETwo z) -> f z)


{-
leastzero :: SNat n ->  (Z <= n)  :~: True
leastzero SZ = Refl
leastzero (SS x) | Refl <- leastzero x = 
-}
-- alternative style
data Plus a b c where
    CaseZ :: Plus Z x x
    CaseS :: Plus a b c -> Plus (S a) b (S c) 

-- for concrete cases, cplus can find values.
class CPlus a b c | a b -> c where -- , c a -> b, c b -> a
    cplus :: Plus a b c

instance (a ~ b) => CPlus Z a b where
    cplus = CaseZ
instance CPlus a b c => CPlus (S a) b (S c) where
    cplus = CaseS (cplus)
{-
unique result. We need to show that given a and b, there is a unique c.
SNat a -> SNat b -> SNat c -> SNat c' -> Plus a b c -> Plus a b c' -> c :~: c'

plus_is_func :: SNat a -> SNat b -> exists c. (SNat c, Plus a b c) 
plus_is_func SZ y = (reflect, cplus)
plus_is_func (SS x) y | (c, p) <- plus_is_func x y = (reflect, cplus)

plus 

-}

uniqueplus :: SNat a -> SNat b -> Plus a b c -> Plus a b c' -> c :~: c'
uniqueplus SZ SZ CaseZ CaseZ = Refl
uniqueplus SZ (SS b) CaseZ CaseZ | Refl <- uniqueplus SZ b CaseZ CaseZ = Refl
uniqueplus (SS a) b (CaseS p) (CaseS p') | Refl <- uniqueplus a b p p' = Refl


-- plus_Z :: SNat n -> Plus Z b b
plus_Z :: SNat a -> Plus a Z a
plus_Z SZ = CaseZ
plus_Z (SS x) = CaseS (plus_Z x) 

-- ploos :: Plus a Z a -> (Plus a Z c, a :~: c)

-- incomplete pattern. These patterns are impossible
plus_Z' :: SNat a -> SNat c -> Plus a Z c -> c :~: a
plus_Z' SZ SZ CaseZ = Refl
-- plus_Z' SZ (SS _) CaseZ = Refl
plus_Z' (SS a) (SS c) (CaseS p) | Refl <- plus_Z' a c p = Refl

-- a rather confusing theorem
plus_comm :: SNat a -> SNat b -> Plus a b c -> Plus b a c
plus_comm SZ y CaseZ = plus_Z y
plus_comm (SS x) SZ (CaseS p) | p' <- plus_Z x, Refl <- uniqueplus x SZ p p' = CaseZ -- Plus b ('S n) ('S c1)
plus_comm (SS x) (SS y) (CaseS p) | (CaseS p'') <- plus_comm x (SS y) p, p''' <- plus_comm y x p'', p' <- plus_comm (SS x) y (CaseS p''') = CaseS p' 
-- SNatI c => 
-- and then we can grab via  | Z <- sing @c
-- plus_comm (SS x) (SS y) (CaseS p) = CaseS _



{-

ISO ::  a -> b, b -> c
iso is meaningful as a theorem. it is an iff.
Lens
(a -> (b, b -> a)

given a then b, but also then also b implies a... well duh. you already have an a.
a -> b -> a  is an easy theorem. const.

fully polymoprhic may still be a theorem.
s -> (a, b -> t)




template haskell based auto?

-}

