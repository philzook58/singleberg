{-# LANGUAGE TypeOperators, DataKinds, GADTs, MultiParamTypeClasses, FlexibleInstances,  FunctionalDependencies, UndecidableInstances, EmptyCase,
 LambdaCase, RankNTypes, PolyKinds #-}
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



nat_ind :: SNat x -> f 'Z -> (forall n. f n -> f ('S n)) -> f x 
nat_ind SZ base step = base
nat_ind (SS x) base step = step (nat_ind x base step)
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

-- compose + LERefl makes NatLE a catgoery
transle :: NatLE a b -> NatLE b c -> NatLE a c
transle p LERefl = p
-- transle LERefl p = p
transle p (LESucc p') | p'' <- transle p p' = LESucc p''

{-
instance Category NatLE where
    (.) = flip transle
    id = LERefl
    -}

zerole :: SNat a -> NatLE Z a
zerole SZ = LERefl
zerole (SS x) = LESucc (zerole x)

{-
-- yikes. The higher order singleton is pain itself.
-- maybe I should be proving in a type family?
-- type families do not check for incomplete patterns?
type family LEUnique :: forall a ->    where

-- ooh. That ryan gl scott patch might be reall nice here.

le_unique :: SNatLE (le :: 'NatLE m n) ->  SNatLE (le' :: 'NatLE m n) -> le :~: le'
le_unique

    -}
-- indirect equality
-- type Iso a b = (a -> b, b -> a)
--  SNat m -> SNat n -> (forall k. Iso (NatLE k m) (NatLE k n) -> m :~: n


{-
le_eq ::  SNat m -> SNat n -> NatLE m n -> NatLE n m -> m :~: n
le_eq _ _ LERefl _ = Refl
le_eq _ _ (LESucc p) (LESucc p') | Refl <- le_eq p p' = Refl 

-}
-- an the other cases are impossible, but this is probably not obvious yet to the compiler

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


id_def :: (Id x) :~: x
id_def = Refl

id_def' :: (IdSym0 @@ x) :~: x
id_def' = Refl

const_def :: (ConstSym0 @@ x @@ y) :~: x
const_def = Refl

const_def' :: (ConstSym1 x @@ y) :~: x
const_def' = Refl


-- proving functor laws.
-- SMaybe x -> (FMap (g :. f) x) :~: (FMap g) (FMap f x))

-- Elem predicate
-- there is Elem in sList as a Bool valued function
data Elem' a xs where
   Here :: Elem' a (a : xs)
   There :: Elem' a xs -> Elem' a (b : xs) 

simp :: Elem' (Lit 1) '[Lit 1]
simp = Here

simp2 :: Elem' (Lit 1) '[Lit 2, Lit 1]
simp2 = There Here

-- there is also an All in foldable
data All' p xs where
   AllNil :: All' p '[]
   AllCons :: (p a) -> All' p xs -> All' p (a : xs)
-- HList vs SList. Kind of similar, except SCons takes a Sing, and HList doesn't

-- Rationals

{-

can we use sbv via the [Bool] -> (forall a. Sing a -> r) -> r interface?
I don't think so. It isn't part of the resolution mechanism

There are also Singleton MonadPlus instances.

auto (ctx) (a -> b)

Auto [[goal]]


-- you can add stuff globally by extending the hint database like so.
class Auto (SNat ('S a))
   auto ctx = SS (auto ctx @a)
class Auto (SNat 'Z)
   auto ctx = SZ


class Auto (a -> b)
   auto ctx = \x -> auto (x : ctx) @b

class Auto (a,b) 
   auto ctx = (auto ctx @a, auto ctx @b)

class SearchCtx ctx b where
   search (ctx )

-}

-- function extensionality, ghc is not happy
-- extensionality :: (forall x. (f @@ x) :~: (g @@ x)) -> f :~: g
-- extensionality = undefined

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

or Auto typeclass
Auto ctx goal fuel

needs hlist to hold everything in context. You need to add everything to context manually. Constructors, etc.
 we don't get partial solves. template haskell might

 need mutiple branches of the search ,with multiple possible goals per branch
 Many branches may share goals. so maybe splitting it up liek this isn't wise.


trything :: (forall a. a -> a) -> (Bool, Maybe b)
trything f = (f True, f Nothing)


intervals

data SInterval l d where -- l is lower bound. l + d is the upper. automatically 
   SInterval :: SInterval n m

-- alternative
data Interval m d where
   Point :: Interval m m
   Inc :: Interval m n -> Interval m ('S n)

-- could have a cnaonical ordering of ExtL ExtR if it helps.
-- probably easier. Strange to be asymmettric though
data SubSet i j where
   IRefl :: SubSet (Interval i i) (Interval i i) 
   ExtL :: SubSet (Interval m l) (Interval k l) -> SubSet (Interval ('S m) l) (Interval k l)
   ExtR :: SubSet (Interval m n) (Interval k l) -> SubSet (Interval m n) (Interval k ('S l)

So a proof will always be of the form ExtR ... ExtL ExtL ... IRefl
Alternative

data SubSet i j where
  SubSet :: (i <= j) -> (k <= l)  -> SubSet (Interval j k) (Interval i l) 

i c= j is decidable


Lists as finite sets of integers. 

A set predicate as
SNat n -> SBool n
A set predicate as
'Nat ~> 'Bool


tewo dimensional space
V2 n m


-}

