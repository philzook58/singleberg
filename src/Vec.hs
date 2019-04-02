{-# LANGUAGE GADTs, DataKinds, TypeFamilies, RankNTypes, UndecidableInstances, PolyKinds #-}

module Vec where


{-

Question:
Is there a way to strip out all the overhead with typed template haskell?


-}

data Nat = Zero | Succ Nat
{-
nplus :: Nat -> Nat -> Nat
nplus Zero x = x
nplus (Succ x) y = nplus x (Succ y)
-}


data SNat s where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)

-- Mostly only work with Singletonized versions if you want to do proving. Ignore that the original Nat exists.

type family NPlus x y where
    NPlus 'Zero x = x
    NPlus ('Succ x) y = 'Succ (NPlus x y)

-- snplus is a direct reflection of the type level function NPlus via the singleton property
snplus :: SNat n -> SNat n' -> SNat (NPlus n n')
snplus SZero x = x
snplus (SSucc x) y = SSucc (snplus x y) 




data Eq1 a b where
    Refl :: Eq1 a a

proof1 :: Eq1 ('Zero) ('Zero)
proof1 = Refl

proof5 :: Eq1 (NPlus ('Succ 'Zero) 'Zero) ('Succ 'Zero)
proof5 = Refl

proof2 :: forall x. SNat x -> Eq1 (NPlus 'Zero x) x
proof2 x = Refl
{-
p3 :: SNat x -> SNat y -> Eq1 ('Succ (NPlus x y)) (NPlus x ('Succ y))
p3 SZero _ = Refl
p3 (SSucc x) y = _
-}

proof3 :: SNat x -> (Eq1 (NPlus x 'Zero) x)
proof3 SZero = Refl
proof3 (SSucc x) | Refl <- proof3 x = Refl

rewrite :: forall f a b. Eq1 a b -> f a -> f b  
rewrite Refl = id

symm :: Eq1 a b -> Eq1 b a
symm Refl = Refl

trans :: Eq1 a b -> Eq1 b c -> Eq1 a c 
trans Refl Refl = Refl

p4 :: SNat x -> SNat y -> Eq1 (NPlus x ('Succ y)) ('Succ (NPlus x y))
p4 SZero _ = Refl
p4 (SSucc x) y | Refl <- p4 x y = Refl

natcomm :: SNat x -> SNat y -> Eq1 (NPlus x y) (NPlus y x)
natcomm SZero y | Refl <- proof3 y = Refl 
natcomm x@(SSucc x') SZero | Refl <- proof3 x = Refl
natcomm (SSucc x) (SSucc y) | Refl <- natcomm x (SSucc y), Refl <- natcomm (SSucc x) y, Refl <- natcomm x y = Refl

data Vec n a where
    VCons :: a -> Vec n a -> Vec ('Succ n) a
    VNil :: Vec 'Zero a


