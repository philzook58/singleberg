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
, TypeApplications
, MultiParamTypeClasses
#-}
module PointFree where

import  Data.Singletons.Prelude.Void
import Data.Singletons.Prelude.Tuple
import Data.Singletons.Prelude.Either
import Data.Singletons

-- This does not appear to do what we'd want. It kind of does. But it recursively requires to be able to Demote Bool? So it may not work polymorphically
{-test1 :: (Bool,Bool) -> Bool
  test1 = demote @(FstSym0 :: ((Bool,Bool) ~> Bool))
-}

{-
Prologful relations rather than functions. In Coq, Agda etc sometimes it is preferable to build a relational data type rather than a functiona specification.
For exmaple in a machine intepreter. In Software foundations they show both styles.

We can build data type copies of functions Many of the below combinators are.
RId is just a reified id
RNat is just a reified id :: Bool -> Bool






-}

data Nat = Z | S Nat
-- ? how is this different from RId specialized to 'Nat? Well I can destrcut on it. I suppose I can prove things by induction now?
-- does this make any sense at all?
data RNat s s' where -- RNatId
    RS :: RNat s s -> RNat ('S s) ('S s) -- make it recursive or not?
    RZ :: RNat 'Z 'Z
data RBool s s' where
    RTrue :: RBool 'True 'True
    RFalse :: RBool 'False 'False

-- Individal functions become 
-- a succesor relations
data RSucc s s' where
    RSucc :: RSucc s ('S s)
-- a boolean indicator function
data RIsZero s s' where
    RIsZero :: RIsZero 'Z 'True
    RNotZero :: RIsZero ('S x) 'False

-- a projection relation. 
data ProjZ s s' where
    ProjZ :: ProjZ 'Z 'Z

data RLTE s s' where
    REq :: RLTE s s
    RUp :: RLTE s s' -> RLTE s ('S s')

type a <= b = RLTE a b

type k <<< k' = RCompose k k' 
type k >>> k' = RCompose k' k
-- RComp? -- Identical to ProCompose
-- existentials tend to be hidden in compose
data RCompose k k' a c where
    RCompose :: k b c -> k' a b -> RCompose k k' a c

-- guess no unary operators
-- type ~~ k = RConverse k
type Con k = RConverse k
{-
Would automatically stirp doulbe converse, which might be nice.
type family Con where
    Con (RConverse k) = k
    Con k = RConverse k 
-}

data RConverse k a b where -- Shorten to RCon?
    RConverse :: k a b -> RConverse k b a




-- similar to bifunctor product :*:. 
newtype RMeet k k' a b = RMeet (k a b, k' a b)
type k /\ k' = RMeet k k'  

meet_assoc :: RMeet k (RMeet k' k'') a b -> RMeet (RMeet k k') k'' a b
meet_assoc (RMeet (k, (RMeet (k',k'')))) = RMeet (RMeet (k,k'), k'')

{-
meet_comm
meet_assoc'

join_assoc
join_comm
join_assoc'
-}
newtype RJoin k k' a b = RJoin (Either (k a b) (k' a b))

type k \/ k' = RJoin k k'  
-- singletonized functions are acceptable as relations also.
type SingleFun a b = (Sing a) -> (Sing b)
-- data RFun a b a' b' where
--     RFun :: (Sing a a' -> Sing b b') -> RFun a b a' b' 
-- newtype RFun a b = RFun
data RId a b where
    RId :: RId a a

data RFst a b where
    RFst :: RFst '(a,b) a  -- should these actually be backticked?

data RSnd a b where
    RSnd :: RSnd '(a,b) b 

    -- http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Ran.html
    -- universals are hidden in Divisions
newtype RDiv g j a b = RDiv { runRDiv :: forall x. g x a -> j x b }
type g // j = RDiv g j
newtype LDiv g j a b = LDiv { runLDiv :: forall x. g a x -> j b x } -- ? Ddid i do this right? I was just guessin. Maybe I need to reverse more stuff.
type g \\ j = LDiv g j -- parse error on single slash

-- Agda paper suggestion 
-- type r \\ s = Con ((Con s) // (Con r))

data IFF a b = IFF {to :: a -> b, from :: b -> a} 
type a <-> b = IFF a b

{-
-- basically kan extension
-- something like
-- http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Ran.html

RLDiv g j a b where
    RLDiv :: (forall c. j c a -> g b c) -> RDiv g j a b

type Iso' a b = IFF a b    

Galois f g = RSub (RCompose f x) y <-> RSub x (RCompose y g) ( an iso)


reynolds :: k a b -> k c d -> RSub ( <<< ) () 

data Reynolds p q a b c d where
    Reynolds :: RSub ((RFun a b) <<< r) (q <<< RFun c d) -> Reynolds p q a b c d 
freetheorem :: Reynolds p q a b a b
freetheorem = Reynods ?

Do I even want to make RSub a special thing?
newtype RSub k k' = RSub (forall a b. (k a b) -> k' a b))

Do I have too much crap layered on? 

data In a s where
    In :: (s a) -> In a s

data Pow k -- use galois connection?


What about the dedekind law?

-}

{- This is par?
data RTup a b where
    RTup :: k a a -> k b b -> RTup k k' (a,b) (a,b)
-}

data RFan k k' a b where
    RFan :: k a b -> k' a c -> RFan k k' a '(b, c) 

rdup = RFan RId RId
data RDup a b where
    RDup :: RDup a '(a,a)
-- rdup, RDup equivlaency proof? 

{-
-- I'm mixing and matching curry howard?
-- http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Types.html#t::-45--62-
-- :-> is rsub 

Iso = forall p. Profunctor p => p a b -> p s t
? = forall p. p a b -> p s t.  -- This is porbably literal equality. a relational form of leibnitz equality. a ~ s, b ~ t

We're using singletons in the type variables. This leads to the question: What is a Lens (a :: 'Nat) (b :: 'Nat)
Or what is Iso? Iso is relation ready to interface with functions.

-}

{-
Hmm. If we assume that the functions are singleton functions, then I'm cool with it. Makes sense.
Profunctor is the same as saying composable with 
FreePro k a b = FreePro (a -> c) (p c d) (d -> b) 
instance Profunctor (RCompose (RCompose RFun k) RFun) where
    dimap f g (RCOmpose (RCompose f' r) g' )= = RCompose (RCompose (f . f') r) (g' . g)  

-- This is the entire space relation
data TNat s s' where
    RZ :: RNat 'Z 'Z
    RSucc1 :: RNat s' s -> RNat (S s') s
    RSucc2 :: RNat s' s -> RNat s' ('S s)
    ) 



data VNat s s'   -- void relation


class ProFunctor p where
    dimap :: ( -> ) ( ->) -> 

-}

-- I bow to precedent.
type k :-> k' = RSub k k'
newtype RSub k k' = RSub (forall a b.  k a b -> k' a b)

subCompose :: RSub g h -> RSub f g -> RSub f h
subCompose (RSub f) (RSub g) = RSub (f . g)

subId :: f :-> f
subId = RSub id


compose_mono :: (p :-> q) -> (g :-> j) -> ( (p <<< g) :-> (q <<< j))
compose_mono (RSub f) (RSub h) = RSub $ \(RCompose p g) -> RCompose (f p) (h g) 

p1 :: RSub (RMeet k k') k
p1 = RSub (\(RMeet (k, k')) -> k)

p2 :: RSub (RMeet k k') k'
p2 = RSub (\(RMeet (k, k')) -> k')

p3 :: RSub k (RJoin k k')
p3 = RSub (\k -> RJoin (Left k))

p4 :: RSub RNat RId 
p4 = RSub (\rn -> case rn of
                  RZ -> RId
                  RS _ -> RId )
p5 :: RSub RId RNat -- ????
p5 = RSub (\RId -> undefined)  -- ??? What can I put here? I kind of need the fact that any type of kind 'Nat either has type 'Z or 'S x. I need to case on the type. Typeclass?

p6 :: RSub (RConverse (RConverse k)) k
p6 = RSub (\(RConverse (RConverse k)) -> k)

p7 :: RSub k (RConverse (RConverse k))
p7 = RSub (\k -> (RConverse (RConverse k)))
-- ? These are different   
-- type RSub' k k' a b = k a b -> k' a b

-- nothin
data RBottom a b

-- anything goes
data RTop a b where
    RTop :: RTop a b

newtype Ker r a b = Ker (RCompose (RConverse r) r a b)
ker r = RCompose (RConverse r) r
newtype Img r a b = Img (RCompose r (RConverse r) a b)
img r = RCompose r (RConverse r)


type Simple f = (Img f) :-> RId
type Entire f = RId :-> (Ker f)
type Function' f = (Simple f, Entire f)


data Trans k a b where
    Trans :: k (a,b) c -> Trans k a (b,c)
untrans :: Trans k a (b,c) -> k (a,b) c
untrans (Trans k) = k

data UnTrans k a b where
    UnTrans :: k a (b,c) -> UnTrans k (a,b) c

trans :: UnTrans k (a,b) c -> k a (b,c)
trans (UnTrans k) = k
{-

Shunting rules
Function equaltity rule - For function RSub == Eq

-}
p8 :: RSub (RCompose RId k) k
p8 = RSub (\(RCompose RId k) -> k)

p9 :: RSub k (RCompose RId k)
p9 = RSub (\k -> (RCompose RId k))

-- indirect eq. Got an Iso feel. just because it has such weird quantification. A quantified expression over a * -> * -> * type
-- such yoneda nonsense
type RSub' k k' = forall x. (x :-> k) -> (x :-> k')
p10 :: RSub' k k' -> k :-> k'
p10 f = f subId

converse_mono :: (Con k :-> Con k') -> (k :-> k')
converse_mono (RSub f) = RSub $ \k -> let (RConverse k') = f (RConverse k) in k'



-- rpar :: k a b -> k' c d -> _ k k'  
rpar f g =  RFan (RCompose f RFst) (RCompose g RSnd)
-- but also we could define it as a new concept

class Function k a b where
    interp :: k -> (a -> b)
instance Function (RId a' a') a a where
    interp _ = id
instance Function (RConverse RId a' a') a a where -- some converse are implementable
    interp _ = id
instance Function (k a' b') a b => Function (RConverse (RConverse k) a' b') a b where -- double converse can be stripped.
    interp (RConverse (RConverse f)) = interp f
instance Function (RSucc s s') Nat Nat where
    interp _ = S
{-
class Search f a b where
    search :: f -> a -> [b]
-- I may wish to interpet the relation into a relational search program.
-- Perhaps other monads? State may make sense.
class Monadable k a b where
    type MConstr :: Constraint
    interp :: (MConstr m) => k -> (a -> m b)
class Category k' => Catable k k' a b where
    interp :: k -> k' a b
-- Template haskell interpretation?
-- should I do the whole thing finally tagless?

class Profunctorable k 

-- maybe being a profunctor is the property I want? That means it is implementable in some sense. I dunno though.
class Profunctor k


    -}
    {-
    
    Fix
    Fold
    RCata :: k (f a) a -> RCata k (Fix f a) a 
    RHylo


WHAT THE HELL AM I DOING?
I'm doing point free singleton programming?
I'm building an exact type level match to the value level function?
What was wrong with the old approach (Point Free DSL) ? I had a value level representation of the functions.
I was only tracking types before. Not the actual function values.
This approach is open. I'm free to add more functions at will.
I'm also free to use regular singletonized haskell functions.
The other approach let meassure type correctness, and any reaosning would happen at the value level. Which is fine.


PF is also a relation, but the objects in the relation are Type. 

    -}
{-

data Set :: * -> *
f :: 'Nat -> Prop
r :: 'Nat -> * -> Prop    
class Set (f :: a -> b)
class Rel (r :: a -> b -> c)    

The difference between if the item is in this list, it abeys this property and if something obeys this property it is in this list.
we need a new reflection convention

data Rel p a b where
    Cons :: p a b -> (a,b) -> Rel p a b  
    Nil :: Rel p a b

a -> b -> p a b -> In (a,b) (Rel p a b)

data AllInts a a where
    Next :: a -> AllInt (S n) (S n)

A reflected type level thing.
FinRel a b 
    Cons :: (a,b) -> FinRel xs -> FinRel  (a,b) :: xs   

Hmm. Putting type level witnesses really helps us none at all. It's the same problems lifted up one level


SndSym0s
FstSym0
CurrySym1
UncurrySym1
LeftSym0
RightSym0
AbsurdSym0
IdSym0
ConstSym1 '()


SwapSym0

Dup?
Dump

We need to singletonize Control.Arrow combinators.
Singletonize recursion schemes.

I'm not clear what using the singleton versions of these things gets us but I thought it was worth a try
-- we can either work with values
newtype TFun l a b = TFun 

-- http://hackage.haskell.org/package/singletons-2.5.1/docs/Data-Singletons.html
-- the demote function



data PF a b where
    Id :: PF a a
    Comp :: PF b c -> PF a b -> PF a c
    Fst :: PF (a,b) a
    Snd :: PF (a,b) b
    Fan :: PF a b -> PF a c -> PF a (b,c)
    Lit :: (a -> b) -> PF a b
    Dump :: PF a ()
    Split :: PF a b -> PF c b -> PF (a :+: c) b
    Lft :: PF a (a :+: b)
    Rgt :: PF b (a :+: b)


class PF f where

class Category PF where
    id = Id
    (.) = Comp
-- finally tagless categorical dsl

-- transformation
data Ctx = PreCompFst | PreCompSnd | Other | IsFan
data CtxWrap ctx k a b = CtxWrap ctx (k a b)

instance Category (CtxWrap k) where
    id = CtxWrap Other id
    (CtxWrap PreCompFst ) . (CtxWrap _ ) = CtxWrap   .


data IsId = IsId | Other

-- retagging?

instance Categroy k => Category (CtxWrap (IsId) k) where
    id = CtxWrap IsId id
    (CtxWrap IsId _) . f = f
    g . (CtxWrap isId _) g
    (CtxWrap _ g) (CtxWrap _ f) = CtxWrap Other (g . f) 

newtype CtxWrap' ctx k a b = CtxWrap (ctx -> k a b) 


data Ctx = IsFst | IsSnd

instance Cartesian k => Cartesian (CtxWrap' Ctx k)
   fan f g = 
   

fusefan (Comp Fst (Fan f g)) = f
fusefan (Comp Snd (Fan f g)) = g


I was conisdering a version of this stuff without the points. Perhaps without body?

data Compose k k'
data Snd
data Fst
data Fan
data Cata k
data Meet k k'
data Join k k'

or perhaps these might be the datakind lifted pieces of the above pf data type

-}