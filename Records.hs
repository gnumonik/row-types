{-# LANGUAGE TypeOperators, NoMonomorphismRestriction, ScopedTypeVariables,GADTs, KindSignatures, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,RankNTypes,AllowAmbiguousTypes, InstanceSigs, PolyKinds #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  OpenRecVar
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
-- 
-- This module implements extensible records  as 
-- described in paper `Extensible Records with Scoped Labels`,
-- Daan Leijen, Proc. 2005 Symp. Trends in Functional Programming
-- available at <http://research.microsoft.com/pubs/65409/scopedlabels.pdf>
--
-- See Examples.hs for examples.
-- 
-- The main difference with the paper is that this module does not extend
-- the type system, but instead uses closed type families, GADTs and
-- type level symbols to implement the system. 
--
-- For this a small extension to GHC is needed which implements the 
-- built-in closed type family 
--  @type family (m :: Symbol) <=.? (n :: Symbol) :: Bool@
-- where Symbol is a type literal.
--
-- Patches to implement this extension to GHC (patchmain) and the base library (patchlib) are also found in the 
-- git repo that hosts this project <https://github.com/atzeus/openrec>
-- I've sent these patches to Iavor Diatchki (who is implementing the type literal stuff) to get these (small) changes into the main repo.
--
-- This small extension allows us to keep lists of (label,type) pairs sorted thereby ensuring
-- that { x = 0, y = 0 } and { y = 0, x = 0 } have the same type.
-- 
-- In this way we can implement standard type classes such as Show, Eq, Ord and Bounded
-- for open records, given that all the elements of the open record satify the constraint.
--
-- Type level operators start with @:@, value level operators start with @.@.
-- 
-- Now uses Hashmaps because of speed <http://blog.johantibell.com/2012/03/announcing-unordered-containers-02.html>
-----------------------------------------------------------------------------


module Records

 (
             -- * Records
             Rec,   
             empty,
             RecordOp(..),
              (.|),
             (.!),
             (.-),
             (.++),(.+),
             IsRow(..),
             Forall(..),
             CRZip(..),
             -- * Rows 
             Row, Empty , (:|), (:!), (:-),(:\), (:\\), 
             -- *  Labels and label type pairs
             KnownSymbol(..),
             Label(..),
             LT(..)
            
           
     ) 
where

import Data.HashMap.Lazy(HashMap)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.HashMap.Lazy as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import Data.List
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds

{--------------------------------------------------------------------
  Labels and Label value pairs
--------------------------------------------------------------------}

-- | A label 
data Label (s :: Symbol) = Label

instance KnownSymbol s => Show (Label s) where
  show = symbolVal

infixr 6 :->
-- | A label-type pair (data kind) 
data LT b = Symbol :-> b

{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

newtype Row a = R [LT a] -- constructor not exported

type family Empty :: Row * where
  Empty = R '[]

infixr 5 :|
-- | Extend the row with a label-type pair
type family (l :: LT *) :|  (r :: Row *) :: Row * where
  l :| (R x) = R (Inject l x)

infixl 6 :!
-- | Get the type associated with a label
type family (r :: Row *) :! (t :: Symbol) :: * where
  (R r) :! l = Get l r

-- | Remove a label from a row
type family (r :: Row *) :- (s :: Symbol)  :: Row * where
  (R r) :- l = R (Remove l r)

type family (l :: Row *) :++  (r :: Row *)  :: Row * where
  (R l) :++ (R r) = R (Merge l r)

type family (l :: Row *) :+  (r :: Row *)  :: Row * where
  (R l) :+ (R r) = R (Merge l r)

-- | Does the row lack (i.e. it has not) the specified label?
class (r :: Row *) :\ (l :: Symbol)
instance (Lacks l r ~ LabelUnique l) => (R r) :\ l

-- | Are the two rows disjoint? (i.e. their sets of labels are disjoint)
class (l :: Row *) :\\ (r :: Row *)
instance (Disjoint l r ~ IsDisjoint) => (R l) :\\ (R r)

-- private things for row operations


-- gives nicer error message than Bool
data Unique = LabelUnique Symbol | LabelNotUnique Symbol

type family Inject (l :: LT *) (r :: [LT *]) where
  Inject (l :-> t) '[] = (l :-> t ': '[])
  Inject (l :-> t) (l' :-> t' ': x) = 
      Ifte (l <=.? l')
      (l :-> t   ': l' :-> t' ': x)
      (l' :-> t' ': (Inject (l :-> t)  x))

type family Ifte (c :: Bool) (t :: [LT *]) (f :: [LT *])   where
  Ifte True  t f = t
  Ifte False t f = f

type family Get (l :: Symbol) (r :: [LT *]) where
  Get l (l :-> t ': x) = t
  Get l (l' :-> t ': x) = Get l x

type family Remove (l :: Symbol) (r :: [LT *]) where
  Remove l (l :-> t ': x) = x
  Remove l (l' :-> t ': x) = l' :-> t ': Remove l x

type family Lacks (l :: Symbol) (r :: [LT *]) where
  Lacks l '[] = LabelUnique l
  Lacks l (l :-> t ': x) = LabelNotUnique l

type family Merge (l :: [LT *]) (r :: [LT *]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) = 
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

-- gives nicer error message than Bool
data DisjointErr = IsDisjoint | Duplicate Symbol

type family IfteD (c :: Bool) (t :: DisjointErr) (f :: DisjointErr)   where
  IfteD True  t f = t
  IfteD False t f = f


type family Disjoint (l :: [LT *]) (r :: [LT *]) where
    Disjoint '[] r = IsDisjoint
    Disjoint l '[] = IsDisjoint
    Disjoint (l :-> al ': tl) (l :-> ar ': tr) = Duplicate l
    Disjoint (hl :-> al ': tl) (hr :-> ar ': tr) = 
      IfteD (hl <=.? hr)
      (Disjoint tl (hr :-> ar ': tr))
      (Disjoint (hl :-> al ': tl) tr)


{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}

data HideType where
  HideType :: a -> HideType

-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap String (Seq HideType) -> Rec r

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

infix 5 :=
infix 5 :!=
infix 5 :<-
-- | Record operations for use with '.|' 
-- 
--  [@:=@] Record extension.
--
--  [@:!=@] Record extension, without shadowing. 
--
--  [@:<-@] Record update.
data RecordOp in' out where
  (:=)  :: KnownSymbol l           => Label l -> a      -> RecordOp r (l :-> a :| r)  
  (:!=) :: (KnownSymbol l, r :\ l) => Label l -> a      -> RecordOp r (l :-> a :| r)  
  (:<-) :: KnownSymbol l           => Label l -> r :! l -> RecordOp r r  

-- | Apply an operation to a record.
infixr 4 .|
(.|) :: RecordOp r r' -> Rec r -> Rec r'
((show -> l) := a) .| (OR m)  = OR $ M.insert l v m where v = HideType a <| M.lookupDefault S.empty l m
((show -> l) :!= a) .| (OR m) = OR $ M.insert l v m where v = HideType a <| M.lookupDefault S.empty l m
((show -> l) :<- a) .| (OR m) = OR $ M.adjust f l m where f = S.update 0 (HideType a)  


infix  8 .-
-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r :! l
(OR m) .! (show -> a) = x'
   where x S.:< t =  S.viewl $ m M.! a 
         -- notice that this is safe because of the external type
         x' = case x of HideType p -> unsafeCoerce p 

-- | Record restriction
(.-) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r :- l)
(OR m) .- (show -> a) = OR m'
   where x S.:< t =  S.viewl $ m M.! a 
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m

-- | Record merge (not commutative)
(.++) :: Rec l -> Rec r -> Rec (l :++ r)
(OR l) .++ (OR r) = OR $ M.unionWith (><) l r

-- | Record disjoint union (commutative)
(.+) :: (l :\\ r) => Rec l -> Rec r -> Rec (l :+ r)
(OR l) .+ (OR r) = OR $ M.unionWith (error "Impossible") l r


unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (show -> a) b (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.lookupDefault S.empty a m


class IsRow (r :: Row *) where

  getLabels :: Rec r -> [String]

instance IsRow (R '[]) where
  getLabels _ = []

instance (KnownSymbol l, IsRow (R t)) =>  IsRow (R (l :-> a ': t)) where
  getLabels r = show l : getLabels (r .- l) where
     l = Label :: Label l


-- | If the constaint @c@ holds for all elements in the row @r@,
--  then the methods in this class are available.
class IsRow r => Forall (r :: Row *) (c :: * -> Constraint) where
 -- | Given a default value @a@, where@a@ can be instantiated to each type in the row,
 -- create a new record in which all elements carry this default value.
 rinit     :: (forall a. c a => a) -> Rec r
 -- | Given a function @(a -> b)@ where @a@ can be instantiated to each type in the row,
 --   apply the function to each element in the record and collect the result in a list.
 -- 
 --    The order of the resulting list is guaranteed to be the same as the order 
 --    when using 'getLabels'. 
 erase    :: (forall a. c a => a -> b) -> Rec r -> [b]
 -- | Given a function @(a -> a -> b)@ where @a@ can be instantiated to each type of the row,
 -- apply the function to each pair of values that can be obtained by indexing the two records
 -- with the same label and collect the result in a list.
 --
 --  The order is guaranteed to be the same as the order 
 --   when using 'getLabels'. 
 eraseZip :: (forall a. c a => a -> a -> b) -> Rec r -> Rec r -> [b]


instance Forall (R '[]) c where
  rinit _ = empty
  erase _ _ = []
  eraseZip _ _ _ = []

instance (KnownSymbol l, Forall (R t) c, c a) => Forall (R (l :-> a ': t)) c where
  rinit f = unsafeInjectFront l a (initnxt f) where
    l = Label :: Label l
    a = (f :: a)
    initnxt = rinit :: (forall a. c a => a) -> Rec (R t)
  erase ::  forall b. (forall a. c a => a -> b) -> Rec (R (l :-> a ': t)) -> [b]
  erase f r = f (r .! l) : erasenxt f (r .- l) where
    l = Label :: Label l
    erasenxt = erase :: (forall a. c a => a ->  b) -> Rec (R t) -> [b]
  eraseZip ::  forall b. (forall a. c a => a -> a ->  b) -> Rec (R ((l :-> a) ': t)) ->  Rec (R ((l :-> a) ': t)) -> [b]
  eraseZip f x y = f (x .! l) (y .! l) : erasenxt f (x .- l) (y .- l) where
    l = Label :: Label l
    erasenxt = eraseZip :: (forall a. c a => a -> a -> b) -> Rec (R t) -> Rec (R t) -> [b]
  
-- some standard type classes

instance (Forall r Show) => Show (Rec r) where
  show r = "{ " ++ meat ++ " }"
    where meat = intercalate ", " binds
          binds = zipWith (\x y -> x ++ "=" ++ y) ls vs
          ls = getLabels r
          vs = toStv show r
          -- higher order polymorphism... need type
          toStv = erase ::  (forall a. Show a => a -> String) -> Rec r -> [String]

instance (Forall r Eq) => Eq (Rec r) where
  r == r' = and $ eqt (==) r r'
      where -- higher order polymorphism... need type
            eqt = eraseZip ::  (forall a. Eq a => a -> a -> Bool) -> Rec r -> Rec r -> [Bool]


instance (Eq (Rec r), Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eqt compare m m'
      where -- higher order polymorphism... need type
            eqt = eraseZip ::  (forall a. Ord a => a -> a -> Ordering) -> Rec r -> Rec r -> [Ordering]
            cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l


instance (Forall r Bounded) => Bounded (Rec r) where
  minBound = hinitv minBound
       where hinitv = rinit :: (forall a. Bounded a => a) -> Rec r
  maxBound = hinitv maxBound
       where hinitv = rinit :: (forall a. Bounded a => a) -> Rec r

-- | Constrained record existential zipping

class Apply p a b where 
  type Res p a b 
  ap :: Proxy p -> a -> b -> Res p a b

                            
class CRZip p (l :: Row *) (r :: Row *) (z :: Row *) | p l r -> z where
  crZip :: Rec l -> Rec r -> Rec z

instance CRZip p (R '[]) (R '[]) (R '[]) where
  crZip _ _ = empty

instance (KnownSymbol l, Apply p x y, z~Res p x y, CRZip p (R tl) (R tr) (R tz)) => CRZip p (R (l :-> x ': tl)) (R (l :-> y ': tr)) (R (l :-> z ': tz)) where
  crZip x y = unsafeInjectFront l i (cy (x .- l) (y .- l)) 
    where
          cy ::  Rec (R tl) -> Rec (R tr) -> Rec (R tz)
          cy = crZip
          i = (ap :: x -> y -> z) (x .! l) (y .! l) :: z
          l = Label :: Label l

data MBind m
instance Monad m => Apply (MBind m) (m a) (a -> m b) where type Res (MBind m) (m a) (a -> m b) = m b
{-
monadBindZip :: forall m l r z .(Monad m ,CRZip (MBind m) l r z) => Rec l -> Rec r -> Rec z
monadBindZip = cr ((>>=) :: forall x y. forall a b. (x~m a, y~(a -> m b), Apply (MBind m) x y) => x -> y -> Res (MBind m) x y) 
  where cr = crZip ::  (forall x y. forall a b.  (x~m a, y~(a -> m b), Apply (MBind m) x y) => x -> y -> Res (MBind m) x y) -> Rec l -> Rec r -> Rec z
  -}       




