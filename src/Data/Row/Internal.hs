{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures#-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, QuantifiedConstraints #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Internal
--
-- This module implements the internals of open records and variants.
--
-----------------------------------------------------------------------------


module Data.Row.Internal
{-  (
  -- * Rows
    Row(..)
  , Label(..)
  , KnownSymbol
  , LT(..)
  , Empty
  , HideType(..)
  -- * Row Operations
  , Extend, Modify, Rename
  , type (.==), type (.!), type (.-), type (.\\)
  -- $merges
  , type (.+), type (.\/), type (.//)
  -- * Row Constraints
  , Lacks, type (.\), HasType
  , Forall(..)
  , ForallX(..)
  , ForallC
  , forall
  , BiForall(..)
  , BiForallX(..)
  , BiForallC
  , biForall
  , BiConstraint
  , Top
  , Top1
  , Top2
  , FrontExtends(..)
  , FrontExtendsDict(..)
  , WellBehaved, AllUniqueLabels
  , Ap, ApSingle, Zip, Map, Subset, Disjoint
  -- * Helper functions
  , Labels, labels, labels'
  , show'
  , toKey
  , type (≈)
  ) -}
where

import Data.Bifunctor (Bifunctor(..))
import Data.Constraint hiding (withDict)
import Data.Functor.Const
import Data.Kind
import Data.Proxy
import Data.String (IsString (fromString))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Type.Equality (type (==),type  (:~:) (Refl))

import GHC.OverloadedLabels
import GHC.TypeLits
import qualified GHC.TypeLits as TL
import GHC.Show
import Data.Singletons
import GHC.TypeLits.Singletons
import Data.Singletons.Decide
import GHC.Magic.Dict

-- NOTE: Remove this once singletons-base is updated for GHC 9.4

singLabel :: forall (l :: Symbol). Sing l -> Label l
singLabel _ = Label @l

{--------------------------------------------------------------------
  Rows
--------------------------------------------------------------------}
-- | The kind of rows. This type is only used as a datakind. A row is a typelevel entity telling us
--   which symbols are associated with which types.
newtype Row a = R [LT a]
  -- ^ A row is a list of symbol-to-type pairs that should always be sorted
  -- lexically by the symbol.
  -- The constructor is exported here (because this is an internal module) but
  -- should not be exported elsewhere.

-- | The kind of elements of rows.  Each element is a label and its associated type.
data LT a = Symbol :-> a

-- | A label
data Label (s :: Symbol) = Label
  deriving (Eq)

instance KnownSymbol s => Show (Label s) where
  show = symbolVal

instance x ≈ y => IsLabel x (Label y) where
#if __GLASGOW_HASKELL__ >= 802
  fromLabel = Label
#else
  fromLabel _ = Label
#endif

-- | A helper function for showing labels
show' :: (IsString s, Show a) => a -> s
show' = fromString . show

-- | A helper function to turn a Label directly into 'Text'.
toKey :: forall s. KnownSymbol s => Label s -> Text
toKey = Text.pack . symbolVal

-- | Type level version of 'empty'
type Empty = R '[]

-- | Elements stored in a Row type are usually hidden.
data HideType where
  HideType :: a -> HideType



{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

infixl 4 .\ {- This comment needed to appease CPP -}
-- | Does the row lack (i.e. it does not have) the specified label?
type family (r :: Row k) .\ (l :: Symbol) :: Constraint where
  R '[] .\ l = Top
  R r   .\ l = LacksR l r r

-- | Type level Row extension
type family Extend (l :: Symbol) (a :: k) (r :: Row k) :: Row k where
  Extend l a (R '[]) = R (l :-> a ': '[])
  Extend l a (R x)   = R (Inject (l :-> a) x)

-- | Type level Row modification
type family Modify (l :: Symbol) (a :: k) (r :: Row k) :: Row k where
  Modify l a (R r') = R (ModifyR l a r')

-- | Type level row renaming
type family Rename (l :: Symbol) (l' :: Symbol) (r :: Row k) :: Row k where
  Rename l l' r = Extend  l' (r .! l) (r .- l)

infixl 5 .!
-- | Type level label fetching
type family (r :: Row k) .! (t :: Symbol) :: k where
  R r .! l = Get l r

infixl 6 .-
-- | Type level Row element removal
type family (r :: Row k) .- (s :: Symbol) :: Row k where
  R r .- l = R (Remove l r)

infixl 6 .\\ {- This comment needed to appease CPP -}
-- | Type level Row difference.  That is, @l '.\\' r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row k) .\\ (r :: Row k) :: Row k where
  R l .\\ R r = R (Diff l r)

-- $merges
-- == Various row-type merges
-- The difference between '.+' (read "append"), '.\/' (read "min-join"), and
-- '.\\' (read "const-union") comes down to how duplicates are handled.
-- In '.+', the two given row-types must be entirely unique.  Even the same
-- entry in both row-types is forbidden.  In '.\/', this final restriction is
-- relaxed, allowing two row-types that have no conflicts to be merged in the
-- logical way.  The '.\\' operator is the most liberal, allowing any two row-types
-- to be merged together, and whenever there is a conflict, favoring the left argument.
--
-- As examples of use:
--
-- - '.+' is used when appending two records, assuring that those two records are
--   entirely disjoint.
--
-- - '.\/' is used when diversifying a variant, allowing some extension to the
--   row-type so long as no original types have changed.
--
-- - './/' is used when doing record overwrite, allowing data in a record to
-- totally overwrite what was previously there.

infixl 6 .+
-- | Type level Row append
type family (l :: Row k) .+ (r :: Row k) :: Row k where
  x .+ R '[] = x
  R '[] .+ y = y
  x .+ R '[l :-> a] = Extend l a x
  R '[l :-> a] .+ y = Extend l a y
  R l .+ R r = R (Merge l r)

infixl 6 .\/
-- | The minimum join of the two rows.
type family (l :: Row k) .\/ (r :: Row k) where
  x .\/ R '[] = x
  R '[] .\/ y = y
  R l .\/ R r = R (MinJoinR l r)

infixl 6 .//
-- | The overwriting union, where the left row overwrites the types of the right
-- row where the labels overlap.
type family (l :: Row k) .// (r :: Row k) where
  x .// R '[] = x
  R '[] .// y = y
  R l .// R r = R (ConstUnionR l r)


{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | Alias for '.\'. It is a class rather than an alias, so that
-- it can be partially applied.
class Lacks (l :: Symbol) (r :: Row *)
instance (r .\ l) => Lacks l r


-- | Alias for @(r .! l) ≈ a@. It is a class rather than an alias, so that
-- it can be partially applied.
class (r .! l ≈ a) => HasType r l a
instance (r .! l ≈ a) => HasType r l a

-- | A type level way to create a singleton Row.
infix 7 .==
type (l :: Symbol) .== (a :: k) = Extend l a Empty


{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

-- Type synonyms to improve readability in complex row operations

type MetamorphX :: forall k. Row k -> (Symbol -> k -> Constraint) -> Type
type MetamorphX (r :: Row k) (c :: Symbol -> k -> Constraint)
      = forall (p :: Type -> Type -> Type)
                       (f :: Row k -> Type)
                       (g :: Row k -> Type)
                       (h :: k -> Type)
             . Bifunctor p
            => Proxies h p
            -> GoEmpty f g
            -> GoUncons c f p h
            -> GoCons c p h g
            -> f r
            -> g r

type Proxies h p = Proxy (Proxy h, Proxy p)

type GoEmpty f g = (f Empty -> g Empty)

type GoUncons c f p h = (forall l t r'
                . ( KnownSymbol l
                , c l t
                , ForallX r' c
                , HasType r' l t
                ) => Sing l
                  -> f r'
                  -> p (f (r' .- l)) (h t))

type GoCons c p h g = (forall l t r'
                  . (KnownSymbol l
                  , c l t
                  , ForallX r' c
                  , FrontExtends l t r'
                  , AllUniqueLabels (Extend l t r')
                  ) => Sing l
                    -> p (g r') (h t)
                    -> g (Extend l t r'))

-- | A dictionary of information that proves that extending a row-type @r@ with
-- a label @l@ will necessarily put it to the front of the underlying row-type
-- list.  This is quite internal and should not generally be necessary.
data FrontExtendsDict l t r = forall ρ. FrontExtendsDict (Dict (r ~ R ρ, R (l :-> t ': ρ) ≈ Extend l t (R ρ), AllUniqueLabelsR (l :-> t ': ρ)))

-- | A class wrapper for 'FrontExtendsDict'.
class FrontExtends l t r where
  frontExtendsDict :: FrontExtendsDict l t r

instance (r ~ R ρ, R (l :-> t ': ρ) ≈ Extend l t (R ρ), AllUniqueLabelsR (l :-> t ': ρ)) => FrontExtends l t r where
  frontExtendsDict = FrontExtendsDict Dict

-- | Relational quantification over the labels and elements of a row
class ForallX (r :: Row k) (c :: Symbol -> k -> Constraint)
  where
  metamorphX :: MetamorphX r c

instance ForallX (R '[]) c  where
  {-# INLINE metamorphX #-}
  metamorphX _ empty _ _ = empty

instance (KnownSymbol l, c l t, ForallX ('R ρ) c, FrontExtends l t ('R ρ), AllUniqueLabels (Extend l t ('R ρ))) => ForallX ('R (l :-> t ': ρ) :: Row k) c where
  {-# INLINE metamorphX #-}
  metamorphX h empty uncons cons = case frontExtendsDict @l @t @('R ρ) of
    FrontExtendsDict Dict ->
      cons (sing @l) . first (metamorphX @_ @('R ρ) @c h empty uncons cons) . uncons (sing @l)

-- | A constraint used to help implement @Forall@.
class (HasType r l t, c t, KnownSymbol l) => ForallC r c l t
instance (HasType r l t, c t, KnownSymbol l) => ForallC r c l t

type Metamorph :: Row k -> (k -> Constraint) -> Type
type Metamorph r c = MetamorphX r (ForallC r c)

-- | Any structure over a row in which every element is similarly constrained can
-- be metamorphized into another structure over the same row.
class ForallX r (ForallC r c) => Forall (r :: Row k) (c :: k -> Constraint) where
  metamorph :: Metamorph r c
  metamorph h empty uncons cons = metamorphX @_ @r @(ForallC r c) @_ @_ @_ h empty uncons cons

instance ForallX r (ForallC r c) => Forall (r :: Row k) (c :: k -> Constraint)

-- | Type synonyms to improve the readability/writeability of BiForall/X

type BiMetamorphX (r1 :: Row k1) (r2 :: Row k2) c
  = forall (b :: Type -> Type -> Type)
           (f :: Row k1 -> Row k2 -> Type)
           (g :: Row k1 -> Row k2 -> Type)
           (h :: k1 -> k2 -> Type)
    . Bifunctor b
   => Proxies h b
   -> GoEmpty2 f g
   -> GoUncons2 c f b h
   -> GoCons2 c b h g
   -> f r1 r2
   -> g r1 r2

type GoEmpty2 :: forall k1 k2. (Row k1 -> Row k2 -> Type) -> (Row k1 -> Row k2 -> Type) -> Type
type GoEmpty2 (f :: Row k1 -> Row k2 -> Type)  (g :: Row k1 -> Row k2 -> Type) = f Empty Empty -> g Empty Empty

type GoUncons2 c f p h
  = forall l t1 t2 r1 r2
    . ( KnownSymbol l
      , BiForallX r1 r2 c
      , c l t1 t2
      , HasType r1 l t1
      , HasType r2 l t2
      ) => Sing l
        -> f r1 r2
        -> p (f (r1 .- l) (r2 .- l)) (h t1 t2)

type GoCons2 c p h g
  = forall l t1 t2 r1 r2
  . ( KnownSymbol l
    , c l t1 t2
    , FrontExtends l t1 r1
    , FrontExtends l t2 r2
    , BiForallX r1 r2 c
    , AllUniqueLabels (Extend l t1 r1)
    , AllUniqueLabels (Extend l t2 r2)
    )  => Sing l
       -> p (g r1 r2) (h t1 t2)
       -> g (Extend l t1 r1) (Extend l t2 r2)

class BiForallX (r1 :: Row k1) (r2 :: Row k2) (c :: Symbol -> k1 -> k2 -> Constraint) where
  biMetamorphX :: BiMetamorphX r1 r2 c

instance BiForallX (R '[]) (R '[]) c1 where
  {-# INLINE biMetamorphX #-}
  biMetamorphX _ empty _ _ = empty

instance ( KnownSymbol l
         , c l t1 t2
         , BiForallX ('R r1) ('R r2) c
         , FrontExtends l t1 ('R r1)
         , FrontExtends l t2 ('R r2)
         , AllUniqueLabels (Extend l t1 ('R r1))
         , AllUniqueLabels (Extend l t2 ('R r2)))
      => BiForallX ('R (l :-> t1 ': r1)) ('R (l :-> t2 ': r2)) c where
  {-# INLINE biMetamorphX #-}
  biMetamorphX h empty uncons cons = case (frontExtendsDict @l @t1 @('R r1), frontExtendsDict @l @t2 @('R r2)) of
    (FrontExtendsDict Dict, FrontExtendsDict Dict) ->
      cons (sing @l) . first (biMetamorphX @_ @_ @('R r1) @('R r2) @c h empty uncons cons) . uncons (sing @l)

-- | A helper class/constraint for BiForall
class (HasType r1 l t1, HasType r2 l t2, c t1 t2) => BiForallC r1 r2 c l t1 t2
instance (HasType r1 l t1, HasType r2 l t2, c t1 t2) => BiForallC r1 r2 c l t1 t2

type BiMetamorph r1 r2 c = BiMetamorphX r1 r2 (BiForallC r1 r2 c)

-- | Any structure over two rows in which the elements of each row satisfy some
--   constraints can be metamorphized into another structure over both of the
--   rows.
class BiForallX r1 r2 (BiForallC r1 r2 c) => BiForall (r1 :: Row k1) (r2 :: Row k2) (c :: k1 -> k2 -> Constraint) where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  biMetamorph :: BiMetamorph r1 r2 c
  biMetamorph h empty uncons cons = biMetamorphX @_ @_ @r1 @r2 @(BiForallC r1 r2 c) @_ @_ @_ @_ h empty uncons cons

instance BiForallX r1 r2 (BiForallC r1 r2 c) => BiForall (r1 :: Row k1) (r2 :: Row k2) (c :: k1 -> k2 -> Constraint) 

-- | A null constraint
class Top where
  top :: ()
  top = ()
instance Top

-- | A null constraint of one argument
class Top1 a where
  top1 :: ()
  top1 = ()
instance Top1 a

withTop1 :: forall k (a :: k) r. (forall (x :: k). Top1 x => r) -> r
withTop1 f = withDict @() @(Top1 a) () (f @a)

-- | A null constraint of two arguments
class Top2 a b where
  top2 :: ()
  top2 = ()
instance Top2 a b

withTop2 :: forall k1 k2 (a :: k1) (b :: k2) r. (forall (x :: k1) (y :: k2). Top2 x y => r) -> r
withTop2 f = withDict @() @(Top2 a b) () (f @a @b)

-- | A pair of constraints
class (c1 x, c2 y) => BiConstraint c1 c2 x y
instance (c1 x, c2 y) => BiConstraint c1 c2 x y

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Return a list of the labels in a row type.
labels :: forall r c s. (IsString s, Forall r c) => [s]
labels = getConst $ metamorph @_ @r @c @Const @(Const ()) @(Const [s]) @Proxy Proxy (const $ Const []) doUncons doCons (Const ())
  where doUncons _ _ = Const $ Const ()
        doCons l (Const (Const c)) = Const $ show' l : c

-- | Return a list of the labels in a row type and is specialized to the 'Top1' constraint.
labels' :: forall r s. (IsString s, Forall r Top1) => [s]
labels' = labels @r @Top1


{--------------------------------------------------------------------
  Convenient type families and classes
--------------------------------------------------------------------}

-- | A convenient way to provide common, easy constraints
type WellBehaved r = (Forall r Top1, AllUniqueLabels r)

-- | Are all of the labels in this Row unique?
type family AllUniqueLabels (r :: Row k) :: Constraint where
  AllUniqueLabels (R r) = AllUniqueLabelsR r

type family AllUniqueLabelsR (r :: [LT k]) :: Constraint where
  AllUniqueLabelsR '[] = Top
  AllUniqueLabelsR '[l :-> a] = Top
  AllUniqueLabelsR (l :-> a ': l :-> b ': _) = TypeError
    (TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not unique."
    :$$: TL.Text "It is assigned to both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b)
  AllUniqueLabelsR (l :-> a ': l' :-> b ': r) = AllUniqueLabelsR (l' :-> b ': r)

-- | Is the first row a subset of the second?
-- Or, does the second row contain every binding that the first one does?
type family Subset (r1 :: Row k) (r2 :: Row k) :: Constraint where
  Subset ('R '[]) r = Top
  Subset ('R (l ':-> a ': x)) r = (r .! l ≈ a, Subset ('R x) r)

-- | A type synonym for disjointness.
type Disjoint l r = ( WellBehaved l
                    , WellBehaved r
                    , Subset l (l .+ r)
                    , Subset r (l .+ r)
                    , l .+ r .\\ l ≈ r
                    , l .+ r .\\ r ≈ l)

-- | Map a type level function over a Row.
type family Map (f :: a -> b) (r :: Row a) :: Row b where
  Map f (R r) = R (MapR f r)

type family MapR (f :: a -> b) (r :: [LT a]) :: [LT b] where
  MapR f '[] = '[]
  MapR f (l :-> v ': t) = l :-> f v ': MapR f t

-- | Take two rows with the same labels, and apply the type operator from the
-- first row to the type of the second.
type family Ap (fs :: Row (a -> b)) (r :: Row a) :: Row b where
  Ap (R fs) (R r) = R (ApR fs r)

type family ApR (fs :: [LT (a -> b)]) (r :: [LT a]) :: [LT b] where
  ApR '[] '[] = '[]
  ApR (l :-> f ': tf) (l :-> v ': tv) = l :-> f v ': ApR tf tv
  ApR _ _ = TypeError (TL.Text "Row types with different label sets cannot be App'd together.")

-- | Take a row of type operators and apply each to the second argument.
type family ApSingle (fs :: Row (a -> b)) (x :: a) :: Row b where
  ApSingle (R fs) x = R (ApSingleR fs x)

type family ApSingleR (fs :: [LT (a -> b)]) (x :: a) :: [LT b] where
  ApSingleR '[] _ = '[]
  ApSingleR (l ':-> f ': fs) x = l ':-> f x ': ApSingleR fs x

-- | Zips two rows together to create a Row of the pairs.
--   The two rows must have the same set of labels.
type family Zip (r1 :: Row *) (r2 :: Row *) where
  Zip (R r1) (R r2) = R (ZipR r1 r2)

type family ZipR (r1 :: [LT *]) (r2 :: [LT *]) where
  ZipR '[] '[] = '[]
  ZipR (l :-> t1 ': r1) (l :-> t2 ': r2) =
    l :-> (t1, t2) ': ZipR r1 r2
  ZipR (l :-> t1 ': r1) _ = TypeError (TL.Text "Row types with different label sets cannot be zipped"
                                  :$$: TL.Text "For one, the label " :<>: ShowType l :<>: TL.Text " is not in both lists.")
  ZipR '[] (l :-> t ': r) = TypeError (TL.Text "Row types with different label sets cannot be zipped"
                                  :$$: TL.Text "For one, the label " :<>: ShowType l :<>: TL.Text " is not in both lists.")

type family Inject (l :: LT k) (r :: [LT k]) where
  Inject (l :-> t) '[] = (l :-> t ': '[])
  Inject (l :-> t) (l :-> t' ': x) = TypeError (TL.Text "Cannot inject a label into a row type that already has that label"
                                  :$$: TL.Text "The label " :<>: ShowType l :<>: TL.Text " was already assigned the type "
                                  :<>: ShowType t' :<>: TL.Text " and is now trying to be assigned the type "
                                  :<>: ShowType t :<>: TL.Text ".")
  Inject (l :-> t) (l' :-> t' ': x) =
      Ifte (l <=.? l')
      (l :-> t   ': l' :-> t' ': x)
      (l' :-> t' ': Inject (l :-> t)  x)

-- | Type level Row modification helper
type family ModifyR (l :: Symbol) (a :: k) (ρ :: [LT k]) :: [LT k] where
  ModifyR l a (l :-> a' ': ρ) = l :-> a ': ρ
  ModifyR l a (l' :-> a' ': ρ) = l' :-> a' ': ModifyR l a ρ
  ModifyR l a '[] = TypeError (TL.Text "Tried to modify the label " :<>: ShowType l
                          :<>: TL.Text ", but it does not appear in the row-type.")

type family Ifte (c :: Bool) (t :: k) (f :: k)   where
  Ifte True  t f = t
  Ifte False t f = f

type family Get (l :: Symbol) (r :: [LT k]) where
  Get l '[] = TypeError (TL.Text "No such field: " :<>: ShowType l)
  Get l (l :-> t ': x) = t
  Get l (l' :-> t ': x) = Get l x

type family Remove (l :: Symbol) (r :: [LT k]) where
  Remove l r = RemoveT l r r

type family RemoveT (l :: Symbol) (r :: [LT k]) (r_orig :: [LT k]) where
  RemoveT l (l :-> t ': x) _ = x
  RemoveT l (l' :-> t ': x) r = l' :-> t ': RemoveT l x r
  RemoveT l '[] r = TypeError (TL.Text "Cannot remove a label that does not occur in the row type."
                          :$$: TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not in "
                          :<>: ShowRowType r)

type family LacksR (l :: Symbol) (r :: [LT k]) (r_orig :: [LT k]) :: Constraint where
  LacksR l '[] _ = Top
  LacksR l (l :-> t ': x) r = TypeError (TL.Text "The label " :<>: ShowType l
                                    :<>: TL.Text " already exists in " :<>: ShowRowType r)
  LacksR l (l' :-> _ ': x) r = Ifte (l <=.? l') Top (LacksR l x r)


type family Merge (l :: [LT k]) (r :: [LT k]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (h :-> a ': tl)   (h :-> a ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " (of type "
          :$$: ShowType a :<>: TL.Text ") has duplicate assignments.")
  Merge (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      MergeCont (CmpSymbol hl hr) hl al tl hr ar tr

type family MergeCont (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                        (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
    MergeCont 'LT hl al tl hr ar tr = (hl :-> al ': Merge tl (hr :-> ar ': tr))
    MergeCont _ hl al tl hr ar tr = (hr :-> ar ': Merge (hl :-> al ': tl) tr)

type family MinJoinR (l :: [LT k]) (r :: [LT k]) where
  MinJoinR '[] r = r
  MinJoinR l '[] = l
  MinJoinR (h :-> a ': tl)   (h :-> a ': tr) =
      (h :-> a ': MinJoinR tl tr)
  MinJoinR (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  MinJoinR (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      MinJoinRCase (CmpSymbol hl hr) hl al tl hr ar tr

type family MinJoinRCase (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                           (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
  MinJoinRCase 'LT hl al tl hr ar tr = hl :-> al ': MinJoinR tl (hr :-> ar ': tr)
  MinJoinRCase _   hl al tl hr ar tr = hr :-> ar ': MinJoinR (hl :-> al ': tl) tr

type family ConstUnionR (l :: [LT k]) (r :: [LT k]) where
  ConstUnionR '[] r = r
  ConstUnionR l '[] = l
  ConstUnionR (h :-> a ': tl)   (h :-> b ': tr) =
      (h :-> a ': ConstUnionR tl tr)
  ConstUnionR (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      ConstUnionRCase (CmpSymbol hl hr) hl al tl hr ar tr

type family ConstUnionRCase (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                           (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
  ConstUnionRCase 'LT hl al tl hr ar tr = hl :-> al ': ConstUnionR tl (hr :-> ar ': tr)
  ConstUnionRCase _   hl al tl hr ar tr = hr :-> ar ': ConstUnionR (hl :-> al ': tl) tr


-- | Returns the left list with all of the elements from the right list removed.
type family Diff (l :: [LT k]) (r :: [LT k]) where
  Diff '[] r = '[]
  Diff l '[] = l
  Diff (l ':-> al ': tl) (l ':-> al ': tr) = Diff tl tr
  Diff (hl ':-> al ': tl) (hr ':-> ar ': tr) =
    -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
    DiffCont (CmpSymbol hl hr) hl al tl hr ar tr

type family DiffCont (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                       (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
    DiffCont 'LT hl al tl hr ar tr = (hl ':-> al ': Diff tl (hr ':-> ar ': tr))
    DiffCont _ hl al tl hr ar tr = (Diff (hl ':-> al ': tl) tr)

type family ShowRowType (r :: [LT k]) :: ErrorMessage where
  ShowRowType '[] = TL.Text "Empty"
  ShowRowType '[l ':-> t] = TL.ShowType l TL.:<>: TL.Text " .== " TL.:<>: TL.ShowType t
  ShowRowType ((l ':-> t) ': r) = TL.ShowType l TL.:<>: TL.Text " .== " TL.:<>: TL.ShowType t TL.:<>: TL.Text " .+ " TL.:<>: ShowRowType r

-- | There doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)

-- | A lower fixity operator for type equality
infix 4 ≈
type a ≈ b = a ~ b

-- | Universal instantiation for Rows. If some row satisfies `Forall r c` then, 
-- if we know that `t` is an element of that row, we also know that `t` satisfies `c`. 
forall :: forall r c l t. (Forall r c, KnownSymbol l) => HasType r l t :- c t
forall = unmapDict go
  where
    go :: Dict (HasType r l t) -> Dict (c t)
    go Dict = getConst $ metamorph @_ @r @c @Either @Proxy @(Const (Dict (c t))) @(Const (Dict (c t)))
      Proxy empty doUncons doCons Proxy
      where
        empty = error "Impossible"

        doUncons :: GoUncons (ForallC r c) Proxy Either (Const (Dict (c t)))
        doUncons sl _ = withSingI sl $ case decideEquality sl (sing @l) of
          Just Refl -> Right $ Const Dict 
          Nothing -> Left Proxy

        doCons :: GoCons (ForallC r c) Either (Const (Dict (c t))) (Const (Dict (c t)))
        doCons _ (Left (Const Dict))  = Const Dict
        doCons _ (Right (Const Dict)) = Const Dict


data BiProxy :: forall k1 k2. k1 -> k2 -> Type where
  BiProxy :: BiProxy a b 

data BiConst :: forall k1 k2. Type -> k1 -> k2 -> Type where
  BiConst :: forall k1 k2 (a :: Type) (j :: k1) (k :: k2). {getBiConst :: a} -> BiConst a j k

biForall :: forall r1 r2 c l t1 t2  
          . (BiForall r1 r2 c, KnownSymbol l) 
         => (HasType r1 l t1, HasType r2 l t2) :- c t1 t2
biForall = unmapDict go 
  where 
    go :: Dict (HasType r1 l t1, HasType r2 l t2) -> Dict (c t1 t2)
    go Dict = getBiConst $ biMetamorph @_ @_ @r1 @r2 @c @Either @BiProxy @(BiConst (Dict (c t1 t2))) @(BiConst (Dict (c t1 t2)))
                Proxy empty doUncons doCons BiProxy 
      where 
        empty = error "Impossible"

        doUncons :: GoUncons2 (BiForallC r1 r2 c) BiProxy Either (BiConst (Dict (c t1 t2)))
        doUncons sl BiProxy = withSingI sl $ case decideEquality sl (sing @l) of
          Just Refl -> Right $ BiConst Dict
          Nothing   -> Left BiProxy 

        doCons :: GoCons2 (BiForallC r1 r2 c) Either (BiConst (Dict (c t1 t2))) (BiConst (Dict (c t1 t2)))
        doCons _ (Left (BiConst Dict)) = BiConst Dict 
        doCons _ (Right (BiConst Dict)) = BiConst Dict 

