{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Dictionaries
--
-- This module exports various dictionaries that help the type-checker when
-- dealing with row-types.
--
-- For the various axioms, type variables are consistently in the following order:
--
--  * Any types that do not belong later.
--
--  * Labels
--
--  * Row-types
--
--      * If applicable, the type in the row-type at the given label goes after
--      each row-type
--
--  * Constraints
-----------------------------------------------------------------------------


module Data.Row.Dictionaries
  ( -- * Axioms
    uniqueMap, uniqueAp, uniqueApSingle, uniqueZip
  , extendHas, mapHas, apHas, apSingleHas
  , mapExtendSwap, apExtendSwap, apSingleExtendSwap, zipExtendSwap
  , mapMinJoin, apSingleMinJoin
  , FreeForall
  , FreeBiForall
  , freeForall
  , mapForall
  , apSingleForall
  , subsetJoin, subsetJoin', subsetRestrict, subsetTrans
  , mapDifference, apSingleDifference
  , forall, inst, unForall, unForallX
  -- ** Helper Types
  , IsA(..)
  , As(..)
  , ActsOn(..)
  , As'(..)
  -- * Re-exports
  , Dict(..), (:-)(..), HasDict(..), (\\), withDict
  , Unconstrained, Unconstrained1, Unconstrained2

  )
where

import Data.Constraint
import Data.Functor.Const
import Data.Proxy
import qualified Unsafe.Coerce as UNSAFE
import GHC.TypeLits

import Data.Row.Internal
import Data.Kind



-- | This data type is used to for its ability to existentially bind a type
-- variable.  Particularly, it says that for the type 'a', there exists a 't'
-- such that @a ~ f t@ and @c t@ holds.
data As c f a where
  As :: forall  c f (a :: *) t. (a ~ f t, c t) => As c f a -- ghc needs the kind annotation on a for mapForallX to typecheck

-- | A class to capture the idea of 'As' so that it can be partially applied in
-- a context.
class IsA c f a where
  as :: As c f a

instance c a => IsA c f (f a) where
  as = As

-- | Like 'As', but here we know the underlying value is some 'f' applied to the
-- given type 'a'.
data As' c t a where
  As' :: forall c f a t. (a ~ f t, c f) => As' c t a

-- | A class to capture the idea of 'As'' so that it can be partially applied in
-- a context.
class ActsOn c t a where
  actsOn :: As' c t a

instance c f => ActsOn c t (f t) where
  actsOn = As'

-- | One half of the isomorphism between the type classes @ForallX r (ForallC r c)@ and @Forall r c@
unForallX :: forall k (r :: Row k) (c :: k -> Constraint). ForallX r (ForallC r c) :- Forall r c 
unForallX = Sub Dict 

-- | The other half of the isomorphism between the type classes @ForallX r (ForallC r c)@ and @Forall r c@
unForall :: forall k (r :: Row k) (c :: k -> Constraint). Forall r c :- ForallX r (ForallC r c) 
unForall = Sub Dict 

-- | An internal type used by the 'metamorphX' in 'mapForallX'.
newtype MapForallX c f p r  = MapForallX {unMapForallX :: Dict (ForallX (Map f r) (ForallC (Map f p) (IsA c f))) }

-- | An internal type used by the 'metamorphX' in 'apSingleForallX'.
--   (the last type parameter is phantom)
newtype ApSingleForallX c a (fs :: Row (k -> k')) (fs' :: Row (k -> k')) = ApSingleForallX
  { unApSingleForallX :: Dict (ForallX  (ApSingle fs' a) (ForallC (ApSingle fs a) (ActsOn c a))) }

-- | Internal function used to implement @mapForall@
mapForallX :: forall k (f :: k -> Type) (ρ :: Row k) (c :: k -> Constraint)
            . ForallX ρ (ForallC ρ c) 
           :- ForallX (Map f ρ) (ForallC (Map f ρ) (IsA c f))
mapForallX = Sub $ unMapForallX $ metamorphX @_ @ρ @(ForallC ρ c) @Const @Proxy @(MapForallX c f ρ) @Proxy Proxy empty uncons cons  Proxy
  where empty _ = MapForallX Dict
        uncons _ _ = Const Proxy
        cons :: forall l t r. (KnownSymbol l, ForallC ρ c l t, FrontExtends l t r, AllUniqueLabels (Extend l t r))
             => Label l 
             -> Const (MapForallX c f ρ r) (Proxy t)
             -> MapForallX c f ρ (Extend l t r)
        cons _ (Const (MapForallX Dict)) = case frontExtendsDict @l @t @r of
          FrontExtendsDict Dict -> MapForallX Dict 
            \\ mapHas @f @l @t @ρ
            \\ mapExtendSwap @f @l @t @r 
            \\ uniqueMap @f @(Extend l t r)

-- | This allows us to derive a @Forall (Map f r) ..@ from a @Forall r ..@.
-- forall f p c. ForallX p (ForallC p c) :- ForallX (Map f p) (ForallC p (IsA c f))
mapForall :: forall f ρ c. Forall ρ c :- Forall (Map f ρ) (IsA c f)
mapForall = unForallX @_ @(Map f ρ) @(IsA c f) 
    `trans` mapForallX @_ @f @ρ @c 
    `trans` unForall @_ @ρ @c   

-- | Internal function used to implement @apSingleForall@
apSingleForallX :: forall k1 k2 (a :: k1) (fs :: Row (k1 -> k2)) (c :: (k1 -> k2) -> Constraint)
                 . ForallX fs (ForallC fs c) 
                :- ForallX (ApSingle fs a) (ForallC (ApSingle fs a) (ActsOn c a))
apSingleForallX = unmapDict (\d -> unApSingleForallX (go @c @a @fs) \\ d) -- using unmapDict vs Sub (...) saves us an unsafeCoerce in the empty case
  where                                                                   
    go :: forall (c :: (k1 -> k2) -> Constraint) (a :: k1) (fs :: Row (k1 -> k2))
        . ForallX fs (ForallC fs c) 
       => ApSingleForallX c a fs fs 
    go = metamorphX @_ @fs @(ForallC fs c) @Const @Proxy @(ApSingleForallX c a fs) @Proxy Proxy empty uncons cons Proxy
      where 
        empty _ = ApSingleForallX Dict 
        
        uncons _ _ = Const Proxy

        cons :: forall (ℓ :: Symbol) (τ :: k1 -> k2) (ρ :: Row (k1 -> k2)).
          ( KnownSymbol ℓ
          , ForallC fs c ℓ τ
          , FrontExtends ℓ τ ρ
          , AllUniqueLabels (Extend ℓ τ ρ)) 
          => Label ℓ
          -> Const (ApSingleForallX c a fs ρ) (Proxy τ)
          -> ApSingleForallX c a fs (Extend ℓ τ ρ)
        cons _ (Const (ApSingleForallX Dict)) = case frontExtendsDict @ℓ @τ @ρ of
          FrontExtendsDict Dict -> ApSingleForallX Dict
            \\ apSingleHas @a @ℓ @τ @fs
            \\ apSingleExtendSwap @a @ℓ @τ @ρ
            \\ uniqueApSingle @a @(Extend ℓ τ ρ) 

-- | This allows us to derive a @Forall (ApSingle f r) ..@ from a @Forall f ..@.
apSingleForall :: forall a fs c. Forall fs c :- Forall (ApSingle fs a) (ActsOn c a)
apSingleForall = unForallX @_ @(ApSingle fs a) @(ActsOn c a) 
         `trans` apSingleForallX @_ @_ @a @fs @c 
         `trans` unForall @_ @fs @c 

-- | Allow any 'Forall' over a row-type, be usable for 'Unconstrained1'.
freeForall :: forall r c. Forall r c :- Forall r Unconstrained1
freeForall = Sub $ UNSAFE.unsafeCoerce @(Dict (Forall r c)) Dict

-- | `FreeForall` can be used when a `Forall` constraint is necessary but there
-- is no particular constraint we care about.
type FreeForall r = Forall r Unconstrained1

-- | `FreeForall` can be used when a `BiForall` constraint is necessary but
-- there is no particular constraint we care about.
type FreeBiForall r1 r2 = BiForall r1 r2 Unconstrained2

-- | If we know that 'r' has been extended with @l .== t@, then we know that this
-- extension at the label 'l' must be 't'.
extendHas :: forall l t r. Dict (Extend l t r .! l ≈ t)
extendHas = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | This allows us to derive @Map f r .! l ≈ f t@ from @r .! l ≈ t@
mapHas :: forall f l t r. (r .! l ≈ t) :- (Map f r .! l ≈ f t, Map f r .- l ≈ Map f (r .- l))
mapHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(Unconstrained, Unconstrained)

-- | This allows us to derive @Ap ϕ ρ .! l ≈ f t@ from @ϕ .! l ≈ f@ and @ρ .! l ≈ t@
apHas :: forall l f ϕ t ρ. (ϕ .! l ≈ f, ρ .! l ≈ t) :- (Ap ϕ ρ .! l ≈ f t, Ap ϕ ρ .- l ≈ Ap (ϕ .- l) (ρ .- l))
apHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(Unconstrained, Unconstrained)

-- | This allows us to derive @ApSingle r x .! l ≈ f x@ from @r .! l ≈ f@
apSingleHas :: forall x l f r. (r .! l ≈ f) :- (ApSingle r x .! l ≈ f x, ApSingle r x .- l ≈ ApSingle (r .- l) x)
apSingleHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(Unconstrained, Unconstrained)

-- | Proof that the 'Map' type family preserves labels and their ordering.
mapExtendSwap :: forall f ℓ τ r. Dict (Extend ℓ (f τ) (Map f r) ≈ Map f (Extend ℓ τ r))
mapExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'Ap' type family preserves labels and their ordering.
apExtendSwap :: forall ℓ f fs τ r. Dict (Extend ℓ (f τ) (Ap fs r) ≈ Ap (Extend ℓ f fs) (Extend ℓ τ r))
apExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'ApSingle' type family preserves labels and their ordering.
apSingleExtendSwap :: forall τ ℓ f r. Dict (Extend ℓ (f τ) (ApSingle r τ) ≈ ApSingle (Extend ℓ f r) τ)
apSingleExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'Ap' type family preserves labels and their ordering.
zipExtendSwap :: forall ℓ τ1 r1 τ2 r2. Dict (Extend ℓ (τ1, τ2) (Zip r1 r2) ≈ Zip (Extend ℓ τ1 r1) (Extend ℓ τ2 r2))
zipExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Map preserves uniqueness of labels.
uniqueMap :: forall f r. Dict (AllUniqueLabels (Map f r) ≈ AllUniqueLabels r)
uniqueMap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Ap preserves uniqueness of labels.
uniqueAp :: forall fs r. Dict (AllUniqueLabels (Ap fs r) ≈ AllUniqueLabels r)
uniqueAp = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | ApSingle preserves uniqueness of labels.
uniqueApSingle :: forall x r. Dict (AllUniqueLabels (ApSingle r x) ≈ AllUniqueLabels r)
uniqueApSingle = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Zip preserves uniqueness of labels.
uniqueZip :: forall r1 r2. Dict (AllUniqueLabels (Zip r1 r2) ≈ (AllUniqueLabels r1, AllUniqueLabels r2))
uniqueZip = UNSAFE.unsafeCoerce $ Dict @(Unconstrained, Unconstrained)

-- | Map distributes over MinJoin
mapMinJoin :: forall f r r'. Dict (Map f r .\/ Map f r' ≈ Map f (r .\/ r'))
mapMinJoin = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | ApSingle distributes over MinJoin
apSingleMinJoin :: forall r r' x. Dict (ApSingle r x .\/ ApSingle r' x ≈ ApSingle (r .\/ r') x)
apSingleMinJoin = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Two rows are subsets of a third if and only if their disjoint union is a
-- subset of that third.
subsetJoin :: forall r1 r2 s. Dict ((Subset r1 s, Subset r2 s) ≈ (Subset (r1 .+ r2) s))
subsetJoin = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | If two rows are each subsets of a third, their join is a subset of the third
subsetJoin' :: forall r1 r2 s. Dict ((Subset r1 s, Subset r2 s) ≈ (Subset (r1 .// r2) s))
subsetJoin' = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | If a row is a subset of another, then its restriction is also a subset of the other
subsetRestrict :: forall r s l. (Subset r s) :- (Subset (r .- l) s)
subsetRestrict = Sub $ UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Subset is transitive
subsetTrans :: forall r1 r2 r3. (Subset r1 r2, Subset r2 r3) :- (Subset r1 r3)
subsetTrans = Sub $ UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Map distributes over Difference
mapDifference :: forall f r r'. Dict (Map f r .\\ Map f r' ≈ Map f (r .\\ r'))
mapDifference = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | ApSingle distributes over Difference
apSingleDifference :: forall r r' x. Dict (ApSingle r x .\\ ApSingle r' x ≈ ApSingle (r .\\ r') x)
apSingleDifference = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- differenceForall :: forall r r' c. Forall r c :- Forall (r .\\ r') c

-- | If every element of a row satisfies some constraint, and a type is an element of that row 
--   (at some known label), then we know the type satisfies the constraint 
inst :: forall l c r t. (Forall r c, HasType l t r, KnownSymbol l) => Dict (c t)
inst = mapDict (forall @r @c @l @t) Dict   
