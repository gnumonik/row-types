{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, QuantifiedConstraints #-}

module Data.Row.List where

import Data.Row.Internal
import Data.Constraint hiding (withDict)
import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Data.Bifunctor
import GHC.Magic.Dict
import GHC.Exts
import Data.Type.Equality

import Unsafe.Coerce

uniqueLabelsUpdate :: forall k (l :: Symbol) (a :: k) (b :: k) (rest :: [LT k])
                    .   AllUniqueLabels (R (l ':-> a ': rest))
                    :-  AllUniqueLabels (R (l ':-> b ': rest))
uniqueLabelsUpdate = unmapDict go
  where
    go :: Dict (AllUniqueLabels (R (l ':-> a ': rest))) -> Dict (AllUniqueLabels (R (l ':-> b ': rest)))
    go d@Dict = unsafeCoerce d

-- make sure this is actually safe!!! i think it is?
extendUpdate :: forall k (l :: Symbol) (a :: k) (b :: k) (r :: Row k)
              . FrontExtendsDict l a r
             -> FrontExtendsDict l b r
extendUpdate (FrontExtendsDict d@Dict) = FrontExtendsDict (unsafeCoerce d)

type Update :: Symbol -> k -> Row k -> Row k ->  Constraint
class Update l (b :: k)  (r :: Row k) (r' :: Row k) | l b r -> r' where
  updateRList :: forall
                 (c :: Symbol -> k -> Constraint)
                 (f :: k -> Type)
               . Dict (c l b)
              -> f b
              -> RowListX c f r
              -> RowListX c f r'

instance (KnownSymbol l) => Update l b (R (l ':-> a ': rest)) (R (l ':-> b ': rest)) where
  updateRList Dict fb (Cons l fa fDict@(FrontExtendsDict d@Dict) rest) = case extendUpdate @_ @l @a @b @(R rest) fDict  of
    FrontExtendsDict Dict -> Cons l fb (FrontExtendsDict Dict) rest

-- need to wrap the method body in an existential elimination
instance (KnownSymbol l, Update l b (R rest) (R rest'), FrontExtends l' a (R rest')) => Update l (b :: k) (R (l' ':-> a ': rest)) (R (l' ':-> a ': rest')) where
  updateRList = go
    where
      go :: forall (c :: Symbol -> k -> Constraint) (f :: k -> Type)
          . Dict (c l b)
         -> f b
         -> RowListX c f (R (l' ':-> a ': rest))
         -> RowListX c f (R (l' ':-> a ': rest'))
      go dx@Dict fb (Cons l fa (FrontExtendsDict dy@Dict) rest) = case frontExtendsDict @l' @a @(R rest') of
        FrontExtendsDict d@Dict -> case updateRList dx fb rest :: RowListX c f (R rest') of
          result@(Cons _ _ (FrontExtendsDict Dict) _) -> Cons l fa (FrontExtendsDict $ unsafeCoerce dy) result


data RowListX :: (Symbol -> k -> Constraint) -> (k -> Type) -> Row k -> Type where
  Nil :: forall k (c :: Symbol -> k -> Constraint) (f :: k -> Type). RowListX c f Empty

  Cons :: forall k (c :: Symbol -> k -> Constraint)
                     (f :: k -> Type)
                     (r :: Row k)
                     (l :: Symbol )
                     (a :: k)
          . ( KnownSymbol l
            , c l a
            , ForallX r c
            , FrontExtends l a r
            , AllUniqueLabels (Extend l a r)
            ) => Label l
              -> f a
              -> FrontExtendsDict l a r
              -> RowListX c f r
              -> RowListX c f (Extend l a r)

toRowListX :: forall k (r :: Row k) (f :: k -> Type) (c :: Symbol -> k -> Constraint)
             . ForallX r c
            => RowListX c Proxy r
toRowListX = metamorphX @k
                         @r
                         @c
                         @(,)
                         @Proxy
                         @(RowListX c Proxy)
                         @Proxy Proxy goEmpty goUncons goCons Proxy
  where
    goEmpty _ = Nil

    goUncons :: forall {ℓ :: Symbol}
                     {τ :: k}
                     {ρ :: Row k}
            . (KnownSymbol ℓ
            , c ℓ τ
            , HasType ℓ τ ρ)
          => Label ℓ
          -> Proxy ρ
          -> (Proxy (ρ .- ℓ), Proxy τ)
    goUncons _ _ = (Proxy,Proxy)

    goCons :: forall {ℓ :: Symbol}
                     {τ :: k}
                     {ρ :: Row k}
            . (KnownSymbol ℓ
            , c ℓ τ
            , ForallX ρ c
            , FrontExtends ℓ τ ρ
            , AllUniqueLabels (Extend ℓ τ ρ)
            ) => Label ℓ
              -> (RowListX c Proxy ρ, Proxy τ)
              -> RowListX c Proxy (Extend ℓ τ ρ)
    goCons l (cfx,Proxy) = case frontExtendsDict @ℓ @τ @ρ of
      fd@(FrontExtendsDict Dict) ->  Cons (Label @ℓ) (Proxy @τ) fd cfx

metamorphList :: forall k
                      (r :: Row k)
                      (c :: Symbol -> k -> Constraint)
                      (p :: Type -> Type -> Type)
                      (g :: Row k -> Type)
                      (f :: k -> Type)
                      (h :: k -> Type)
            . Bifunctor p
          => Proxy (Proxy h, Proxy p)
          -> (RowListX c f Empty -> g Empty)
              -- ^ The way to transform the empty element
          -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, ForallX ρ c, HasType ℓ τ ρ)
              => Label ℓ -> RowListX c f ρ -> p (RowListX c f (ρ .- ℓ)) (h τ))
              -- ^ The unfold
          -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, ForallX ρ c, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
              => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
              -- ^ The fold
          -> RowListX c f r  -- ^ The input structure
          -> g r
metamorphList proxy goEmpty goUncons goCons = \case
    Nil -> goEmpty Nil

    e@(Cons l t d rest) -> case d of
      FrontExtendsDict Dict -> goCons l . first (metamorphList proxy goEmpty goUncons goCons) . goUncons l $ e

type MetamorphX :: forall k. Row k -> (Symbol -> k -> Constraint) -> Type
type MetamorphX (r :: Row k) (c :: Symbol -> k -> Constraint)  = forall (p :: * -> * -> *)
                       (f :: Row k -> *)
                       (g :: Row k -> *)
                       (h :: k -> *)
             . Bifunctor p
            => Proxies h p
            -> GoEmpty f g
            -> GoUncons c f p h
            -> GoCons c p h g
            -> f r  -- ^ The input structure
            -> g r

type Proxies h p = Proxy (Proxy h, Proxy p)

type GoEmpty f g = (f Empty -> g Empty)

type GoUncons c f p h = (forall ℓ τ ρ
                . ( KnownSymbol ℓ
                , c ℓ τ
                , ForallX ρ c
                , HasType ℓ τ ρ
                ) => Label ℓ
                  -> f ρ
                  -> p (f (ρ .- ℓ)) (h τ))

type GoCons c p h g = (forall ℓ τ ρ
                  . (KnownSymbol ℓ
                  , c ℓ τ
                  , ForallX ρ c
                  , FrontExtends ℓ τ ρ
                  , AllUniqueLabels (Extend ℓ τ ρ)
                  ) => Label ℓ
                    -> p (g ρ) (h τ)
                    -> g (Extend ℓ τ ρ))

withMetamorphX :: forall k
                         {r :: Row k}
                         {c :: Symbol -> k -> Constraint}
                         {f :: Row k -> Type}
                         {g :: Row k -> Type}
                         {p :: Type -> Type -> Type}
                         {h :: k -> Type}
                . Bifunctor p
               => MetamorphX r c
               -> (forall {r' :: Row k}
                          {c' :: Symbol -> k -> Constraint}
                   . ForallX r' c'
                  => Proxies h p
                  -> GoEmpty f g
                  -> GoUncons c' f p h
                  -> GoCons c' p h g
                  -> f r'
                  -> g r')
               -> Proxies h p
               -> GoEmpty f g
               -> GoUncons c f p h
               -> GoCons c p h g
               -> f r
               -> g r
withMetamorphX m k
  = withDict
     @(MetamorphX r c)
     @(ForallX r c)
     m
     k
