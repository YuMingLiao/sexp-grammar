{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}


module Data.InvertibleGrammar
  ( Grammar (..)
  , Taggy (..)
  , Demoteable (..)
  , Tag (..)
  , Hinted (..)
  , HintedGrammar (..)
  , (:-) (..)
  , iso
  , osi
  , partialIso
  , partialOsi
  , push
  , pushForget
  , select
  , forward
  , backward
  , GrammarError (..)
  , Mismatch
  , expected
  , unexpected
  ) where

import Prelude hiding ((.), id)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Category
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as M
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup
#endif
import Data.InvertibleGrammar.Monad
import Data.Kind
import GHC.Exts
import Data.Text (pack)

import GHC.TypeLits (Nat, Symbol, KnownNat, KnownSymbol, natVal, symbolVal)


data h :- t = h :- t deriving (Eq, Show, Functor, Foldable, Traversable)
infixr 5 :-

instance Bifunctor (:-) where
  bimap f g (a :- b) = (f a :- g b)

instance Bifoldable (:-) where
  bifoldr f g x0 (a :- b) = a `f` (b `g` x0)

instance Bitraversable (:-) where
  bitraverse f g (a :- b) = (:-) <$> f a <*> g b


class (Typeable a, Ord (Hint a), Show (Hint a)) => Taggy a where
  type Original a
  type Hint a
  mkTag :: proxy a -> Original a -> Hint a
  mkMismatch :: proxy a -> Hint a -> Mismatch

newtype Hinted (h :: Type) (hs :: [h]) where
  Hinted :: { getHinted :: Original h } -> Hinted h hs

class Demoteable (a :: k) where
  type Demote a
  demote :: proxy a -> Demote a

instance (KnownNat n) => Demoteable (n :: Nat) where
  type Demote n = Integer
  demote = natVal

instance (KnownSymbol s) => Demoteable (s :: Symbol) where
  type Demote s = String
  demote = symbolVal

instance {-# OVERLAPPING #-} (Demoteable a) => Demoteable ('[a] :: [k]) where
  type Demote '[a] = [Demote a]
  demote _ = [demote (Proxy @a)]

instance (Demoteable a, Demoteable as, [Demote a] ~ Demote as) => Demoteable (a ': as :: [k]) where
  type Demote (a ': as) = [Demote a]
  demote _ = demote (Proxy @a) : demote (Proxy @as)

newtype Tag a = Tag Nat

instance Typeable a => Taggy (Tag (a :: Type)) where
  type Original (Tag a) = a
  type Hint (Tag a) = Int
  mkTag _ a = I# (dataToTag# a)
  mkMismatch _ = expected . pack . show

instance (KnownNat n) => Demoteable ('Tag n) where
  type Demote ('Tag n) = Int
  demote _ = fromIntegral (demote (Proxy @n))

-- foo :: Hinted (Tag (Either Int Char)) '[ 'T 0 ]
-- foo = Hinted (Left 42)

-- reifyHints :: forall t hints. (Demoteable hints) => Hinted t hints -> Demote hints
-- reifyHints _ = demote (Proxy @hints)

data Grammar p a b where
  Iso        :: (a -> b) -> (b -> a) -> Grammar p a b
  PartialIso :: (a -> b) -> (b -> Either Mismatch a) -> Grammar p a b
  Flip       :: Grammar p a b -> Grammar p b a
  (:.:)      :: Grammar p b c -> Grammar p a b -> Grammar p a c
  (:<>:)     :: Grammar p a b -> Grammar p a b -> Grammar p a b
  Traverse   :: (Traversable f) => Grammar p a b -> Grammar p (f a) (f b)
  Bitraverse :: Grammar p a b -> Grammar p c d -> Grammar p (a :- c) (b :- d)

  Select     :: (Taggy ia, Taggy ib, Original ia ~ a, Original ib ~ b) =>
                Proxy ia
             -> Proxy ib
             -> Map (Hint ia) (Grammar p (a :- t) (b :- t))
             -> Map (Hint ib) (Grammar p (a :- t) (b :- t))
             -> Grammar p (a :- t) (b :- t)

  Dive       :: Grammar p a b -> Grammar p a b
  Step       :: Grammar p a a
  Locate     :: Grammar p p p


instance Category (Grammar p) where
  id                                              = Iso id id

  Iso f g               . Iso f' g'               = Iso (f . f') (g' . g)
  PartialIso f g        . Iso f' g'               = PartialIso (f . f') (fmap g' . g)
  Iso f g               . PartialIso f' g'        = PartialIso (f . f') (g' . g)
  PartialIso f g        . PartialIso f' g'        = PartialIso (f . f') (g' <=< g)
  Flip (PartialIso f g) . Flip (PartialIso f' g') = Flip (PartialIso (f' . f) (g <=< g'))
  g                     . h                       = g :.: h

instance Semigroup (Grammar p a b) where
  (<>) = (:<>:)


-- | Make a grammar from a total isomorphism on top element of stack
iso :: (a -> b) -> (b -> a) -> Grammar p (a :- t) (b :- t)
iso f' g' = Iso f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = g' b :- t


-- | Make a grammar from a total isomorphism on top element of stack (flipped)
osi :: (b -> a) -> (a -> b) -> Grammar p (a :- t) (b :- t)
osi f' g' = Iso g f
  where
    f (a :- t) = f' a :- t
    g (b :- t) = g' b :- t


-- | Make a grammar from a partial isomorphism which can fail during backward
-- run
partialIso :: (a -> b) -> (b -> Either Mismatch a) -> Grammar p (a :- t) (b :- t)
partialIso f' g' = PartialIso f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = (:- t) <$> g' b


-- | Make a grammar from a partial isomorphism which can fail during forward run
partialOsi :: (b -> a) -> (a -> Either Mismatch b) -> Grammar p (a :- t) (b :- t)
partialOsi f' g' = Flip $ PartialIso f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = (:- t) <$> g' b


-- | Unconditionally push given value on stack, i.e. it does not consume
-- anything on parsing. However such grammar expects the same value as given one
-- on the stack during backward run.
push :: (Eq a) => a -> Grammar p t (a :- t)
push a = PartialIso f g
  where
    f t = a :- t
    g (a' :- t)
      | a == a' = Right t
      | otherwise = Left $ unexpected "pushed element"


-- | Same as 'push' except it does not check the value on stack during backward
-- run. Potentially unsafe as it \"forgets\" some data.
pushForget :: a -> Grammar p t (a :- t)
pushForget a = Iso f g
  where
    f t = a :- t
    g (_ :- t) = t


data HintedGrammar p t ah bh where
  HintedGrammar
    :: forall p ah (ahs :: [ah]) bh (bhs :: [bh]) t.
       (Taggy ah, Taggy bh, Demoteable ahs, Demote ahs ~ [Hint ah], Demoteable bhs, Demote bhs ~ [Hint bh]) =>
       Grammar p (Hinted ah ahs :- t) (Hinted bh bhs :- t)
    -> HintedGrammar p t ah bh


reifyGrammar
  :: forall p ah ahs bh bhs t.
     (Taggy ah, Taggy bh, Demoteable ahs, Demote ahs ~ [Hint ah], Demoteable bhs, Demote bhs ~ [Hint bh]) =>
     Grammar p (Hinted ah ahs :- t) (Hinted bh bhs :- t)
  -> ( Map (Hint ah) (Grammar p (Original ah :- t) (Original bh :- t))
     , Map (Hint bh) (Grammar p (Original ah :- t) (Original bh :- t))
     )
reifyGrammar g =
  ( M.fromListWith (<>) $ map (\h -> (h, unhinted)) (demote (Proxy @ahs))
  , M.fromListWith (<>) $ map (\h -> (h, unhinted)) (demote (Proxy @bhs))
  )
  where
    unhinted :: Grammar p (Original ah :- t) (Original bh :- t)
    unhinted = iso Hinted getHinted >>> g >>> iso getHinted Hinted


select :: forall p t ah bh. (Taggy ah, Taggy bh) => [HintedGrammar p t ah bh] -> Grammar p (Original ah :- t) (Original bh :- t)
select lst =
  let (as, bs) = unzip (map (\(HintedGrammar g) -> reifyGrammar g) lst)
  in Select (Proxy @ah) (Proxy @bh) (M.unionsWith (<>) as) (M.unionsWith (<>) bs)


forward :: Grammar p a b -> a -> ContextError (Propagation p) (GrammarError p) b
forward (Iso f _)        = return . f
forward (PartialIso f _) = return . f
forward (Flip g)         = backward g
forward (g :.: f)        = forward g <=< forward f
forward (f :<>: g)       = \x -> forward f x `mplus` forward g x
forward (Traverse g)     = traverse (forward g)
forward (Bitraverse g h) = bitraverse (forward g) (forward h)
forward (Select f _ mg _)    = \x@(a :- _) ->
  case M.lookup (mkTag f a) mg of
    Nothing -> throwInContext (\ctx -> GrammarError ctx (unexpected "unhandled case"))
    Just g  -> forward g x

forward (Dive g)         = dive . forward g
forward Step             = \x -> step >> return x
forward Locate           = \x -> locate x >> return x
{-# INLINE forward #-}


backward :: Grammar p a b -> b -> ContextError (Propagation p) (GrammarError p) a
backward (Iso _ g)        = return . g
backward (PartialIso _ g) = either (\mis -> throwInContext (\ctx -> GrammarError ctx mis)) return . g
backward (Flip g)         = forward g
backward (g :.: f)        = backward g >=> backward f
backward (f :<>: g)       = \x -> backward f x `mplus` backward g x
backward (Traverse g)     = traverse (backward g)
backward (Bitraverse g h) = bitraverse (backward g) (backward h)
backward (Select _ f _ mg)    = \x@(a :- _) ->
  case M.lookup (mkTag f a) mg of
    Nothing -> throwInContext (\ctx -> GrammarError ctx (unexpected "unhandled case"))
    Just g  -> backward g x

backward (Dive g)         = dive . backward g
backward Step             = \x -> step >> return x
backward Locate           = \x -> locate x >> return x
{-# INLINE backward #-}
