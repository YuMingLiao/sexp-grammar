{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.InvertibleGrammar
  ( Grammar (..)
  , (:-) (..)
  , iso
  , osi
  , partialIso
  , partialOsi
  , push
  , pushForget
  , InvertibleGrammar (..)
  , GrammarError (..)
  , Mismatch
  , expected
  , unexpected
  , optimize
  ) where

import Prelude hiding ((.), id)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Category
import Control.Monad
import Data.DList (DList)
import qualified Data.DList as DL
import Data.Foldable (toList)
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import qualified Data.Monoid as Monoid
import Data.Semigroup

import Data.HetCompare
import Data.InvertibleGrammar.Monad

data Grammar g t t' where
  -- Partial isomorphism
  PartialIso :: String -> (a -> b) -> (b -> Either Mismatch a) -> Grammar g a b

  -- Total isomorphism
  Iso :: (a -> b) -> (b -> a) -> Grammar g a b

  -- Run a grammar in the opposite direction
  Flip :: Grammar g a b -> Grammar g b a

  -- Grammar composition
  (:.:) :: Grammar g b c -> Grammar g a b -> Grammar g a c

  -- Grammar alternation
  (:<>:) :: Grammar g a b -> Grammar g a b -> Grammar g a b

  -- Embed a subgrammar
  Inject :: g a b -> Grammar g a b

instance Category (Grammar c) where
  id = Iso id id
  (.) x y = x :.: y

instance Semigroup (Grammar c t1 t2) where
  (<>) = (:<>:)

instance (GEq g) => GEq (Grammar g) where
  geqHet PartialIso{} PartialIso{} = Nothing
  geqHet Iso{}        Iso{}        = Nothing
  geqHet (Flip g)     (Flip g')    =
    case geqHet g g' of
      Nothing        -> Nothing
      Just ReflInOut -> Just ReflInOut
  geqHet (g :.: h)    (g' :.: h')  =
    case geqHet g g' of
      Nothing        -> Nothing
      Just ReflInOut ->
        case geqHet h h' of
          Nothing        -> Nothing
          Just ReflInOut -> Just ReflInOut
  geqHet (g :<>: h)   (g' :<>: h') =
    case geqHet g g' of
      Nothing        -> Nothing
      Just ReflInOut ->
        case geqHet h h' of
          Nothing        -> Nothing
          Just ReflInOut -> Just ReflInOut
  geqHet (Inject g)   (Inject g')  =
    case geqHet g g' of
      Nothing        -> Nothing
      Just ReflInOut -> Just ReflInOut
  geqHet _ _ = Nothing


data h :- t = h :- t deriving (Eq, Show, Functor)
infixr 5 :-

-- | Make a grammar from a total isomorphism on top element of stack
iso :: (a -> b) -> (b -> a) -> Grammar g (a :- t) (b :- t)
iso f' g' = Iso f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = g' b :- t

-- | Make a grammar from a total isomorphism on top element of stack (flipped)
osi :: (b -> a) -> (a -> b) -> Grammar g (a :- t) (b :- t)
osi f' g' = Iso g f
  where
    f (a :- t) = f' a :- t
    g (b :- t) = g' b :- t

-- | Make a grammar from a partial isomorphism which can fail during backward
-- run
partialIso :: String -> (a -> b) -> (b -> Either Mismatch a) -> Grammar g (a :- t) (b :- t)
partialIso prismName f' g' = PartialIso prismName f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = (:- t) <$> g' b

-- | Make a grammar from a partial isomorphism which can fail during forward run
partialOsi :: String -> (b -> a) -> (a -> Either Mismatch b) -> Grammar g (a :- t) (b :- t)
partialOsi prismName f' g' = Flip $ PartialIso prismName f g
  where
    f (a :- t) = f' a :- t
    g (b :- t) = (:- t) <$> g' b

-- | Unconditionally push given value on stack, i.e. it does not consume
-- anything on parsing. However such grammar expects the same value as given one
-- on the stack during backward run.
push :: (Eq a) => a -> Grammar g t (a :- t)
push a = PartialIso "push" f g
  where
    f t = a :- t
    g (a' :- t)
      | a == a' = Right t
      | otherwise = Left $ unexpected "pushed element"

-- | Same as 'push' except it does not check the value on stack during backward
-- run. Potentially unsafe as it \"forgets\" some data.
pushForget :: a -> Grammar g t (a :- t)
pushForget a = Iso f g
  where
    f t = a :- t
    g (_ :- t) = t

class InvertibleGrammar m g where
  forward  :: g a b -> (a -> m b)
  backward :: g a b -> (b -> m a)

instance
  ( Monad m
  , MonadPlus m
  , MonadContextError (Propagation p) (GrammarError p) m
  , InvertibleGrammar m g
  ) => InvertibleGrammar m (Grammar g) where
  forward (Iso f _)           = return . f
  forward (PartialIso _ f _)  = return . f
  forward (Flip g)            = backward g
  forward (g :.: f)           = forward g <=< forward f
  forward (f :<>: g)          = \x -> forward f x `mplus` forward g x
  forward (Inject g)          = forward g
  {-# INLINE forward #-}

  backward (Iso _ g)          = return . g
  backward (PartialIso _ _ g) = either (\mis -> throwInContext (\ctx -> GrammarError ctx mis)) return . g
  backward (Flip g)           = forward g
  backward (g :.: f)          = backward g >=> backward f
  backward (f :<>: g)         = \x -> backward f x `mplus` backward g x
  backward (Inject g)         = backward g
  {-# INLINE backward #-}

-- class Optimize g where
--   optimize :: g a b -> g a b

optimize :: forall g a b. (GEq g) => Grammar g a b -> Grammar g a b
optimize g@PartialIso{} = g
optimize g@Iso{}        = g
optimize g@(Flip x)     =
  case x of
    PartialIso{} -> g
    Iso y z      -> Iso z y
    Flip y       -> optimize y
    x :.: y      -> optimize (Flip y) :.: optimize (Flip x)
    x :<>: y     -> optimize (Flip x) :<>: optimize (Flip y)
    Inject _     -> g
optimize (f :.: g)      = optimize f :.: optimize g
optimize (f :<>: g)     = foldr1 (:<>:) $ map compilePrefix $ groupGrammars splitted
  where
    alts :: [Grammar g a b]
    alts = toList $ collectAlternatives f Monoid.<> collectAlternatives g
    splitted :: [SplitHead g a b]
    splitted = map splitHead alts
optimize (Inject g)     = Inject g

compilePrefix :: forall g a c. SomeSplitHeadsMid g a c -> Grammar g a c
compilePrefix (SomeSplitHeadsMid (g :| gs)) =
  case g of
    NoSuffixMid hd ->
      case gs' of
        []        -> hd
        g' : gs'' -> foldl' (:<>:) g' gs'' :.: hd
    WithSuffixMid hd tl ->
      foldl' (:<>:) tl gs' :.: hd
  where
    -- gs' :: [(Maybe Grammar g b0 c)]
    gs' = mapMaybe (snd . splitGrammarMid) gs

collectAlternatives :: Grammar g a b -> DList (Grammar g a b)
collectAlternatives (f :<>: g) = collectAlternatives f Monoid.<> collectAlternatives g
collectAlternatives g          = DL.singleton g

groupGrammars
  :: (GEq g)
  => [SplitHead g a c]
  -> [SomeSplitHeadsMid g a c]
  -- ^ Grammars groups, each group starting with grammar that is geqHet to
  -- all other grammars in the group.
groupGrammars []     = []
groupGrammars [x]    = [mkSplitHeads x]
groupGrammars (x:xs) =
  case x of
    NoSuffix g ->
      SomeSplitHeadsMid common : groupGrammars different
      where
        (common, different) = findCommonStart g (NoSuffixMid g) xs
    WithSuffix g h ->
      SomeSplitHeadsMid common : groupGrammars different
      where
        (common, different) = findCommonStart g (WithSuffixMid g h) xs

findCommonStart
  :: forall g a b c. (GEq g)
  => Grammar g a b
  -> SplitHeadMid g a b c
  -> [SplitHead g a c]
  -> (NonEmpty (SplitHeadMid g a b c), [SplitHead g a c])
findCommonStart x initial = go (initial :| []) []
  where
    go :: NonEmpty (SplitHeadMid g a b c)
       -> [SplitHead g a c]
       -> [SplitHead g a c]
       -> (NonEmpty (SplitHeadMid g a b c), [SplitHead g a c])
    go eqs nonEqs []       = (eqs, nonEqs)
    go eqs nonEqs (y : ys) =
      case y of
        NoSuffix g ->
          case geqHet x g of
            Nothing        -> go eqs                           (y : nonEqs) ys
            Just ReflInOut -> go (NE.cons (NoSuffixMid g) eqs) nonEqs       ys
        WithSuffix hd tl ->
          case geqHet x hd of
            Nothing        -> go eqs                                 (y : nonEqs) ys
            Just ReflInOut -> go (NE.cons (WithSuffixMid hd tl) eqs) nonEqs       ys

data SomeSplitHeadsMid g a c = forall b. SomeSplitHeadsMid (NonEmpty (SplitHeadMid g a b c))

data SplitHeadMid g a b c where
  NoSuffixMid :: Grammar g a c -> SplitHeadMid g a c c
  WithSuffixMid
    :: Grammar g a b
    -> Grammar g b c
    -> SplitHeadMid g a b c

splitGrammarMid :: SplitHeadMid g a b c -> (Grammar g a b, Maybe (Grammar g b c))
splitGrammarMid (NoSuffixMid g)     = (g, Nothing)
splitGrammarMid (WithSuffixMid g h) = (g, Just h)

mkSplitHeads :: SplitHead g a b -> SomeSplitHeadsMid g a b
mkSplitHeads (NoSuffix g)      = SomeSplitHeadsMid $ NoSuffixMid g :| []
mkSplitHeads (WithSuffix g g') = SomeSplitHeadsMid $ WithSuffixMid g g' :| []

grammarFromSplitHeadMid :: SplitHeadMid g a b c -> Grammar g a c
grammarFromSplitHeadMid (NoSuffixMid g)     = g
grammarFromSplitHeadMid (WithSuffixMid g h) = h :.: g

data SplitHead g a b where
  NoSuffix :: Grammar g a b -> SplitHead g a b
  WithSuffix
    :: Grammar g a c -- head
    -> Grammar g c b -- tail (suffix)
    -> SplitHead g a b

getSplitGrammar :: SplitHead g a b -> Grammar g a b
getSplitGrammar (NoSuffix g)     = g
getSplitGrammar (WithSuffix g h) = h :.: g

splitHead :: Grammar g a b -> SplitHead g a b
splitHead g@PartialIso{} = NoSuffix g
splitHead g@Iso{}        = NoSuffix g
splitHead (Flip x)       =
  case splitTail x of
    NoPrefix g      -> NoSuffix $ Flip g
    WithPrefix g g' -> WithSuffix (Flip g') (Flip g)
splitHead (g :.: h)      =
  case splitHead h of
    NoSuffix hd      -> WithSuffix hd g
    WithSuffix hd tl -> WithSuffix hd (g :.: tl)
splitHead (_ :<>: _)     = error "splitHead: unexpected alternative"
splitHead g@(Inject _)   = NoSuffix g

data SplitTail g a b where
  NoPrefix :: Grammar g a b -> SplitTail g a b
  WithPrefix
    :: Grammar g a c -- ^ prefix
    -> Grammar g c b -- ^ last item
    -> SplitTail g a b

splitTail :: Grammar g a b -> SplitTail g a b
splitTail g@PartialIso{} = NoPrefix g
splitTail g@Iso{}        = NoPrefix g
splitTail (Flip x)       =
  case splitHead x of
    NoSuffix g      -> NoPrefix (Flip g)
    WithSuffix g g' -> WithPrefix (Flip g') (Flip g)
splitTail (g :.: h)      =
  case splitTail g of
    NoPrefix g'           -> WithPrefix h g'
    WithPrefix prefix end -> WithPrefix (prefix :.: h) end
splitTail (_ :<>: _)     = error "splitTail: unexpected alternative"
splitTail g@(Inject _)   = NoPrefix g

