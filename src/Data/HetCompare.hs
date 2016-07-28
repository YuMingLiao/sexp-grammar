----------------------------------------------------------------------------
-- |
-- Module      :  Data.HetCompare
-- Copyright   :  (c) Sergey Vinokurov 2016
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Created     :  Saturday, 23 July 2016
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}

module Data.HetCompare where

data ReflInOut a b c d where
  ReflInOut :: ReflInOut a b a b

class GEq g where
  geqHet :: g a b -> g c d -> Maybe (ReflInOut a b c d)

data GOrderingInOut a b c d where
  GLT :: GOrderingInOut a b c d
  GEQ :: ReflInOut a b c d -> GOrderingInOut a b c d
  GGT :: GOrderingInOut a b c d

class GOrd g where
  gcompareHet :: g a b -> g c d -> ReflInOut a b c d
