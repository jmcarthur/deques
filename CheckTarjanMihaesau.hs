{-# LANGUAGE OverlappingInstances #-}

module CheckTarjanMihaescu where

import TarjanMihaescu
import DequeTest

import Test.QuickCheck
import Deque

checkTM = quickCheck $ checkArb (empty :: TM Int)
