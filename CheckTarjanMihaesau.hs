{-# LANGUAGE OverlappingInstances #-}

module CheckTarjanMihaesau where

import TarjanMihaesau
import DequeTest

import Test.QuickCheck
import Deque

checkTM = quickCheck $ checkArb (empty :: TM Int)
