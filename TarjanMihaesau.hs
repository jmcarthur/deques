{-# LANGUAGE TypeSynonymInstances #-}

module TarjanMihaesau where

import qualified ThreeDequeGADT as T
import Deque
import Loose

type TM = T.Deque

instance Deque TM where
    empty = T.tempty
    push = T.push
    pop = T.pop
    inject = T.inject
    eject = T.eject

instance Loose (TM a) where
    proper = T.invariants