{-# LANGUAGE TypeSynonymInstances #-}

module TarjanMihaesau where

import qualified ThreeDequeGADT as T
import Deque
import Loose

type TM = T.Deque

instance Deque TM where
    push = T.push
    pop = T.pop
    inject = T.inject
    eject = T.eject

instance Empty TM where
    empty = T.tempty

instance Loose (TM a) where
    proper = T.invariants

instance Eq a => Eq (TM a) where
    xs == ys =
        case (pop xs,pop ys) of
          (Nothing,Nothing) -> True
          (Just (a,as), Just (b,bs)) -> a == b && as == bs
          _ -> False