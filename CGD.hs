module CGD (module CGD, module R) where

import qualified RebuildDeque as R
import Deque

type CGD = R.Deque

instance Empty R.Deque where
    empty = R.new

instance Deque R.Deque where
    push = R.push
    inject = R.inject
    pop = R.pop
    eject = R.eject