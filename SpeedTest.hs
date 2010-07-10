module SpeedTest where

import qualified DequeTest as DT
import qualified CGD as R
import qualified Data.Sequence as S
import qualified TarjanMihaesau as T
import qualified LazyRealTimeDeque as L
import qualified Deque as D
import qualified BankersDeque as B
import qualified Beque as Q
import Test.QuickCheck
import Data.List(foldl')

operate (DT.Ops ops') = 
    let ops = {- reverse -} ops'
    in (soper ops == D.empty &&
        roper ops == D.empty &&
        toper ops == D.empty &&
        loper ops == D.empty &&
        boper ops == D.empty &&
        qsoper ops == D.empty &&
        qroper ops == D.empty &&
        qtoper ops == D.empty &&
        qloper ops == D.empty &&
        qboper ops == D.empty)
        
soper = foldl' (flip DT.act) S.empty
roper = foldl' (flip DT.act) (D.empty :: R.CGD Int) 
toper = foldl' (flip DT.act) (D.empty :: T.TM Int) 
loper = foldl' (flip DT.act) (D.empty :: L.LRT Int) 
boper = foldl' (flip DT.act) (D.empty :: B.BankersDeque Int) 
qsoper = foldl' (flip DT.act) (D.empty :: Q.Beque S.Seq Int)
qroper = foldl' (flip DT.act) (D.empty :: Q.Beque R.CGD Int) 
qtoper = foldl' (flip DT.act) (D.empty :: Q.Beque T.TM Int) 
qloper = foldl' (flip DT.act) (D.empty :: Q.Beque L.LRT Int) 
qboper = foldl' (flip DT.act) (D.empty :: Q.Beque B.BankersDeque Int) 

main = sequence_ $ replicate (max 1 ((2^16) `div` DT.prob)) $ quickCheck operate