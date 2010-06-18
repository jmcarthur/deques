{-# LANGUAGE FlexibleInstances #-}

module DequeTest where

import Deque
import Loose
import Data.List
import Data.Maybe
import qualified Data.Sequence as S
import Test.QuickCheck

data Op a = Push a | Inject a | Pop | Eject deriving (Show)

{-
opSeqs 0 = []
opSeqs 1 = [([Push 0],1), ([Inject 0],1)]
opSeqs n =
    let m = n-2
        f (l,0) = [((Push n):l,1),((Inject n):l,1)]
        f (l,k) = [((Push n):l,k+1),((Inject n):l,k+1),(Pop:l,k-1),(Eject:l,k-1)]
    in concatMap f (opSeqs (n-1))
-}

act (Push x) y = push x y
act (Inject x) y = inject y x
act Pop x = snd $ fromJust $ pop x
act Eject x = fst $ fromJust $ eject x

acts (Push x) y = x S.<| y
acts (Inject x) y = y S.|> x
acts Pop x = 
    case S.viewl x of
      _ S.:< y -> y
acts Eject x = 
    case S.viewr x of
      y S.:> _ -> y

slist x =
    case S.viewl x of
      y S.:< ys -> y:(slist ys)
      _ -> []

popList x = unfoldr pop x

ejectList xs = ejectList' xs []
ejectList' xs r =
    case eject xs of
      Nothing -> r
      Just (ys,y) -> ejectList' ys (y:r)

check x y =
    let z = slist y
    in popList x == z
       &&
       ejectList x == z
       &&
       proper x



checkOps dqt xs = checkOps' xs (empty `asTypeOf` dqt) S.empty
checkOps' [] x y = check x y
checkOps' (p:ps) x y =
    check x y &&
    checkOps' ps (act p x) (acts p y)

--form tt x = (foldr act (empty `asTypeOf` tt) x, foldr acts S.empty x)
--checkAll n tt = filter (not . uncurry check) $ map (form tt . fst) $ opSeqs n
--checkOne tt = uncurry check . form tt

prob :: Int
prob = 2^9

arbList 0 i = 
    do b <- arbitrary
       let hed = if b
                 then Push i
                 else Inject i
       c <- arbitrary
       if (c `mod` prob) /= 0
          then
              do tyl <- arbList 1 (i+1)
                 return $ hed:tyl
          else return [hed]
arbList n i = 
    do b0 <- arbitrary
       b1 <- arbitrary
       let (hed,m) = case (b0,b1) of 
                       (True,True) -> (Push i,n+1)
                       (True,_) -> (Inject i,n+1)
                       (False,False) -> (Pop,n-1)
                       _ -> (Eject,n-1)
       c <- arbitrary
       if (c `mod` prob) /= 0
          then
              do tyl <- arbList m (i+1)
                 return $ hed:tyl
          else return [hed]

arbSet 0 i = 
    do b <- arbitrary
       let hed = if b
                 then Push i
                 else Inject i
       if i > 0
          then
              do tyl <- arbSet 1 (i-1)
                 return $ hed:tyl
          else return [hed]
arbSet n i = 
    do b0 <- arbitrary
       b1 <- arbitrary
       let (hed,m) = case (b0,b1) of 
                       (True,True) -> (Push i,n+1)
                       (True,_) -> (Inject i,n+1)
                       (False,False) -> (Pop,n-1)
                       _ -> (Eject,n-1)
       if i > 0
          then
              do tyl <- arbSet m (i-1)
                 return $ hed:tyl
          else return [hed]

newtype Ops = Ops [Op Int] deriving (Show)

instance Arbitrary Ops where
    arbitrary = fmap Ops $ arbSet 0 prob

checkArb dqt (Ops r) = checkOps dqt $  r
{-
checkArb tt =
    do ll <- arbList
-}


       
pushList x = foldr push empty x

injectList x = foldl' inject empty x


popPreserves f x =
    case pop x of
      Nothing -> True
      Just (_,z) -> f z && popPreserves f z

ejectPreserves f x =
    case eject x of
      Nothing -> True
      Just (z,_) -> f z && ejectPreserves f z

pushPreserves [] _ f _ = True
pushPreserves (y:ys) r f xs =
    let zs = push y xs
    in f (y:r) zs && pushPreserves ys (y:r) f zs

injectPreserves [] _ f _ = True
injectPreserves (y:ys) r f xs =
    let zs = inject xs y
    in f (r++[y]) zs && pushPreserves ys (y:r) f zs

test 1 n x = and [let v = [1..i] in proper (f v `asTypeOf` x) | i <- [1..n], f <- [pushList,injectList]]
test 2 n x = and [let v = [1..i] in f (g v `asTypeOf` x) == v | i <- [1..n], g <- [pushList,injectList], f <- [popList,ejectList]]
test 3 n x = and [let v = [1..i] in f proper (g v `asTypeOf` x) | i <- [1..n], g <- [pushList,injectList], f <- [popPreserves,ejectPreserves]]
test 4 m x = 
    let n = m `div` 6
    in and [let v = [1..i] in g (f (replicate i 42) [] (const proper)) (h v `asTypeOf` x) 
            | i <- [1..n], h <- [pushList,injectList], g <- [popPreserves,ejectPreserves], f <- [pushPreserves,injectPreserves]]
{-
test 4 n = and [let v = [1..i] in popPreserves invariants (fromList v) | i <- [1..n]]
test 6 n = and [let v = [1..i] in invariants (injectList v) | i <- [1..n]]
test 8 n = and [let v = [1..i] in ejectPreserves invariants (fromList v) | i <- [1..n]]
test 10 n = and [let v = [1..i] in popPreserves invariants (injectList v) | i <- [1..n]]
test 12 n = and [let v = [1..i] in ejectPreserves invariants (injectList v) | i <- [1..n]]
test 15 n = and [let v = [1..i] in f (g invariants) (h v) | i <- [1..n], 
                         l <- [[popPreserves, ejectPreserves, pushPreserves (2*i) 42, injectPreserves (2*i) 42]], 
                         f <- l, g <- l,
                         h <- [injectList, fromList]]
test 16 n = and [let v = [1..i] in v == f (g v) | i <- [1..n], f <- [toList, unList, nuList], g <- [fromList, injectList]]
test _ _ = True
-}
tests k n x = and [test i n x | i <- [1..k]]
