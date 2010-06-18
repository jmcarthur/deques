{-# LANGUAGE FlexibleInstances #-}

module DivisibleTest where

import Divisible
import Deque
import Loose
import Data.List
import Data.Maybe
import qualified Data.Sequence as S
import Test.QuickCheck

data Op a = Push a | Inject a | Pop | Eject | DivideLeft | DivideRight deriving (Show)

--act :: Deque d => Op a -> (DD d a, S.Seq a) -> Either (DD d a, S.Seq a) ((DD d a, S.Seq a),(DD d a, S.Seq a))
act (Push x) (y,z) =  (push x y, x S.<| z)
act (Inject x) (y,z) =  (inject y x, z S.|> x)
act Pop (y,z) = 
    case (pop y, S.viewl z) of
      (Just (_,y'), _ S.:< z') -> (y',z')
      (Nothing, S.EmptyL) -> (empty, S.empty)
      _ -> error "pop"
act Eject (y,z) = 
    case (eject y, S.viewr z) of
      (Just (y',_), z' S.:> _) -> (y',z')
      (Nothing, S.EmptyR) -> (empty, S.empty)
      _ -> error "eject"
act DivideLeft (y,z) = 
    let (y1,_) = divide y
        s = fromIntegral $ size y1
        (z1,_) = S.splitAt s z
    in (y1,z1)
act DivideRight (y,z) = 
    let (y1,y2) = divide y
        s = fromIntegral $ size y1
        (_,z2) = S.splitAt s z
    in (y2,z2)

data Tree a = Zero
            | One (Op a) (Tree a)
--            | Two (Op a) (Tree a) (Tree a)
 deriving (Show)

prob :: Int
prob = 2^10

--tip Divide = Two Divide Zero Zero
tip x = One x Zero

arbTree :: Int -> Gen (Tree Int)
arbTree i = 
    do b <- arbitrary :: Gen Int
       let hed = case b `mod` 6 of
                   0 -> DivideLeft
                   1 -> Inject i
                   2 -> Pop
                   3 -> Eject
                   4 -> Push i
                   _ -> DivideRight
       c <- arbitrary
       if (c `mod` prob) /= 0
          then do tyl <- arbTree (i+1)
                  return $ One hed tyl
          else return $ tip hed

{-
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
-}

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

fromLeft (Left x) = x
fromLeft _ = error "fromLeft"

checkOps dqt xs = checkOps' xs (empty `asTypeOf` dqt,S.empty)
checkOps' Zero (x,y) = check x y
checkOps' (One p ps) (x,y) =
    check x y &&
    let (a,b) = act p (x,y)
    in checkOps' ps (a,b) &&
       (case p of
          DivideLeft -> (size a + 1)*4 > size x
          DivideRight -> (size a + 1)*4 > size x
          _ -> True)

--form tt x = (foldr act (empty `asTypeOf` tt) x, foldr acts S.empty x)
--checkAll n tt = filter (not . uncurry check) $ map (form tt . fst) $ opSeqs n
--checkOne tt = uncurry check . form tt


newtype Ops = Ops (Tree Int) deriving (Show)

instance Arbitrary Ops where
    arbitrary = fmap Ops $ arbTree 0

checkArb dqt (Ops r) = checkOps dqt $  r
{-
checkArb tt =
    do ll <- arbList
-}


{-     
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
-}