{-# LANGUAGE GADTs #-}

{- http://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/Notes%20on%20Catenable%20Deques.doc -}

module ThreeDeque where

import Monad
import Maybe
import Data.List

data Buffer a = B0
              | B1 a
              | B2 a a deriving (Show)

data Tree a = Leaf a
            | Node (Tree a) (Tree a) deriving (Show)

type PB a = (Buffer (Tree a),Buffer (Tree a))

type NEL a = (a,[a])

data Deque a = Deque [PB a] [NEL (NEL (PB a))] (Maybe (Tree a)) deriving (Show)

data Top = Prefix | Suffix | Both deriving (Show)

topCheck (B1 _, B1 _) = Nothing
topCheck (B0,B1 _) = Just Prefix
topCheck (B2 _ _,B1 _) = Just Prefix
topCheck (B1 _,B0) = Just Suffix
topCheck (B1 _,B2 _ _) = Just Suffix
topCheck _ = Just Both

nextTop1 Prefix Prefix = True
nextTop1 Suffix Suffix = True
nextTop1 _ _ = False

cons13 :: [PB a] -> [NEL (NEL (PB a))] -> [NEL (NEL (PB a))]
cons13 [] [] = []
cons13 [] y = y
cons13 (x:xs) [] = [((x,xs),[])]
cons13 (x:xs) r@(((c,cs),bs):as) = 
    let Just p = topCheck x
        Just q = topCheck c
    in if nextTop1 p q
       then ((x,xs),((c,cs):bs)):as
       else ((x,xs),[]):r

npush x (Deque [] [] Nothing) = Deque [] [] (Just x)
npush x (Deque [] [] (Just y)) = Deque [(B1 x, B1 y)] [] Nothing
npush x (Deque [] ((((B0,B1 z),zs),[]):xs) q) = Deque ((B1 x,B1 z):zs) xs q
npush x (Deque [] ((((B0,B1 z),zs),(y:ys)):xs) q) = Deque ((B1 x,B1 z):zs) ((y,ys):xs) q
npush x (Deque [] ((((B0,z),zs),[]):xs) q) = Deque [] (cons13 ((B1 x,z):zs) xs) q 
npush x (Deque [] [(((B1 y,B0),[]),[])] Nothing) = Deque [(B1 x,B1 y)] [] Nothing
npush x (Deque [] ((((B1 y,z),zs),[]):xs) q) = Deque [] ((((B2 x y,z),zs),[]):xs) q 
npush x (Deque [] ((((B1 y,z),zs),(r:rs)):xs) q) = Deque [] ((((B2 x y,z),zs),[]):((r,rs):xs)) q
npush x (Deque ((B1 y,z):zs) rs q) = Deque [] (cons13 ((B2 x y,z):zs) rs) q

ninject (Deque [] [] Nothing) x = Deque [] [] (Just x)
ninject (Deque [] [] (Just y)) x = Deque [(B1 y, B1 x)] [] Nothing
ninject (Deque [] ((((B1 z,B0),zs),[]):xs) q) x = Deque ((B1 z,B1 x):zs) xs q
ninject (Deque [] ((((B1 z,B0),zs),(y:ys)):xs) q) x = Deque ((B1 z,B1 x):zs) ((y,ys):xs) q
ninject (Deque [] ((((z,B0),zs),[]):xs) q) x = Deque [] (cons13 ((z,B1 x):zs) xs) q 
ninject (Deque [] [(((B0,B1 y),[]),[])] Nothing) x = Deque [(B1 y,B1 x)] [] Nothing
ninject (Deque [] ((((z,B1 y),zs),[]):xs) q) x = Deque [] ((((z,B2 y x),zs),[]):xs) q 
ninject (Deque [] ((((z,B1 y),zs),(r:rs)):xs) q) x = Deque [] ((((z,B2 y x),zs),[]):((r,rs):xs)) q
ninject (Deque ((z,B1 y):zs) rs q) x = Deque [] (cons13 ((z,B2 y x):zs) rs) q

npop (Deque [] [] Nothing) = Nothing
npop (Deque [] [] (Just y)) =  Just (y,empty)
npop (Deque [] ((((B2 y x,B1 z),zs),[]):xs) q) = Just (y,Deque ((B1 x,B1 z):zs) xs q)
npop (Deque [] ((((B2 y x,B1 z),zs),(r:rs)):xs) q) = Just (y,Deque ((B1 x,B1 z):zs) ((r,rs):xs) q)
npop (Deque [] ((((B2 y x,z),zs),[]):xs) q) = Just (y,Deque [] (cons13 ((B1 x,z):zs) xs) q)
npop (Deque [] [(((B1 y,B2 x z),[]),[])] Nothing) = Just (y,Deque [(B1 x,B1 z)] [] Nothing)
npop (Deque [] [(((B1 y,B0),[]),[])] Nothing) = Just (y,empty)
npop (Deque [] [(((B1 y,B0),[]),[])] (Just (Node x z))) = Just (y, Deque [(B1 x,B1 z)] [] Nothing)
npop (Deque [] ((((B1 y,z),zs),[]):xs) q) = Just (y,Deque [] ((((B0,z),zs),[]):xs) q)
npop (Deque [] ((((B1 y,z),zs),(r:rs)):xs) q) = Just (y,Deque [] ((((B0,z),zs),[]):((r,rs):xs)) q)
npop (Deque [(B1 y,B1 z)] [] Nothing) = Just (y,Deque [] [] (Just z))
npop (Deque ((B1 y,z):zs) rs q) = Just (y,Deque [] (cons13 ((B0,z):zs) rs) q)

neject (Deque [] [] Nothing) = Nothing
neject (Deque [] [] (Just y)) =  Just (empty,y)
neject (Deque [] ((((B1 x,B2 z y),zs),[]):xs) q) = Just (Deque ((B1 x,B1 z):zs) xs q,y)
neject (Deque [] ((((B1 x,B2 z y),zs),(r:rs)):xs) q) = Just (Deque ((B1 x,B1 z):zs) ((r,rs):xs) q,y)
neject (Deque [] ((((z,B2 x y),zs),[]):xs) q) = Just (Deque [] (cons13 ((z,B1 x):zs) xs) q,y)
neject (Deque [] [(((B2 x z,B1 y),[]),[])] Nothing) = Just (Deque [(B1 x,B1 z)] [] Nothing,y)
neject (Deque [] [(((B0,B1 y),[]),[])] Nothing) = Just (empty,y)
neject (Deque [] [(((B0,B1 y),[]),[])] (Just (Node x z))) = Just (Deque [(B1 x,B1 z)] [] Nothing,y)
neject (Deque [] ((((z,B1 y),zs),[]):xs) q) = Just (Deque [] ((((z,B0),zs),[]):xs) q,y)
neject (Deque [] ((((z,B1 y),zs),(r:rs)):xs) q) = Just (Deque [] ((((z,B0),zs),[]):((r,rs):xs)) q,y)
neject (Deque [(B1 z,B1 y)] [] Nothing) = Just (Deque [] [] (Just z),y)
neject (Deque ((z,B1 y):zs) rs q) = Just (Deque [] (cons13 ((z,B0):zs) rs) q,y)

prefix0' (Deque p ((((B2 x y,z),zs),[]):xs) q) = 
    let Deque a c q' = npush (Node x y) (Deque zs xs q)
    in Deque p (cons13 ((B0,z):a) c) q' 
prefix0' (Deque p ((((B2 x y,z),zs),(r:rs)):xs) q) = 
    let Deque a c q' = npush (Node x y) (Deque zs ((r,rs):xs) q)
    in Deque p (cons13 ((B0,z):a) c) q'

prefix0 (Deque p ((((B1 x,z),zs),[]):xs) q) = 
    let Deque a c q' = prefix0' (Deque zs xs q)
    in Deque p (cons13 ((B1 x,z):a) c) q' 
prefix0 (Deque p ((((B1 x,z),zs),(r:rs)):xs) q) = 
    let Deque [] c q' = prefix0' (Deque [] xs q)
    in Deque p ((((B1 x,z),zs),(r:rs)):c) q' 
prefix0 x = prefix0' x

suffix0' (Deque p ((((z,B2 x y),zs),[]):xs) q) = 
    let Deque a c q' = ninject (Deque zs xs q) (Node x y)
    in Deque p (cons13 ((z,B0):a) c) q' 
suffix0' (Deque p ((((z,B2 x y),zs),(r:rs)):xs) q) = 
    let Deque a c q' = ninject (Deque zs ((r,rs):xs) q) (Node x y)
    in Deque p (cons13 ((z,B0):a) c) q'

suffix0 (Deque p ((((z,B1 x),zs),[]):xs) q) = 
    let Deque a c q' = suffix0' (Deque zs xs q)
    in Deque p (cons13 ((z,B1 x):a) c) q' 
suffix0 (Deque p ((((z,B1 x),zs),(r:rs)):xs) q) = 
    let Deque [] c q' = suffix0' (Deque [] xs q)
    in Deque p ((((z,B1 x),zs),(r:rs)):c) q' 
suffix0 x = suffix0' x

prefix2' (Deque p ((((B0,z),zs),[]):xs) q) = 
    let Just (Node x y,Deque a c q') = npop (Deque zs xs q)
    in Deque p (cons13 ((B2 x y,z):a) c) q' 
prefix2' (Deque p ((((B0,z),zs),(r:rs)):xs) q) = 
    let Just (Node x y,Deque a c q') = npop (Deque zs ((r,rs):xs) q)
    in Deque p (cons13 ((B2 x y,z):a) c) q'

prefix2 (Deque p ((((B1 x,z),zs),[]):xs) q) = 
    let Deque a c q' = prefix2' (Deque zs xs q)
    in Deque p (cons13 ((B1 x,z):a) c) q' 
prefix2 (Deque p ((((B1 x,z),zs),(r:rs)):xs) q) = 
    let Deque [] c q' = prefix2' (Deque [] xs q)
    in Deque p ((((B1 x,z),zs),(r:rs)):c) q' 
prefix2 x = prefix2' x

suffix2' (Deque p ((((z,B0),zs),[]):xs) q) = 
    let Just (Deque a c q',Node x y) = neject (Deque zs xs q)
    in {-case (a,c,q') of
         ([],[],Nothing) -> Deque [((B1 x,B1 y)] [] Nothing 
         _ -> -} Deque p (cons13 ((z,B2 x y):a) c) q' 
suffix2' (Deque p ((((z,B0),zs),(r:rs)):xs) q) = 
    let Just (Deque a c q',Node x y) = neject (Deque zs ((r,rs):xs) q)
    in Deque p (cons13 ((z,B2 x y):a) c) q'

suffix2 (Deque p ((((z,B1 x),zs),[]):xs) q) = 
    let Deque a c q' = suffix2' (Deque zs xs q)
    in Deque p (cons13 ((z,B1 x):a) c) q' 
suffix2 (Deque p ((((z,B1 x),zs),(r:rs)):xs) q) = 
    let Deque [] c q' = suffix2' (Deque [] xs q)
    in Deque p ((((z,B1 x),zs),(r:rs)):c) q' 
suffix2 x = suffix2' x

data Size = S0 | S1 | S2 deriving (Show)

prepose' (Deque _ [] _) = S1
prepose' (Deque _ ((((B0,_),_),_):_) _) = S0
prepose' (Deque _ ((((B2 _ _,_),_),_):_) _) = S2

prepose (Deque p ((((B1 _,_),_),_):xs) q) = prepose' (Deque p xs q)
--prepose (Deque p ((((B1 _,_),_),(r:rs)):xs) q) = prepose' (Deque p ((r,rs):xs) q)
prepose x = prepose' x

sufpose' (Deque _ [] _) = S1
sufpose' (Deque _ ((((_,B0),_),_):_) _) = S0
sufpose' (Deque _ ((((_,B2 _ _),_),_):_) _) = S2

sufpose (Deque p ((((_,B1 _),_),_):xs) q) = sufpose' (Deque p xs q)
--sufpose (Deque p ((((_,B1 _),_),(r:rs)):xs) q) = sufpose' (Deque p ((r,rs):xs) q)
sufpose x = sufpose' x

{-

Deque [] [(((B2 (Leaf 1) (Leaf 2),B1 (Leaf 9)),[]),[((B0,B1 (Node (Leaf 7) (Leaf 8))),[])])] (Just (Node (Node (Leaf 3) (Leaf 4)) (Node (Leaf 5) (Leaf 6))))

-}
push x xs =
    let y = Leaf x
    in case prepose xs of
         S2 -> npush y (prefix0 xs)
         _  -> npush y xs

inject xs x =
    let y = Leaf x
    in case sufpose xs of
         S2 -> ninject (suffix0 xs) y
         _  -> ninject xs y

pop xs =
    let ans = case prepose xs of
                S0 -> npop (prefix2 xs)
                _ -> npop xs
    in case ans of
         Nothing -> Nothing
         Just (Leaf y,ys) -> Just (y,ys)

eject xs =
    let ans = case sufpose xs of
                S0 -> neject (suffix2 xs)
                _ -> neject xs
    in case ans of
         Nothing -> Nothing
         Just (ys,Leaf y) -> Just (ys,y)

empty = Deque [] [] Nothing

-----------------------------------

fromList = foldr push empty

---------------------------------

toListTree' (Leaf x) r = x:r
toListTree' (Node x y) r = toListTree' x (toListTree' y r)

toListTree x = toListTree' x []

nelist (x,xs) = x:xs

joinUp = concatMap (concatMap nelist . nelist)

toList (Deque x y Nothing) = wrapMap toListTree (x ++ (joinUp y))
toList (Deque x y (Just z)) = wrapMap toListTree (x ++ (joinUp y) ++ [(B0,B1 z)])

wrapMap _ [] = []
wrapMap f ((B0,B0):xs) = wrapMap f xs
wrapMap f ((B0,B1 x):xs) = wrapMap f xs ++ f x
wrapMap f ((B0,B2 x y):xs) = wrapMap f xs ++ f x ++ f y
wrapMap f ((B1 x, y):xs) = f x ++ wrapMap f ((B0,y):xs)
wrapMap f ((B2 x y,z):xs) = f x ++ f y ++ wrapMap f ((B0,z):xs)

nextPre0 [] = True
nextPre0 ((B0,_):xs) = nextPre2 xs
nextPre0 ((B1 _,_):xs) = nextPre0 xs
nextPre0 _ = False

nextPre2 [] = True
nextPre2 ((B1 _,_):xs) = nextPre2 xs
nextPre2 ((B2 _ _,_):xs) = nextPre0 xs
nextPre2 _ = False

regularPreAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextPre0 d || nextPre2 d

nextSuf0 [] = True
nextSuf0 ((_,B0):xs) = nextSuf2 xs
nextSuf0 ((_,B1 _):xs) = nextSuf0 xs
nextSuf0 _ = False

nextSuf2 [] = True
nextSuf2 ((_,B1 _):xs) = nextSuf2 xs
nextSuf2 ((_,B2 _ _):xs) = nextSuf0 xs
nextSuf2 _ = False

regularSufAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextSuf0 d || nextSuf2 d

bottomBias [] = True
bottomBias [(B2 _ _,B2 _ _)] = True
bottomBias [(B2 _ _,B1 _)] = True
bottomBias [(B1 _,B2 _ _)] = True
bottomBias [(B1 _,B1 _)] = True
bottomBias [_] = False
bottomBias (x:y:ys) = bottomBias (y:ys)

bottomSkip [] = True
bottomSkip [(B0,B0)] = False
bottomSkip [_] = True
bottomSkip (x:y:ys) = bottomSkip (y:ys)

bottomOK (Deque a c (Just _)) =
    let d = a ++ (joinUp c)
    in bottomSkip d
bottomOK (Deque a c Nothing) = 
    let d = a ++ (joinUp c)
    in bottomBias d

bigEnough (Deque _ _ (Just _)) = True
bigEnough x@(Deque _ _ Nothing) =
    case toList x of
      [x] -> False
      _ -> True

ones (B1 _,B1 _) = True
ones _ = False

top1 (x,xs) =
    do v <- topCheck x
       guard (all ones xs)
       return v

top2 (x,[]) = top1 x
top2 (x,y:ys) =
    do v <- top1 x
       w <- top2 (y,ys)
       guard (nextTop1 v w)
       return v

top3 x [] = top2 x
top3 x (y:ys) =
    do v <- top2 x
       w <- top3 y ys
       guard (not (nextTop1 v w))
       return v

topShape [] = True
topShape (x:xs) = isJust $ top3 x xs

allShape (Deque a b _) =
    all ones a && topShape b

treeDepth (Leaf _) = return 1
treeDepth (Node x y) =
    do i <- treeDepth x
       j <- treeDepth y
       guard (i == j)
       return (i+1)

depthIs i [] = return i
depthIs i ((B0,B0):xs) = depthIs (i+1) xs
depthIs i ((B0,B1 x):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs (i+1) xs
depthIs i ((B0,B2 x y):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B0,B1 y):xs)
depthIs i ((B1 x,y):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B0,y):xs) 
depthIs i ((B2 x y,z):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B1 y,z):xs)

dequeDepth (Deque a c Nothing) = 
    let d = a ++ (joinUp c)
    in isJust $ depthIs 1 d
dequeDepth (Deque a c (Just q)) = 
    let d = a ++ (joinUp c)
    in isJust $
       do i <- depthIs 1 d
          j <- treeDepth q
          guard (i == j)
          return i

invariants x = allShape x && regularSufAlt x && regularPreAlt x && bottomOK x && bigEnough x && dequeDepth x

{-
unList . fromList = id
toList . fromList = id
-}

-------------------------

unList = unfoldr pop
nuList xs =
    case eject xs of
      Nothing -> []
      Just (ys,y) -> (nuList ys)++[y]

popPreserves f x =
    case pop x of
      Nothing -> True
      Just (_,z) -> f z && popPreserves f z

ejectPreserves f x =
    case eject x of
      Nothing -> True
      Just (z,_) -> f z && ejectPreserves f z

pushPreserves f 0 _ _ = True
pushPreserves f n x xs =
    let m = n-1
        ys = push x xs
    in f ys && pushPreserves f m x ys

injectList = foldl' inject empty

test 1 n = and [let v = [1..i] in v == toList (fromList v) | i <- [1..n]]
test 2 n = and [let v = [1..i] in invariants (fromList v) | i <- [1..n]]
test 3 n = and [let v = [1..i] in v == unList (fromList v) | i <- [1..n]]
test 4 n = and [let v = [1..i] in popPreserves invariants (fromList v) | i <- [1..n]]
test 5 n = and [let v = [1..i] in v == toList (injectList v) | i <- [1..n]]
test 6 n = and [let v = [1..i] in invariants (injectList v) | i <- [1..n]]
test 7 n = and [let v = [1..i] in popPreserves (pushPreserves invariants (2*i) (42)) (fromList v) | i <- [1..n]]
test 8 n = and [let v = [1..i] in ejectPreserves invariants (fromList v) | i <- [1..n]]
test 9 n = and [let v = [1..i] in v == unList (injectList v) | i <- [1..n]]
test 10 n = and [let v = [1..i] in popPreserves invariants (injectList v) | i <- [1..n]]
test 11 n = and [let v = [1..i] in popPreserves (pushPreserves invariants (2*i) (42)) (injectList v) | i <- [1..n]]
test 12 n = and [let v = [1..i] in ejectPreserves invariants (injectList v) | i <- [1..n]]
test 13 n = and [let v = [1..i] in v == nuList (fromList v) | i <- [1..n]]
test 14 n = and [let v = [1..i] in v == nuList (injectList v) | i <- [1..n]]

tests k n = and [test i n | i <- [1..k]]