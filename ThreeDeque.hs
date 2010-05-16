{-# LANGUAGE GADTs #-}

{- http://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/Notes%20on%20Catenable%20Deques.doc -}

module ThreeDeque where

import Monad
import Maybe
import List

data Buffer a = B0
              | B1 a
              | B2 a a deriving (Show)

data Tree a = Leaf a
            | Node (Tree a) (Tree a) deriving (Show)

type PB a = (Buffer (Tree a),Buffer (Tree a))

-- TODO: non-empty substacks

data Deque a = Deque [PB a] [[PB a]] [[[PB a]]] (Maybe (Tree a)) deriving (Show)

toListTree' (Leaf x) r = x:r
toListTree' (Node x y) r = toListTree' x (toListTree' y r)

toList' (Deque [] [] [] Nothing) r = r
toList' (Deque [] [] [] (Just x)) r = toListTree' x r
toList' (Deque [] [] (x:xs) q) r = toList' (Deque [] x xs q) r
toList' (Deque [] (x:xs) ys q) r = toList' (Deque x xs ys q) r
toList' (Deque ((B0,B0):xs) ys zs q) r = toList' (Deque xs ys zs q) r
toList' (Deque ((B0,B1 x):xs) ys zs q) r = toList' (Deque xs ys zs q) (toListTree' x r)
toList' (Deque ((B0,B2 x y):xs) ys zs q) r = toList' (Deque xs ys zs q) (toListTree' x (toListTree' y r))
toList' (Deque ((B1 x,y):xs) ys zs q) r = toListTree' x (toList' (Deque ((B0,y):xs) ys zs q) r)
toList' (Deque ((B2 x y,z):xs) ys zs q) r = toListTree' x (toListTree' y (toList' (Deque ((B0,z):xs) ys zs q) r))

npush x (Deque [] [] [] Nothing) = Deque [] [] [] (Just x)
npush x (Deque [] [] [] (Just y)) = Deque [(B1 x, B1 y)] [] [] Nothing
npush x (Deque [] [] ((((B0,z):zs):ys):xs) q) = Deque [] (((B1 x,z):zs):ys) xs q
npush x (Deque [] (((B0,z):zs):ys) xs q) = Deque ((B1 x,z):zs) ys xs q
npush x (Deque [] [[(B1 y,B0)]] [] q) = Deque [(B1 x,B1 y)] [] [] q
npush x (Deque [] (((B1 y,z):zs):ys) xs q) = Deque [] [] ((((B2 x y,z):zs):ys):xs) q
npush x (Deque ((B1 y,z):zs) ys xs q) = Deque [] (((B2 x y,z):zs):ys) xs q

npop (Deque [] [] [] Nothing) = Nothing
npop (Deque [] [] [] (Just x)) = Just (x,empty)
npop (Deque [] [] ((((B2 x y,z):zs):ys):xs) q) = Just (x,Deque [] (((B1 y,z):zs):ys) xs q)
npop (Deque [] (((B2 x y,z):zs):ys) xs q) = Just (x,Deque ((B1 y,z):zs) ys xs q)
npop (Deque [] [[(B1 x,B2 y z)]] [] q) = Just (x,Deque [(B1 y,B1 z)] [] [] q)
npop (Deque [] (((B1 y,z):zs):ys) xs q) = Just (y,Deque [] [] ((((B0,z):zs):ys):xs) q)
npop (Deque [(B1 y,B1 z)] [] [] Nothing) = Just (y,Deque [] [] [] (Just z))
npop (Deque ((B1 y,z):zs) ys xs q) = Just (y,Deque [] (((B0,z):zs):ys) xs q)

smaller (Deque p [] ((((B2 x y,z):zs):ys):xs) q) = 
    let Deque a b c q' = npush (Node x y) (Deque zs ys xs q)
    in Deque p [] ((((B0,z):a):b):c) q'
smaller (Deque p [((B1 x,z):zs)] xs q) = 
    let Deque [] [] c q' = smaller (Deque [] [] xs q)
    in Deque p [((B1 x,z):zs)] c q'
smaller (Deque p (((B1 x,z):zs):(y:ys)) xs q) = 
    let Deque [] b c q' = smaller (Deque [] (y:ys) xs q)
    in Deque p (((B1 x,z):zs):b) c q'
smaller (Deque p (((B2 x y,z):zs):ys) xs q) = 
    let Deque a b c q' = npush (Node x y) (Deque zs ys xs q)
    in Deque p (((B0,z):a):b) c q'

larger (Deque p [] ((((B0,z):zs):ys):xs) q) = 
    let Just (Node x y,Deque a b c q') = npop (Deque zs ys xs q)
    in Deque p [] ((((B2 x y,z):a):b):c) q'
larger (Deque p [((B1 x,z):zs)] xs q) = 
    let Deque [] [] c q' = larger (Deque [] [] xs q)
    in Deque p [((B1 x,z):zs)] c q'
larger (Deque p (((B1 x,z):zs):(y:ys)) xs q) = 
    let Deque [] b c q' = larger (Deque [] (y:ys) xs q)
    in Deque p (((B1 x,z):zs):b) c q'
larger (Deque p (((B0,z):zs):ys) xs q) = 
    let Just (Node x y,Deque a b c q') = npop (Deque zs ys xs q)
    in Deque p (((B2 x y,z):a):b) c q'

data Size = S0 | S1 | S2 deriving (Show)

prepose (Deque _ [] [] _) = S1
prepose (Deque _ [] ((((B0,_):_):_):_) _) = S0
prepose (Deque _ [] ((((B2 _ _,_):_):_):_) _) = S2
prepose (Deque _ (((B0,_):_):_) _ _) = S0
prepose (Deque _ [((B1 _,_):_)] [] _) = S1
prepose (Deque _ [((B1 _,_):_)] ((((B0,_):zs):ys):xs) _) = S0
prepose (Deque _ [((B1 _,_):_)] ((((B2 _ _,_):zs):ys):xs) _) = S2
prepose (Deque _ (((B1 _,_):_):(((B0,_):_):_)) _ _) = S0
prepose (Deque _ (((B1 _,_):_):(((B2 _ _,_):_):_)) _ _) = S2
prepose (Deque _ (((B2 _ _,_):_):_) _ _) = S2
prepose _ = S1

push x xs =
    let y = Leaf x
    in case prepose xs of
         S2 -> npush y (smaller xs)
         _  -> npush y xs

pop xs =
    let ans = case prepose xs of
                S0 -> npop (larger xs)
                _ -> npop xs
    in case ans of
         Nothing -> Nothing
         Just (Leaf y,ys) -> Just (y,ys)

empty = Deque [] [] [] Nothing

-----------------------------------

fromList = foldr push empty
toList x = toList' x []
unList = unfoldr pop

nextPre0 [] = True
nextPre0 ((B0,_):xs) = nextPre2 xs
nextPre0 ((B1 _,_):xs) = nextPre0 xs
nextPre0 _ = False

nextPre2 [] = True
nextPre2 ((B1 _,_):xs) = nextPre2 xs
nextPre2 ((B2 _ _,_):xs) = nextPre0 xs
nextPre2 _ = False

regularPreAlt (Deque a b c _) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in nextPre0 d || nextPre2 d

nextSuf0 [] = True
nextSuf0 ((_,B0):xs) = nextSuf2 xs
nextSuf0 ((_,B1 _):xs) = nextSuf0 xs
nextSuf0 _ = False

nextSuf2 [] = True
nextSuf2 ((_,B1 _):xs) = nextSuf2 xs
nextSuf2 ((_,B2 _ _):xs) = nextSuf0 xs
nextSuf2 _ = False

regularSufAlt (Deque a b c _) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in nextSuf0 d || nextSuf2 d

bottomBias [] = True
bottomBias [(B2 _ _,B1 _)] = True
bottomBias [(B1 _,B2 _ _)] = True
bottomBias [(B1 _,B1 _)] = True
bottomBias [_] = False
bottomBias (x:y:ys) = bottomBias (y:ys)

bottomOK (Deque a b c (Just _)) = True
bottomOK (Deque a b c Nothing) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in bottomBias d

bigEnough (Deque _ _ _ (Just _)) = True
bigEnough x@(Deque _ _ _ Nothing) =
    case toList x of
      [x] -> False
      _ -> True

ones (B1 _,B1 _) = True
ones _ = False

halfNot [] = False
halfNot ((B0,B1 _):xs) = all ones xs
halfNot ((B1 _,B0):xs) = all ones xs
halfNot ((B1 _,B2 _ _):xs) = all ones xs
halfNot ((B2 _ _,B1 _):xs) = all ones xs
halfNot _ = False

bothNot [] = False
bothNot (((B0,B0):xs):ys) = all ones xs && all halfNot ys
bothNot (((B2 _ _,B0):xs):ys) = all ones xs && all halfNot ys
bothNot (((B0,B2 _ _):xs):ys) = all ones xs && all halfNot ys
bothNot (((B2 _ _,B2 _ _):xs):ys) = all ones xs && all halfNot ys
bothNot _ = False

allShape (Deque a b c _) =
    all ones a && all halfNot b && all bothNot c

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

dequeDepth (Deque a b c Nothing) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in isJust $ depthIs 1 d
dequeDepth (Deque a b c (Just q)) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in isJust $
       do i <- depthIs 1 d
          j <- treeDepth q
          guard (i == j)
          return i

invariants x = allShape x && regularSufAlt x && regularPreAlt x && bottomOK x && bigEnough x && dequeDepth x

popPreserves x =
    case pop x of
      Nothing -> True
      Just (_,z) -> invariants z && popPreserves z

{-
unList . fromList = id
toList . fromList = id
-}