{-# LANGUAGE GADTs #-}

{- http://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/Notes%20on%20Catenable%20Deques.doc -}

module ThreeDeque where

data Buffer a = B0
              | B1 a
              | B2 a a deriving (Show)

data Tree a = Leaf a
            | Node (Tree a) (Tree a) deriving (Show)

type PB a = (Buffer (Tree a), Buffer (Tree a))

-- TODO: non-empty substacks

data Deque a = Deque [PB a] [[PB a]] [[[PB a]]] deriving (Show)

toListTree' (Leaf x) r = x:r
toListTree' (Node x y) r = toListTree' x (toListTree' y r)

toList' (Deque [] [] []) r = r
toList' (Deque [] [] (x:xs)) r = toList' (Deque [] x xs) r
toList' (Deque [] (x:xs) ys) r = toList' (Deque x xs ys) r
toList' (Deque ((B0,B0):xs) ys zs) r = toList' (Deque xs ys zs) r
toList' (Deque ((B0,B1 x):xs) ys zs) r = toList' (Deque xs ys zs) (toListTree' x r)
toList' (Deque ((B0,B2 x y):xs) ys zs) r = toList' (Deque xs ys zs) (toListTree' x (toListTree' y r))
toList' (Deque ((B1 x,y):xs) ys zs) r = toListTree' x (toList' (Deque ((B0,y):xs) ys zs) r)
toList' (Deque ((B2 x y,z):xs) ys zs) r = toListTree' x (toListTree' y (toList' (Deque ((B0,z):xs) ys zs) r))

npush x (Deque [] [] []) = Deque [] [[(B1 x,B0)]] []
npush x (Deque [] [] ((((B0,z):zs):ys):xs)) = Deque [] (((B1 x,z):zs):ys) xs
npush x (Deque [] (((B0,z):zs):ys) xs) = Deque ((B1 x,z):zs) ys xs
npush x (Deque [] [[(B1 y,B0)]] []) = Deque [(B1 x,B1 y)] [] []
npush x (Deque [] (((B1 y,z):zs):ys) xs) = Deque [] [] ((((B2 x y,z):zs):ys):xs)
npush x (Deque ((B1 y,z):zs) ys xs) = Deque [] (((B2 x y,z):zs):ys) xs

smaller (Deque p [] ((((B2 x y,z):zs):ys):xs)) = 
    let Deque a b c = npush (Node x y) (Deque zs ys xs)
    in Deque p [] ((((B0,z):a):b):c)
smaller (Deque p [((B1 x,z):zs)] xs) = 
    let Deque [] [] c = smaller (Deque [] [] xs)
    in Deque p [((B1 x,z):zs)] c
smaller (Deque p (((B1 x,z):zs):(y:ys)) xs) = 
    let Deque [] b c = smaller (Deque [] (y:ys) xs)
    in Deque p (((B1 x,z):zs):b) c
smaller (Deque p (((B2 x y,z):zs):ys) xs) = 
    let Deque a b c = npush (Node x y) (Deque zs ys xs)
    in Deque p (((B0,z):a):b) c

data Size = S0 | S1 | S2 deriving (Show)

prepose (Deque _ [] []) = S1
prepose (Deque _ [] ((((B0,_):_):_):_)) = S0
prepose (Deque _ [] ((((B2 _ _,_):_):_):_)) = S2
prepose (Deque _ (((B0,_):_):_) _) = S0
prepose (Deque _ [((B1 _,_):_)] []) = S1
prepose (Deque _ [((B1 _,_):_)] ((((B0,_):zs):ys):xs)) = S0
prepose (Deque _ [((B1 _,_):_)] ((((B2 _ _,_):zs):ys):xs)) = S2
prepose (Deque _ (((B1 _,_):_):(((B0,_):_):_)) _) = S0
prepose (Deque _ (((B1 _,_):_):(((B2 _ _,_):_):_)) _) = S2
prepose (Deque _ (((B2 _ _,_):_):_) _) = S2
prepose _ = S1

push x xs =
    let y = Leaf x
    in case prepose xs of
         S2 -> npush y (smaller xs)
         _  -> npush y xs

empty = Deque [] [] []

fromList = foldr push empty
toList x = toList' x []

nextPre0 [] = True
nextPre0 ((B0,_):xs) = nextPre2 xs
nextPre0 ((B1 _,_):xs) = nextPre0 xs
nextPre0 _ = False

nextPre2 [] = True
nextPre2 ((B1 _,_):xs) = nextPre2 xs
nextPre2 ((B2 _ _,_):xs) = nextPre0 xs
nextPre2 _ = False

regularPreAlt (Deque a b c) = 
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

regularSufAlt (Deque a b c) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in nextSuf0 d || nextSuf2 d

bottomBias [] = True
bottomBias [(B2 _ _,B0)] = False
bottomBias [(B0,B2 _ _)] = False
bottomBias [_] = True
bottomBias (x:y:ys) = bottomBias (y:ys)

bottomOK (Deque a b c) = 
    let d = a ++ (concat b) ++ (concat $ concat c)
    in bottomBias d

ones (B1 _,B1 _) = True
ones _ = False

{-
allOnes [] = True
allOnes ((B1 _,B1 _):xs) = allOnes xs
allOnes _ = False
-}

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

allShape (Deque a b c) =
    all ones a && all halfNot b && all bothNot c

invariants x = allShape x && regularSufAlt x && regularPreAlt x && bottomOK x