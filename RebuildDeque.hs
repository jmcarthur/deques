{- Chuang and Goldberg's global rebuild deque -}

module RebuildDeque where

type Nat = Integer

data List a = Nil
            | Cons a !(List a) deriving (Show)

headList (Cons ans _) = ans
tailList (Cons _ ans) = ans

type Stack a = (List a, List a)

emptyStack = (Nil,Nil)

nullStack (Nil,Nil) = True
nullStack _ = False

pushStack x (ys,zs) = (Cons x ys,zs)

popStack (Cons x ys,zs) = Just (x,(ys,zs))
popStack (Nil,Cons z zs) = Just (z,(zs,Nil))
popStack _ = Nothing

tailStack x =
    case popStack x of
      Just (_,ans) -> ans
headStack x =
    case popStack x of
      Just (ans,_) -> ans

type Current a = (List a, Nat, Stack a, Nat)

data State a = Norm  !(Stack a)   !Nat
             | RevB  !(Current a) !(Stack a) !(List a)  !Nat
             | RevS1 !(Current a) !(Stack a) !(List a)
             | RevS2 !(Current a) !(List a)  !(Stack a) !(List a) !Nat
             | Copy  !(Current a) !(List a)  !(List a)  !Nat deriving (Show)

put e (extra, added, old, remained) = (Cons e extra, added+1, old, remained)

--get :: Current a -> (a, Current a)
get (Nil, added, old, remained) = (headStack old, (Nil, added, tailStack old, remained-1))
get (Cons e es, added, old, remained) = (e, (es, added-1, old, remained))

top current = 
    let (element, _) = get current
    in element
bot current = 
    let (_,rest) = get current
    in rest

normalize state@(Copy (extra,added,_,remained) _ new moved) =
    if moved == remained
    then Norm (extra, new) (added+moved)
    else state
normalize x = x

tick state@(Norm _ _) = state
tick (RevB current big aux count) = RevB current (tailStack big) (Cons (headStack big) aux) (count-1)
tick state@(RevS1 current small aux) =
    case popStack small of
      Nothing -> state
      Just (hed,tyl) -> RevS1 current tyl (Cons hed aux)
tick (RevS2 current aux big newS count) =
    case popStack big of
      Nothing -> normalize (Copy current aux newS count)
      Just (hed,tyl) -> RevS2 current aux tyl (Cons hed newS) (count+1)
tick state@(Copy current@(_,_,_,remained) aux newS moved) =
    if moved < remained
    then normalize (Copy current (tailList aux) (Cons (headList aux) newS) (moved+1))
    else normalize state

ticks (RevB currentB big auxB 0, RevS1 currentS _ auxS) =
    (normalize (Copy currentB auxB Nil 0), RevS2 currentS auxS big Nil 0)
ticks (RevS1 currentS _ auxS, RevB currentB big auxB 0) =
    (RevS2 currentS auxS big Nil 0, normalize (Copy currentB auxB Nil 0))
ticks (lhs, rhs) = (tick lhs, tick rhs)

steps 0 pair = pair
steps n pair = steps (n-1) (ticks pair)

data Deque a = List !(List a)
             | Pair !(State a) !(State a) deriving (Show)

new = List Nil

empty (List Nil) = True
empty _ = False

rev x = rev' x Nil

rev' Nil r = r
rev' (Cons x xs) r = rev' xs (Cons x r)

swap (List x) = List (rev x)
swap (Pair lhs rhs) = Pair rhs lhs

pop' (Norm a b) = (headStack a, Norm (tailStack a) (b-1))
pop' (RevB a b c d) = (top a, RevB (bot a) b c d)
pop' (RevS1 a b c) = (top a, RevS1 (bot a) b c)
pop' (RevS2 a b c d e) = (top a, RevS2 (bot a) b c d e)
pop' (Copy a b c d) = (top a, Copy (bot a) b c d)

pair (x,y) = Pair x y

append Nil r = r
append (Cons x xs) r = Cons x (append xs r)

pop (List Nil) = Nothing
pop (List (Cons x xs)) = Just (x, List xs)
pop (Pair (Norm ls l) rhs@(Norm rs r)) = Just $
  let Just (h, hs) = popStack ls 
  in if 3*(l-1) >= r
     then (h, Pair (Norm hs (l-1)) rhs)
     else if l >= 2
          then (h, pair (steps 6 (RevS1 (Nil, 0, hs, 2*l-1) hs Nil,
                                  RevB  (Nil, 0, rs, r-l)   rs Nil (r-l))))
          else let (rs1,rs2) = rs 
               in (h, List (rev (append rs1 rs2)))
pop (Pair ls rs) = Just $
  let (e,es) = pop' ls
  in (e, pair (steps 4 (es,rs)))

eject xyz = 
    let zyx = swap xyz
    in case pop zyx of
         Nothing -> Nothing
         Just (z,yx) -> 
             let xy = swap yx
             in Just (xy,z)

push' z (Norm a b) = Norm (pushStack z a) (b+1)
push' z (RevB a b c d) = RevB (put z a) b c d
push' z (RevS1 a b c) =  RevS1 (put z a) b c
push' z (RevS2 a b c d e) =  RevS2 (put z a) b c d e
push' z (Copy a b c d) = Copy (put z a) b c d

size Nil = 0
size (Cons _ xs) = 1+(size xs)

push e (List Nil) = List (Cons e Nil)
push e (List (Cons hed Nil)) = List (Cons e (Cons hed Nil))
push e (List (Cons h1 (Cons h2 Nil))) = List $ Cons e $ Cons h1 $ Cons h2 Nil
push e (List (Cons h1 (Cons h2 (Cons h3 tyl)))) =
    Pair (Norm (Cons e (Cons h1 Nil), Nil) 2)
         (Norm (Cons h3 (Cons h2 Nil), Nil) 2)
push e (Pair (Norm ls l) rhs@(Norm rs r)) =
    let hs = pushStack e ls 
    in if 3*r >= l+1
       then Pair (Norm hs (l+1)) rhs
       else pair (steps 3 (RevB  (Nil, 0, hs, l-r) hs Nil (l-r),
                           RevS1 (Nil, 0, rs, 2*r+1) rs Nil))
push e (Pair ls rs) = pair (steps 4 (push' e ls, rs))

inject xy z =
    let yx = swap xy
        zyx = push z yx
        xyz = swap zyx
    in xyz

instance Eq a => Eq (Deque a) where
    xs == ys =
        case (pop xs,pop ys) of
          (Nothing,Nothing) -> True
          (Just (a,as), Just (b,bs)) -> a == b && as == bs
          _ -> False