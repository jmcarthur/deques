module Divisible where

import Deque
import qualified Data.List as L
import Loose 

type Nat = Integer

data Leven d s = L0 (d s)
               | L2 s s (d s)

data Reven d s = R0 (d s)
               | R2 (d s) s s

instance (Deque d, Show s) => Show (Leven d s) where
    show (L0 x) = "(L0 "++(showDeque x)++")"
    show (L2 x y z) = "(L2 ("++(show x)++") "++(show y)++" "++(showDeque z)++")"

instance (Deque d, Show s) => Show (Reven d s) where
    show (R0 x) = "(R0 "++(showDeque x)++")"
    show (R2 x y z) = "(R2 ("++(showDeque x)++") "++(show y)++" "++(show z)++")"

data LSpine d a = LSpine Nat a (d (RSpine d a)) (d (Leven d (RSpine d a)))
data RSpine d a = RSpine Nat (d (Reven d (LSpine d a))) (d (LSpine d a)) a

instance (Show a, Deque d) => Show (LSpine d a) where
    show (LSpine n x ys zs) = "(LSpine "++(show n)++" "++(show x)++" "++(showDeque ys)++" "++(showDeque zs)++")"

instance (Show a,Deque d) => Show (RSpine d a) where
    show (RSpine n xs ys z) = "(RSpine "++(show n)++" "++(showDeque xs)++" "++(showDeque ys)++" "++(show z)++")"

showDeque xs = show $ dequeToList xs
dequeToList xs = 
    case pop xs of
      Nothing -> []
      Just (y,ys) -> y : (dequeToList ys)

data DD d a = Empty
            | Full (LSpine d a) deriving (Show)

full x =
    case pop x of
      Nothing -> False
      _ -> True

nil x = not (full x)

rsize (RSpine n _ _ _) = n
lsize (LSpine n _ _ _) = n

lrr l r@(RSpine m ds es f) =
    let nm = lsize l+m
    in case pop ds of
         Nothing -> RSpine nm empty (push l es) f
         Just (R0 d,ds') -> RSpine nm (push (R0 (push l d)) ds') es f
         Just (R2 d d1 d2,ds') -> RSpine nm (push (R2 (push l d) d1 d2) ds') es f

lrl l@(LSpine n a bs cs) r =
    let nm = n+rsize r
    in case eject cs of
         Nothing -> LSpine nm a (inject bs r) empty
         Just (cs',L0 c) -> LSpine nm a bs (inject cs' (L0 (inject c r)))
         Just (cs',L2 c1 c2 c) -> LSpine nm a bs (inject cs' (L2 c1 c2 (inject c r)))

data Lean x l r = Lingle x
                | Liny l
                | Lenter l r
                | Rightist l r r

ltop (LSpine n a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of 
            Nothing -> Lingle a
            Just (bs',b) -> Lenter (LSpine (n-rsize b) a bs' empty) b
      Just (cs',L0 c) -> 
          case eject c of
            Nothing -> Liny (LSpine n a bs cs')
            Just (c',d) -> Lenter (LSpine (n-rsize d) a bs (inject cs' (L0 c'))) d
      Just (cs',L2 c1 c2 c) -> 
          case eject c of
            Nothing -> Rightist (LSpine (n-rsize c1-rsize c2) a bs cs') c1 c2
            Just (c',d) -> Lenter (LSpine (n-rsize d) a bs (inject cs' (L2 c1 c2 c'))) d

data RMid x l r = RMid1 x
                | RMid2 l r

rmidTop (RSpine n cs bs a) =
    case pop cs of
      Nothing ->
          case pop bs of 
            Nothing -> RMid1 a
            Just (b,bs') -> RMid2 b (RSpine (n-lsize b) empty bs' a)
      _ -> error "rmidTop"

rmidl r =
    case rmidTop r of
      RMid1 x -> LSpine 1 x empty empty
      RMid2 p q -> lrl p q

lrrr p q (RSpine n ds es f) =
    case pop ds of
      Just (R2 _ _ _,_) -> RSpine (n+lsize p+rsize q) (push (R0 (push (lrl p q) empty)) ds) es f
      _ -> RSpine (n+lsize p+rsize q) (push (R2 empty p (rmidl q)) ds) es f

ltor x =
    case ltop x of
      Lingle p -> (RSpine 1 empty empty p)
      Liny p -> ltor p
      Lenter p q -> lrr p q
      Rightist p q r -> lrrr p q r

mpop bs cs = 
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> Nothing
            Just (L2 c1 c2 c', cs') -> Just (c1,push c2 c',cs')
            _ -> error "mpop D0"
      Just (b,bs') -> Just (b,empty, push (L0 bs') cs)


meject cs bs = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> Nothing
            Just (cs',R2 c' c1 c2) -> Just (cs',inject c' c1,c2)
            _ -> error "meject D0"
      Just (bs',b) -> Just (inject cs (R0 bs'),empty,b)

suffix2 x@(RSpine n cs bs a) =
    case eject cs of
      Just (fs,R0 es) ->
          case meject fs es of
            Nothing -> RSpine n empty bs a
            Just (rs,qs,p) -> 
                case ltop p of
                  Lingle _ -> error "Lingle suffix2 - too small"
                  Liny p' -> {- rs is a singleton with only (R0 empty), qs is empty -}
                            RSpine n empty (push p' bs) a
                  Lenter p1 p2 -> RSpine n (inject rs (R2 qs p1 (rmidl p2))) bs a
                  Rightist p1 p2 p3 -> {- rs is a singleton with only (R0 empty), qs is empty -}
                                       RSpine n empty (push (lrl p1 p2) (push (rtol p3) bs)) a
      _ -> x

prefix2 x@(LSpine n a bs cs) =
    case pop cs of
      Just (L0 es,fs) ->
          case mpop es fs of
            Nothing -> LSpine n a bs empty
            Just (p,qs,rs) -> 
                case rtop p of
                  Ringle _ -> error "Ringle prefix2 - too small"
                  Riny p' -> {- rs is a singleton with only (R0 empty), qs is empty -}
                            LSpine n a (inject bs p') empty
                  Renter p1 p2 -> LSpine n a bs (push (L2 (lmidr p1) p2 qs) rs)
                  Leftist p1 p2 p3 -> {- rs is a singleton with only (R0 empty), qs is empty -}
                                       LSpine n a (inject (inject bs (ltor p1)) (lrr p2 p3)) empty
      _ -> x


ronly (RSpine 1 _ _ x) = x
ronly _ = error "ronly"

npop (LSpine n a bs cs) =
    case mpop bs cs of
      Nothing -> (a,Empty)
      Just (p,q,r) -> (a,Full (LSpine (n-1) (ronly p) q r))

dpop Empty = Nothing
dpop (Full xs) = Just $ npop $ prefix2 xs

lonly (LSpine 1 x _ _) = x
lonly _ = error "lonly"

neject (RSpine n cs bs a) =
    case meject cs bs of
      Nothing -> (Empty,a)
      Just (ps,qs,r) -> (Full (rtol (RSpine (n-1) ps qs (lonly r))),a)

deject Empty = Nothing
deject (Full xs) = Just $ neject $ suffix2 $ ltor xs

data Rean x l r = Ringle x
                | Riny r
                | Renter l r
                | Leftist l l r

rtop (RSpine n cs bs a) =
    case pop cs of
      Nothing ->
          case pop bs of 
            Nothing -> Ringle a
            Just (b,bs') -> Renter b (RSpine (n-lsize b) empty bs' a)
      Just (R0 c,cs') -> 
          case pop c of
            Nothing -> Riny (RSpine n cs' bs a)
            Just (d,c') -> Renter d (RSpine (n-lsize d) (push (R0 c') cs') bs a)
      Just (R2 c c1 c2,cs') -> 
          case pop c of
            Nothing ->  Leftist c1 c2 (RSpine (n-lsize c1-lsize c2) cs' bs a)
            Just (d,c') -> Renter d (RSpine (n-lsize d) (push (R2 c' c1 c2 ) cs') bs a)

lmidTop (LSpine n a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of 
            Nothing -> RMid1 a
            Just (bs',b) -> RMid2 (LSpine (n-rsize b) a bs' empty) b
      _ -> error "lmidTop"

lmidr l =
    case lmidTop l of
      RMid1 x -> RSpine 1 empty empty x
      RMid2 p q -> lrr p q

llrl (LSpine n a bs cs) p q = 
    case eject cs of
      Just (_,L2 _ _ _) -> LSpine (n+lsize p+rsize q) a bs (inject cs (L0 (push (lrr p q) empty)))
      _ -> LSpine (n+lsize p+rsize q) a bs (inject cs (L2 (lmidr p) q empty))

rtol x =
    case rtop x of
      Ringle p -> LSpine 1 p empty empty
      Riny p -> rtol p
      Renter p q -> lrl p q
      Leftist p q r -> llrl p q r

mpush a bs cs = 
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> (push a empty, empty)
            Just (L0 c', cs') -> (push a c', cs')
            _ -> error "mpush L2"
      Just (b,bs') -> (empty, push (L2 a b bs') cs)

prefix0 x@(LSpine n a bs cs) =
    case pop cs of
      Just (L2 c d es,fs) ->
          let cd = lrr (rtol c) d
              (gs,hs) = mpush cd es fs
          in LSpine n a bs (push (L0 gs) hs)
      _ -> x

npush x (LSpine n a bs cs) =
    let (bs',cs') = mpush (RSpine 1 empty empty a) bs cs
    in LSpine (n+1) x bs' cs'

dpush x Empty = Full (LSpine 1 x empty empty)
dpush x (Full xs) = Full $ npush x $ prefix0 xs


minject cs bs a = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> (empty,inject empty a)
            Just (cs', R0 c) -> (cs',inject c a)
            _ -> error "minject R2"
      Just (bs',b) -> (inject cs (R2 bs' b a),empty)

suffix0 x@(RSpine n cs bs a) =
    case eject cs of
      Just (fs, R2 es d c) ->
          let dc = lrl d (ltor c)
              (hs,gs) = minject fs es dc
          in RSpine n (inject hs (R0 gs)) bs a
      _ -> x

ninject (RSpine n cs bs a) x =
    let (cs',bs') = minject cs bs (LSpine 1 a empty empty)
    in RSpine (n+1) cs' bs' x

dinject' Empty x = RSpine 1 empty empty x
dinject' (Full xs) x = ninject (suffix0 $ ltor xs) x

dinject xs x = Full $ rtol $ dinject' xs x


instance Deque d => Deque (DD d) where
    empty = Empty
    push = dpush
    pop = dpop
    inject = dinject
    eject = deject

instance ({- Loose d, -}Deque d) => Loose (DD d a) where
    proper x = depthP x && alternateP x && perfectP x {- && nestP x -}

{-

ldivlr (LSpine n a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of 
            Nothing -> (Nothing, RSpine 1 empty empty a)
            Just (bs',b) -> (Just (LSpine (n-rsize b) a bs' empty), b)
      Just (cs',D0 c) -> 
          case eject c of
            Nothing -> ldivlr (LSpine n a bs cs')
            Just (c',d) -> (Just (LSpine (n-rsize d) a bs (inject cs' (D0 c'))), d)
      Just (cs',D2 c1 c2 c) -> 
          case eject c of
            Nothing -> 
                case eject cs' of
                  Nothing -> (Just (LSpine (n-rsize c2) a (inject bs c1) empty), c2)
                  Just (ds, D0 d) -> (Just (LSpine (n-rsize c2) a bs (inject ds (D0 (inject d c1)))), c2)
                  Just (ds, D2 d1 d2 d) -> (Just (LSpine (n-rsize c2) a bs (inject ds (D2 d1 d2 (inject d c1)))), c2)
            Just (c',d) -> (Just (LSpine (n-rsize d) a bs (inject cs' (D2 c1 c2 c'))), d)

rdivlr (RSpine n cs bs a) =
    case pop cs of
      Nothing ->
          case pop bs of 
            Nothing -> (LSpine 1 a empty empty, Nothing)
            Just (b,bs') -> (b,Just (RSpine (n-lsize b) empty bs' a))
      Just (D0 c,cs') -> 
          case pop c of
            Nothing -> rdivlr (RSpine n cs' bs a)
            Just (d,c') -> (d, Just (RSpine (n-lsize d) (push (D0 c') cs') bs a))
      Just (D2 c1 c2 c,cs') -> 
          case pop c of
            Nothing -> 
                case pop cs' of
                  Nothing -> (c1, Just (RSpine (n-lsize c1) empty (push c2 bs) a))
                  Just (D0 d, ds) -> (c1, Just (RSpine (n-lsize c1) (push (D0 (push c2 d)) ds) bs a))
                  Just (D2 d1 d2 d, ds) -> (c1, Just (RSpine (n-lsize c1) (push (D2 d1 d2 (push c2 d)) ds) bs a))
            Just (d,c') -> (d, Just (RSpine (n-lsize d) (push (D2 c1 c2 c') cs') bs a))

{-
ldiv (LSpine a bs cs')
            Just (c',d) -> (LSpine a bs (inject cs (D0 c')), d)
-}

{-
BUG 
eject $ push 4 $ push 3 $ push 2 (Empty :: DD TM Int)
-}

ltor' x =
    let (p,q) = ldivlr x 
    in case p of
         Nothing -> q
         Just p' -> lrr p' q



data Rean l r = Rone l
              | Rentrist l r
              | Leftist l l r


-- TODO sizeP invariant



l2div x = 
    case ltop x of
      Lone y -> Left y
      Lentrist y z -> Right (y,z)
      Rightist p q r -> Right (lrl p q,r)

rtol x =
    case rtop x of
      Rone y -> y
      Rentrist y z -> lrl y z
      Leftist p q r -> llrr p q r


r2div x =
    case rtop x of
      Rone y -> Left y
      Rentrist y z -> Right (y,z)
      Leftist p q r -> Right (p,lrr q r)





{-
nestP Empty = True
nestP (Full l) = nestL l

nestL (LSpine _ x xs) =
    case (pop x, pop xs) of
      (Nothing, Nothing) -> True
      _ -> proper x && proper seach nestR x xs
            
    proper x &&
    case pop xs of
      Nothing -> True
      Just (D0 
-}
-- TODO: replicate
-- TODO: deques that can be joined on left or right
-- TODO: tests
-- TODO: slower split?
-- TODO: proof of divide's evenness
-- TODO: replace (since no split/join
-- TODO: interpolation search? better measure on indexing complexit (fast near ends and middle?)

fromList xs = foldr dpush Empty xs
toList xs = L.unfoldr dpop xs

divide Empty = (Empty,Empty)
divide (Full x) =
    let (p,q) = l2div x 
        q' = Full $ rtol q
        p' = Full p
    in (p',q')
-}

size Empty = 0
size (Full x) = lsize x

data DBG = Leaf Bool String
         | Branch Bool String DBG DBG deriving (Show)

dval (Leaf x _) = x
dval (Branch x _ _ _) = x

band v p q = p && q --Branch (dval p && dval q) v p q
leaf x y = x -- Leaf x y

--ldepth :: Deque d => Nat -> Maybe Nat -> d (RSpine d a) -> d (Even d (RSpine d a)) -> Bool
ldepth n m bs cs =
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> 
                case m of
                  Nothing -> leaf True (show n) 
                  Just m' -> leaf (n==m') (show (n,m'))
            Just (L0 c',ds) 
              -> ldepth (n+1) m c' ds
            Just (L2 (RSpine _ p1 p2 _ ) q r,ss) 
              -> band "L2" 
                 (rdepth (Just (n-0)) 1 p1 p2)
                 (ldepth n m (push q r) ss)
      Just (RSpine _ b1 b2 _,bs') 
          -> band "Lall"
             (rdepth (Just (n-0)) 1 b1 b2)
             (ldepth (n+1) m bs' cs)

--rdepth :: Deque d => Maybe Nat -> Nat -> d (Even d (LSpine d a)) -> d (LSpine d a) -> Bool
rdepth m n cs bs = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> 
                case m of
                  Nothing -> leaf True (show n)
                  Just m' -> leaf (n == m') (show (n,m'))
            Just (ds,R0 c') 
              -> rdepth m (n+1) ds c'
            Just (ss,R2 r (LSpine _ _ p1 p2) q) 
              -> band "R2"
                 (ldepth 1 (Just (n-0)) p1 p2)
                 (rdepth m n ss (inject r q))
      Just (bs',LSpine _ _ b1 b2) 
          -> band "Rall"
             (ldepth 1 (Just (n-0)) b1 b2)
             (rdepth m (n+1) cs bs')

depthP Empty = True
depthP (Full (LSpine _ _ x y)) = ldepth 1 Nothing x y

data Force = Big | Small | Any

{-
biggest _ 1 = 1
biggest Nothing n = maximum
-}

topalt Any x = 
    case pop x of
      Nothing -> True
      Just (L0 _,xs) -> topalt Big xs
      Just (L2 _ _ _,xs) -> topalt Small xs
topalt Big x = 
    case pop x of
      Nothing -> True
      Just (L0 _,xs) -> False
      Just (L2 _ _ _,xs) -> topalt Small xs
topalt Small x = 
    case pop x of
      Nothing -> True
      Just (L0 _,xs) -> topalt Big xs
      Just (L2 _ _ _,xs) -> False

topaltR Any x = 
    case pop x of
      Nothing -> True
      Just (R0 _,xs) -> topaltR Big xs
      Just (R2 _ _ _,xs) -> topaltR Small xs
topaltR Big x = 
    case pop x of
      Nothing -> True
      Just (R0 _,xs) -> False
      Just (R2 _ _ _,xs) -> topaltR Small xs
topaltR Small x = 
    case pop x of
      Nothing -> True
      Just (R0 _,xs) -> topaltR Big xs
      Just (R2 _ _ _,xs) -> False

dlast xs =
    case eject xs of
      Nothing -> Nothing
      Just (_,ans) -> Just ans

lastRight xs ys =
    case eject ys of
      Nothing -> dlast xs
      Just (zs,L0 z) -> 
          case dlast z of
            Nothing -> lastRight xs zs
            x -> x
      Just (_,L2 _ z' z) -> 
          case dlast z of
            Nothing -> Just z'
            x -> x

alternateP Empty = True
alternateP (Full (LSpine _ _ xs ys)) = 
    topalt Any ys &&
    case lastRight xs ys of
      Nothing -> True
      Just (RSpine _ zs _ _) -> topaltR Any zs

deach f xs =
    case pop xs of
      Nothing -> True
      Just (y,ys) -> f y && deach f ys

leven (LSpine _ _ xs ys) =
    case pop ys of
      Nothing -> deach reven xs
      Just _ -> False
reven (RSpine _ ys xs _) =
    case pop ys of
      Nothing -> deach leven xs
      Just _ -> False

seject xs ys =
    case eject ys of
      Nothing -> 
          case eject xs of
            Nothing -> Nothing
            Just (zs,z) -> Just (zs,empty,z)
      Just (zs,L0 z) -> 
          case eject z of
            Nothing -> seject xs zs
            Just (ps,p) -> Just (xs,inject zs (L0 ps),p)
      Just (zs,L2 z1 z2 z) -> 
          case eject z of
            Nothing -> 
                case eject zs of
                  Nothing -> Just (inject xs z1,empty,z2)
                  Just (ps, L0 p) -> Just (xs, inject ps (L0 (inject p z1)), z2)
                  Just (ps, L2 p1 p2 p) -> Just (xs, inject ps (L2 p1 p2 (inject p z1)), z2)
            Just (ps,p) -> Just (xs,inject zs (L2 z1 z2 ps),p)

sejectR xs ys =
    case eject ys of
      Nothing -> 
          case eject xs of
            Nothing -> Nothing
            Just (zs,z) -> Just (zs,empty,z)
      Just (zs,R0 z) -> 
          case eject z of
            Nothing -> sejectR xs zs
            Just (ps,p) -> Just (xs,inject zs (R0 ps),p)
      Just (zs,R2 z z1 z2) -> 
          case eject z of
            Nothing -> 
                case eject zs of
                  Nothing -> Just (inject xs z1,empty,z2)
                  Just (ps, R0 p) -> Just (xs, inject ps (R0 (inject p z1)), z2)
                  Just (ps, R2 p p1 p2) -> Just (xs, inject ps (R2 (inject p z1) p1 p2), z2)
            Just (ps,p) -> Just (xs,inject zs (R2 ps z1 z2),p)

seach f xs ys =
    deach f xs &&
    case pop ys of
      Nothing -> True
      Just (L0 z,zs) -> seach f z zs
      Just (L2 z1 z2 z,zs) -> f z1 && f z2 && seach f z zs

seachR f xs ys =
    deach f xs &&
    case pop ys of
      Nothing -> True
      Just (R0 z,zs) -> seachR f z zs
      Just (R2 z z1 z2,zs) -> f z1 && f z2 && seachR f z zs

perfectP Empty = True
perfectP (Full (LSpine a b xs ys)) =
    case seject xs ys of
      Nothing -> True
      Just (ps,qs,RSpine _ ss rs _) -> 
          seach reven ps qs &&
          seachR leven rs ss

-- middle trees perfect
