{-# LANGUAGE StandaloneDeriving #-}

module Divisible where

import Deque


-- Necessary? Maybe no cntr type
data Leven dq midl rite = L0 (dq rite)
                        | L2 midl rite (dq rite)
data Reven dq left midl = R0 (dq left)
                        | R2 (dq left) left midl

instance (Deque dq, Show midl, Show rite) => Show (Leven dq midl rite) where
    show (L0 x) = "(L0 "++(showDeque x)++")"
    show (L2 x y z) = "(L2 ("++(show x)++") "++(show y)++" "++(showDeque z)++")"

instance (Deque dq, Show midl, Show left) => Show (Reven dq left midl) where
    show (R0 x) = "(R0 "++(showDeque x)++")"
    show (R2 x y z) = "(R2 "++(showDeque x)++" "++(show y)++" ("++(show z)++"))"

data LSpine d a = LSpine a (d (RSpine d a)) (d (Leven d (Spine d a) (RSpine d a)))
data RSpine d a = RSpine (d (Reven d (LSpine d a) (Spine d a))) (d (LSpine d a)) a

instance (Show a, Deque d) => Show (LSpine d a) where
    show (LSpine x ys zs) = "(LSpine "++(show x)++" "++(showDeque ys)++" "++(showDeque zs)++")"

instance (Show a,Deque d) => Show (RSpine d a) where
    show (RSpine xs ys z) = "(RSpine "++(showDeque xs)++" "++(showDeque ys)++" "++(show z)++")"

showDeque xs = show $ dequeToList xs
dequeToList xs = 
    case pop xs of
      Nothing -> []
      Just (y,ys) -> y : (dequeToList ys)

data Spine d a = Empty
               | Single a
               | More (LSpine d a) (Spine d a) (RSpine d a) deriving (Show)

divide Empty = (Empty,Empty)
divide (Single x) = (Single x,Empty)
divide (More l Empty r) = (ltoc l, rtoc r)
divide (More l (Single c) r) =
    let l' = get1l l
    in (More l Empty (RSpine empty empty c), rtoc r)
{-
divide (More l (More a b c) r) =
    let abc = ctor a b c
    in (More l Empty abc,r)

ctor a b (RSpine cs ds e) =
-}    

ltoc (LSpine a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of
            Nothing -> Single a
            Just (bs',b) -> More (LSpine a bs' empty) Empty b
      Just (cs',L0 c) ->
          case eject c of
            Nothing -> ltoc (LSpine a bs cs')
            Just (ds,d) -> More (LSpine a bs (inject cs' (L0 ds))) Empty d
      Just (cs',L2 c1 c2 c) ->
          case eject c of
            Nothing -> More (LSpine a bs cs') c1 c2
            Just (ds,d) -> More (LSpine a bs (inject cs' (L2 c1 c2 ds))) Empty d

rtoc (RSpine as bs c) =      
    case pop as of
      Nothing ->
          case pop bs of
            Nothing -> Single c
            Just (b,bs') -> More b Empty (RSpine empty bs' c)
      Just (R0 a,as') ->
          case pop a of
            Nothing -> rtoc (RSpine as' bs c)
            Just (z,zs) -> More z Empty (RSpine (push (R0 zs) as') bs c)
      Just (R2 a a1 a2,as') ->
          case pop a of
            Nothing -> More a1 a2 (RSpine as' bs c)
            Just (z,zs) -> More z Empty (RSpine (push (R2 zs a1 a2) as') bs c)


data Opt a = None
           | Some a deriving (Show)


{-
divide (More (LSpine a bs cs) ds (RSpine es fs g)) =
    case 
-}
{-
data Div d a = Spine (Spine d a)
             | Single a deriving (Show)
-}

-- TODO: Maybe bit at end?

get1l (LSpine p q r) = 
    case (pop q, pop r) of
      (Nothing,Nothing) -> p
      _ -> error "LSpine too big"
get1r (RSpine p q r) = 
    case (pop p, pop q) of
      (Nothing,Nothing) -> r
      _ -> error "RSpine too big"
{-
get1c (Dem p) = get1l p
get1c (Gop p) = get1r p
-}                            

npush x Empty = Single x 
npush x (Single y) = More (LSpine x empty empty) Empty (RSpine empty empty y) 
npush x (More (LSpine a bs cs) cn rs) =
    case pop bs of
      Just (b',bs') -> More (LSpine x empty (push (L2 (Single a) b' bs') cs)) cn rs 
      Nothing ->
          case pop cs of
            Just (L0 cs1,cs2) -> More (LSpine x (push (RSpine empty empty a) cs1) cs2) cn rs
            Just (L2 _ _ _,_) -> error "npush 2-exposed"
            Nothing -> 
                case cn of
                  Empty -> More (LSpine x empty empty) (Single a) rs {-
                  Some cn' ->
                        let cx = get1c cn'
                            rx = get1r rs
                        in More (LSpine x (push (RSpine empty empty a) empty) empty) None (RSpine empty (inject empty (LSpine cx empty empty)) rx)

-}

{-
mpush xy bs cs cn rs =
    case pop bs of
      Just (b',bs') -> (empty,push (L2 (Gop xy) b' bs') cs,cn,rs)
      Nothing ->
          case pop cs of
            Just (L0 cs1,cs2) -> (push xy cs1, cs2, cn, rs)
            Just (L2 _ _ _,_) -> error "npush 2-exposed"
            Nothing -> 
                case cn of
                  None -> (empty,empty,Some (Gop xy),rs) -} {-
                  Some cn' ->
                        let cx = get1c cn'
                            rx = get1r rs
                        in More (LSpine x (push xy empty) empty) None (RSpine empty (inject empty (LSpine cx empty empty)) rx) -}
    

{-
prefix0 x@(LSpine a bs cs) =
    case pop cs of
      Just (L2 c d es,fs) ->
      _ -> x
  
-}    

{-
--lrlcomb :: LSpine d a -> RSpine d a -> LSpine d a
lrlcomb (LSpine x y z) r = 
    case eject z of
      Nothing -> LSpine x (inject y r) empty
      Just (zs,L0 w) -> LSpine x y (zs `inject` (L0 (w `inject` r)))
      Just (zs,L2 p q w) -> LSpine x y (zs `inject` (L2 p q (w `inject` r)))

lrrcomb l (RSpine z y x) = 
    case pop z of
      Nothing -> RSpine empty (push l y) x
      Just (R0 w,zs) -> RSpine (push (R0 (push l w)) zs) y x
      Just (R2 w p q,zs) -> RSpine (push (R2 (push l w) p q) zs) y x
          
ltor (LSpine x y z) =
    case eject z of
      Nothing ->
          case eject y of
            Nothing -> RSpine empty empty x
            Just (rs,r) -> lrrcomb (LSpine x rs empty) r
      Just (rs,L0 r) -> 
          case eject r of
            Nothing -> ltor (LSpine x y rs) --error "ends in 0 error 1"
            Just (ss,s) -> 
                case pop ss of
                  Nothing -> lrrcomb (LSpine x y rs) s 
                  _ -> lrrcomb (LSpine x y (rs `inject` (L0 ss))) s
      Just (rs,L2 p q r) -> 
          case eject r of
            Nothing -> 
                larrcomb (LSpine x y rs
                let RSpine qc qb qa = q
                in case pop qc of
                     


ltor (LSpine x y rs)
            Just (ss,s) -> 
                case pop ss of
                  Nothing -> lrrcomb (LSpine x y rs) s
                  _ -> lrrcomb (LSpine x y (rs `inject` (L0 ss))) s
-}