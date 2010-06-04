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
    show (L2 x y z) = "(L2 "++(show x)++" "++(show y)++" "++(showDeque z)++")"

instance (Deque dq, Show midl, Show left) => Show (Reven dq left midl) where
    show (R0 x) = "(R0 "++(showDeque x)++")"
    show (R2 x y z) = "(R2 "++(showDeque x)++" "++(show y)++" "++(show z)++")"

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

data Spine d a = Dem (LSpine d a) 
               | Gop (RSpine d a) deriving (Show)

data Opt a = None
           | Some a deriving (Show)

data Div d a = Empty
             | Single a
             | More (LSpine d a) (Opt (Spine d a)) (RSpine d a) deriving (Show)
-- TODO: Maybe bit at end?

npush x Empty = Single x
npush x (Single y) = More (LSpine x empty empty) None (RSpine empty empty y)
npush x (More (LSpine a bs cs) cn rs) =
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> 
                case cn of
                  None -> More (LSpine x empty empty) (Some (Dem (LSpine a empty empty))) rs
                  Some cn' ->
                        let get1l (LSpine p q r) = 
                                case (pop q, pop r) of
                                  (Nothing,Nothing) -> p
                                  _ -> error "npush: LSpine too big"
                            get1r (RSpine p q r) = 
                                case (pop p, pop q) of
                                  (Nothing,Nothing) -> r
                                  _ -> error "npush: RSpine too big"
                            get1c (Dem p) = get1l p
                            get1c (Gop p) = get1r p
                            cx = get1c cn'
                            rx = get1r rs
                        in More (LSpine x (push (RSpine empty empty a) empty) empty) None (RSpine empty (inject empty (LSpine cx empty empty)) rx)
            Just (L0 cs1,cs2) -> More (LSpine x (push (RSpine empty empty a) cs1) cs2) cn rs
            Just (L2 _ _ _,_) -> error "npush 2-exposed"
      Just (b',bs') -> More (LSpine x empty (push (L2 (Gop (RSpine empty empty a)) b' bs') cs)) cn rs

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