Set Implicit Arguments.
(*Set Maximal Implicit Insertion.*)
(*Set Contextual Implicit.*)
(*Unset Strict Implicit.*)

Inductive Both t := Two : t -> t -> Both t.

Inductive MStack a : Type -> Type :=
  M0 : MStack a a
| MS : forall b, a -> a -> MStack (Both a) b -> MStack a b.

Set Maximal Implicit Insertion.
Implicit Arguments M0 [a].
Implicit Arguments MS [a b].
Unset Maximal Implicit Insertion.


Inductive Buffer a := 
  B0
| B1: a -> Buffer a
| B2: a -> a -> Buffer a.

Inductive Stuck a b :=
  Stack :  Buffer a -> Buffer a -> MStack (Both a) b -> Stuck a b.

Inductive Nest f a : Type -> Type :=
  Empty : Nest f a a
| Full : forall b c, f a b -> Nest f b c -> Nest f a c.

Set Maximal Implicit Insertion.
Implicit Arguments Empty [f a].
Implicit Arguments Full [f a b c].
Unset Maximal Implicit Insertion.

Inductive SE f a c :=
  NE : forall b, f a b -> Nest f b c -> SE f a c.

Set Maximal Implicit Insertion.
Implicit Arguments NE [f a b c].
Unset Maximal Implicit Insertion.

Definition StackStack := SE Stuck.

Definition ThreeStack := Nest StackStack.

Inductive SM a :=
  None
| Some : a -> SM a.

Set Maximal Implicit Insertion.
Implicit Arguments None [a].
Unset Maximal Implicit Insertion.

Inductive Deq a :=
 Deque : forall b c, MStack a b -> ThreeStack b c -> SM c -> Deq a.

Inductive Size := Small | Medium | Large.

Definition bufSize t (x:Buffer t) :=
  match x with
    | B0 => Small
    | B1 _ => Medium
    | B2 _ _ => Large
  end.

Definition sameSize x y :=
  match x,y with
    | Small,Small => true
    | Large,Large => true
    | _,_ => false
  end.

Definition nextSize x y :=
  match y with
    | Medium => x
    | _ => y
  end.

Definition SameSize x y :=
  match x,y with
    | Small,Small => True
    | Large,Large => True
    | _,_ => False
  end.

(*
Inductive BufsAltStart (xs ys:Size) 
  : forall a b, ThreeStack a b -> Prop :=
    Stop : forall a, BufsAltStart xs ys (Empty _ a)
  | Bit : forall t (x y:Buffer t) s u (r:ThreeStack s u) z, 
    ~(SameSize xs (bufSize x)) ->
    ~(SameSize ys (bufSize y)) ->
    BufsAltStart (nextSize xs (bufSize x))
                 (nextSize ys (bufSize y))
                 r ->
    BufsAltStart xs ys (Full _ (NE _ (Stack x y z) (Empty _ _)) r)
  | Go : forall t (x y:Buffer t) za (q:MStack (Both t) za) zb (z:Stuck za zb) zc (zs:Nest Stuck zb zc) zd (r:ThreeStack zc zd), 
    ~(SameSize xs (bufSize x)) ->
    ~(SameSize ys (bufSize y)) ->
    BufsAltStart (nextSize xs (bufSize x))
                 (nextSize ys (bufSize y))
                 (Full _ (@NE Stuck za zc zb z zs) r) ->
    BufsAltStart xs ys (Full _ (NE _ (Stack x y q) (Full za z zs)) r).
*)


Ltac cutThis x :=
  let xx := fresh
    in remember x as xx; destruct xx.

Inductive Top := Prefix | Suffix | Twofix.

Ltac crush := subst; (*unfold not;*) intros;
  simpl in *; auto; subst; simpl in *; auto; subst;
    match goal with
      | [H:True |- _] => clear H; crush
      | [H:~ False |- _] => clear H; crush
      | [H:?x = ?x |- _] => clear H; crush
      | [F:False |- _] => inversion F
      | [H:?x = ?x -> False |- _] 
        => pose (H (@eq_refl _ x)); crush
      | [H:?x <> ?x |- _] 
        => pose (H (@eq_refl _ x)); crush
      | [H:Some _ = ?x 
        |- context[
          match ?x with 
            | None => _ 
            | Some _ => _
          end]]
        => rewrite <- H; crush
      | [H:true = ?x 
        |- context[if ?x then _ else _]]
        => rewrite <- H; crush
      | [H:false = ?x 
        |- context[if ?x then _ else _]]
        => rewrite <- H; crush
      | [H:false = true |- _] => inversion H
      | [H:true = false |- _] => inversion H
      | [H: _ /\ _ |- _] => destruct H; crush
      | [|- _ /\ _ ] => split; crush
      | [H: _ \/ _ |- _] => destruct H; crush
      | [H: None = Some _ |- _] => inversion H
      | [H: Some _ = None |- _] => inversion H
      | [H: Some ?x = Some ?y |- _] 
        => assert (x = y); inversion H; clear H; crush
      | [H: Suffix = Prefix |- _] => inversion H
      | [H: Prefix = Suffix |- _] => inversion H
      | [H : None = ?x,
         I : Some _ = ?x |- _] 
        => rewrite <- I in H; crush
      | [H : Some _ = ?x,
         I : Some _ = ?x |- _] 
        => rewrite <- I in H; inversion H
      | [H: Small = Medium |- _] => inversion H
      | [H: Large = Medium |- _] => inversion H
      | [H: Medium = Small |- _] => inversion H
      | [H: Medium = Large |- _] => inversion H
      | [H: Large = Small |- _] => inversion H
      | [H: Small = Large |- _] => inversion H
      | [|- Small <> Medium] => discriminate
      | [|- Small <> Large] => discriminate
      | [|- Large <> Medium] => discriminate
      | [|- Medium <> Large] => discriminate
      | [|- Medium <> Small] => discriminate
      | [|- Large <> Small] => discriminate
      | [|- Some _ <> None] => discriminate
      | [|- None <> Some _] => discriminate
      | [|- Some _ <> Some _] => discriminate; crush
      | [|- Some _ = Some _] => f_equal; crush
      | [|- pair _ _ = pair _ _] => f_equal; crush      
      | [H: ~ True |- _] => 
        let J := fresh
          in pose (H I) as J; inversion J
      | [H:(?x,?y) = (?p,?q) |- _] =>
        inversion_clear H; crush
      | _ => idtac
    end.


Fixpoint bufsAltStart2 a b (m:Stuck a b) c d (n:Nest Stuck c d) (*d e (r:ThreeStack d e) *) (xs ys:Size) :=
  match m with
    | Stack x y _ =>
      let xs' := bufSize x in
        let ys' := bufSize y in
          match sameSize xs xs', sameSize ys ys' with
            | false,false =>
              let xs2 := nextSize xs xs' in
                let ys2 := nextSize ys ys' in
                  match n with
                    | Empty => Some (xs2,ys2)
                    | Full _ _ z zs => bufsAltStart2 z zs xs2 ys2
                  end
            | _,_ => None
          end
  end.


Ltac equate x y :=
  let H := fresh "H" in
    assert (H : x = y); [ reflexivity | clear H ].

Ltac crush1 :=
  crush;
  match goal with
    | [_:context[
      match topCheck ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (topCheck x y); desall
    | [_:context[
      match bufSize ?x with
        | Small => _
        | Medium => _
        | Large => _
      end] |- _]
      => cutThis x; desall
    | [|- context[
      match topCheck ?x ?y with
        | None => _
        | Some _ => _
      end]]
      => cutThis (topCheck x y); desall
    | [_:context[if nextTop1 ?x ?y then _ else _] |- _]
      => cutThis (nextTop1 x y); desall
    | [|- context[if nextTop1 ?x ?y then _ else _]]
      => cutThis (nextTop1 x y); desall
    | [|- context[if sameSize ?x ?y then _ else _]]
      => cutThis (sameSize x y); desall
    | [_: context[if sameSize ?x ?y then _ else _] |- _]
      => cutThis (sameSize x y); desall
    | [_:context[
      match top2' ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (top2' x y); desall
    | [_:context[
      match top3 ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (top3 x y); desall
    | [|- context[
      match top3 ?x ?y with
        | None => _
        | Some _ => _
      end]]
      => cutThis (top3 x y); desall
    | [ H:_ |- context[
      match ?x with
        | None => _
        | Some _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x in MStack _ _ return _ with
        | M0 => _
        | MS _ _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x in Nest _ _ _ return _ with
        | Empty => _
        | Full _ _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | NE _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | Stack _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | Stack _ _ _ => _
      end] |- _] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | B0 => _
        | B1 _ => _
        | B2 _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | Prefix => _
        | Suffix => _
        | Twofix => _
      end]] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | Prefix => _
        | Suffix => _
        | Twofix => _
      end] |- _] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | B0 => _
        | B1 _ => _
        | B2 _ _ => _
      end] |- _] => equate H x; cutThis x; desall
    | [|- context[
      match bufsAltStart2 ?p ?q ?r ?s with
        | None => _
        | Some _ => _
      end]]
      => cutThis (bufsAltStart2 p q r s); desall
    | _ => idtac
  end.


Lemma medPreNone :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) q p,
    None = bufsAltStart2 x y Medium p ->
    None = bufsAltStart2 x y q p.
Proof.
  induction y; crush.

  Ltac crush1 :=
    crush;
    match goal with
      | [|- None = match x with
                     | Stack _ _ _ => _


  destruct x; crush.
  destruct p; destruct q; destruct b0; destruct b; crush.
  destruct x; crush.
  destruct p; destruct q; destruct b0; destruct b1; crush.
Qed.
Hint Resolve medPreNone.

Lemma medPreSomeExt :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) p n q,
    q <> Medium ->
    Some (Medium,n) <> bufsAltStart2 x y q p.
Proof.
  induction y; crush.
  destruct x; crush.
  destruct q; destruct b; crush;
    destruct p; destruct b0; crush.
  destruct x; crush.
  destruct q; destruct b0; crush;
    destruct p; destruct b1; crush;
      try (eapply IHy; eauto); crush.
Qed.
Hint Resolve medPreSomeExt.

Lemma medPreSomeMed :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) p n q,
    Some (Medium,n) = bufsAltStart2 x y Medium p ->
    Some (q,n) = bufsAltStart2 x y q p.
Proof.
  induction y; crush.
  destruct x; crush.
  destruct p; destruct q; destruct b0; destruct b; crush.
  destruct x; crush.
  
  Ltac extMed :=
    crush;
    match goal with
      | [ H:Some (Medium,_) = bufsAltStart2 _ _ Small _ |- _]
        => assert False; apply medPreSomeExt in H; extMed
      | [ H:Some (Medium,_) = bufsAltStart2 _ _ Large _ |- _]
        => assert False; apply medPreSomeExt in H; extMed
      | _ => crush
    end.

  destruct p; destruct q; destruct b0; destruct b1; extMed.
Qed.
Hint Resolve medPreSomeMed.
    
Definition topCheck t (x y:Buffer t) :=
  match x,y with
    | B1 _, B1 _ => None
    | B0, B1 _ => Some Prefix
    | B2 _ _, B1 _ => Some Prefix
    | B1 _, B0 => Some Suffix
    | B1 _, B2 _ _ => Some Suffix
    | _,_ => Some Twofix
  end.

Definition top1 a b (z:Stuck a b) :=
  match z with
    | Stack x y _ => topCheck x y
  end.

Definition nextTop1 x y :=
  match x,y with
    | Prefix,Prefix => true
    | Suffix,Suffix => true
    | _,_ => false
  end.

Fixpoint top2' a b (x:Stuck a b) c d (yys:Nest Stuck c d) {struct yys} :=
  match yys with
    | Empty => top1 x
    | (Full _ _ y ys) => 
      match top1 x, top2' y ys with
        | Some v, Some w =>
          if nextTop1 v w
            then Some v
            else None
        | _,_ => None
      end
  end.


Lemma medPreSomeOth :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) p n r,
    r <> Medium ->
    Some (r,n) = bufsAltStart2 x y Medium p ->
    ((Some (r,n) = bufsAltStart2 x y Small p 
      /\ None = bufsAltStart2 x y Large p)
    \/ (Some (r,n) = bufsAltStart2 x y Large p 
      /\ None = bufsAltStart2 x y Small p)).
Proof.
  induction y; crush.
  destruct x; crush.
  destruct b; crush; destruct p; destruct b0; crush.
  destruct x; crush.
  destruct p; destruct b1; crush;
    destruct b0; crush.
Qed.
Hint Resolve medPreSomeOth.

Lemma extPreSomeSame :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) q p n,

    Some (q,n) = bufsAltStart2 x y q p ->
    (Some (Medium,n) = bufsAltStart2 x y Medium p \/
     Some (q,n) = bufsAltStart2 x y Medium p).
Proof.
  induction y; crush.
  destruct x; crush.
  destruct q; destruct b; crush; destruct p; destruct b0; crush.
  destruct x; crush.
  destruct q; destruct b0; crush; destruct p; destruct b1; crush.
Qed.
Hint Resolve extPreSomeSame.
  
Lemma extPreSomeMed :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) q p,
    None <> bufsAltStart2 x y q p ->
    None <> bufsAltStart2 x y Medium p.
Proof.
  induction y; crush.
  destruct x; crush.
  destruct q; destruct b; crush; destruct p; destruct b0; crush.
  destruct x; crush.
  destruct q; destruct b0; crush; destruct p; destruct b1; crush;
    try (eapply IHy in H; eauto); crush.
Qed.
Hint Resolve extPreSomeMed.

Lemma extPreSomeSame2 :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) q p n,
    q <> Medium ->
    Some (q,n) = bufsAltStart2 x y q p ->
    ((forall z, Some (z,n) = bufsAltStart2 x y z p) 
      \/ (Some (q,n) = bufsAltStart2 x y Medium p
        /\ forall r, r <> q -> r <> Medium -> 
          None = bufsAltStart2 x y r p)).
Proof.
  induction y; crush.
  destruct x; crush.
  destruct q; destruct b; crush; destruct p; destruct b0; crush;
    left; crush; destruct z; crush.
  destruct x; crush.
  cutThis (bufsAltStart2 f y (nextSize Medium (bufSize b0))
    (nextSize p (bufSize b1))); crush.
  left.
  destruct z; crush; 
    destruct q; destruct b0; crush; 
      destruct b1; destruct p; crush;
        eapply IHy in H0; crush.
  destruct q; destruct b0; crush;
    destruct p; destruct b1; crush;
      try (eapply IHy in H0); crush;
        try (abstract (left; crush; destruct z; crush));
          try (abstract (right; crush; destruct r; crush)).
Qed.
Hint Resolve extPreSomeSame2.

Require Import caseTactic.

Lemma extPreSomeOpp :
  forall 
    C D (y:Nest Stuck C D) 
    A B (x:Stuck A B) q p n r,
    r <> q ->
    Some (r,n) = bufsAltStart2 x y q p ->
    (Some (r,n) = bufsAltStart2 x y Medium p /\
     None = bufsAltStart2 x y r p).
Proof.
  induction y; crush;
    destruct x; crush.
  destruct p; crush; destruct b0; crush;
    destruct q; crush; destruct b; crush.
  destruct p; crush; destruct b0; crush;
    destruct q; crush; destruct b; crush.
  destruct p; crush; destruct b0; crush;
    destruct q; crush; destruct b1; crush;
      eapply IHy in H0; crush.
  destruct p; crush; destruct b0; crush;
    destruct q; crush; destruct b1; crush;
      pose H0 as hcopy;
        eapply IHy in hcopy; crush;
          destruct r; crush.
Abort.

Fixpoint bufsAltStart a b (r:ThreeStack a b) (xs ys:Size) :=
  match r with
    | Empty => True
    | Full _ _ (NE _ p ps) qs => 
      match bufsAltStart2 p ps xs ys with
        | None => False
        | Some (xs',ys') => bufsAltStart qs xs' ys'
      end
  end.

Definition BufsAlternate t (x:Deq t) :=
  match x with
    | Deque _ _ _ y _ => bufsAltStart y Medium Medium
  end.

Definition NextTop1 x y :=
  match x,y with
    | Prefix,Prefix => True
    | Suffix,Suffix => True
    | _,_ => False
  end.

Definition top2 a b (x:StackStack a b) :=
  match x with
    | NE _ p q => top2' p q
  end.

Fixpoint top3 a b (x:StackStack a b) d e (yys:ThreeStack d e) {struct yys} :=
  match yys with
    | Empty => top2 x
    | Full _ _ y ys => 
      match top2 x, top3 y ys with
        | Some v, Some w =>
          if nextTop1 v w
            then None
            else Some v
        | _,_ => None
      end
  end.

Definition topShape a b (x:ThreeStack a b) :=
  match x with
    | Empty => True
    | Full _ _ y ys => 
      match top3 y ys with
        | None => False
        | _ => True
      end
  end.
Hint Unfold topShape.

Definition allShape a (x:Deq a) :=
  match x with
    | Deque _ _ _ b _ => topShape b
  end.

Fixpoint lastPair2 (ans:Prop) (cont:Size->Size->Prop) a b (x:Stuck a b) c d (xs:Nest Stuck c d) :=
  match xs with
    | Empty => 
      match x with
        | Stack p q rs =>
          match rs with
            | M0 => cont (bufSize p) (bufSize q)
            | _ => cont Medium Medium
          end
      end
    | Full _ _ y ys => lastPair2 ans cont y ys
  end.

Fixpoint LastPair (ans:Prop) (cont:Size->Size->Prop) a b (x:ThreeStack a b)  :=
  match x with
    | Empty => ans
    | Full _ _ y ys =>
      match ys with
        | Empty =>
          match y with
            | NE _ z zs => lastPair2 ans cont z zs
          end
        | _ => LastPair ans cont ys
      end
  end.

Definition BottomSome x y :=
  match x,y with
    | Small,Small => False
    | _,_ => True
  end.

Definition BottomNone x y :=
  match x,y with
    | Small,Small => False
    | Small,_ => False
    | _,Small => False
    | _,_ => True
  end.

Definition BottomOK a (x:Deq a) :=
  match x with
    | Deque _ _ _ b (Some _) => LastPair True BottomSome b
    | Deque _ _ _ b None => LastPair True BottomNone b
  end.

Definition invariants a (x:Deq a) := BottomOK x /\ allShape x /\ BufsAlternate x.

Definition cons13 a (x y:Buffer a) b (xs:MStack (Both a) b) c (t:ThreeStack b c) : ThreeStack a c := 
    match t with
      | Empty => Full (NE (Stack x y xs) Empty) Empty
      | Full _ _ (NE _ (Stack p q pq) r) s => 
        let t' := Full (NE (Stack p q pq) r) s in
          let default := Full (NE (Stack x y xs) Empty) t' in 
        match topCheck x y, topCheck p q with
          | Some i, Some j => 
            if nextTop1 i j
              then Full (NE (Stack x y xs) (Full (Stack p q pq) r)) s
              else Full (NE (Stack x y xs) Empty) t'
          | _,_ => default
        end
    end.
Hint Unfold cons13.

Ltac equate x y :=
  let H := fresh "H" in
    assert (H : x = y); [ reflexivity | clear H ].

Ltac desall :=
  crush;
  match goal with
    | [_:context[
      match topCheck ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (topCheck x y); desall
    | [_:context[
      match bufSize ?x with
        | Small => _
        | Medium => _
        | Large => _
      end] |- _]
      => cutThis x; desall
    | [|- context[
      match topCheck ?x ?y with
        | None => _
        | Some _ => _
      end]]
      => cutThis (topCheck x y); desall
    | [_:context[if nextTop1 ?x ?y then _ else _] |- _]
      => cutThis (nextTop1 x y); desall
    | [|- context[if nextTop1 ?x ?y then _ else _]]
      => cutThis (nextTop1 x y); desall
    | [|- context[if sameSize ?x ?y then _ else _]]
      => cutThis (sameSize x y); desall
    | [_: context[if sameSize ?x ?y then _ else _] |- _]
      => cutThis (sameSize x y); desall
    | [_:context[
      match top2' ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (top2' x y); desall
    | [_:context[
      match top3 ?x ?y with
        | None => _
        | Some _ => _
      end] |- _]
      => cutThis (top3 x y); desall
    | [|- context[
      match top3 ?x ?y with
        | None => _
        | Some _ => _
      end]]
      => cutThis (top3 x y); desall
    | [ H:_ |- context[
      match ?x with
        | None => _
        | Some _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x in MStack _ _ return _ with
        | M0 => _
        | MS _ _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x in Nest _ _ _ return _ with
        | Empty => _
        | Full _ _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | NE _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | Stack _ _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | Stack _ _ _ => _
      end] |- _] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | B0 => _
        | B1 _ => _
        | B2 _ _ => _
      end]] => equate H x; cutThis x; desall
    | [ H:_ |- context[
      match ?x with
        | Prefix => _
        | Suffix => _
        | Twofix => _
      end]] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | Prefix => _
        | Suffix => _
        | Twofix => _
      end] |- _] => equate H x; cutThis x; desall
    | [ H:_,
        _:context[
      match ?x with
        | B0 => _
        | B1 _ => _
        | B2 _ _ => _
      end] |- _] => equate H x; cutThis x; desall
    | [|- context[
      match bufsAltStart2 ?p ?q ?r ?s with
        | None => _
        | Some _ => _
      end]]
      => cutThis (bufsAltStart2 p q r s); desall
    | _ => idtac
  end.


Lemma cons13shape : 
  forall a (x y:Buffer a)
    b (xs:MStack (Both a) b)
    c (t:ThreeStack b c)
    i,
    Some i = topCheck x y ->
    topShape t ->
    topShape (cons13 x y xs t).
Proof.
  Ltac ifneq x y t :=
    assert (x = y); [reflexivity|auto] || t.
  Ltac here3 := unfold cons13 in *; desall;
    match goal with
      | [_ : Some _ = top3 (NE (Stack ?a ?b _) ?f) ?e,
         _ : None = topCheck ?a ?b
         |- _] => destruct e; desall; destruct f; desall; here3
      | [_ : None = top3 (NE _ (Full (Stack ?a ?b _) ?f)) ?e,
         _ : Some _ = topCheck ?a ?b
         |- _] => destruct e; desall; destruct f; desall; here3
      | [_ : _ = nextTop1 ?a ?b 
         |- _] => destruct a; destruct b; desall; here3
      | [_ : Some ?d = top3 (NE (Stack ?a ?b _) ?f) ?e,
         _ : Some ?c = topCheck ?a ?b
         |- _] => 
      let thisone := destruct e; desall; destruct f; desall; here3
        in ifneq c d thisone      
      | _ => desall
    end.
  here3.
Qed.

Definition empty {a} := Deque M0 Empty (@None a).

Definition prepose' a b (x:ThreeStack a b) :=
  let default := Medium in 
    match x with
      | Empty => Medium
      | Full _ _ (NE _ (Stack B0 _ _) _) _ => Small
      | Full _ _ (NE _ (Stack (B2 _ _) _ _) _) _ => Large
      | _ => default
    end.

Definition prepose a (x:Deq a) :=
  match x with
    | Deque _ _ _ (Full _ _ (NE _ (Stack (B1 _) _ _) _) x) _ => prepose' x
    | Deque _ _ _ x _ => prepose' x
  end.

(*
Definition npushHelp a (x:a) (xx:Deq a) : Deq a.
intros.
destruct xx.
destruct m. destruct t. destruct s.
eapply Deque. apply M0. apply Empty. apply Some. exact x.
eapply Deque. apply MS. exact x. exact a0. apply M0. apply Empty. apply None.
apply empty.
apply empty.
Defined.

Print npushHelp.
*)

Ltac sizeSplit t :=
  here3; eauto;
    match goal with
      | [_ : _ = sameSize ?a _,
        b : Size |- _]
        => equate a b; destruct a; sizeSplit t
      | [_ : _ = sameSize _ (bufSize ?a),
        b : Buffer _ |- _]
        => equate a b; destruct a; sizeSplit t
      | [|- Some _ <> None] => discriminate
      | [|- Some _ <> Some _] => discriminate
      | _ => let foo := eapply t; here3 in try (abstract foo)
    end.

Ltac nextSize t :=
  sizeSplit t;
  match goal with
    | [|- Some _ = Some _] => f_equal; nextSize t
    | [_: _ = nextSize Medium (bufSize ?b) |- _]
        => destruct b; nextSize t
    | [H : Some (Medium,_) = bufsAltStart2 _ _ Small _ |- _]
        => eapply medPreSomeExt in H; nextSize t
    | [H : Some (Medium,_) = bufsAltStart2 _ _ Large _ |- _]
        => eapply medPreSomeExt in H; nextSize t
    | _ => auto
  end.

  Ltac topFix' t :=
    nextSize t;
    match goal with
      | [_:Some Suffix = top2' (Stack (B2 _ _) _ _) ?a ,
         A:_ |- _]
        => equate A a; assert False; destruct a; topFix' t
      | [_:Some Suffix = top2' (Stack (@B0 _) _ _) ?a ,
         A:_ |- _]
        => equate A a; assert False; destruct a; topFix' t
      | _ => nextSize t
    end.
  Ltac topFix t :=
    topFix' t;
    match goal with
      | _ => let foo := eapply t; eauto; topFix' t in try (abstract foo)
    end.

(*
Lemma startExt :
  forall A B C D (f:Stuck A B) (N:Nest Stuck C D)
    p w,
    p <> Medium ->
    forall z,
      Some (Medium,z) <> bufsAltStart2 f N p w.
Proof.
  
  intros A B C D f N.
  
  
  generalize dependent A;
    generalize dependent B.
  
  induction N; sizeSplit IHN.
Qed.
Hint Resolve startExt.
*)

(*  
Lemma bufsAlt2PreExtNone : 
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    None = bufsAltStart2 M N Medium w ->
    forall p, None = bufsAltStart2 M N p w.
Proof.
  induction N; sizeSplit IHN.
Qed.
Hint Resolve bufsAlt2PreExtNone.

Lemma bufsAlt2PreExtSoMed : 
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall d, Some (Medium,d) = bufsAltStart2 M N Medium w ->
    forall p, Some (p,d) = bufsAltStart2 M N p w.
Proof.
  Print nextSize.

  induction N; nextSize IHN.
Qed.
Hint Resolve bufsAlt2PreExtSoMed.
*)


Lemma bufsAlt2PreExtSoExt : 
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall c, 
      c <> Medium ->
      forall d, 
        Some (c,d) = bufsAltStart2 M N Medium w ->
        Medium = prepose' (Full (NE M N) Empty) ->
        topShape (Full (NE M N) Empty) ->
        False.
Proof.
  induction N; topFix IHN.
Qed.
Hint Resolve bufsAlt2PreExtSoExt.
  
Ltac ese t :=
    topFix t;
    match goal with
      | [_:?c <> Medium,
         _:Some (?c,_) = bufsAltStart2 _ _ Medium _ |- False]
        => eapply bufsAlt2PreExtSoExt; eauto; ese t
      | _ => let foo := eapply t; eauto; topFix t in try (abstract foo)
    end.

Lemma bufsAlt2PreExtSoExtExt : 
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall c, 
      c <> Medium ->
      forall d, 
        Some (c,d) = bufsAltStart2 M N Medium w ->
        match prepose' (Full (NE M N) Empty) with
          | Medium => topShape (Full (NE M N) Empty) -> False
          | Small => Some (c,d) = bufsAltStart2 M N Large w
          | Large => Some (c,d) = bufsAltStart2 M N Small w
        end.
Proof.

  induction N; ese IHN.
Qed.
Hint Resolve bufsAlt2PreExtSoExtExt.

Lemma bufsAlt2PreExtSoMedMed :
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall c, 
      c <> Medium ->
      forall d, 
        Some (c,d) = bufsAltStart2 M N Medium w ->
        Medium = prepose' (Full (NE M N) Empty) ->
        topShape (Full (NE M N) Empty) -> False.
Proof.
  eauto.
Qed.
Hint Resolve bufsAlt2PreExtSoMedMed.

Lemma bufsAlt2PreExtSoMedBig :
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall c, 
      c <> Medium ->
      forall d, 
        Some (c,d) = bufsAltStart2 M N Medium w ->
        Small = prepose' (Full (NE M N) Empty) ->
        Some (c,d) = bufsAltStart2 M N Large w.
Proof.
  intros.
  eapply bufsAlt2PreExtSoExtExt in H0; eauto.
  rewrite <- H1 in H0. auto.
Qed.
Hint Resolve bufsAlt2PreExtSoMedBig.

Lemma bufsAlt2PreExtSoMedSml :
  forall 
    B C (N:Nest Stuck B C)
    A (M:Stuck A B) w,
    forall c, 
      c <> Medium ->
      forall d, 
        Some (c,d) = bufsAltStart2 M N Medium w ->
        Large = prepose' (Full (NE M N) Empty) ->
        Some (c,d) = bufsAltStart2 M N Small w.
Proof.
  intros.
  eapply bufsAlt2PreExtSoExtExt in H0; eauto.
  rewrite <- H1 in H0. auto.
Qed.
Hint Resolve bufsAlt2PreExtSoMedSml.



(*
Lemma bufsAltPreExt :
  forall a b (t:ThreeStack a b) p q,
    topShape t ->
    prepose' t <> p ->
    bufsAltStart t Medium q ->
    bufsAltStart t p q.
Proof.



  Ltac badMatch t :=
    ese t;
    match goal with
      | [_:Some _ = top3 (NE ?a ?b) _,
         _:None = bufsAltStart2 ?a ?b _ _,
         B:_ |- _]
        => equate B b; destruct b; badMatch t
      | [J:match ?a with
             | None => False
             | Some _ => _
           end,
         I:None = ?a |- _]
        => rewrite <- I in J; assert False; badMatch t
      | [J:match ?a with
             | None => _
             | Some _ => _
           end,
         I:Some _ = ?a |- _]
        => rewrite <- I in J; badMatch t
      | [|- let 'pair _ _ := ?b in _] => destruct b; badMatch t
      | [_:Some _ = top3 (NE (Stack (B1 _) (B1 _) _) (Full ?a ?b)) ?c,
        _:None = bufsAltStart2 ?a ?b _ _,
        A:_,
        B:_,
        C:_
        |- False]
        => equate A a; equate B b; equate C c;
        destruct a; destruct b; destruct c; badMatch t
      | _ => let foo := eapply t; eauto; ese t in try (abstract foo)
    end.
  induction t; badMatch IHt.
  
  Focus 3.
  cutThis (bufsAltStart2 s n Medium Large); desall.
  destruct p; desall.
  erewrite <- bufsAlt2PreExtSoMedBig in HeqH.
  Focus 4. destruct s; destruct n; destruct t; desall.

rewrite

  destruct t0.
  destruct t; desall.
  destruct t; desall. Print bufsAltStart2.
  destruct s; desall. Print bufsAltStart2.
  destruct n; desall.

  Focus 2.

  Focus 3.
  destruct n; destruct s; destruct t; badMatch IHt. 
  destruct s0; destruct n; badMatch IHt.
  cutThis (bufsAltStart2 s n Medium Large); badMatch IHt.
  destruct p. destruct s0; badMatch IHt.
  erewrite <- bufsAlt2PreExtSoMedBig in HeqH.
  Focus 3. eauto. Focus 4. badMatch IHt.
  Focus 4. destruct s; destruct n; badMatch IHt.
  destruct s; destruct n; badMatch IHt.

  Focus 2.

  destruct n; destruct s; destruct t; badMatch IHt. 

  destruct s0; destruct n; badMatch IHt.


Unfocus.
  


  Lemma matchLetPair :
    forall (t:Type) (x:prod t t),
      let (a,b) := x in a = b.
  Proof.
  Ltac noMatch :=
    match goal with
      | [|- let (_,_) := ?p in _]
        => destruct p
      | [|- match ?p with
              | pair _ _ => _
            end]
        => destruct p
    end.

  noMatch.
      

  Ltac uh :=
    match goal with
      | [|- let (pair ?xs' ?ys') := ?p0 in bufsAltStart ?t ?xs' ?ys'] 
        => destruct p0
    end.
  Locate "(_,_)".
  Print pair.

  destruct p0.
  destruct p; desall.
  badMatch t.
  eapply IHt.
  desall.

; topFix IHt.

ese IHt.
  destruct n; badMatch IHt.

  
  
  


  destruct p0. 
  destruct t; simpl in *; auto.
  destruct s1; simpl in *.

eapply IHt.
  destruct n;  badMatch IHt.

  destruct t; destruct n; badMatch IHt.


  destruct p; ese IHt.



  desall.
  intros; simpl in *.
  destruct f; simpl in *.
  cutThis (bufsAltStart2 s n Medium q); simpl in *.
  desall.
  destruct p0; simpl in *.
  destruct s0; simpl in *.

  apply bufsAlt2PreExtSoExtExt in HeqH2.
  desall. destruct t; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall; 
    destruct p; desall;
      destruct q; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall; 
    destruct p; desall;
      destruct q; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct p0; desall. eapply IHt; desall.
  destruct t; desall. 
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.
  destruct t; destruct n; desall.

  cutThis (prepose' (Full (NE s n) Empty)).
  

  

  Focus 2.
  eapply bufsAlt2PreExtSoMed in HeqH2.
  rewrite <- HeqH2.
  eapply IHt; auto.
  destruct t; desall.
  desall; destruct t; desall.
  destruct s; simpl in *.
  destruct t; simpl in *.
  destruct n; destruct b1; simpl in *;
    destruct b2; simpl in *;
      destruct p; simpl in *; desall.
  destruct q; desall.

  Focus 2.

  destruct t; desall.
  destruct t; desall.
  destruct n


  induction t; desall.
  cutThis (bufsAltStart2 (Stack (B0 a) b2 m) n Medium q); desall; eauto.
  
  cutThis (bufsAltStart2 s n p q); desall;
    cutThis (bufsAltStart2 s n Medium q); desall.
  Focus 2.
  destruct p0. destruct p1.
  destruct s; simpl in *.
  fold (bufSize b1) in *.
  

  assert (
    bufSize b1 <> p ->
    match top3 (NE (Stack b1 b2 m) n) t with
      | None => True
      | Some _ => 
        bufsAltStart t s2 s3 ->
        bufsAltStart t s0 s1
    
  

  destruct s; destruct p; desall.
  cutThis (bufsAltStart2 (Stack (B1 a0) b2 m) n Medium q); desall.

  Ltac crr := 
    match goal with
      | [H:(?x = ?x) -> False |- _] 
        => pose (H (@eq_refl _ x))
    end.
  crr.




Lemma bufsAlt2PreExt : 
  forall (f:Size -> Size -> Prop) 
    A B (M:Stuck A B) 
    C (N:Nest Stuck B C) 
    E (R:ThreeStack C E) p w,
    (forall q z, (*prepose' R <> q*) (*q = p ->*) f Medium z -> f q z) ->
    topShape R ->
    topShape (Full (NE M N) R) ->
    prepose' (Full (NE M N) R) <> p ->
    bufsAltStart2 f M N R Medium w ->
    bufsAltStart2 f M N R p w.
Proof.
  intros f A B M C N.
  generalize dependent f; generalize dependent A.
  induction N; intros; desall;
    repeat split; desall;
      destruct p; desall.
  eapply IHN; desall.
  destruct R; desall;
    destruct f; desall.
  destruct f; desall;
    destruct R; desall;
      destruct N; desall.
  eapply IHN; desall.
  destruct R; desall;
    destruct N; desall.
  destruct f; desall;
    destruct R; desall;
      destruct N; desall.
Qed.

Lemma bufsAltPreExt :
  forall a b (t:ThreeStack a b) p q,
    topShape t ->
    prepose' t <> p ->
    bufsAltStart t Medium q ->
    bufsAltStart t p q.
Proof.
  induction t; intros; desall.
  destruct p; desall.
  eapply bufsAlt2PreExt; desall.
  eapply IHt; desall.
  destruct t; desall.
  destruct s; desall.
  destruct t; desall.
      destruct n; desall.
  

  destruct s; destruct p; desall; eapply IHt; desall;
    destruct t; desall.
  destruct s; desall.
  destruct s; desall.
  destruct n; desall.
  destruct
  des
  destruct s; desall.
*)  

(*
Lemma bufsAlt2PreExt : 
  forall (f:Size -> Size -> Prop) 
    A B (M:Stuck A B) 
    C (N:Nest Stuck B C) 
    E (R:ThreeStack C E) p w,
    (forall q z, (*prepose' R <> q -> *) f Medium z -> f q z) ->
    topShape R ->
    topShape (Full (NE M N) R) ->
    prepose' (Full (NE M N) R) <> p ->
    bufsAltStart2 f M N R Medium w ->
    bufsAltStart2 f M N R p w.
Proof.
  intros f A B M C N.
  generalize dependent f; generalize dependent A.
  induction N; intros; desall;
    repeat split; desall;
      destruct p; desall.
  eapply IHN; desall.
  destruct R; desall.
  destruct f; desall.
  destruct R; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct R; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct N; desall.
  destruct p; desall.
Qed.
*)

(*
  destruct b1; desall.
  destruct R; desall;
    destruct N; desall;
      destruct f; desall.
  
  destruct p; desall.
  destruct p; desall.
  destruct p; desall.
  



  eapply H; desall.
  destruct R; desall. 
  destruct s; desall.
  destruct s; desall.
  destruct R; desall.
  destruct n; desall.

  destruct p; desall.
  cutThis (prepose' R); desall.
  destruct R; desall.
  destruct w; destruct s; desall.
  destruct s; destruct R; desall.
  destruct n; desall.
  eapply H; desall.
  destruct p; desall.
  destruct p; desall.
  destruct p; desall.
  eapply IHN; desall.
  destruct f; desall.
  destruct p; desall.
  destruct p; desall.
  apply H; desall.
  destruct w; destruct p; destruct b0; desall.
  destruct p; desall.
  destruct w; destruct p; destruct b1; desall.
  destruct w; destruct p; destruct b1; desall.
  eapply IHN; desall.
  Focus 2.
  destruct w; destruct b1; desall.
  Unfocus.
  destruct w; destruct b1; desall.
  destruct f; destruct N; desall.


  destruct w; destruct p; destruct b1; desall.

  Print bufsAltStart2.
  destruct p; desall;
    destruct w; desall;
      destruct R; desall;
        destruct N; desall;
          repeat split; desall.
  apply H; crush.
  pose (H3 I). inversion f0.
  inversion H3.
  simpl in *.
  unfold not in *. crush.
  crush.
  unfold bufSize in *. desall. eapply H; auto.
  eapply H; eauto; desall. destruct b0; desall.

          destruct M; desall.

  assert (forall A B (C:ThreeStack A B),
    prepose' C <> Large ->
    forall z,
      z <> Medium ->
      bufsAltStart C Medium z ->
      bufsAltStart C Large z) as ans.

Lemma bufsAlt2PreMed : 
  forall 
    A B (M:Stuck A B) 
    C (N:Nest Stuck B C) p w
    X Y (t : ThreeStack X Y),
    (forall q r, bufsAltStart t q r -> bufsAltStart t Medium r) ->
    let ext := bufsAltStart2 M N p w in
      let med := bufsAltStart2 M N Medium w in
        match ext with
          | Some (a,b) =>
            match med with
              | None => False
              | Some (c,d) => 
                
                  bufsAltStart t a b -> 
                  bufsAltStart t c d
            end
          | _ => True
        end.
Proof.
  intros. generalize dependent w. generalize dependent A.
  generalize dependent p.
  induction N; desall.
  destruct w; destruct b; destruct b0; desall; eauto.
  destruct p0.
  destruct b0; desall.
  pose (IHN p _ f (nextSize w (bufSize b1))) as ans.
  rewrite <- HeqH2 in *.
  rewrite <- HeqH3 in *; desall.
  destruct p0; destruct p1; desall.
  destruct b0; desall; crush.
  pose (IHN p _ f (nextSize w (bufSize b1))) as ans.
  rewrite <- HeqH2 in *.
  rewrite <- HeqH3 in *; desall.
Qed.

Lemma bufsAltPreMedium :
  forall a b (t:ThreeStack a b) p q,
    bufsAltStart t p q ->
    bufsAltStart t Medium q.
Proof.
  induction t; desall.
  cutThis (bufsAltStart2 s n p q); desall.
  pose (bufsAlt2PreMed s n p q) as C.
  desall.
  rewrite <- HeqH0 in C.
  destruct p0; desall.
  rewrite <- HeqH1 in C. desall.
  eapply C; desall.
  eapply IHt. eauto.
  destruct p0.
  cutThis (bufsAltStart2 s n p q).
  pose (bufsAlt2PreMed s n p q) as C.
  desall.
  destruct p0.
  pose (bufsAlt2PreMed s n p q) as C. desall.
  rewrite <- HeqH0 in C.
  rewrite <- HeqH1 in C. desall.
Qed.
Hint Resolve bufsAltPreMedium.
*)

(*
npush :: a -> Deque a -> Deque a
npush x (Deque M0 Empty None) = Deque M0 Empty (Some x) 
npush x (Deque M0 Empty (Some y)) = Deque (MS x y M0) Empty None 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) Empty) xs) q) = Deque (MS x z zs) xs q 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) (Full y ys)) xs) q) = Deque (MS x z zs) (Full (NE y ys) xs) q 
npush x (Deque M0 (Full (NE (Stack B0 z zs) Empty) xs) q) = Deque M0 (cons13 (B1 x) z zs xs) q
*)
(*
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) Empty) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) xs) q
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) (Full r rs)) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) (Full (NE r rs) xs)) q
npush x (Deque (MS y z zs) rs q) = Deque M0 (cons13 (B2 x y) (B1 z) zs rs) q
*)

Definition npush a (x:a) (xx:Deq a) : Deq a :=
  let default := xx in
  match xx with
    | Deque _ _ b c d =>
      match b in MStack _ B return ThreeStack B _ -> Deq a with
        | M0 => fun cc =>
          match cc in Nest _ _ C return SM C -> Deq a with
            | Empty =>
              fun dd =>
              match dd with
                | None => Deque M0 Empty (Some x)
                | Some y => Deque (MS x y M0) Empty None
              end
            | Full _ _ e xs => fun dd => 
              match e with
                | NE _ f g =>
                  match f  with
                    | Stack B0 (B1 z) zs =>
                      match g in Nest _ _ G return Nest _ G _ -> Deq a with
                        | Empty => fun xsxs => Deque (MS x z zs) xsxs dd
                        | Full _ _ y ys => fun xsxs => Deque (MS x z zs) (Full (NE y ys) xsxs) dd
                      end xs
                    | Stack B0 z zs => 
                      match g in Nest _ _ G return Nest _ G _ -> Deq a with
                        | Empty => fun xsxs => Deque M0 (cons13 (B1 x) z zs xsxs) dd
                        | _ => fun _ => default
                      end xs
                    | Stack (B1 y) z zs =>
                      match g in Nest _ _ G return Nest _ G _ -> Deq a with
                        | Empty => fun xsxs => Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) xsxs) dd
                        | Full _ _ r rs => fun xsxs => Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) (Full (NE r rs) xsxs)) dd
                      end xs

                    | _ => default
                  end
              end
          end d
        | _ => fun _ => default
      end c
  end.


Lemma npushBottom : 
  forall a (x:a) xs,
    BottomOK xs ->
    BottomOK (npush x xs).
Proof.
  intros; destruct xs.
  ese H.


  Ltac badMatch t :=
    ese t;
    match goal with
      | [_:Some _ = top3 (NE ?a ?b) _,
         _:None = bufsAltStart2 ?a ?b _ _,
         B:_ |- _]
        => equate B b; destruct b; badMatch t
      | [J:match ?a with
             | None => False
             | Some _ => _
           end,
         I:None = ?a |- _]
        => rewrite <- I in J; assert False; badMatch t
      | [J:match ?a with
             | None => _
             | Some _ => _
           end,
         I:Some _ = ?a |- _]
        => rewrite <- I in J; badMatch t
      | [|- let 'pair _ _ := ?b in _] => destruct b; badMatch t
      | [_:Some _ = top3 (NE (Stack (B1 _) (B1 _) _) (Full ?a ?b)) ?c,
        _:None = bufsAltStart2 ?a ?b _ _,
        A:_,
        B:_,
        C:_
        |- False]
        => equate A a; equate B b; equate C c;
        destruct a; destruct b; destruct c; badMatch t
      | [_:match ?x with
             | Empty => _
             | Full _ _ _ _ => _
           end,
         X:_ |- _]
         => equate x X; destruct x; badMatch t
      | _ => let foo := eapply t; eauto; ese t in try (abstract foo)
    end.
  badMatch H.
  badMatch H.
Qed.

Lemma npushShape :
  forall a (x:a) xs,
    allShape xs ->
    allShape (npush x xs).
Proof.

  Ltac shapDes t :=
    badMatch t;
    match goal with
      | [_:Some _ = top3 _ ?x,
         X:_ |- topShape ?x]
         => equate X x; destruct x; shapDes t
      | [_:Some _ = top3 _ ?x,
         _:None = top3 _ ?x,
         X:_ |- False]
         => equate X x; destruct x; shapDes t
      | [_:Some ?a = top3 _ ?x,
         _:Some ?b = top3 _ ?x,
         X:_ |- False]
         => equate X x; 
         let t1 := destruct x; shapDes t
           in ifneq a b t1
      | _ => let foo := eapply t; eauto; badMatch t in try (abstract foo)
    end.

  destruct xs;
  shapDes H.
Qed.

Lemma npushSmallHelp : 
  forall A B (y:Nest Stuck A B) C (x:Stuck C A) p,
    match bufsAltStart2 x y Small p with
      | None => False
      | Some (pair _ _) => True
    end ->
    None = bufsAltStart2 x y Medium p ->
    Some Suffix = top2' x y ->
    False.
Proof.
  induction y; badMatch IHy.
Qed.
Hint Resolve npushSmallHelp.


Lemma npushSmallOth :
  forall E A (n0:Nest Stuck E A) 
    B F (s1 : Stuck F B) C D (H0 : Nest StackStack C D)  p,
    match bufsAltStart2 s1 n0 Small p with
      | None => False
      | Some (pair xs' ys') => bufsAltStart H0 xs' ys'
    end -> 
    None = bufsAltStart2 s1 n0 Medium p -> 
    False.
Proof.
  induction n0; badMatch IHn0.
Qed.
Hint Resolve npushSmallOth.


Lemma npushSmallThd :
  forall 
    B A (n0:Nest Stuck B A) 
     F (s1 : Stuck F B)  
     C D (H0 : Nest StackStack C D)
     s0 s2,
    Some Prefix = top3 (NE s1 n0) H0 ->
    match bufsAltStart2 s1 n0 Small Large with
      | None => False
      | Some (pair xs' ys') => bufsAltStart H0 xs' ys'
    end ->
    Some (s0, s2) = bufsAltStart2 s1 n0 Medium Large ->
    bufsAltStart H0 s0 s2.
Proof.
  induction n0; badMatch IHn0;
    induction H0; badMatch IHH0.
Qed.
Hint Resolve npushSmallThd.

Lemma npushSmall4 :
  forall 
    B A (n0:Nest Stuck B A) 
     F (s1 : Stuck F B)  
     C D (H0 : Nest StackStack C D)
     s0 s2,
    Some Twofix = top3 (NE s1 n0) H0 ->
    match bufsAltStart2 s1 n0 Small Large with
      | None => False
      | Some (pair xs' ys') => bufsAltStart H0 xs' ys'
    end ->
    Some (s0, s2) = bufsAltStart2 s1 n0 Medium Large ->
    bufsAltStart H0 s0 s2.
Proof.
  induction n0; badMatch IHn0;
    induction H0; badMatch IHH0.
Qed.
Hint Resolve npushSmall4.

(*
Lemma npushSmall5 :
  forall 
     C D (H0 : Nest StackStack C D)
     B A (n0:Nest Stuck B A) 
     G H (n : Nest Stuck G H)
     F (s1 : Stuck F B)  
     I (s0 : Stuck I G) p q,
     Some Prefix = top3 (NE s1 n0) H0 ->
     q <> Medium ->
     match bufsAltStart2 s0 n Small q with
       | None => False
       | Some (pair xs' ys') => 
         match bufsAltStart2 s1 n0 xs' ys' with
           | None => False
           | Some (pair xs'0 ys'0) => bufsAltStart H0 xs'0 ys'0
         end
     end ->
     Some p = bufsAltStart2 s0 n Medium q ->
     Some Suffix = top2' s0 n ->
     let (xs',ys') := p in 
       let (xs', ys') := p in
         match bufsAltStart2 s1 n0 xs' ys' with
           | None => False
           | Some (pair xs'0 ys'0) => bufsAltStart H0 xs'0 ys'0
         end.
Proof.
  
  intros.
  destruct p.
  cutThis (bufsAltStart2 s0 n Small q).
  induction n; badMatch IHn.
  destruct p.
  cutThis (bufsAltStart2 s1 n0 s3 s4).
  assert False; crush.
  destruct p.
  induction n0; desall.
  destruct b; destruct b0; destruct s3; destruct s4; 
    destruct H0; desall.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.
  badMatch m.

 badMatch IHn0.
  

  
  cutThis q.
  
  induction H0; badMatch IHH0.
  induction n0; badMatch IHn0.
  eapply IHn. eauto. Focus 2. eauto. badMatch IHn. eauto. eauto.
  eapply IHn. eauto. Focus 2. eauto. crush. eauto. auto.
Qed.
(*Hint Resolve npushSmall5.*)

(*  let (xs', ys') := p in
   match bufsAltStart2 s1 n0 xs' ys' with
   | None => False
   | Some (pair xs'0 ys'0) => bufsAltStart H0 xs'0 ys'0
   end
*)
*)

Lemma npushBufs :
  forall a (x:a) xs,
    prepose xs <> Large ->
    allShape xs ->
    BufsAlternate xs ->
    BufsAlternate (npush x xs).
Proof.
  intros.
  unfold BufsAlternate in *.
  destruct xs; simpl in *.
  destruct t; simpl in *.
  desall.

  desall.
  unfold cons13; desall.
  cutThis (bufsAltStart2 (Stack b2 b3 m0) n Small Small); crush.
  eapply medPreNone in HeqH1. rewrite <- HeqH1 in HeqH3; crush.
  destruct p.

  cutThis (bufsAltStart2 (Stack b2 b3 m0) n Small Small); crush.
  destruct p; crush.

  destruct s2; desall.
  pose HeqH3 as hh.
  eapply extPreSomeSame2 in hh. desall.
  pose HeqH1 as hh.
  rewrite <- H2 in hh. desall.
  destruct H0; desall.
  eapply medPreNone in HeqH0. 
  rewrite <- HeqH0 in H1; crush.
  destruct p; desall.


  cutThis (bufsAltStart2 s1 n0 Small s3); crush.
  destruct p; crush.
  destruct s0; desall.
  pose HeqH7 as hh.
  eapply extPreSomeSame2 in hh. desall.
  pose HeqH0 as hh.
  rewrite <- H3 in hh. desall. crush. crush.
  Check medPreNone.
  destruct H0; desall.
  cutThis (bufsAltStart2 s1 n0 Small s3); crush.
  destruct p; crush.
  
  rewrite <- HeqH0 in Heq


  assert 
    (forall E F (z:ThreeStack E F) 
      s t r u A B (x:Stuck A B) C D (y:Nest Stuck C D) v
      m n w,
      Some (s,t) = bufsAltStart2 x y m v ->
      bufsAltStart z s t ->
      Some (r,u) = bufsAltStart2 x y n w ->
      bufsAltStart z r u) as ans.
  clear.
  induction z; desall.
  cutThis (bufsAltStart2 s0 n0 s t); crush.
  destruct p; desall. Focus 2.
  cutThis (bufsAltStart2 s0 n0 s t); crush.
  destruct p; desall. destruct p0; desall.
  eapply IHz. Focus 2. eapply H0.
  Focus 2. eapply HeqH0.
  Focus 2. eauto.
  pose (IHz _ _ _ _ _ _ _ _ _ _ _ _ _ _ HeqH0 H0 H1).
  

  destruct r; desall.
  eapply IHz in HeqH0. Focus 3.

  destruct t; desall.

  clear HeqH1 HeqH0 H s m.

  destruct p.
  
  assert 
    (forall E F (z:ThreeStack E F) 
      s t A B (x:Stuck A B) C D (y:Nest Stuck C D) v,
      Some (s,t) = bufsAltStart2 x y Small v ->
      bufsAltStart z s t ->
      None = bufsAltStart2 x y Medium v ->
      False) as ans.
  clear.
  induction z; desall.
  eapply medPreNone in H1. rewrite <- H1 in H. crush.
  eapply medPreNone in H1. rewrite <- H1 in H. crush.
  
  eapply ans; eauto.
  destruct p.
  
  destruct f.
  cutThis (bufsAltStart2 s0 n s t). crush. destruct p.
  eapply IHz. eapply HeqH2.
  destruct


  eapply medPreNone in HeqH2. rewrite <- HeqH2 in H1. crush.
  destruct p; desall. destruct s0; desall.
  eapply medPreSomeOth in HeqH2; desall.
  rewrite <- H0 in H1.
  destruct t; desall. rewrite <- H2 in H1. crush.
  eapply medPreSomeMed in HeqH2. rewrite <- HeqH2 in H1.
  destruct t; desall.
  eapply medPreNone in HeqH0. rewrite <- HeqH0 in H1. crush.
  destruct p; desall. destruct s0; desall.
  eapply medPreSomeOth in HeqH0; desall.
  rewrite <- H0 in H1.
  destruct t; desall. rewrite <- H2 in H1. crush.
  eapply medPreSomeMed in HeqH0. rewrite <- HeqH0 in H1.
  destruct t; desall.
  eapply medPreNone in HeqH0. rewrite <- HeqH0 in H1. crush.
  destruct p; desall. destruct s0; desall.

  Check medPreSomeOth.
  Check medPreSomeExt.
  destruct m; desall. destruct t; desall.
  Focus 5.

  destruct s0; simpl in *.
  cutThis (bufsAltStart2 s0 n Medium Medium).
  inversion H1.
  destruct p.
  destruct s1.
  eapply medPreSomeOth in HeqH2; desall.

  destruct s0; simpl in *.
  destruct b2; simpl in *.
  destruct m; desall.
  destruct t; desall.
  Print cons13.
  crush.
  Print SM.











  intros.
  destruct xs; ese H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  
  eapply npushSmall5 with (s0 := s0) (n := n) (q := Large).
  Focus 3.
  cutThis (bufsAltStart2 s0 n Small Large). auto.
  destruct p0.
 simpl in *.
  eapply H1.

eauto.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.

  destruct p. (* bookmark *)
  induction n0; badMatch IHn0.

  assert False.
  eapply npushSmallHelp; eauto.

  badMatch H1;
    try (eapply npushSmallHelp; eauto);  
      try (eapply npushSmallOth; eauto);  
        badMatch H1.

  clear s m H.
  clear HeqH4.
  induction n0; badMatch IHn0.


  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.
  try (eapply npushSmallHelp; eauto);  badMatch H1.



  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.
  eapply npushSmallHelp; eauto;  badMatch H1.



(*bookmark*)
  clear H m0 m s.
  assert (forall A B (y:Nest Stuck A B) C (x:Stuck C A) p,
    match bufsAltStart2 x y Small p with
      | None => False
      | Some (pair _ _) => True
    end ->
    None = bufsAltStart2 x y Medium p ->
    Some Suffix = top2' x y ->
    False) as ans.
  clear.
  induction y; badMatch IHy.
  badMatch ans.


  eapply IHn.
  induction n; badMatch IHn0.
  destruct
  eapply IHn0.
  
  destruct s0; destruct n; badMatch H.
  destruct s0; destruct n; badMatch H.

  shapDes H.



  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.
  badMatch H.

Lemma npushBufs :
  forall a (x:a) xs,
    prepose xs <> Large ->
    allShape xs ->
    BufsAlternate xs ->
    BufsAlternate (npush x xs).
Proof.
  intros.
  destruct xs; desall.
  destruct m; desall; destruct H2; desall;
    repeat split; desall; eauto.
  eauto.
  destruct m; desall; destruct H2; desall;
    repeat split; desall; eauto.
  repeat split; desall; eauto.
  Focus 2.
  eauto. Focus 2.
  repeat split; desall; eauto.
  Unfocus. Print nextSize. Print top3.
  assert (forall A B (C:ThreeStack A B),
    prepose' C <> Large ->
    forall z,
      z <> Medium ->
      bufsAltStart C Medium z ->
      bufsAltStart C Large z) as ans.
  clear.
  Print bufsAltStart.
  Print bufsAltStart2.
  destruct C. Focus 2.
  simpl. destruct s; desall.
  unfold bufsAltStart.
  forall A B
  assert (fora

  induction C.
  intros.
  destruct z; desall.
  intros.
  destruct f; desall.
  desall s; desall; destruct n; desall
  destruct C; desall.
  destruct s0; desall; destruct n; desall;
    repeat split; desall.
  destruct b2
  
  
  cutThis (prepose' C); desall.
  destruct C; desall. 
  destruct s0; desall; destruct n; desall; destruct C; desall;
    repeat split; desall.
  destruct C; desall.
  destruct s0; desall; destruct n; desall; destruct C; desall;
    repeat split; desall.
  destruct b2; desall; destruct s0; desall; destruct n; desall; destruct C; desall.
  destruct b2; desall; destruct b3; desall; destruct s0; desall; destruct n; desall; destruct C; desall.
  
    repeat split; desall.


  destruct z; desall;
  destruct s0; desall; destruct n; desall; destruct C; desall;
    repeat split; desall.
  destruct s0; desall; destruct n; desall; destruct C; desall;
    repeat split; desall.
  destruct b2; destruct z; desall.

  cutThis (prepose' H2); desall.
  destruct H2; desall. 
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; destruct m; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H. auto.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; desall; destruct s1; desall; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.

  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.
  destruct H2; destruct s1; destruct n; desall.

  destruct H2; desall. destruct H2; desall. destruct n; desall.
  repeat split; desall; eauto.
  eauto.
Qed.
  
npush :: a -> Deque a -> Deque a
npush x (Deque M0 Empty None) = Deque M0 Empty (Some x) 
npush x (Deque M0 Empty (Some y)) = Deque (MS x y M0) Empty None 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) Empty) xs) q) = Deque (MS x z zs) xs q 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) (Full y ys)) xs) q) = Deque (MS x z zs) (Full (NE y ys) xs) q 
npush x (Deque M0 (Full (NE (Stack B0 z zs) Empty) xs) q) = Deque M0 (cons13 (B1 x) z zs xs) q
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) Empty) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) xs) q
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) (Full r rs)) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) (Full (NE r rs) xs)) q
npush x (Deque (MS y z zs) rs q) = Deque M0 (cons13 (B2 x y) (B1 z) zs rs) q

ninject :: Deque a -> a -> Deque a
ninject (Deque M0 Empty None) x = Deque M0 Empty (Some x)
ninject (Deque M0 Empty (Some y)) x = Deque (MS y x M0) Empty None
ninject (Deque M0 (Full (NE (Stack (B1 z) B0 zs) Empty) xs) q) x = Deque (MS z x zs) xs q
ninject (Deque M0 (Full (NE (Stack (B1 z) B0 zs) (Full y ys)) xs) q) x = Deque (MS z x zs) (Full (NE y ys) xs) q
ninject (Deque M0 (Full (NE (Stack z B0 zs) Empty) xs) q) x = Deque M0 (cons13 z (B1 x) zs xs) q 
ninject (Deque M0 (Full (NE (Stack z (B1 y) zs) Empty) xs) q) x = Deque M0 (Full (NE (Stack z (B2 y x) zs) Empty) xs) q 
ninject (Deque M0 (Full (NE (Stack z (B1 y) zs) (Full r rs)) xs) q) x = Deque M0 (Full (NE (Stack z (B2 y x) zs) Empty) (Full (NE r rs) xs)) q
ninject (Deque (MS z y zs) rs q) x = Deque M0 (cons13 (B1 z) (B2 y x) zs rs) q

npop :: Deque a -> Maybe (a,Deque a)
npop (Deque M0 Empty None) = Nothing
npop (Deque M0 Empty (Some y)) =  Just (y,empty)
npop (Deque M0 (Full (NE (Stack (B2 y x) (B1 z) zs) Empty) xs) q) = Just (y,Deque (MS x z zs) xs q)
npop (Deque M0 (Full (NE (Stack (B2 y x) (B1 z) zs) (Full r rs)) xs) q) = Just (y,Deque (MS x z zs) (Full (NE r rs) xs) q)
npop (Deque M0 (Full (NE (Stack (B2 y x) z zs) Empty) xs) q) = Just (y,Deque M0 (cons13 (B1 x) z zs xs) q)
npop (Deque M0 (Full (NE (Stack (B1 y) (B2 x z) M0) Empty) Empty) None) = Just (y,Deque (MS x z M0) Empty None)
npop (Deque M0 (Full (NE (Stack (B1 y) B0 M0) Empty) Empty) (Some (Both x z))) = Just (y,Deque (MS x z M0) Empty None)
npop (Deque M0 (Full (NE (Stack (B1 y) z zs) Empty) xs) q) = Just (y,Deque M0 (Full (NE (Stack B0 z zs) Empty) xs) q)
npop (Deque M0 (Full (NE (Stack (B1 y) z zs) (Full r rs)) xs) q) = Just (y,Deque M0 (Full (NE (Stack B0 z zs) Empty) (Full (NE r rs) xs)) q)
npop (Deque (MS y z M0) Empty None) = Just (y,Deque M0 Empty (Some z))
npop (Deque (MS y z zs) rs q) = Just (y,Deque M0 (cons13 B0 (B1 z) zs rs) q)

neject :: Deque a -> Maybe (Deque a,a)
neject (Deque M0 Empty None) = Nothing
neject (Deque M0 Empty (Some y)) = Just (empty,y)
neject (Deque M0 (Full (NE (Stack (B1 x) (B2 z y) zs) Empty) xs) q) = Just (Deque (MS x z zs) xs q,y)
neject (Deque M0 (Full (NE (Stack (B1 x) (B2 z y) zs) (Full r rs)) xs) q) = Just (Deque (MS x z zs) (Full (NE r rs) xs) q, y)
neject (Deque M0 (Full (NE (Stack z (B2 x y) zs) Empty) xs) q) = Just (Deque M0 (cons13 z (B1 x) zs xs) q, y)
neject (Deque M0 (Full (NE (Stack (B2 x z) (B1 y) M0) Empty) Empty) None) = Just (Deque (MS x z M0) Empty None, y)
neject (Deque M0 (Full (NE (Stack B0 (B1 y) M0) Empty) Empty) (Some (Both x z))) = Just (Deque (MS x z M0) Empty None, y)
neject (Deque M0 (Full (NE (Stack z (B1 y) zs) Empty) xs) q) = Just (Deque M0 (Full (NE (Stack z B0 zs) Empty) xs) q, y)
neject (Deque M0 (Full (NE (Stack z (B1 y) zs) (Full r rs)) xs) q) = Just (Deque M0 (Full (NE (Stack z B0 zs) Empty) (Full (NE r rs) xs)) q, y)
neject (Deque (MS z y M0) Empty None) = Just (Deque M0 Empty (Some z), y)
neject (Deque (MS z y zs) rs q) = Just (Deque M0 (cons13 (B1 z) B0 zs rs) q, y)

Inductive Back a where
    Back :: !(ThreeStack a b) -> !(SM b) -> Back a

prefix0' :: ThreeStack a b -> SM b -> Back a
prefix0' (Full (NE (Stack (B2 x y) z zs) Empty) xs) q = 
    case npush (Both x y) (Deque zs xs q) of
      Deque a c q' -> Back (cons13 B0 z a c) q'
prefix0' (Full (NE (Stack (B2 x y) z zs) (Full r rs)) xs) q = 
    case npush (Both x y) (Deque zs (Full (NE r rs) xs) q) of
      Deque a c q' -> Back (cons13 B0 z a c) q'

prefix0 :: ThreeStack a b -> SM b -> Back a
prefix0 (Full (NE (Stack (B1 x) z zs) rs) xs) q = 
    case prefix0' xs q of
      Back c q' -> Back (Full (NE (Stack (B1 x) z zs) rs) c) q'
prefix0 x y = prefix0' x y

suffix0' :: ThreeStack a b -> SM b -> Back a
suffix0' (Full (NE (Stack z (B2 x y) zs) Empty) xs) q = 
    case ninject (Deque zs xs q) (Both x y) of
       Deque a c q' -> Back (cons13 z B0 a c) q'
suffix0' (Full (NE (Stack z (B2 x y) zs) (Full r rs)) xs) q = 
    case ninject (Deque zs (Full (NE r rs) xs) q) (Both x y) of
       Deque a c q' -> Back (cons13 z B0 a c) q'

suffix0 :: ThreeStack a b -> SM b -> Back a
suffix0 (Full (NE (Stack z (B1 x) zs) rs) xs) q = 
    case suffix0' xs q of
      Back c q' -> Back (Full (NE (Stack z (B1 x) zs) rs) c) q'
suffix0 x y = suffix0' x y

prefix2' :: ThreeStack a b -> SM b -> Back a
prefix2' (Full (NE (Stack B0 z zs) Empty) xs) q = 
    case npop (Deque zs xs q) of
      Just (Both x y,Deque a c q') ->
          Back (cons13 (B2 x y) z a c) q' 
prefix2' (Full (NE (Stack B0 z zs) (Full r rs)) xs) q = 
    case npop (Deque zs (Full (NE r rs) xs) q) of
      Just (Both x y,Deque a c q') ->
          Back (cons13 (B2 x y) z a c) q' 

prefix2 (Full (NE (Stack (B1 x) z zs) rs) xs) q = 
    case prefix2' xs q of
      Back c q' -> 
          Back (Full (NE (Stack (B1 x) z zs) rs) c) q'
prefix2 x y = prefix2' x y

suffix2' :: ThreeStack a b -> SM b -> Back a
suffix2' (Full (NE (Stack z B0 zs) Empty) xs) q = 
    case neject (Deque zs xs q) of
      Just (Deque a c q',Both x y) ->
          Back (cons13 z (B2 x y) a c) q' 
suffix2' (Full (NE (Stack z B0 zs) (Full r rs)) xs) q = 
    case neject (Deque zs (Full (NE r rs) xs) q) of
      Just (Deque a c q',Both x y) ->
          Back (cons13 z (B2 x y) a c) q' 

suffix2 (Full (NE (Stack z (B1 x) zs) rs) xs) q = 
    case suffix2' xs q of
      Back c q' ->
          Back (Full (NE (Stack z (B1 x) zs) rs) c) q'
suffix2 x y = suffix2' x y

fixHelp :: (forall a b . ThreeStack a b -> SM b -> Back a) -> Deque t -> Deque t
fixHelp f (Deque b c d) = 
    case f c d of
      Back c' d' -> Deque b c' d'

sufpose' :: ThreeStack a b -> Size
sufpose' Empty = Medium
sufpose' (Full (NE (Stack _ B0{} _) _) _) = Small
sufpose' (Full (NE (Stack _ B2{} _) _) _) = Large

sufpose (Deque _ (Full (NE (Stack _ B1{} _) _) x) _) = sufpose' x
sufpose (Deque _ x _) = sufpose' x

push x xs =
    case prepose xs of
      Large -> npush x (fixHelp prefix0 xs)
      _  -> npush x xs

inject xs x =
    case sufpose xs of
      Large -> ninject (fixHelp suffix0 xs) x
      _  -> ninject xs x

pop xs =
    case prepose xs of
      Small -> npop (fixHelp prefix2 xs)
      _ -> npop xs

eject xs =
    case sufpose xs of
      Small -> neject (fixHelp suffix2 xs)
      _ -> neject xs

*)