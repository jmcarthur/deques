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

Fixpoint bufsAltStart2 a b (m:Stuck a b) c (n:Nest Stuck b c) (*d e (r:ThreeStack d e) *) (xs ys:Size) :=
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

Fixpoint bufsAltStart a b (r:ThreeStack a b) (xs ys:Size) :=
  match r with
    | Empty => True
    | Full _ _ (NE _ p ps) qs => 
      match bufsAltStart2 p ps xs ys with
        | None => False
        | Some (xs',ys') => bufsAltStart qs xs' ys'
      end
  end.

(*
Fixpoint bufsAltStart2 (f:Size -> Size -> Prop) a b (m:Stuck a b) c (n:Nest Stuck b c) (*d e (r:ThreeStack d e) *) (xs ys:Size) :=
  match m with
    | Stack x y _ =>
      let xs' := bufSize x in
        let ys' := bufSize y in
          (~ (SameSize xs xs')
           /\
           ~ (SameSize ys ys')
           /\
           (match n with
              | Empty => f 
              | Full _ _ z zs => bufsAltStart2 f z zs (*r*)
            end) (nextSize xs xs') (nextSize ys ys')
           )
  end.

Fixpoint bufsAltStart a b (r:ThreeStack a b) (xs ys:Size) :=
  match r with
    | Empty => True
    | Full _ _ (NE _ p ps) qs => bufsAltStart2 (bufsAltStart qs) p ps (*qs*) xs ys
  end.
*)

Definition BufsAlternate t (x:Deq t) :=
  match x with
    | Deque _ _ _ y _ => bufsAltStart y Medium Medium
  end.

Inductive Top := Prefix | Suffix | Twofix.

Definition topCheck t (x y:Buffer t) :=
  match x,y with
    | B1 _, B1 _ => None
    | B0, B1 _ => Some Prefix
    | B2 _ _, B1 _ => Some Prefix
    | B1 _, B0 => Some Suffix
    | B1 _, B2 _ _ => Some Suffix
    | _,_ => Some Twofix
  end.

Definition NextTop1 x y :=
  match x,y with
    | Prefix,Prefix => True
    | Suffix,Suffix => True
    | _,_ => False
  end.

Definition nextTop1 x y :=
  match x,y with
    | Prefix,Prefix => true
    | Suffix,Suffix => true
    | _,_ => false
  end.

Definition top1 a b (z:Stuck a b) :=
  match z with
    | Stack x y _ => topCheck x y
  end.

Fixpoint top2' a b (x:Stuck a b) c (yys:Nest Stuck b c) {struct yys} :=
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

Ltac cutThis x :=
  let xx := fresh
    in remember x as xx; destruct xx.

Ltac crush := unfold not; intros;
  simpl in *; auto; subst; simpl in *; auto;
    match goal with
      | [H:True |- _] => clear H; crush
      | [H:~ False |- _] => clear H; crush
      | [H:?x = ?x |- _] => clear H; crush
      | [F:False |- _] => inversion F
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
      | [H: ~ True |- _] => 
        let J := fresh
          in pose (H I) as J; inversion J
      | _ => idtac
    end.

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
  intros.
  unfold cons13. crush.
  destruct t; crush.
  destruct s; crush.
  destruct s; crush.
  destruct t; crush;
    destruct n; crush;
      desall.
  cutThis i; cutThis t0; cutThis t1; crush.
  cutThis i; cutThis t0; cutThis t1; cutThis t2; crush.
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
  destruct p; destruct w; destruct b; destruct b0; desall; eauto.
  cutThis (sameSize p (bufSize b0)); desall.
  cutThis (sameSize w (bufSize b1)); desall.
  destruct b0; desall.
  cutThis (bufsAltStart2 f N Small (nextSize w (bufSize b1))); desall.
  destruct p0; desall.
  eapply IHN.
  cutThis (bufsAltStart2 f N Large (nextSize w (bufSize b1))); desall.
  destruct p0; desall.
Qed.
Hint Resolve bufsAlt2PreMed.

Lemma bufsAltPreMedium :
  forall a b (t:ThreeStack a b) p q,
    bufsAltStart t p q ->
    bufsAltStart t Medium q.
Proof.
  induction t; desall.
  cutThis (bufsAltStart2 s n p q); desall.
  cutThis (bufsAltStart2 s n Medium q); desall.
  pose bufsAlt2PreMed as B.
  pose (B _ _ s _ n p q) as C.
  desall.
  rewrite <- HeqH0 in C.
  destruct p0; desall.
  rewrite <- HeqH1 in C. desall.
  eapply C; desall.
  eapply IHt. eauto.
  destruct p1.
  destruct p0.
  pose bufsAlt2PreMed as B.
  pose (B _ _ s _ n p q) as C.
  desall.
  rewrite <- HeqH0 in C.
  rewrite <- HeqH1 in C. desall.
Qed.
Hint Resolve bufsAltPreMedium.

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
  intros.
  destruct xs; crush.
  desall.
  destruct H0; desall.
  destruct H0; desall.
  destruct H0; desall.
  destruct H0; desall.
  destruct H0; desall.
  destruct H0; desall.
Qed.

Lemma npushShape :
  forall a (x:a) xs,
    allShape xs ->
    allShape (npush x xs).
Proof.
  intros.
  destruct xs; crush.
  desall.
  eapply cons13shape; crush. 
  destruct H0; desall; destruct m; desall.
  destruct H0; desall; destruct m; desall.
  eapply cons13shape; crush. 
  destruct H0; desall; destruct m; desall.
  destruct H0; desall; destruct m; desall.
  destruct H0; desall; destruct H1; desall.
  destruct H0; desall; destruct H1; desall.
  destruct H0; desall; destruct H1; desall.
  destruct H0; desall; destruct H1; desall.
  destruct H0; desall; destruct H1; desall.
Qed.

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