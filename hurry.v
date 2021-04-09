(* 1 *)
(* 1.1 *)

Check True.

Check False.

Check 3.

Check (3 + 4).

Check (3 = 5).

Check (3, 4).

Check ((3=5) /\ True).

Check nat -> Prop.

Check (3 <= 6).

Check (3, 3=5) : nat * Prop.

Check (fun x:nat => x = 3).

Check (forall x:nat, x < 3 /\ (exists y:nat, x = y + 3)).

Check (let f := fun x => (x * 3, x) in f 3).

Locate "_ <= _".

Check and.

Check (and True False).

Eval compute in
  let f := fun x => (x * 3, x) in f 3.

Check (fun (x:nat) (y:nat) => x + y).

Eval compute in (let f := fun x y z => x + y + z in f 1 2 3).

(* 2 *)
(* 2.1 *)

Definition example1 := fun x => x * x + 2 * x + 1.

Check example1.

Eval compute in example1 1.

Reset example1.

(* 2.2 *)

Require Import Bool.

Eval compute in if true then 3 else 5.

Search bool.

(* 2.3 *)

Require Import Arith.

Definition is_zero (n:nat) :=
  match n with
    0 => true
  | S p => false
  end.

Definition is_zero_p (n:nat) :=
  match n with
    0 => True
  | S p => False
  end.

Check (is_zero, is_zero_p).

Eval compute in (is_zero 1, is_zero_p 1).

Print pred.

Print Init.Nat.pred.

Definition myPred n :=
  match n with
    0 => 0
  | S p => p
  end.

Eval compute in myPred 0.

Fixpoint sum_n n :=
    match n with
      0 => 0
    | S p => p + sum_n p
    end.

(* 2.4 *)

Require Import List.

Check 1::2::3::nil.

Check nil.

Check (nil: list nat).

Eval compute in map (fun x => x + 3) (1::3::2::nil).

Eval compute in map S (1::3::S 1::nil).

Eval compute in 1::2::nil ++ 3::nil.

(* Exercise. *)
Fixpoint lrange n :=
  match n with
    0 => nil
  | S n => lrange n ++ n::nil
  end.

Eval compute in lrange 10.

Definition head_evb l :=
  match l with
    nil => false
  | a::tl => Nat.even a
  end.

Check head_evb.

Fixpoint sum_list l :=
  match l with
    nil => 0
  | n::tl => n + sum_list tl
  end.

Eval compute in sum_list (1::2::3::nil) = sum_list (3::2::1::nil).

Fixpoint insert n l :=
  match l with
    nil => n::nil
  | p::tl => if leb n p then n::l else p::insert n tl
  end.

Eval compute in insert 2 (1::2::3::nil).

Fixpoint sort l :=
  match l with
    nil => nil
  | p::tl => insert p (sort tl)
  end.

Eval compute in sort (3::2::3::nil).

(* 3 *)

(* 3.1 *)

Search leb.

(* SearchAbout leb. Doesn't work for me.*)

SearchPattern (_ + _ <= _ + _).
SearchRewrite (_ + _).

(* 3.2 *)

Lemma example2: forall a b:Prop, a /\ b -> b /\ a.

Proof.

intros a b h.

destruct h as [h1 h2].
split.

exact h2.
exact h1.

Qed.

(* 3.3 *)

Lemma example3: forall a b, a \/ b -> b \/ a.
Proof.

intros a b aob.

destruct aob as [h1 | h2].

right; assumption.

left; assumption.
Qed.

(* 3.4 *)

Check le_n.
Check le_S.

Lemma example4: 3 <= 5.

apply le_S.
apply le_S.
apply le_n.

Qed.

Check le_trans.

Lemma example5: forall x y, x <= 10 -> 10 <= y -> x <= y.

intros x y.
apply le_trans with (m := 10).

Qed.

(* 3.4.1 *)

SearchRewrite (_ + (_ + _)).
SearchPattern (?x * ?y = ?y * ?x).
SearchPattern ((S ?n) * ?x = ?n * ?x + ?x).
SearchRewrite (S _ * _).

Lemma example6: forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.

intros x y.
(* SearchRewrite (_ * (_ + _)). *)

rewrite Nat.mul_add_distr_l.
(* SearchRewrite ((_ + _) * _). *)
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_add_distr_r.
rewrite Nat.add_assoc.
rewrite <-Nat.add_assoc with (n:=x * x).

rewrite Nat.mul_comm with (n := y) (m := x).

pattern (x * y) at 1; rewrite <-Nat.mul_1_l.

rewrite <-Nat.mul_succ_l with (n:=1) (m:=x * y).

rewrite Nat.mul_assoc.

reflexivity.

Qed.

(* 3.5 *)

Require Import Lia.

Lemma omega_example:
  forall f x y,
  0 < x ->
  0 < f x ->
  3 * f x <= 2 * y ->
  f x <= y.

intros; lia.

Qed.

Lemma exercise56_A1:
  forall a b c,
  a /\ b /\ c ->
  (a /\ b) /\ c.

intros.

destruct H as [h1 h2].
destruct h2 as [h3 h4].

split. split.

exact h1. exact h3. exact h4.

Qed.

Lemma exercise56_A2:
  forall a b c,
  a /\ b /\ c ->
  (a /\ b) /\ c.
intuition.
Qed.

Lemma exercise56_B1:
  forall a b c d: Prop,
  (a -> b) /\ (c -> d) /\ a /\ c ->
  b /\ d.

intros.

destruct H as [h1 h2].
destruct h2 as [h3 h4].

destruct h4 as [h5 h6].

split.
apply h1.
exact h5.
apply h3.
exact h6.

Qed.

Lemma exercise56_B2:
  forall a b c d: Prop,
  (a -> b) /\ (c -> d) /\ a /\ c ->
  b /\ d.

intuition.
Qed.

SearchPattern (_ /\ ~_).

Lemma exercise56_C1:
  forall a: Prop,
  ~(a /\ ~a).

intros.
intro h.

destruct h as [h1 h2].

apply h2.
exact h1.
Qed.

Lemma exercise56_C2:
  forall a: Prop,
  ~(a /\ ~a).

intuition.
Qed.

Lemma exercise56_D1:
  forall a b c: Prop,
  a \/ (b \/ c) ->
  (a \/ b) \/ c.

intros.

destruct H as [h1 | h2].

left.
left.
exact h1.

destruct h2 as [h3 | h4].

left.
right.
exact h3.

right.
exact h4.

Qed.

Lemma exercise56_D2:
  forall a b c: Prop,
  a \/ (b \/ c) ->
  (a \/ b) \/ c.

intuition.
Qed.

Lemma exercise56_E1:
  forall a b: Prop,
  (a \/ b) /\ ~a ->
  b.

intros.

destruct H as [h1 h2].
destruct h1 as [h3 | h4].

exfalso.
apply (h2 h3).

exact h4.
Qed.

Lemma exercise56_E2:
  forall a b: Prop,
  (a \/ b) /\ ~a ->
  b.

intuition.
Qed.

Lemma exercise57:
  forall A:Type,
  forall P Q: A -> Prop,
  (forall x, P x) \/ (forall y, Q y) ->
  forall x, P x \/ Q x.

intros.

destruct H as [h1 | h2].

left.
exact (h1 x).

Check h2 x.
right.
exact (h2 x).

Qed.

(* 4 *)

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.

induction n.

reflexivity.

assert (SnSn : S n * S n = n * n + 2 * n + 1).

ring.

rewrite SnSn.
rewrite <-IHn.
simpl.
ring.
Qed.

Lemma evenb_p :
  forall n,
  Nat.even n = true ->
  exists x, n = 2 * x.

assert (Main:
  forall n,
  (Nat.even n = true -> exists x, n = 2 * x) /\ (Nat.even (S n) = true -> exists x, S n = 2 * x)
).

induction n.

simpl.

split.

exists 0.
ring.

discriminate.

split.

destruct IHn as [ih1 ih2].

exact ih2.

simpl.

intros.

destruct IHn as [ih1 ih2].

assert (h': exists x, n = 2 * x).

apply ih1.
exact H.

destruct h' as [x q].

exists (x + 1).

rewrite q.

ring.

intros.

destruct (Main n) as [hm _].

exact (hm H).

Qed.

Fixpoint add n m :=
  match n with
    0 => m
  | S n' => add n' (S m)
  end.

Eval compute in add 1 2.

Lemma exercise41 :
  forall n m
  , add n (S m) = S (add n m).

induction n.

simpl. reflexivity.

simpl.

intros.
rewrite (IHn (S m)). reflexivity.

Qed.

Lemma exercise42 :
  forall n m
  , add (S n) m = S (add n m).

simpl.
intros.
rewrite (exercise41 n m).
reflexivity.

Qed.

Lemma exercise43 :
  forall n m
  , add n m = n + m.

induction n.

simpl. reflexivity.

intros.

rewrite (exercise42 n m).
rewrite (IHn m).
ring.
Qed.

Fixpoint sum_odd_n (n:nat) : nat :=
  match n with
    0 => 0
  | S p => 1 + 2 * p + sum_odd_n p
  end.

Lemma exercise44 :
  forall n:nat
  , sum_odd_n n = n * n.

induction n.

reflexivity.

assert (SnSn : S n * S n = n * n + 2 * n + 1).

ring.

rewrite SnSn.
simpl.

rewrite IHn.

ring.
Qed.

(* 5 *)

Fixpoint count n l :=
  match l with
    nil => 0
  | a::tl =>
    let r := count n tl in if beq_nat n a then 1+r else r
  end.

Eval compute in count 2 (2::2::nil).

SearchRewrite (beq_nat _ _).
Search beq_nat.

Lemma insert_incr :
  forall n l,
  count n (insert n l) = 1 + count n l.

intros.

induction l.

simpl.

rewrite <-beq_nat_refl.
reflexivity.

simpl.

case (n <=? a).

simpl.

rewrite <-beq_nat_refl.
reflexivity.

simpl.

case (n =? a).

rewrite IHl.

reflexivity.

rewrite IHl.

reflexivity.

Qed.

(* 6 *)
(* 6.1 *)
Inductive bin : Type :=
  L : bin
| N : bin -> bin -> bin.

Check N L (N L L).

(* 6.1e1 *)

Inductive foo : Type :=
  fooc : foo
| foo3 : nat -> foo -> foo -> foo
| foo4 : bool -> foo -> foo -> foo -> foo.

Check (fooc, foo3 1 fooc fooc, foo4 false fooc fooc fooc).

(* 6.2 *)

Definition isBalanced3 (b : bin) : bool :=
  match b with
    N L L => true
  | _ => false
  end.

Eval compute in isBalanced3 L.
Eval compute in isBalanced3 (N L L).

(* 6.3 *)

Fixpoint flatten_aux (t1 t2:bin) : bin :=
  match t1 with
    L => N L t2
  | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
    L => L
  | N t1 t2 => flatten_aux t1 (flatten t2)
  end.

Fixpoint size (t:bin): nat :=
  match t with
    L => 1
  | N t1 t2 => 1 + size t1 + size t2
  end.

Eval compute in flatten_aux (N L L) L.

(* 6.4 *)

Lemma balanced3_size :
  forall t,
  isBalanced3 t = true ->
  size t = 3.

intros.

destruct t.

simpl.
discriminate.

destruct t1.

destruct t2.

simpl.
reflexivity.

simpl.

discriminate.

discriminate.

Qed.

(* 6.5 *)

Lemma flatten_aux_size :
  forall t1 t2: bin,
  size (flatten_aux t1 t2) = size t1 + size t2 + 1.

induction t1.

simpl.

intros.

ring.

intros.

simpl.

rewrite IHt1_1.

rewrite IHt1_2.

ring.

Qed.

(* 6.5e1 *)

Lemma flatten_size :
  forall t,
  size (flatten t) = size t.

induction t.

simpl.

reflexivity.

simpl.

rewrite flatten_aux_size.

rewrite IHt2.
ring.

Qed.

(* 6.6 *)

Lemma not_subterm_self_l :
  forall x y,
  ~ x = N x y.

induction x.

discriminate.



intros.
intro abs.

injection abs.

intros.

assert (IHx1' : x1 <> N x1 x2).

rewrite H.

exact (IHx1 y).

exact (IHx1' H0).

Qed.

(* 7 *)

Print nat.

Fixpoint nat_fact (n:nat): nat :=
  match n with
    0 => 1
  | S p => S p * nat_fact p
  end.

Eval compute in nat_fact 3.

Fixpoint fib (n:nat) : nat :=
  match n with
    0 => 1
  | S q => match q with
      0 => 1
    | S p => fib q + fib p
    end
  end.

Eval compute in fib 4.

Require Import ZArith.

Open Scope Z_scope.
Check iter.

Definition fact_aux (n:Z) :=
  iter
    n
    (Z * Z)
    (fun p => (fst p + 1, snd p * (fst p + 1)))
    (0, 1).

Eval compute in fact_aux 3.

Definition Z_fact (n:Z): Z :=
  snd (fact_aux n).

Eval compute in Z_fact 3.

Eval vm_compute in Z_fact 100.

Close Scope Z_scope.

(* 8 *)

Inductive even : nat -> Prop :=
  even0 : even 0
| evenS : forall x:nat, even x -> even (S (S x)).

Check even 2.
Eval compute in (evenS 0 even0).

Lemma even_mult :
  forall x,
  even x ->
  exists y, x = 2*y.

intros.

elim H.

exists 0.
ring.

intros x0 Hevenx0 IHx.

destruct IHx as [y Heq].

rewrite Heq.

exists (S y).

ring.

Qed.

Lemma not_even_1 : ~even 1.

intros even1.

inversion even1.

Qed.

Lemma even_inv :
  forall x,
  even (S (S x)) ->
  even x.

intros.

inversion H.

exact H1.

Qed.
