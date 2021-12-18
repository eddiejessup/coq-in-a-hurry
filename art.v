(* Chapter 1  *)

(* (No exercises) *)

(* Chapter 2 *)

(* Ex 2.1 *)

Open Scope nat_scope.

(* Ex 2.1.a *)

Check (plus 3).

(* Application:

-----------------
Definition: 'App'
-----------------

E, G |- e1 : A -> B    E, G |- e2 : A
-------------------------------------
E, G |- e1 e2 : B

Simplification: make the context implicit.

e1 : A -> B    e2 : A
---------------------
e1 e2 : B

Clarification: add parens.

(e1) : (A -> B)  ,  (e2) : (A)
---------------------
(e1 e2) : B

Clarification: put assumptions long-wise instead of wide-wise.

- e1 : (A -> B)
- e2 : A
-----------------
(e1 e2) : B

Clarification: use words and indentation.

if:
  - e1 : (A -> B)
  - e2 : A
then:
  (e1 e2) : B

*)

(* Now let's instantiate 'App' for the expression-term `plus 3`

if:
  - plus : (A -> B)
  - 3 : A
then:
  (plus 3) : B  -- (1)

if:
  - A = nat
  - B = nat
  - (1)
then:
  - plus : nat -> nat  -- (2)
  - 3 : nat  -- (3)

if:
  - (2)
  - (3)
then:
  - (plus 3) : nat
*)

(* Ex 2.1.b *)

Require Import ZArith.

Open Scope Z_scope.
Check (Zmult (-5)).

(*

if:
  - e1 : (A -> B)
  - e2 : A
then:
  (e1 e2) : B

Use that:

if:
  - ZMult : (A ~ Z -> B ~ (Z -> Z))
  - (-5) : A ~ Z
then:
  (ZMult (-5)) : B ~ (Z -> Z)

*)

(* Ex 2.1.c *)

Check Z.abs_nat : Z -> nat.

(*

No application, instead it's an identifier. Identifier typing rule, as an inference rule:

-----------------
Definition: 'Var'
-----------------

(x, A) \in E \or G
------------------
E, G |- x : A

in words: 'if the identifier 'x' appears with type 'A' in the env or ctx, then x has type A in this (env, ctx).

Long-wise and iffily:

if:
  - (x, A) \in ctx
then:
  x : A

Instantiate:

if:
  - (Z.abs_nat, Z -> nat) \in ctx
then:
  Z.abs_nat : Z -> nat
*)

(* Ex 2.1.d *)

Open Scope nat_scope.
Check Z.abs_nat.
Check ((5) + Z.abs_nat (5 - 19)) : nat.

(* Ex 2.2 *)

(* Abstraction

-----------------
Definition: 'Lam'
-----------------

E, G :: (v : A) |- e : B
------------------------
E, G |- ((fun (v: A) => e): A -> B)

Simplification: make context implicit:

augmenting (v : A) |- e : B
---------------------------
(fun v: A => e) : A -> B

Clarification: long-wise:

if:
  - augmenting (v : A) |- e : B
then:
  (fun (v: A) => e) : A -> B
*)

(*
infer type: fun a b c: Z => (b * b - 4*a*c)%Z

Z -> Z -> Z -> Z
*)

Check (fun a b c: Z => (b * b - 4*a*c)%Z) : Z -> Z -> Z -> Z.

(* Ex 2.3

infer type: fun (f g : nat -> nat) (n:nat) => g (f n)

(nat -> nat) -> (nat -> nat) -> nat -> nat
*)

Check (fun (f g : nat -> nat) (n:nat) => g (f n)) : (nat -> nat) -> (nat -> nat) -> nat -> nat.

(* Ex 2.4

--------------------
Definition: 'Let-in'
--------------------


E, G |- t1 : A       E, G :: (v := t1 : A) |- t2 : B
----------------------------------------------------
E, G |- let v := t1 in t2 : B

Simplification:

if
  - t1 : A
  - augmenting (v := t1 : A) |- t2 : B
then
  (let v := t1 in t2) : B

Expression to type:

fun n p : nat =>
  (
    let diff := n - p in
    let square := diff * diff in
        square * (square + n)
  )%nat

How many typing rules to type this expression?

Not yet sure of order, but some points:

- Lam (for fun n)
- Lam (for fun p)
- Let-in (for diff)
  - Var (for (-))
  - App* (for (-))
- Let-in (for square)
  - Var (for ( * ))
  - Var (for (+))
  - App* (for ( * ))
- App* (for (+))
- App* (for ( * ))

So 8 rules, of type: Lam, Let-in, App*.
Ignoring duplicated 'Var' rules, assuming we cache the identifier lookup.

*)

(* Ex 2.5 *)

Open Scope Z_scope.

Definition add5 := fun x1 x2 x3 x4 x5 : Z => x1 + x2 + x3 + x4 + x5.

(* Ex 2.6 *)

Section ex26.

  Variables x1 x2 x3 x4 x5 : Z.

  Definition add5s := x1 + x2 + x3 + x4 + x5.
End ex26.

Eval compute in add5s 1 2 3 4 5.
Eval compute in add5 1 2 3 4 5.

(* Ex 2.7 *)

Definition ex27 := fun x:Z => 2 * x * x + 3 * x + 3.

Eval compute in ex27 2.
Eval compute in ex27 3.
Eval compute in ex27 4.

(*

Definition: Every term whose type is 'Set' is called a 'specification'
Definition: Every term whose type is a specification is called a 'program'

nat : Set -- the term 'nat' is a specification
5 : nat   -- the term '5' is a program, because its type is 'nat', and nat is a specification.

How do we type types? There are typing rules for that. For function types:

----------------------
Definition: 'Prod-Set'
----------------------

E, G |- A : Set    E, G |- B : Set
----------------------------------
E, G |- (A -> B) : Set

Simplify:

if:
  - A : Set
  - B : Set
then:
  (A -> B) : Set


Higher types
============

5 : nat
nat : Set
Set : Type (i), forall i
Type (i) : Type (j), j > i

To summarise, terms are organised in levels:

Level 0: Programs. Examples: `0`, `S`, `trinomial`, `my_fun`
Level 1: Specifications. Examples: `nat`, `nat -> nat`, `(Z -> Z) -> nat -> nat`
Level 2: Sorts. Example: `Set`
Level 3, Universe-0s: `Type (0)`
Level 3 + i, Universe-is: `Type (i)`

The type of every term at level j is a term at level j + 1. As an ambiguity,
however, any universe of rank i also has as type *any* universe at rank j, j >
i. But let's not worry about that too much.


*)

(*
3. Propositions and Proofs

Minimal prepositional logic: formulas comprise just variables and implication, such as:

(P => Q) => ((Q => R) => (P => R))

Tarski's method of solution
---------------------------
Enumerate each possible value of each variable: true or false. Check the
expression is true under all assignments.

Heyting's method of solution
----------------------------
Try to find a process to construct a proof of the right-hand side from a proof
of the left-hand side.

- Tarski's method corresponds to classical logic, where we assume the principle of excluded middle (each proposition is either true or false).
- Heyting's method corresponds to intuitionistic logic, where we don't assume that.

Some formulas are true in classical logic, but can't be proved in intuitionistic logic.

Observation: Intuitionistic logic is less powerful than classical logic.

Coq mainly supports Heyting's intuitionistic approach.

Propositions and Proofs in terms of Coq's terms
===============================================

There is another term in Level 2 (Sorts), alongside `Set`: we now have `{Set, Prop}`.

As for `Set`, `Prop : Type(i), forall i`.

Terms of type `Prop` (at Level 1) are called 'propositions'.

Terms whose type is a proposition are called 'proofs'.

We have some equivalences:

`Set` <=> `Prop`
specification <=> proposition
proof <=> program

More fully,

                     Type(i)
                      ^  ^
                      |  |
                      |  |
                    Set Prop
                      ^  ^
                      |  |
 +-------+------------+  +-----------+------+
 |       |            |  |           |      |
 |       |            |  |           |      |
 |       |            |  |           |      |
...    specB      specA  propA     propB   ...
                  ^ ^ ^  ^  ^ ^
     +------------+ | |  |  | +------------+
     |              | |  |  |              |
     |      +-------+ |  |  +-------+      |
     |      |         |  |          |      |
    ...  progA2  progA1 proofA1  proofA2  ...


One asymmetry between programs and proofs is that we generally care about the
difference between programs fulfilling the same specification, while we don't
care as much about the difference between two proofs of the same proposition: we
only care that one exists. This irrelevance of the nature of proof terms is
called 'proof irrelevance'.

Where we can declare local variables that are programs, using the syntax,

`Variable h : nat`

we can also declare variables that are proofs, using the same syntax. If the
term is a proof, we call the variable a 'hypothesis'.

There is actually alternative syntax in such a case,

`Hypothesis h: P`, (where P stands for some proposition.)

Where we can declare *global* variables that are programs, using the syntax,

`Parameter x: nat`

we can also declare variables that are proofs using the same syntax. If the term
is a proof, we call the variable an 'axiom'.

There is actually alternative syntax in such as case,

`Axiom x: P`

The environment contains all the axioms, while the context contains all the
current hypotheses.

Definition: A global *definition* of an identifier whose type is a proposition
(i.e. an identifier that is a proof term) is called either a 'theorem' or a
'lemma'.

Definition: A 'goal' is a pair (local context, well-formed type, `t`). Typically
`t` is a proposition, i.e. a term of type `Prop`.

In the context of a goal, a term of type `t`, i.e. a proof of that proposition,
is called a 'solution'.

Definition: A tactic is a command that is applied to a goal, whose effect is to
produce a new, possibly empty, list of goals. The tactic is able to construct a
solution to the input goal, given a solution for each output goal.
*)

Section Minimal_propositional_logic.
  Variables P Q R T : Prop.

  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.

  intros H H' p.

  apply H'.

  apply H.

  assumption.

  Qed.


(*

We have typing rules just like we had in the world of `Set`, but in the world of `Prop`.

Note this is a typing rule for typing propositions themselves, i.e. terms of type `Prop`, not for typing proofs.

As we had _Prod-Set_, for typing specifications involving arrows, we have _Prod-Prop_, for typing propositions involving arrows

-----------------------
Definition: 'Prod-Prop'
-----------------------

E, G |- P : Prop        E, G |- Q : Prop
----------------------------------------
          E, G |- (P -> Q) : Prop

*)

(* Ex 3.1

Type this:

(P -> Q) -> (Q -> R) -> P -> R

- Apply _Var_ at P                                     P : Prop
- Apply _Var_ at R                                     R : Prop
- Apply _Prop-Prop_ at P, R                            P -> R : Prop
- Apply _Prop-Prop_ at Q, R                            Q -> R : Prop
- Apply _Prop-Prop_ at (Q -> R), (P ->R)               (Q -> R) -> (P -> R) : Prop
- Apply _Prop-Prop_ at P, Q                            P -> Q : Prop
- Apply _Prop-Prop_ at (P -> Q), (Q -> R) -> P -> R    (P -> Q) -> ((Q -> R) -> (P -> R)) : Prop

*)

(*

We can unify Prod-Set and Prod-Prop by parametrizing the type:

------------------
Definition: 'Prod'
------------------

E, G |- P : s        E, G |- Q : s    s \in {Set, Prop}
-------------------------------------------------------
          E, G |- (P -> Q) : s

if:
  - s \in {Set, Prop}
  - P : s
  - Q : s
then:
  (P -> Q) : s
*)

(*
Definition: For a term `t : P_1 -> ... P_n -> Q`,

  the 'head type of rank k of t' is the term `P_k -> P_n -> Q`

  Examples:
    - The head type of rank 1 is just the type of t
    - The head type of rank n is P_n -> Q

  The term Q is also called the 'final type' of t
*)

(* Ex 3.2 *)

(* 3.2a *)
Lemma id_P : P -> P.
intro H.
exact H.
Qed.

(* 3.2b *)
Lemma id_PP : (P -> P) -> (P -> P).
intro H.
exact H.
Qed.

(* (3.2c done earlier) *)

(* 3.2d *)
Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
intros pqr q p.
exact (pqr p q).
Qed.

(* 3.2e *)
Lemma ignore_Q : (P -> R) -> P -> Q -> R.
intros pr p q.
exact (pr p).
Qed.

(* 3.2f *)
Lemma delta_imp : (P -> P -> Q) -> P -> Q.
exact (fun ppq p => ppq p p).
(* exact (ppq p p). *)
Qed.

(* 3.2g *)
Lemma delta_impR : (P -> Q) -> (P -> P -> Q).

intros pq p1 p2.
exact (pq p1).
Qed.

(* 3.2h *)
Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
intros pq pr qrt p.
exact (qrt (pq p) (pr p)).
Qed.

(* 3.2i *)
Lemma weak_peirce :((((P -> Q) -> P) -> P) -> Q) -> Q.
intro f.
apply f.
intro g.
apply g.
intro p.

apply f.
intro h.
exact p.
Qed.

(*
Tacticals
=========

Simple composition
------------------

`tac1; tac2`: When applied to a goal `g`, this command applies `tac1` to `g`, and `tac2` to all the goals generated by `tac1`.

This can be chained, like `tac1; tac2; tac3`.

Generalised composition
-----------------------

Simple composition requires that `tac2` succeeds when applied to all goals
generated by `tac1`. If not, we can provide a tactic to apply to each generated
goal:

`tac1; [tac11 | tac12 | tac13]`

This works when `tac1` generates exactly 3 goals.

The sub-tactics can themselves use tacticals:

`tac1; [tac11a; tac11b | tac12 | tac13]`

Alternative (||)
----------------

We can combine tactics so that a second tactic is applied to those goals on which the first fails.

`tac1 || tac2`

This applies `tac1` to the goal. If this succeeds then we are done; if it fails, we apply `tac2`

Utility tacticals
-----------------

`idtac`: the identity tactic: always succeeds, and leaves the goal unchanged.
`fail`: always fails.

Optional (`try`)
----------------

We can apply a tactic, and do nothing if it fails:

`try tac1`

This is equivalent to `tac1 || idtac`.

If the argument of `try` is a complex expression, we can use parentheses:

`try (tac1; fail)`

*)

(* Ex 3.3 *)

(* 3.3a *)
Lemma id_P_tactically : P -> P.
intro; assumption.
Qed.

(* 3.3b *)
Lemma id_PP_tactically : (P -> P) -> (P -> P).
intro; assumption.
Qed.

(* 3.3c *)
Lemma imp_trans_tactically : (P -> Q) -> (Q -> R) -> P -> R.
intros pq qr p; apply qr; apply pq; assumption.
Qed.

(* 3.3d *)
Lemma imp_perm_tactically : (P -> Q -> R) -> (Q -> P -> R).
intros pqr q p; apply pqr; assumption.
Qed.

(* 3.3e *)
Lemma ignore_Q_tactically : (P -> R) -> P -> Q -> R.
intros pr p q; apply pr; assumption.
Qed.

(* 3.3f *)
Lemma delta_imp_tactically : (P -> P -> Q) -> P -> Q.
intros ppq p; apply ppq; assumption.
Qed.

(* 3.3g *)
Lemma delta_impR_tactically : (P -> Q) -> (P -> P -> Q).
intros pq p; assumption.
Qed.

(* 3.3h *)
Lemma diamond_tactically : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
intros pq pr qrt p. apply qrt; [apply pq; assumption | apply pr; assumption].
Qed.

(* 3.3i *)
Lemma weak_peirce_tactically :((((P -> Q) -> P) -> P) -> Q) -> Q.
intro f; apply f; intro g; apply g; intro p; apply f; intro g2; assumption.
Qed.

(* The `cut` tactic *)

Section section_for_cut_example.

Hypotheses (H : P -> Q)
           (H0 : Q -> R)
           (H1 : (P -> R) -> T -> Q)
           (H2 : (P -> R) -> T).

Theorem cut_example : Q.
Proof.

cut (P -> R).

intro pr.
apply H1.
exact pr.
apply H2.
exact pr.
intro p.
apply H0.
apply H.
exact p.

Qed.

(* Ex 3.5 *)

Theorem cut_example_without_cut : Q.
Proof.

apply H1.

(* Note that without cut, we repeat this pattern *)
intro p.
apply H0.
apply H.
exact p.

apply H2.

(* Note that without cut, we repeat this pattern *)
intro p.
apply H0.
apply H.
exact p.

Qed.


(*
Tactics
=======

Basic

- `exact p`: Use `p` to prove the current goal.
- `assumption`: Search the current context for a proof of the current goal, and use that.
- `apply f`: For a function whose final type matches the current goal, produce a goal to solve each non-final type (i.e. each argument) of `f`.
- `intro`, `intros`: When the current goal is a function, extract the leftmost argument of that function as a hypothesis in the context

Intermediate

- `cut (P : Prop)`: Provide a new goal to prove, that will then become a hypothesis of the current goal (an extra argument), and we will generate an extra goal to prove the argument-goal itself.
- `assert (P : Prop)`: Like `cut`, but we prove the provided goal first. You can name the proof like so: `assert (H : P)`
- `auto`: Uses a combination of `assumption`, `intros`, `apply` to solve a goal. It either solves a goal, or leaves it unchanged.
*)

Theorem cut_example_with_assert: Q.
Proof.

assert (H3 : (P -> R)).

intro p.
apply H0.
apply H.
exact p.

apply H1.

exact H3.
apply H2.
exact H3.

Qed.

End section_for_cut_example.

(* Ex 3.6 *)

Theorem auto_example_1: (P -> Q) -> P -> Q.
Proof.
auto 1.
Qed.

Theorem auto_example_3: (((P -> Q) -> Q) -> Q) -> P -> Q.
Proof.
auto 3.
Qed.

Theorem auto_example_4: (((((P -> Q) -> Q) -> Q) -> Q) -> Q) -> P -> Q.
Proof.
auto 4.
Qed.

Theorem auto_example_5: (((((((P -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> P -> Q.
Proof.
auto 5.
Qed.

Theorem auto_example_6: (((((((((P -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> P -> Q.
Proof.
auto 6.
Qed.

(* General pattern: Add two '-> Q' on the RHS of the first hypothesis, to increase the 'auto' ceiling by one. *)

End Minimal_propositional_logic.

(* Chapter 4: Dependent Products *)

(*

A dependent product lets us build functions where the result type depends on the argument value.

Categorisation of value-type interactions
-----------------------------------------

- Function argument is a program of some type. Function result is a program of another type.

  Gives us: Simply-typed lambda calculus.

  Example, in Haskell syntax:

    succ : Nat -> Nat

- Function argument is a program of some type. Function result is a program, whose type depends on the type of the function argument.

  Gives us: polymorphism.

  Example, in Haskell syntax:

    just : (a : Type) -> (x : a) -> Maybe a

  So the result is a program, whose type depends on the value of the type-term `a`.

- Function argument is a type. Function result is a type, whose value depends on the value of the function argument.

  Gives us: type families, i.e. type-level functions.

  Example, in pseudo-Haskell syntax:

    a : (t : Type) -> Type

- Function argument is a program of some type. Function result is a type, whose value depends on the value of the function argument.

  Gives us: Dependent types.

  Examples, in pseudo-Haskell syntax:

    zeros : (n : Nat) -> Vec n [ (Vec n) is a specification, i.e. `(Vec n) : Set`]

    lt : (n : Nat) -> (n <= n)  [ (n <= n) is a proposition, i.e. `(n <= n) : Prop` ]

    disj_comm : P -> Q -> (P \/ Q) -> (Q \/ P)

A dependent type is a type that is the result of functions applied to appropriate expressions.

---------------------------------------------
input output  what it allows
---------------------------------------------
| term | term | simply typed lambda calculus
| type | term | polymorphism
| term | type | dependent types
| type | type | type operators, define type constructors like Maybe

Typing rules to type dependent types
------------------------------------

----------------------
Definition: 'Prod-dep'
----------------------

E, G |- A : Set       E, G |- B : Type
--------------------------------------
         E, G |- (A -> B) : Type

Simplifying, dropping env & ctx, writing iffily:

if:
  - A : Set
  - B : Type
then:
  - (A -> B) : Type

Note that in this case, the function returns a value of type 'Type', such as
'Prop' or 'Set'. This is _not_ generalising the earlier product rules, it's
supplementing them with a new rule that lets us generate types that return types
(specifications, or propositions).

If we choose `B ~ Prop`, then we have a rule that lets us type predicates:
functions of the form `A -> Prop`.

If we choose `B = Set`, then we have a rule that lets us type
value-parametrized-types: functions of the form `A -> Set`, such as `nat -> Set`
to define types of length-indexed vectors.

Compare with rule 'Prod':

E, G |- P : s        E, G |- Q : s    s \in {Set, Prop}
-------------------------------------------------------
          E, G |- (P -> Q) : s

The 'Prop' typing rule lets us type functions that return proofs or programs.

*)

(* Ex 4.1

1. (nat -> nat) -> Prop

- nat : Set ('Var', x = nat, A = Set)
- (nat -> nat) : Set ('Prod-Set', A = nat, B = nat)
- (nat -> nat) -> Prop : Type ('Prod-dep', A = (nat -> nat), B = Prop)

Example such a term might represent:

*)
(* L1: Simple types *)
(* ================ *)
(* (s={Set, Prop}, s'={Set, Prop}) *)

(* s=Set, s'=Set *)
Check (nat -> bool).
(* Same, restated with dependent product syntax *)
Check (forall n: nat, bool).

(* s=Set, s'=Prop *)
Check (nat -> 1 < 2).
(* Same, restated with dependent product syntax *)
Check (forall n: nat, 1 < 2).
(* Actually defining dependent product *)

Open Scope nat_scope.

Check (forall n: nat, n < 2).

(* s=Prop, s'=Set *)
Check (1 < 2 -> bool).
(* Same, restated with dependent product syntax *)
Check (forall p: (1 < 2), bool).
Check (forall n:nat, forall p: (n < 2), bool).

(* s=Prop, s'=Prop *)
Check (1 < 2 -> 1 < 3).
Check (forall n:nat, n < 2 -> n < 3).

(* L2: Impredicativity in `Prop` *)
(* ============================= *)
(* (s=Type, s'=s''=Prop) *)

(* A=Set *)
Check (Set -> 1 < 2).
(* With dependent product syntax *)
Check (forall t: Set, 1 < 2).

(* A=Prop *)
Check (Prop -> 1 < 2).
(* With dependent product syntax, and actually using it *)
Check (forall p: Prop, p /\ (not p)).

(* L3: Dependence *)
(* ============== *)
(* (s={Set, Prop}, s'=s''=Type) *)

(* s=Set, B=Set *)
Check (nat -> Set).
(* Dependent syntax *)
Check (forall n: nat, Set).

(* s=Set, B=Prop *)
Check (nat -> Prop).
(* Dependent syntax *)
Check (forall n: nat, Prop).

(* s=Prop, B=Set *)
Check (1 < 2 -> Set).
(* Dependent syntax *)
Check (forall p: Prop, Set).

(* s=Prop, B=Prop *)
Check (1 < 2 -> Prop).
(* Dependent syntax *)
Check (forall p: Prop, Prop).

Check eq nat nat.
Check eq 2 2.
Check nat = nat.

Check (forall p: nat, eq p p).
Check (eq 1 1).
Check (eq_refl 1).

(* Ex 4.3 *)

Section A_declared.

  Variables (A: Set) (P Q: A -> Prop) (R: A -> A -> Prop).

  Theorem all_perm : (forall a b: A, R a b) -> forall a b: A, R b a.
  Proof.
  intro H.
  intros a b.
  apply H.
  Qed.

  Theorem all_imp_dist : (forall a b:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
  Proof.

  intros H1 H2.
  intro a.

  apply H1.

  exact a.
  apply H2.
  Qed.

  Theorem all_delta : (forall a b:A, R a b) -> forall a:A, R a a.
  Proof.
  intros H a.
  exact (H a a).
  Qed.

End A_declared.

Definition id: forall A: Set, A -> A := fun A x => x.

Eval compute in (id nat 21).

Definition diag: forall (A B: Set), (A -> A -> B) -> A -> B
  := fun A B f a => f a a.

Eval compute in (diag nat nat (fun a b => a) 0).

(* Ex 5.3 *)

Theorem ex53_1 : ~False.
Proof.
intro.
exact H.
Qed.

Theorem ex53_2: forall P: Prop, ~~~P -> ~P.
Proof.

intros Prp H P.

apply H.
intro.

exact (H0 P).
Qed.

Theorem ex53_3: forall P Q: Prop, ~~~P -> P -> Q.
intros.

exfalso.

apply H.
intro.

exact (H1 H0).
Qed.

Theorem ex53_4: forall P Q: Prop, (P -> Q) -> ~Q -> ~P.
intros.
intro.
exact (H0 (H H1)).
Qed.

Theorem ex53_5: forall P Q R: Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
intros.
exfalso.
exact ((H0 H1) (H H1)).
Qed.

(* Ex 5.4 *)

Theorem ex54_1: ~(forall P Q: Prop, (P -> Q) -> (Q -> P)).
intro.

apply (H False True).

intro.
elim H0.

trivial.
Qed.

Theorem ex54_2: ~(forall P Q: Prop, (P -> Q) -> (~P -> ~Q)).

intro.
apply (H False True).

intro.
elim H0.

intro.
elim H0.

trivial.
Qed.

(* Ex 5.5 *)

Theorem ex55 : forall (A: Set) (a b c d: A), a=c \/ b=c \/ c=c \/ d=c.

Proof.

intros.

right.
right.
left.

Check eq_refl.
exact eq_refl.
Qed.

(* Ex 5.6 *)

Theorem ex56_1 : forall (A B C: Prop), A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.

intros.

case H as [H1 [H2 H3]].
split.

exact (conj H1 H2).

exact H3.
Qed.

Theorem ex56_2 : forall (A B C D: Prop), (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.

intros.

case H as [H1 [H2 [H3 H4]]].
split.

exact (H1 H3).
exact (H2 H4).
Qed.

Theorem ex56_3 : forall A: Prop, ~(A /\ ~A).
Proof.

intros.
intro.
case H as [HA HNA].
exact (HNA HA).
Qed.

Theorem ex56_4 : forall A B C: Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.

intros.

case H as [H1 | [H2 | H3]].
left.
left.
assumption.

left.
right.
assumption.

right.
assumption.

Qed.


Theorem ex56_5 : forall A: Prop, ~~(A \/ ~A).
intros.
intro.
apply H.
right.
intro.
apply H.
left.
exact H0.
Qed.

Theorem ex56_6 : forall A B: Prop, (A \/ B) /\ ~A -> B.
intros.
case H as [H1 H2].
case H1 as [H1A | H1B].

elim (H2 H1A).

exact H1B.
Qed.

(* Ex 5.7 *)

Theorem ex57_peirce_imp_classic : (forall P Q: Prop, ((P -> Q) -> P) -> P) -> (forall R: Prop, ~~R -> R).
intros.

apply (H R False).
intro.
elim (H0 H1).
Qed.

Theorem ex57_classic_imp_exclmiddle : (forall R: Prop, ~~R -> R) -> (forall P: Prop, P \/ ~P).
intros.

apply H.
exact (ex56_5 P).
Qed.

Theorem ex57_exclmiddle_imp_demorgannotandnot : (forall P: Prop, P \/ ~P) -> (forall P Q: Prop, ~(~P /\ ~Q) -> P \/ Q).
intros.

case (H P) as [H1 | H2].

left.
exact H1.

right.

case (H Q) as [HQ1 | HQ2].

exact  HQ1.

exfalso.
exact (H0 (conj H2 HQ2)).
Qed.

Theorem ex57_demorgannotandnot_imp_impliestoor : (forall P Q: Prop, ~(~P /\ ~Q) -> P \/ Q) -> (forall P Q: Prop, (P -> Q) -> (~P \/ Q)).
intros.

apply (H (~P) Q).

intro.

case H1 as [H1A H1B].

apply H1A.
intro.

apply (ex56_3 Q).

exact (conj (H0 H1) H1B).
Qed.

(* TODO *)
(* Theorem ex57_impliestoor_imp_peirce
  :
  (forall P Q: Prop, (P -> Q) -> (~P \/ Q))
  ->
  (forall R S: Prop, ((R -> S) -> R) -> R)
  .

intros.

apply H0.
intro.
intuition. *)

(*
More Tacticals
==============

repeat
------

Repeat a tactic until failure or complete success
*)

(* Ex 5.8 *)

(* Ex 5.8.1 *)
(* Q. What does the tactic `repeat idtac` do? *)
(* A.

The textbook says:
'apply <tactic> until failure or complete success'

I think it would loop indefinitely. *)

Theorem ex58_1 : forall A: Prop, A -> A.
intros.
idtac.
repeat idtac.

(* Ex 5.8.2 *)
(* Q. What does the tactic `repeat fail` do? *)
(* A. . *)

Theorem ex58_1 : forall A: Prop, A -> A.
intros.
idtac.
repeat idtac.

