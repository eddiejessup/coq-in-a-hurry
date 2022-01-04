(* Inductive Data Types *)

(* Ex 6.1 *)

Inductive month : Set := January | February | March | April | May | June | July | August | September | October | November | December.

Inductive season : Set := Spring | Summer | Autumn | Winter.

Definition month_to_season : (month -> season) := month_rec (fun _ => season) Winter Winter Winter Spring Spring Spring Summer Summer Summer Autumn Autumn Autumn.

(* Ex 6.2 *)

Check (bool_ind : forall P: bool -> Prop, P true -> P false -> forall b: bool, P b).
Check (bool_rec : forall P: bool -> Set, P true -> P false -> forall b: bool, P b).

Theorem month_equal : forall m : month, m = January \/ m = February \/ m = March \/ m = April \/ m = May \/ m = June \/ m = July \/ m = August \/ m = September \/ m = October \/ m = November \/ m = December.
intros.
elim m; (repeat ((left; reflexivity) || right)).
reflexivity.
Qed.

(* Ex 6.3 *)

Theorem bool_equal : forall b : bool, b = true \/ b = false.
intro b.
Check or_introl.
Check or_intror.
exact (or_introl )
