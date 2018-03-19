# hyp-naming
A library for automatic namnig if hypothesis in Coq. Entirely written in Ltac.

## Credit:
Tricky parts of Ltac were suggested by Jonathan Leivant.

## Use:

The user has to maintain a Ltac function that computes hypothesis name
from its current name and its type. Some basic naming are defined by
default (see Ltac function `fallback_rename_hyp`.

To maintain this function one needs to make use of the `::=` operator
in Coq which overwrite an Ltac function. See below for a full example.


### A full example:

```coq

Require LibHypRenaming.

Ltac rename_hyp_1 h th :=
  match th with
  | _ => rename_hyp_neg h th
  | ?A -> ?B =>
    let nme := fallback_rename_hyp h B in
    fresh "impl_" nme
  end.

Ltac rename_hyp_2 h th :=
  match th with
  | true = false => fresh "trueEQfalse"
  | _ => rename_hyp_1 h th
  end.

Ltac rename_hyp ::= rename_hyp_2.

Lemma foo: forall x y,
    x <= y -> 
    ~1 < 0 ->
    (0 < 1 -> ~(true=false)) ->
    (0 < 1 -> ~(1<0)) ->
    (0 < 1 -> 1<0) -> 0 < 1.
  (* auto naming at intro: *)
 !intros.
 Undo.
 (* intros first, rename after: *)
 intros.
 rename_all_hyps.
 Undo.
 (* intros first, rename some hyp only: *)
 intros.
 autorename H0.
 (* put !! before a tactic to rename all new hyps: *)
 rename_all_hyps.
 !!destruct h_le_x_y eqn:?.
 - auto with arith.
 - auto with arith.
Qed.

```