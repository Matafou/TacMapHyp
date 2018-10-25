(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu, credit to Jonathan Leivant                     *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)

(** This file defined three tacticals for iterating a tactic on sets
    of hypothesis. In all these tactical "tac" must be a tactic taking
    a hyp name as argument.
    
    [onAllHyp tac] applies [tac H] for each H of the proof context
    (natural order: newer hyps first).
    
    [onAllHypRev tac] applies [tac H] for each H of the proof context
    (reverse order).

    [tac1 ;; tac] applies tac1 on the current goal, then applies tac
    on each "new" hypothesis generated by tac1. A hypothesis is "new"
    if its name was not present before tac1 was applied. older
    hypothesis are taken first.

    [tac1 ;!; tac] same as ;; but applies tac on newer hyps first.

    In all these tacticals, a failure in applying tac to a hypothesis
    is ignored and does not make the whole tactic fail. *)

(* Credit for the harvesting of hypothesis: Jonathan Leivant *)
Ltac harvest_hyps harvester := constr:(ltac:(harvester; constructor) : True).

Ltac revert_clearbody_all := 
  repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac all_hyps := harvest_hyps revert_clearbody_all.

Ltac next_hyp hs step last := 
  lazymatch hs with 
  | (?hs' ?H) => step H hs'
  | _ => last
  end.

Ltac map_hyps tac hs :=
  idtac;
  let rec step H hs := next_hyp hs step idtac; tac H in
  next_hyp hs step idtac.

Ltac map_hyps_rev tac hs :=
  idtac;
  let rec step H hs := tac H ; next_hyp hs step idtac in
  next_hyp hs step idtac.

Ltac map_all_hyps tac := map_hyps tac all_hyps.
Ltac map_all_hyps_rev tac := map_hyps_rev tac all_hyps.

(* apply tac to H unless H appear in old_hyps *)
Ltac tac_if_not_old tac old_hyps H :=
  match old_hyps with
  | context [H] => idtac (* old_hyps contains all old hyps in a product *)
  | _ => tac H + idtac (* never fail, this could be configurable *)
  end.


(* Applies tac and then aftertac to each new hypothesis older first
   (top to bottom) *)
Ltac tac_new_hyps tac aftertac :=
  let old_hyps := all_hyps in
  let substnew H := tac_if_not_old aftertac old_hyps H in
  tac ;
  let new_hyps := all_hyps in
  map_hyps substnew new_hyps.

(* Same as tac_new_hyps but tac is applied on newer hyps first (bottom
   to top). *)
Ltac tac_new_hyps_rev tac aftertac :=
  let old_hyps := all_hyps in
  let substnew H := tac_if_not_old aftertac old_hyps H in
  tac ;
  let new_hyps := all_hyps in
  map_hyps_rev substnew new_hyps.

Tactic Notation (at level 3) "onAllHyps" tactic(Tac) := (map_all_hyps Tac).
Tactic Notation (at level 3) "onAllHypsRev" tactic(Tac) := (map_all_hyps_rev Tac).
(* Tactic Notation (at level 3) "onNewHypsOf" tactic(Tac) "do" tactic3(Tac2) := (tac_new_hyps Tac Tac2). *)
(* Tactic Notation (at level 3) "onNewHypsOfRev" tactic(Tac) "do" tactic3(Tac2) := (tac_new_hyps_rev Tac Tac2). *)

(* Tactical "tac1;;tac2" means apply "tac1" to the goal, then apply "(tac2
   h)" to each subgoal for each new hyp h. *)
Tactic Notation (at level 4) tactic4(tac1) ";;" tactic3(tac2) := (tac_new_hyps tac1 tac2).
Tactic Notation (at level 4) tactic4(tac1) ";!;" tactic3(tac2) := (tac_new_hyps_rev tac1 tac2).

(* Some usual tactics one may want to use with onNewHypsOf: *)
(* subst. *)
Ltac substHyp H :=
  match type of H with
  | ?x = ?y => subst x + subst y
  end.

(* revert, fails if impossible, should not fail if hyps are ordered in the right order *)
Ltac revertHyp H := revert H. (* revert is a tactic notation *)

(* revert if subst fails. Never fail, be careful to not use this tactic i n the
   left member of a "+" tactical: *)
Ltac subst_or_revert H := try (substHyp H + revert H).

(* A tactic which moves up a hypothesis if it sort is Type or Set.
   These hypothesis are generally less interesting, having them far
   from the goal is harmless. Moreover with Set Printing Compact
   Context. Coq can group them in horizontal boxes. *)
Ltac move_up_types H := match type of H with
                        | ?T => match type of T with
                                | Prop => idtac
                                | Set => move H at top
                                | Type => move H at top
                                end
                        end.

Ltac subst_or_move_up H := (substHyp H + move_up_types H).


(* Typical use, subst with all hyps created by inversion, and move
Type-sorted hyps to the top of the goal:

inversion H ;; subst_or_move_up. *)

(* See also LibHypsNaming.v for a generic tactic for auto naming new
   hypothesis. *)

(* Examples of use: *)
(*
Lemma foo: forall x y a t : nat,
    x = y -> a+1 = t+2 ->forall u v, u+1 = v -> a+1 = t+2 -> False.
Proof.
  intros.
  onAllHyps move_up_types.
  Undo.
  onAllHyps subst_or_revert.
  Undo.
  onAllHypsRev subst_or_revert.
  Restart.
  intros until 1.
  intros;(destruct x eqn:? ;; substHyp).
  Undo.
  (* left associativity *)
  intros;destruct x eqn:? ;; substHyp.
  (* left associativity with ";" and ";;" *)
  Restart.
  intros ? ? ? ? ?; intros;; substHyp.
  Restart.
 (* Some hyps are not reverted due to the order in which tac is applied: *)
  (destruct x eqn:heq;intros) ;; revertHyp.
  Undo.
  (* Doing revert in the other order is better: *)
  (destruct x eqn:heq;intros) ;!; revertHyp.
  Undo.
  destruct x eqn:heq;intros ;; (fun h => substHyp h || move_up_types h).
  Undo.
  destruct x eqn:heq;intros ;; subst_or_revert.
Abort.

(* Example of tactic notations to define shortcuts: *)
Local Tactic Notation "=" tactic3(Tac) := Tac ;; substHyp.

Lemma bar: forall x y a t u v : nat,
    x = y -> a = t -> u = v -> False.
Proof.
  intros until 2.
  =intros. =destruct x eqn:heq.
Abort.
*)