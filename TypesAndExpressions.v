Require Import Arith.
Require Import ZArith.
Require Import Bool.

(** Opening a scope *)
Open Scope Z_scope.

(** Looking at all interpretations of a notation*)
Locate "_ * _".

(** Printing all the notations in a scope *)
Print Scope Z_scope.


(** [Check t] checks whether the term t is well formed or not*)
Check 33%nat.
Check 0%nat.

Open Scope nat_scope.

Check 33.
Check 0.

Check 33%Z.
Check (-12)%Z.

Open Scope Z_scope.

Check -12.
Check 33%nat.

Check true.
Check false.

(** All natural numbers are obtained by the repetie application of
    a successor function [S] to the number 0, written as [O] *)
Open Scope nat_scope.

Check S (S (S O)).
Check mult (mult 5 (minus 5 4)) 7.
Check 5 * (5 - 4) * 7.

(** By removing decimal notations, its easy to see composition of [S] *)
Unset Printing Notations.

Check S (S (S O)).
Check mult (mult 5 (minus 5 4)) 7.

Set Printing Notations.

Open Scope Z_scope.
Print Scope Z_scope.
Check (Z.opp (Z.mul 3 (Z.sub (-5) (-8)))).


(**  Functions are arrow types. *)
Check fun (f g:nat -> nat)(n: nat) => g (f n).
Fail Check (fun x => x x).

(** Terms can be locally binded using the [let ... in] construct *)
Check fun n p: nat =>
    (let diff := n - p in
        let square := diff * diff in
            square * (square + n))%nat.
(** In the above example, [n], [p], [diff], and [square] are bound *)

(** All these definitions of cube are the same *)
Definition cube1 := fun z:Z => z*z*z.
Definition cube2 (z:Z) : Z := z*z*z.
Definition cube3 z := z*z*z.

Check cube1.
Check cube2.
Check cube3.

(** * Reduction Rules*)

Definition Zsqr z: Z := z * z.
Definition my_fun f z:Z := f (f z).

Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).
Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).


