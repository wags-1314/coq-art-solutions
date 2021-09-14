(** * Dependent Products *)
(** ** Exercise 4.3 *)

Section A_declared.

Variables
  (A: Set)
  (P Q: A -> Prop)
  (R: A -> A -> Prop).

Theorem all_perm:
  (forall a b, R a b) -> forall a b, R b a.
Proof.
  intros.
  exact (H b a).
Qed.

Theorem all_imp_dist:
  (forall a, P a -> Q a) -> (forall a, P a) ->
    forall a, Q a.
Proof.
  intros.
  apply H.
  exact (H0 a).
Qed.

Theorem all_delta:
  (forall a b, R a b) -> forall a, R a a.
Proof.
  intros.
  exact (H a a).
Qed.

End A_declared.

(** * Exercise 4.5 *)
Section ex_4_5.

Theorem all_perm_prop: forall (A: Type) P,
  (forall x y: A, P x y) ->
    forall x y: A, P y x.
Proof.
  intros.
  exact (X y x).
Qed.

Theorem resolution: forall (A: Type) (P Q R S: A -> Prop),
  (forall a, Q a -> R a -> S a) -> (forall b, P b -> Q b) ->
    forall c, P c -> R c -> S c.
Proof.
  intros.
  apply H; [apply H0 | idtac]; assumption.
Qed.

