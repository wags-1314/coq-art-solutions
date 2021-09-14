Section Minimal_propositional_logic.
Variables P Q R T: Prop.

Theorem imp_trans:
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H1 H2 H3.
  apply H2.
  apply H1.
  assumption.
Qed.

Print imp_trans.

Theorem apply_example:
  (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros H1 H2 Hp.
  apply H1.
  exact (H2 Hp).
Qed.

(** * Exercise 3.2*)

Lemma id_P: P -> P.
Proof.
  intros.
  assumption.
Qed.

Lemma id_PP: (P -> P) -> (P -> P).
Proof.
  intros.
  assumption.
Qed.

Lemma imp_perm: (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Lemma ignore_Q: (P -> R) -> P -> Q -> R.
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma delta_imp: (P -> P -> Q) -> P -> Q.
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Lemma delta_impR: (P -> Q) -> (P -> P -> Q).
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma diamond:
  (P -> Q) -> (P -> R) -> (Q -> R -> T) -> (P -> T).
Proof.
  intros.
  apply H1.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

Lemma weak_peirce:
  ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  assumption.
Qed.

Definition f:
  (nat->bool)->(nat->bool)->nat->bool.
  intros f1 f2.
  assumption.
Qed.

Print f.

(** * Tacticals *)
(** [tac; tac'] means tac' is applied to
    all subgoals generated by tac. [;] is the
    composition tactical. *)
Theorem then_example:
  P -> Q -> (P -> Q -> R) -> R.
Proof.
  intros.
  apply H1; assumption.
Qed.

(** Sometimes each subgoal requires a specific
    treatment. We can use a generalised form of
    [;]. [tac; [tac1|tac2|...|tacn]] will apply
    tac1 on the first subgoal and so on. *)
Theorem compose_example:
  (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros.
  apply H; [
    assumption |
    apply H0; assumption].
Qed.

Section section_for_cut_example.
Hypotheses
  (H: P -> Q)
  (H0: Q -> R)
  (H1: (P -> R) -> T -> Q)
  (H2: (P -> R) -> T).

Theorem proof_with_cut: Q.
Proof.
  cut (P -> R).
  intros.
  apply H1; [idtac | apply H2]; assumption.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Theorem withought_cut: Q.
Proof.
  apply H1; [idtac | apply H2];
  intros; apply H0; apply H; assumption.
Qed.
