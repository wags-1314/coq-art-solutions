(** * Everyday Logic *)
(** [eapply] *)

Require Import Arith.
Require Import ZArith.
Require Import Bool.

Section Test.

Theorem mult_le_r: forall n m p: nat,
  n <= p -> n * m <= p * m.
Proof.
  intros.
  inversion H.
  - apply le_n.
Admitted.

Theorem le_mult_mult: forall a b c d,
  a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros.
  try apply le_trans.
  apply le_trans with (m := c * b).
  - apply mult_le_r. assumption. - apply mult_le_compat_l. assumption.
Qed.

Theorem le_mult_mult': forall a b c d,
  a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros.
  eapply le_trans.

  eapply mult_le_r.
  eexact H.
  eapply mult_le_compat_l.
  assumption.
Qed.

End Test.

Section ex_5_3.
  Lemma ex5_3_1: ~False.
    intro. assumption.
  Qed.

  Lemma ex5_3_2: forall P,
    ~~~P -> ~P.
  Proof.
    unfold not in *.
    intros.
    apply H.
    intros.
    apply H1.
    assumption.
  Qed.

  Lemma ex_falso : forall P,
    False -> P.
  Proof.
    intros.
    destruct H.
  Qed.


  Lemma ex5_3_3:forall P Q,
    ~~~P -> P -> Q.
  Proof.
    intros.
    apply ex5_3_2 in H.
    apply ex_falso.
    apply H.
    assumption.
  Qed.

  Lemma ex5_3_4: forall P Q: Prop,
    (P -> Q) -> (~ Q) -> ~ P.
  Proof.
    intros P Q H1 H2 H3.
    apply H2.
    apply H1.
    assumption.
  Qed.

  Lemma ex5_3_5: forall P Q R: Prop,
    (P -> Q) -> (P -> ~Q) -> P -> R.
  Proof.
    intros.
    apply ex_falso.
    apply H in H1 as H2.
    apply H0 in H1 as H3.
    apply H3.
    assumption.
  Qed.

End ex_5_3.

Section ex_5_4.
  Definition dyslexic_imp :Prop :=
    forall P Q: Prop, (P -> Q) -> Q -> P.

  Lemma false_from_dyslexic_imp:
    dyslexic_imp -> False.
  Proof.
    unfold dyslexic_imp.
    intros.
    apply (H False (False -> False));
    intros;
    assumption.
  Qed.

End ex_5_4.

Theorem and_commutes: forall P Q: Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  elim H.
  split;
  assumption.
Qed.

Section ex_5_5.
  Lemma ex5_5_1: forall (A: Set) (a b c d: A),
    a=c \/ b=c \/ c=c \/ d=c.
  Proof.
    right.
    right.
    left.
    reflexivity.
  Qed.
End ex_5_5.

Section ex_5_6.

  Lemma ex5_6_1: forall A B C,
    A /\ (B /\ C) -> (A /\ B) /\ C.
  Proof.
    intros.
    elim H.
    intros.
    elim H1.
    intros.
    split. split;
    assumption. assumption.
  Qed.

  Lemma ex5_6_2: forall A B C D: Prop,
    (A -> B) -> (C -> D) -> (A /\ C) -> B /\ D.
  Proof.
    intros.
    elim H1.
    split;
    [apply H | apply H0]; assumption.
  Qed.

  Lemma ex5_6_3: forall A,
    ~(A /\ ~A).
  Proof.
    intros A H1.
    elim H1.
    intros H2 H3.
    apply H3.
    assumption.
  Qed.

  Lemma ex5_6_4: forall A B C,
    A \/ (B \/ C) ->
      (A \/ B) \/ C.
  Proof.
    intros A B C H1.
    elim H1.
    left. left. assumption.
    intros H2.
    elim H2.
    left. right. assumption.
    right. assumption.
  Qed.

  Lemma ex5_6_5: forall A,
    ~~(A \/ ~A).
  Proof.
    intros A H1.
    unfold not in *.
  Admitted.

  Lemma ex5_6_7: forall A B,
    (A \/ B) /\ (~A) -> B.
  Proof.
    intros A B H1.
    elim H1.
    intros H2 H3.
    elim H2.
    - intros. exfalso. apply H3. assumption.
    - intros. assumption.
  Qed.
End ex_5_6.

Section ex_5_9.
  Parameter
    (A: Set)
    (P Q: A -> Prop).

  Lemma ex5_9_1: (ex (fun x => P x \/ Q x)) ->
    (ex P) \/ (ex Q).
  Proof.
    intros.
    elim H.
    intros.
    elim H0;
    intros;[left | right]; exists x;
    assumption.
  Qed.

  Lemma ex5_9_2: (ex P) \/ (ex Q) ->
  (ex (fun x => P x \/ Q x)).
  Proof.
      intros H1.
      elim H1;
      intros H2;
      elim H2;
      intros x H3;
      exists x; [left | right];
      assumption.
  Qed.

  Lemma ex5_9_3: (ex (fun x => forall R: A -> Prop, R x)) ->
    2 = 3.
  Proof.
    intros H1.
    elim H1.
    intros x H2.
  Admitted.

  Lemma ex5_9_4: (forall x, P x) ->
    ~(ex (fun y => ~ (P y))).
  Proof.
    intros H1 H2.
    elim H2.
    intros x H3.
    apply H3.
    exact (H1 x).
  Qed.


End ex_5_9.

Lemma ex5_10: forall n m p: nat,
  n + m + p = n + p + m.
Proof.
  intros.
  rewrite <- plus_assoc.
  pattern (m + p) at 1.
  rewrite plus_comm.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem eq_trans1: forall (A: Type) (x y z: A),
  x = y -> y = z -> x = z.
Proof.
  intros.
  Print eq_ind.
  eapply eq_ind.
  apply H.
  apply H0.
Qed.


