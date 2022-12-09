Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

(* Logical Connectives *)

(* Conjunction *)
Example and_example : 2 + 4 = 6 /\ 4 * 4 = 16.
Proof.
  split.
  * reflexivity.
  * reflexivity.
  Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B H1 H2.
  split.
  * apply H1.
  * apply H2.
  Qed.


(* Exercise: 2 stars, standard (and_exercise) *)
Example and_exercise : forall n m : nat,
  m + n = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H1.
  split.
  - induction m in H1. (* MEMO: ここで分解した時に、若干の簡略化がなされている？ どっちも nが0のパターン飲みかも *)
    simpl in H1.
    * apply H1.
      Abort.
      (* TODO: solve *)

Lemma and_exercise2 : forall n m : nat,
  n = 0 /\ m = 0 -> m + n = 0.
Proof.
  intros n m H1.
  destruct H1. (* MEMO: 仮定に conjunctive な命題があった場合は destruct で崩す *)
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
  Qed.


