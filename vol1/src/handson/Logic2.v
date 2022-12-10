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


(* Disjunction *)
(* MEMO: conjunctionの時はsplitを使ったが、disjunctionの時は
      destructを使う. *)
Lemma factor_is_O: forall n m : nat,
   n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H1.
  destruct H1.
  * rewrite -> H.
    reflexivity.
  * rewrite -> H.
    assert (n * 0 = 0) as H1.
    {
      induction n.
      - reflexivity.
      - simpl. 
        apply IHn.
    }
    apply H1.
  Qed.

Lemma or_intro_l : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B H.
  (* MEMO: leftをゴールに設定する. *)
  left.
  apply H.
  Qed.

Lemma zero_or_succ : forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros n.
  destruct n.
  * left.
    reflexivity.
  * right.
    simpl.
    reflexivity.
  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P H.
  (* MEMO: 矛盾命題を分解するのにdestructしている *)
  destruct H.
  Qed.

 (* MEMO: この証明の意味がよくわからん *)
Theorem not_implies_our_not : forall (P:Prop),
  not P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H0 Q H1.
  destruct H0.
  apply H1.
  Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  (* MEMO: x <> y -> not (x = y) -> (x = y -> false) ってことらしい *)
  unfold not.
  intros contra.
  (* MEMO: discriminate についての復讐 ( https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html#:~:text=These%20examples%20are%20instances%20of%20a%20logical%20principle%20known%20as%20the%20principle%20of%20explosion%2C%20which%20asserts%20that%20a%20contradictory%20hypothesis%20entails%20anything%20(even%20manifestly%20false%20things!). ) *)
  discriminate contra.





















