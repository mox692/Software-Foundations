From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.

(* 普通の証明 *)
(* Proof.
    intros n m eq.
    rewrite -> eq.
    reflexivity.
    Qed. *)

Proof.
    intros n m eq.
    apply eq.
    Qed.

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
    intros n m o p eq1 eq2.
    apply eq2. (* MEMO: なんでこれが言えるんだ？？ 前提は自由に導入してもいいってことかな？ *)
    (* 
    意味がわかったかも:
    - [n;o] = [m;p] が言いたい
    - n = m -> [n;o] = [m;p] が仮定として与えられているので、n = m が代わりに言えれば証明できることにもなる(ここでgoalがn = mになる)
    - n = m は仮定で与えられている
    - Qed.

    「代わりにこれが言えればいい」を連鎖させているイメージ.
    *)
    apply eq1.
    Qed.

Theorem silly2a : forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
    intros n m eq1 eq2.
    apply eq2.
    apply eq1.
    Qed.

Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true -> 
    odd (S p) = true.
Proof.
    intros p H H0 H1.
    apply H0. (* TODO: ここの変換がピンとこない *)
    apply H.
    apply H1.
    Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  symmetry.
  apply H.
  Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
    intros l l' H.
    (* TODO: work *)
    Admitted.
Search rev.

(* The apply with Tactic *)
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m ->
  m = o ->
  n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
    (* このwithが必要かどうかの判断をプログラマがどうやってやるのかが気になる *)
    apply trans_eq with (m:=[c;d]).
    apply eq1.
    apply eq2.
    Qed.

(* The injection and discriminate Tactics *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  (*
    MEMO:
    一般的に、ある型のinjectiveの証明はその型の解体子に相当するものを用いると
    うまく証明できるらしい.
   *)
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* MEMO: Coqにおける構成子(Constructor)はinjectiveだから、このような簡単なコマンドで
  injective性を導入できる？ *)
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem list_injective : forall (X : Type)(x y : X),
    cons x nil = cons y nil ->
    x = y.
Proof.
    intros X x y H1.
    injection H1 as H2.
    apply H2.
    Qed.

Theorem injection_ex1 : forall (n m o : nat),
    [n;m] = [o;o] ->
    n = m.
Proof.
    intros n m o H1.
    injection H1 as H2. (* ここでのinjectionは、listのそれぞれの要素が等しいと主張する*)
    rewrite -> H2.
    rewrite -> H.
    reflexivity.
    Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
    intros X x y z l j H1 H2.
    injection H1 as H3 H4.
    (* TODO: この in キーワードはめっちゃ便利そう！！ *)
    rewrite H2 in H4.
    injection H4 as H4.
    rewrite H3.
    rewrite H4.
    reflexivity.
    Qed.


(* Using Tactics on Hypotheses *)
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
    intros n m p q H1 H2.
    symmetry.
    symmetry in H2.
    apply H1 in H2 as H3.
    apply H3.
    Qed.


(* Exercise: 2 stars, standard (eqb_true) *)
 (* TODO: はじめにintroをすると、stackしてしまうケースがある. *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
    intros n. induction n as [| n' IHn'].
    * destruct m.
      - reflexivity. 
      - discriminate.
    * destruct m. 
      - discriminate. 
      (* - injection S_injective' with (n:=n')(m:=m). *)
      - intros H. 
        apply IHn' in H.
        rewrite -> H.
        reflexivity.
    Qed.

      (* apply le_trans with (a := (S n)) (b := (S m)) (c := o). *)













































