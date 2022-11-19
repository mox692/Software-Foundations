
* Gallina 
  * coqでプログラムを記述する際に使用する言語
  * haskellやocamlみたいな普通の関数型言語

# Functional Programming in Coq    (Basics)
* This facility is very interesting, since it gives us a path from proved-correct algorithms written in Gallina to efficient machine code. 
  * GallinaからHaskell等のコードを生成できるっぽい
* simplがどのように動くのかが、よくわからない

## New Types from Old
* 型引数を持つ型の定義
* 依存型っぽい話題もチラついてた
* tacticについての説明
  * The keywords intros, simpl, and reflexivity are examples of tactics. A tactic is a command that is used between Proof and Qed to guide the process of checking some claim we are making

## その他
* 下記は証明のreflexivityのstepで行き詰まる.
  * これはおそらくn(=nat)がどういう値なのか(O or S n')なのかをCoqが判断できないためだと思われる
  * destruct、もしくはinductionをn(=nat)に対して用いれば証明がうまくできるかも
```coq
Theorem plus_O_n : forall n : nat, n + O = n.
Proof.
  intros n. reflexivity. Qed.
```
* 簡約ルールに関して
  * [ゼータ簡約](https://coq.inria.fr/refman/language/core/conversion.html#:~:text=these%20conversion%20rules.-,Reductions,-convert%20terms%20to)
