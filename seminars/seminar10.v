From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section LectureExercise.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then e :: s
    else x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then
    insert x (sort s')
  else [::].

Lemma sorted_cons e s :
  sorted leT (e :: s) -> sorted leT s.
Proof.
Admitted.


(** Refactor the proof in the lecture 10 into an idiomatic one *)
Lemma insert_path z e s :
  leT z e ->
  path leT z s ->
  path leT z (insert e s).
Proof.
Admitted.


Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
Admitted.

Lemma count_insert p e s :
  count p (insert leT e s) = p e + count p s.
Proof.
Admitted.

End LectureExercise.


Section Stability.
Variables (T : eqType) (leT leT' : rel T).
Implicit Types s : seq T.

(** Hint: you are free to assume [transitivity] of [leT] / [leT'] should
    you need that. E.g.
Hypothesis leT_tr : transitive leT.
 *)

Lemma sort_stable s :
  sorted leT' s ->
  sorted
    [rel x y | leT x y && (leT y x ==> leT' x y)]
    (sort leT s).
Proof.
Admitted.

End Stability.
