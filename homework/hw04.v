(**
Exercises on Generalizing the Induction Hypothesis
https://homes.cs.washington.edu/~jrw12/InductionExercises.html
by James Wilcox (2017)

Adapted to SSReflect syntax and Mathcomp library.
*)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sum (l : seq nat) : nat :=
  if l is (x :: xs) then x + sum xs
  else 0.

Fixpoint sum_iter' (l : seq nat) (acc : nat) : nat :=
  if l is (x :: xs) then sum_iter' xs (x + acc)
  else acc.

Definition sum_iter (l : seq nat) : nat :=
  sum_iter' l 0.

Lemma sum_iter'_correct l x0 :
  sum_iter' l x0 = x0 + sum l.
Proof.
Admitted.

Theorem sum_iter_correct l :
  sum_iter l = sum l.
Proof.
Admitted.


(** Continuation-passing style
    https://en.wikipedia.org/wiki/Continuation-passing_style
 *)
Fixpoint sum_cont' {A} (l : seq nat) (k : nat -> A) : A :=
  if l is (x :: xs) then sum_cont' xs (fun ans => k (x + ans))
  else k 0.

Definition sum_cont (l : seq nat) : nat :=
  sum_cont' l (fun x => x).

Lemma sum_cont'_correct A l (k : nat -> A) :
  sum_cont' l k = k (sum l).
Proof.
Admitted.

Theorem sum_cont_correct l :
  sum_cont l = sum l.
Proof.
Admitted.

Fixpoint rev_rec {A : Type} (xs : seq A) : seq A :=
  if xs is (x::xs') then
    rev_rec xs' ++ [:: x]
  else xs.

Lemma rev_correct A (l1 l2 : seq A) :
  catrev l1 l2 = rev_rec l1 ++ l2.
Proof.
Admitted.

Theorem rev_iter_correct A (l : seq A) :
  rev l = rev_rec l.
Proof.
Admitted.

Fixpoint map_iter' {A B}
    (f : A -> B) (l : seq A) (acc : seq B) : seq B :=
  if l is (x :: l') then map_iter' f l' (f x :: acc)
  else rev acc.

Definition map_iter {A B} (f : A -> B) l := map_iter' f l [::].

Lemma map_iter'_correct A B (f : A -> B) l1 l2 :
  map_iter' f l1 l2 = rev l2 ++ (map f l1).
Proof.
Admitted.

Theorem map_iter_correct A B (f : A -> B) l :
  map_iter f l = map f l.
Proof.
Admitted.

Inductive expr : Type :=
| Const of nat
| Plus of expr & expr.

Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  end.

Fixpoint eval_expr_iter' (e : expr) (acc : nat) : nat :=
  match e with
  | Const n => n + acc
  | Plus e1 e2 => eval_expr_iter' e2 (eval_expr_iter' e1 acc)
  end.

Definition eval_expr_iter e := eval_expr_iter' e 0.

Lemma eval_expr_iter'_correct e acc :
  eval_expr_iter' e acc = acc + eval_expr e.
Proof.
Admitted.

Theorem eval_expr_iter_correct e :
  eval_expr_iter e = eval_expr e.
Proof.
Admitted.

Fixpoint eval_expr_cont' {A} (e : expr) (k : nat -> A) : A :=
  match e with
  | Const n => k n
  | Plus e1 e2 => eval_expr_cont' e2 (fun n2 =>
                  eval_expr_cont' e1 (fun n1 => k (n1 + n2)))
  end.

Definition eval_expr_cont (e : expr) : nat :=
  eval_expr_cont' e (fun n => n).

Lemma eval_expr_cont'_correct A e (k : nat -> A) :
  eval_expr_cont' e k = k (eval_expr e).
Proof.
Admitted.

Theorem eval_expr_cont_correct e :
  eval_expr_cont e = eval_expr e.
Proof.
Admitted.

Inductive instr := Push (n : nat) | Add.

Definition prog := seq instr.

Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  if p is (i :: p') then
    let s' :=
        match i with
        | Push n => n :: s
        | Add => if s is (a1 :: a2 :: s') then a2 + a1 :: s'
                 else s
        end
    in
    run p' s'
  else s.

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  end.

Lemma run_append p1 p2 s :
  run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
Admitted.

Lemma compile_correct_generalized e s :
  run (compile e) s = (eval_expr e) :: s.
Proof.
Admitted.

Theorem compile_correct e :
  run (compile e) [:: ] = [:: eval_expr e].
Proof.
Admitted.
