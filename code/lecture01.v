(** Use some very basic facilities of mathcomp library *)
From mathcomp Require Import ssreflect.

Module My.
(** We introduce these definitions inside a new module
    to avoid name clashes with the standard library later *)

Inductive bool : Type :=
| true
| false.

Check true : bool.
Check true.

(** Definitions (not part of Coq's type theory, by the way, it's
    a meta-linguistic feature) *)
Definition idb := fun b : bool => b.

Check (fun b : bool => b).
Check idb.

(** Pattern-matching *)
Definition negb (b : bool) :=
  match b with
  | true => false
  | false => true
  end.

Compute idb true.
Compute idb false.

Compute negb true.
Compute negb false.

Variable c : bool.

Compute idb c.

Compute negb c.

Definition andb (b c : bool) : bool :=
  match b with
  | true => c
  | false => false
  end.

(** Symbolic computations *)
Compute andb c true.
Compute andb c false.
Compute andb false c.




(** Peano numbers -- tthe first truly inductive type *)
Inductive nat : Type :=
| S of nat
| O.
Print nat.

Check O.
Check S.
Check (S O).
Check S (S O).
Check S (S (S O)).

(** Incrementing function *)
Definition inc := S.
(** [Definition inc (n : nat) := S n.] is the same definition,
    only eta-expanded *)

(**
eta-expansion is baked into Coq' notion of definitional equality, i.e
(fun x => f x) and f are definitionally equal
but
extensionally equal functions are not necessarily equal, i.e.
(forall x, f x = g x -> f = g)
does not have to hold.
*)
Print inc.

Compute inc (S (S O)).


Definition inc2 (n : nat) := S (S n).
Compute inc2 (S (S O)).

(** predecessor function *)
Definition pred (n : nat) : nat :=
  match n with
  | S n' => n'
  | O => O   (* truncation! Coq's funcation are total *)
  end.

(**
Some options to go about implementing [pred] function:

 pred : nat -> nat  (* way to go *)
 pred : nat -> option nat
 pred : forall (n : nat), (n <> 0) -> nat

*)

(** Addititon of natural numbers *)

(** [{struct n}] means structural recursion on parameter [n].
    Coq can infer the [struct] annotation in this case. *)

Fixpoint addn (n m : nat) {struct n} : nat :=
  match n with
  | S n' => S (addn n' m)
  | O => m
  end.

Compute addn (S (S O)) (S (S O)).  (* 2 + 2 is 4 *)

(** Alternative implementation by recursion on the second parameter *)
Fixpoint addn' (n m : nat) : nat :=
  match m with
  | S m' => S (addn' n m')
  | O => n
  end.

Print addn'.

Fixpoint muln (n m : nat) : nat :=
  match n with
  | S n' => addn m (muln n' m)
  | O => O
  end.

Compute muln (S (S (S O))) (S (S O)).  (* 3 * 2 is 6 *)
Compute muln (S (S O)) O.              (* 2 * 0 is 0 *)

Definition square (n : nat) : nat := muln n n.

Definition two := (S (S O)).
Definition apply2 (f : nat -> nat) (n : nat) :=
  f (f n).
Eval hnf in (apply2 (apply2 square) two).
(** Various reduction strategies:
- Eval cbn in ...              call-by-name
- Eval lazy in ...             call-by-need
- Eval cbv in ...              call-by-value
- Eval compute in ...          call-by-value (cbv's synonym)
- Eval vm_compute in ...       call-by-value using a bytecode virtual machine
                               [Compute] is synonym for [Eval vm_compute in]
- Eval native_compute in ...   compile to OCaml and evaluate
*)

End My.

(** After closing a module, the identifiers defined in it,
    get prefixed with the module's name *)
Check My.apply2.

From mathcomp Require Import ssrfun ssrbool ssrnat.

(** Some interacive queries *)
About nat.
About S.

Locate ".+1".     (* Notation "n .+1" := (S n). *)


(** Apply [n] times a function [f] on natural numbers to
    an input [x] *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.

(* a test *)
Compute applyn S 5 42.

(** An alternative implementation whose behavior is
    different when we evaluate it symbolically *)
Definition applyn' :=
  fix rec (f : nat -> nat) (n : nat) (x : nat) :=
    if n is n'.+1 then rec f n' (f x)
    else x.


Axiom fun_ext :
  forall (A B : Type) (f g : A -> B),
    forall x, f x = g x -> f = g.

(** A way of defining [applyn] using Coq's section mechanism *)
Section Applyn.

Variable f : nat -> nat.

Fixpoint applyn'' (n : nat) (x : nat) : nat :=
  if n is n'.+1 then applyn'' n' (f x)
  else x.

Variable n : nat.
Compute applyn'' (S n) 0.

Print applyn''.

End Applyn.

Print applyn''.  (* compare the output to the one inside the above section *)

(** A proposition which can never be constructed (in the empty context *)
Inductive False : Prop :=
  .    (* no constructors! *)

Print False.

(** Let's illustrate why "in the empty context" is important *)
Check (fun f : False => f (* here we construct a value of type
                             [False], but the context in not empty,
                             since the function parameter becomes
                             part of context here *)
      ).
(** Since it's impossible to construct a value of an empty type,
    it's impossible to call a function of type
    False -> SomeType *)
(** ... provided we are talking about empty contexts again: *)
Check (fun g : False =>
         (fun f : False => f) g     (* call [fun f : False => f]
                                       with [g] as the argument *)
      ).

(** This is why Coq does not allow non-terminating functions *)
Fail Fixpoint loop (n : nat) : False :=
  loop n.
(* loop : n -> False *)

(** If this was allowed, we could construct a value of an empty type
    in the empy context like so: *)
Fail Check (loop O : False).

(** And this would preclude Coq from being a logic *)

(** To be continued... *)

