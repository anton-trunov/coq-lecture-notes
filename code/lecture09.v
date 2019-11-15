From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Prop and Type *)

Lemma sig_exists A (P : A -> Prop) :
  {x : A | P x} -> exists x : A, P x.
Proof.
case=> x px.
by exists x.
Qed.

Definition exists_sig A (P : A -> Prop) :
  (exists x : A, P x) ->
  {x : A | P x}.
Proof.
Fail case=> x px.
(**
Error: ...
Case analysis on sort [Type] is not allowed
for inductive definition [ex].
*)
Abort.
(** Recall that [exists x : A, P x] is a notation
    for [ex P] *)
Check ex :  forall A : Type, (A -> Prop) -> Prop.
Check sig : forall A : Type, (A -> Prop) -> Type.

(** This happens because [ex] lives in [Prop] --
    the universe of logical proposititons and
    [sig] belongs to [Type] -- the universe of
    computations.
    If Coq wants to stay compatible with classical
    logic it needs to prohibit information flow
    from [Prop] to [Type].
    In other words, one can _only_ use proofs to
    build other proofs.
*)

(** ** But why exactly this restriction? *)

(** First of all, we should mention that [Prop]
    is _impredicative_, meaning the following
    typechecks just fine:
 *)
Section Impredicativity.

Check (forall P : Prop, P) : Prop.

(**
This formula quantifies over all formulas,
including itself:
 *)

Variable p : (forall P : Prop, P).
Check p (forall P : Prop, P).

End Impredicativity.


Section TypeInType.
(** But what about [Type]? Doesn't it have
    the same property?  *)

Check (forall P : Type, P) : Type.

(** Well, no. [Type] is not a primitive universe,
    in fact, it's a family of indexed universes
    but the indices are hidden by default.
    We can recover those like so: *)

Set Printing Universes.
Check (forall P : Type, P) : Type.
(**
(forall P : Type@{Top.246}, P) : Type@{Top.245}
     : Type@{Top.245}
(* {Top.246 Top.245} |= Top.246 < Top.245 *)
*)

(** To make this more readable we can declare
    explicit universe levels: *)
Universe i j.
Check (forall P : Type@{i}, P) : ( Type@{j} ).
(** Coq infers [i < j] in this case, so following
    predictably fails: *)
Fail Check (forall P : Type@{i}, P) : ( Type@{i} ).
(**
universe inconsistency:
Cannot enforce i < i because i = i.
*)

(** This restriction prevents us from getting
    the so-called "type-in-type" paradox --
    had we not introduced this hierarchy of
    universes we would get
    [Type : Type] which leads to inconsistency
    as famously shown by Girard.
 *)

Check Type@{i}.
(** Type@{i} : Type@{i+1} *)

(** Some more examples: *)

Check nat.
(** nat : Set *)

Check Set.
(** Set : Type@{Set+1} *)

Check Prop.
(** Prop : Type@{Set+1} *)

Unset Printing Universes.
End TypeInType.



(** * Large elimination *)

(**
Next, let's look at _large elimination
Large elimination is the ability to build values
of type [Type] by eliminating an inductive value.

We used it to prove the disjointness of constructors
in Lecture 03:
*)

Definition false_implies_False_term :
  false = true -> False
:=
  fun     eq :  false = true =>
    match eq in (_    = b)
             return (if b then False else True)
                    (* ^^^^^^^^^^^^^^^^^^^^^^^ *)
                    (* large elimination       *)
    with
    | erefl => I
    end.


(** Now, Coq is known to be consistent with the
    Law of Excluded Middle, i.e. the following
    axiom can be safely added
 *)

Axiom LEM : forall P : Prop, P \/ ~ P.

(** But, as shown by Berardi in the 1990s,
  impredicativity + excluded middle
  => proof irrelevance

See the paper "Proof-irrelevance out of
Excluded-middle and Choice in the Calculus of
Constructions" - F. Barbanera, S. Berardi(1996)
 *)

(** Had we not prohibited large elimination for
    the impredicative universe [Prop],
    we would get a means to proving disjointness
    of constructors, i.e. that proofs can differ
    from each other. *)
Inductive Bool : Prop := T : Bool | F : Bool.

Fail Definition prf_rel_Bool (Eq : T = F) : False :=
  match Eq in (_ = y)
        return (match y with
                | T => True
                | F => False
                end)
  with
  | eq_refl => I
  end.

(** no large elimination for [Prop] *)
Fail Check match F with T => True | F => False end.

(** no such restriction for [Type] *)
Check
  match false with true => True | false => False end.

(**
  Upshot:
  proof irrelevance + large elimination
  => False

  Hence
  impredicative [Prop] + large elimination + excluded middle
  => False

  Overall, this lets [Prop] be impredicative
  and Coq compatible with the law of excluded
  middle, which is commonly used in mathematics.

  See also https://github.com/FStarLang/FStar/issues/360

*)


(** It's now easy to see that some exceptions
    that won't result in proof _relevance_
    are fine:
 *)
Definition False_to_nat (prf : False) : nat :=
  match prf with end.

Definition true_to_nat (prf : True) : nat :=
  match prf with | I => 0 end.

(** The above examples work because
    the corresponding inductive types have only
    zero or one constructors, i.e. not enough
    to prove the disjointness *)

Fail Definition or_to_nat (prf : True \/ True) : nat :=
  match prf with
  | or_introl _ => 0
  | or_intror _ => 1
  end.
(**
Incorrect elimination of "prf" in the inductive type "or":
the return type has sort "Set" while it should be "Prop".
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.
*)



(** * Totality and termination *)

(** There is a plugin to control
    - the guardedness check,
    - strict positivity rule, and
    - universe inconsistency check
    It's not needed with the current development
    version of Coq (8.11+alpha).
    For Coq versions 8.7 - 8.9 it can be installed
    with opam package manager:
      opam install coq-typing-flags
    or compiled manually using instructions from
    the plugin's homepage:
    https://github.com/SimonBoulier/TypingFlags
    To start using the plugin in a Coq file:
      From TypingFlags Require Import Loader.
    This adds
    Set Type In Type / Unset Type In Type
    and
    Set Guard Checking / Unset Guard Checking.
    vernacular commands.
 *)

From TypingFlags Require Import Loader.



(** We already mentioned earlier that
    Coq is a total language.
    This ensures its consistency as a logic
    because it rules out things like the following:
 *)

(** Disable termination checker *)
Unset Guard Checking.

Fixpoint proof_of_False (n : nat) : False :=
  proof_of_False n.

Check proof_of_False 0 : False.

(** The following vernacular reveals that
    the proof of falsehood was obtained due to
    bypassing of one of the checkers *)
Print Assumptions proof_of_False.
(** Axioms:
    proof_of_False is positive. *)


(** Remark: Coq's implementation does not enforce
    _strong_ normalization, only weak one *)

(** Enable termination checker again *)
Set Guard Checking.

Fixpoint weak_normalization (n : nat) : nat :=
  let bar := weak_normalization n in
  0.

Print Assumptions weak_normalization.
(** [Closed under the global context]
    This means neither axioms were used nor any checker was disabled *)



(** * Intermezzo: [interleave] function *)

(** ** Elegant, but non-structural recursive [interleave] function *)

Unset Guard Checking.
Fixpoint interleave_ns {T} (xs ys : seq T)
           {struct xs} : seq T :=
  if xs is (x :: xs') then x :: interleave_ns ys xs'
  else ys.

(** A simple unit test. *)
Check erefl :
interleave_ns [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].
(** As you can see the evaluator does not care
    if the function passes the guardedness check
    or not *)

Print Assumptions interleave_ns.
(**
  Axioms:
  interleave_ns is positive.
*)


(** Here is how [interleave] can be actually defined in Coq: *)
Set Guard Checking.
Fixpoint interleave {T} (xs ys : seq T) : seq T :=
  match xs, ys with
  | (x :: xs'), (y :: ys') =>
       x :: y :: interleave xs' ys'
  | [::], _ => ys
  | _, [::] => xs
  end.

(** We can even prove the two implementations
    are "the same" *)
Lemma interleave_ns_eq_interleave {T} :
  (@interleave_ns T) =2 (@interleave T).
Proof.
by elim=> // x xs IHxs [|y ys] //=; rewrite IHxs.
Qed.


(** Coq offers more ways of defining [interleave]
    function *)

(** ** 1. Using the builtin [Function] plugin *)

(** To activate [Function] plugin,
    this makes available a new piece of vernacular:
    [Function] *)
From Coq Require Import Recdef.

Definition sum_len {T} (xs_ys : seq T * seq T) : nat :=
  length xs_ys.1 + length xs_ys.2.

Function interleave_f' {T} (xs_ys : (seq T * seq T))
         {measure sum_len xs_ys} : seq T :=
  if xs_ys is (x :: xs', ys) then
    x :: interleave_f' (ys, xs')
  else [::].
Proof.
move=> X xs_ys xs ys x xs' _ _.
by rewrite /sum_len /= addnC.
Qed.
(**
Notice a bunch of autogenerated definitions:

interleave_f'_tcc is defined
interleave_f'_terminate is defined
interleave_f'_ind is defined
interleave_f'_rec is defined
interleave_f'_rect is defined
R_interleave_f'_correct is defined
R_interleave_f'_complete is defined
 *)

Fail Check erefl :
  interleave_f' ([:: 1; 3], [:: 2; 4]) =
  [:: 1; 2; 3; 4].
Eval hnf in interleave_f' ([:: 1; 3], [:: 2; 4]).
(**
The above gets stuck on:
  = let (v, _) :=
      interleave_f'_terminate ([:: 1; 3], [:: 2; 4])
    in v
  : seq nat
*)
About interleave_f'_terminate.
(**
...
interleave_f'_terminate is opaque
...
 *)

(** First, we are going to fix evaluation
    by making [interleave_f_terminate]
    transparent: *)
Function interleave_f {T} (xs_ys : (seq T * seq T))
         {measure sum_len xs_ys} : seq T :=
  if xs_ys is (x :: xs', ys) then
    x :: interleave_f (ys, xs')
  else [::].
Proof.
move=> X xs_ys xs ys x xs' _ _.
by rewrite /sum_len /= addnC.
(** [Defined] makes [interleave_f_terminate]
    transparent *)
Defined.

(** Now evaluation works: *)
Check erefl :
  interleave_f ([:: 1; 3], [:: 2; 4]) =
  [:: 1; 2; 3; 4].
About interleave_f_terminate.
(**
...
interleave_f_terminate is transparent
...
*)


(** Now let us see how [interleave_f] is built *)
Print interleave_f.
(**
interleave_f =
fun (x : Type) (x0 : seq x * seq x) =>
  let (v, _) := interleave_f_terminate x0 in v
     : forall x : Type, seq x * seq x -> seq x
*)
About interleave_f_terminate.
(**
interleave_f_terminate :
forall (T : Type) (xs_ys : seq T * seq T),
{v : seq T |
exists p : nat,
  forall k : nat,
  (p < k)%coq_nat ->
  forall def : forall T0 : Type,
                 seq T0 * seq T0 -> seq T0,
  iter (forall T0 : Type, seq T0 * seq T0 -> seq T0)
       k
       interleave_f_F
       def
       T
       xs_ys
  = v}
*)

(** Under the hood [interleave_f_terminate]
    is (of course) a structural recursive function.
    To understand what type we do recursion over,
    let's print the definition of the function and
    search for [fix] *)
Print interleave_f_terminate.
(**
...
fix hrec (T0 : Type) (xs_ys0 : seq T0 * seq T0)
         (Acc_xs_ys0 : Acc (Wf_nat.ltof
                              (seq T0 * seq T0)
                              [eta sum_len])
                           xs_ys0)
         {struct Acc_xs_ys0} :
...
*)

(** Here we meet the accessibility predicate [Acc]
    which can be used to define well-founded
    induction principles *)
Print Acc.
(**
Inductive Acc (A : Type)
              (R : A -> A -> Prop)
              (x : A) : Prop :=
  | Acc_intro :
      (forall y : A, R y x -> Acc R y) -> Acc R x

[Acc R x] can be read as "x is accessible under
relation R if all elements staying in relation R
with it are also accessible"
*)

(** Notice that Coq allows us do structural
    recursion on a term of type [Acc]
    which lives in [Prop] while building
    a term of a type living in [Type].
    (structural recursion involves pattern-matching).
    But the accessibility predicate is defined
    to be non-informative (one constructor!).
 *)



(** ** More on choice operator *)
Section Find.

(** Getting a concrete value from
    an abstract existence proof. *)

Variable (P : pred nat).

(** This construction lets us count up *)
Inductive acc_nat i : Prop :=
| AccNat0 of P i
| AccNatS of acc_nat i.+1.

Lemma find_ex :
  (exists n, P n) -> {m | P m}.
Proof.
move=> exP.

have: acc_nat 0.
  case exP => n; rewrite -(addn0 n); elim: n 0 => [|n IHn] j; first by left.
  by rewrite addSnnS; right; apply: IHn.

move: 0.
fix find_ex 2 => m IHm.
case Pm: (P m).
- by exists m.
apply: find_ex m.+1 _.
case: IHm.
- by rewrite Pm.
by [].
Defined.

End Find.



(** ** 2. Using the builtin [Program] mechanism *)

From Coq Require Import Program.

Program Fixpoint interleave_p {A} (xs ys : seq A)
  {measure (length xs + length ys)} : list A :=
  if xs is (x :: xs') then
    x :: interleave_p ys xs'
  else ys.
Next Obligation. by rewrite addnC. Qed.

Check erefl :
  interleave_p [:: 1; 3] [:: 2; 4] =
  [:: 1; 2; 3; 4].

(** [Program] also relies on [Acc] predicate *)

Print Assumptions interleave_p.
(** [Closed under the global context]

    But sometimes [Program] relies on
    [JMeq_eq] axiom to do dependent pattern
    matching.
 *)
Check JMeq_eq.
(**
JMeq_eq : forall (A : Type) (x y : A),
            x ~= y -> x = y
*)
Print JMeq.
(**
"JMeq" means "John Major equality", a.k.a.
heterogenous equality.

Inductive JMeq (A : Type) (x : A) :
  forall B : Type, B -> Prop :=
| JMeq_refl : x ~= x

[~=] is a notation for [JMeq]
*)


(** ** 3. Using the [Equations] plugin *)

(** The plugin can be installed via opam:
      opam install coq-equations *)

From Equations Require Import Equations.

Equations interleave_e {T} (xs ys : seq T) : seq T
  by wf (length xs + length ys) lt :=
interleave_e (x :: xs) ys :=
  x :: (interleave_e ys xs);
interleave_e [::] ys :=
  ys.
Next Obligation. by rewrite addnC. Qed.

Check erefl :
  interleave_e [:: 1; 3] [:: 2; 4] =
  [:: 1; 2; 3; 4].


(** One more trick to teach Coq termination:
    nested [fix] *)

(** Ackermann's function *)

Fixpoint ack (n m : nat) : nat :=
  if n is n'.+1 then
    let fix ackn (m : nat) :=
        if m is m'.+1 then ack n' (ackn m')
        else ack n' 1
    in ackn m
  else m.+1.




(** * Strict positivity rule *)

Print Typing Flags.

Fail Inductive prop :=
  RemoveNegation of (prop -> False).
(**
Non strictly positive occurrence of "prop" in
"(prop -> False) -> prop".
*)

Unset Guard Checking.
Print Typing Flags.

Inductive prop :=
  RemoveNegation of (prop -> False).
Print Assumptions prop.
(**
Axioms:
prop is positive.
*)

Definition not_prop (p : prop) : False :=
  let '(RemoveNegation not_p) := p in not_p p.
Check not_prop : prop -> False.

Check RemoveNegation not_prop : prop.

Definition yet_another_proof_of_False : False :=
  not_prop (RemoveNegation not_prop).

Print Assumptions yet_another_proof_of_False.
(**
Axioms:
yet_another_proof_of_False is positive.
not_prop is positive.
prop is positive.
*)
Set Guard Checking.

(**
Roughly, the positivity condition says that
constructors for an inductive data type can
only depend on maps to the data type but not on
maps from it.
*)



(** * Bonus: Universe polymorphism *)

Definition idf {A} : A -> A := fun x => x.
Fail Definition selfidfun := idf (@idf).
(**
The term "@idf" has type "forall A : Type, A -> A"
while it is expected to have type "?A"
(unable to find a well-typed instantiation for "?A": cannot ensure that
"Type@{Top.1849+1}" is a subtype of "Type@{Top.1849}").
*)

Set Universe Polymorphism.

Definition idf' {A} : A -> A := fun x => x.
Definition selfidfun' := idf' (@idf').
Print selfidfun'.

(** See more examples in the Coq Reference Manual *)
