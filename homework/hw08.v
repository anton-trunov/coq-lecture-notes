From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma enum_example m (r : rel 'I_m) f v (x : nat) :
  (forall j, r v j -> f v j > 0) ->
  x \in [seq f v j | j <- enum 'I_m & r v j] ->
  0 < x.
Proof.
Admitted.



Section TriFinType.
(** Define [finType] structure for the following datatype *)
(**
Hints:
1. To build a [finType] structure you need to build all of its parent structures,
   i.e. [eqType], [choiceType], [countType].
2. An easy way to solve this is to use [CanChoiceMixin], [CanCountMixin], and [CanFinMixin] constructors.
3. The above hint requires mapping [tri] into an already existsing isomorphic [finType], e.g. [ordinal].
4. The [ordinal] type from above is ['I_3]

 *)
(** CanFinMixin *)
Inductive tri : predArgType :=       (* [predArgType] is necessary to make [_ \in _] notation work, see below *)
| Yes | No | Maybe.


(** Your definitions here *)


(** This should work now: *)
Check (Yes != No) && (No \in tri) && (#| tri | == 3).
End TriFinType.



Section RecordFinType.

Variables A B C : finType.

(** Define [finType] structure for the following datatype *)
Record record : predArgType := Mk_record {
  field_A : A;
  field_B : B;
  field_C : C
  }.

(** This should work now: *)
Variable test : record.
Check (test == test) && (test \in record) && (#| record | == #| record |).

End RecordFinType.



Section DBranch.

Variable ft : finType.

(** Consider a sequence over a finite type with the restriction that all the sequence elements are unique *)
Structure dbranch : predArgType :=
  {branch :> seq ft;
   buniq : uniq branch}.

(** * Define [finType] structure for [dbranch] *)


(** Hints:
1. One way of building a [finType] structure is to embed the new construction
   into a (possibly bigger) finite type.
2. [sigT] is like [sig], but allows the second projection to live in [Type], not in [Prop].
3. Build an embedding of [dbranch] into {k : 'I_#|ft|.+1 & k.-tuple ft}
   and its partial inverse, i.e.

    Definition tag_of_dbranch d : {k : 'I_#|ft|.+1 & k.-tuple ft} := ...
    Definition dbranch_of_tag (t : {k : 'I_#|ft|.+1 & k.-tuple ft}) : option dbranch := ...

4. [PcanFinMixin] is very useful in this setting.
*)

(** Your definitions here *)

(** This should work now: *)
Variable test : dbranch.
Check (test == test) && (test \in dbranch) && (#| dbranch | == #| dbranch |).

End DBranch.



(** Bonus exercises:
There is a library to reduce boilerplate while building instances of basic MathComp classes
for inductive data types: https://github.com/arthuraa/deriving.
Install it (it's available from extra-dev opam repository) an use it to solve some of the above exercise.
*)

