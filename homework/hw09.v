From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma bij_card_eq (T T' : finType) (f : T -> T') :
  bijective f -> #|T| = #|T'|.
Proof.
Admitted.


Section bool_irrelevance.

Implicit Types b c : bool.

(** Let's define a projection function which projects any two
    proofs into one canonical proof: *)
Definition proj {b c} (pf : b = c) : b = c :=
  if b =P c is ReflectT pf'
  then pf'   (* the canonical proof *)
  else pf.   (* this is an impossible case, we could have used [False_rect] here *)

(** A key property of [proj] function *)
Lemma proj_constant {b c} :
  forall (pf1 pf2 : b = c), proj pf1 = proj pf2.
Proof.
Admitted.

(** Another key property of [proj]: it's invertible!
    (although we only need injectivity) *)

Definition join b c d (pf : b = c) : b = d -> c = d :=
  etrans (esym pf).

Definition proj_inv {b c} (pf : b = c) : b = c :=
  join (proj (erefl b)) pf.

Lemma trans_sym_eq b c :
  forall pf : b = c, join pf pf = erefl c.
Proof.
Admitted.

Lemma proj_cancL b c :
  cancel (@proj b c) (@proj_inv b c).
Proof.
Admitted.

Theorem bool_irrelevance b c :
  forall (pf1 pf2 : b = c), pf1 = pf2.
Proof.
Admitted.



(** Now let's put [bool_irrelevance] to work *)
Lemma UIP_refl b :
  forall (pf : b = b), pf = erefl b.
Proof.
Admitted.


(** The Altenkirch-Streicher K axiom for booleans.
    See also https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29
*)
Lemma Streicher_K b (P : b = b -> Prop) :
  P (erefl b) -> forall pf : b = b, P pf.
Proof.
Admitted.

End bool_irrelevance.
