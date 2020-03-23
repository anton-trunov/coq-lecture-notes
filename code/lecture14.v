(** * Verification of imperative programs *)

(**
Verifiable C
- C light intermediate language
  • Dialect of C with side effects
    factored out of expressions;
  • No casting between integers
    and pointers;
  • No goto statements;
  • Only structured switch statements
    (no Duff’s device)
- Program logic for reasoning about
  the functional correctness of C programs
  (higher-order separation logic)
*)


(**
Verifiable C is foundationally sound:
all proven properties of C programs
are preserved by translation down to the
assembly code.

The program logic is proved sound with
respect to the semantics of CompCert C.

And the C compiler is proved correct with
respect to those same semantics.

This chain of proofs from top to bottom,
connected in Coq at specification
interfaces, is part of the Verified
Software Toolchain (VST).
*)

(**
Real-world verifications with VST:
- "Verified correctness and security of
   OpenSSL HMAC" - Beringer, Petcher, KQ, Appel (2015)
- "Verification of a cryptographic
   primitive: SHA-256" - Appel(2015)

See "Position paper:
     the Science of Deep Specification" -
     A.W. Appel, L. Beringer, A. Chlipala,
     B.C. Pierce, Z. Shao, S. Weirich,
     S. Zdancewic(2017)
*)

(**
How to install VST:
- Make sure you have Coq 8.10
- opam install coq-compcert.3.6
- git clone https://github.com/PrincetonUniversity/VST
- cd VST
- make IGNORECOQVERSION=true -j3

See also "Verifiable C" by A.W. Appel
*)


(** Let's consider a concrete example:
    sumarray.c program, this example
    is a slightly adopted version of
    VST's sumarray example described
    in "Verifiable C" by A.W. Appel,
    version 2.4 *)

(**
First, we need to embed it into Coq
using CompCert's [clightgen] tool:

clightgen -normalize sumarray.c

[clightgen] translates C into
abstract syntax trees (ASTs) of Clight:
• Factors out function calls and
  assignments from inside subexpressions;
• Factors [&&] and [||] operators into
  [if] statements;
• When the [-normalize] flag is used,
  factors each memory dereference into
  a top level expression, i.e.
    x=a[b[i]];
  becomes
    t=b[i]; x=a[t].

This is needed because the program logic
works only on a restricted subset of
the language.

To see the result of this translation
take a look at sumarray.v file.
But you don't have to do it usually.
 *)

(** some automation *)
From Coq Require Import Lia.

(** The directory you installed VST into *)
Add LoadPath "~/prj/coq/vst/".

(** Import the Verifiable C system *)
From VST Require Import floyd.proofauto.


(** Import the AST of sumarray C program *)
From VST Require Import sumarray.

(** The next few line is "boilerplate",
    always required after importing an AST
 *)
Instance CompSpecs : compspecs.
  make_compspecs prog. Defined.
Definition Vprog : varspecs.
  mk_varspecs prog. Defined.

(** Functional spec of this program:
    Notice that it is independent of
    sumarray.v file
 *)
Definition sum_Z : list Z -> Z :=
  fold_right Z.add 0.

Lemma sum_Z_app a b :
  sum_Z (a ++ b) =  sum_Z a + sum_Z b.
Proof.
  induction a; simpl; lia.
(** Vanilla tactics!
- [induction] == [elim]
- [simpl] == [move=> /=]
- [lia] -- linear integral arithmetic
           solver
 *)
Qed.

(** Beginning of the API spec
    for the sumarray.c program.
    Funspecs correspond to
    function prototypes.
 *)
Definition sumarray_spec :
  ident * funspec :=

DECLARE _sumarray
 WITH a: val, sh : share,
      contents : list Z, size: Z
 PRE [ _a OF (tptr tuint), _n OF tint ]
   PROP (
     (** [PROP] desribes propositions
         independent of state *)
     readable_share sh;
     0 <= size <= Int.max_signed;
     Forall
      (fun x => 0 <= x <= Int.max_unsigned)
      contents
   )
   LOCAL (
     (** variable bindings of type
         [localdef]
         relate C local variables to
         Coq values *)
     temp _a a;
     temp _n (Vint (Int.repr size))
   )
   SEP (
     (** spatial assertions in
         separation logic *)
     data_at
       sh
       (tarray tuint size)
       (map Vint (map Int.repr contents))
       a
     (** This says that at address [a]
         there is an array of type
         unsigned int [size] with
         access-permission [sh] and the
         contents is a list related to
         [contents] *)
   )
 POST [ tuint ]
   PROP ()
   LOCAL (
     temp
       ret_temp
       (Vint (Int.repr (sum_Z contents)))
   )
   SEP (
     data_at
       sh
       (tarray tuint size)
       (map Vint (map Int.repr contents))
       a
   ).

(** Note:
It would also be reasonable to let
[contents] have type [list int].
Then the [Forall] would not be needed
in the [PROP] part of [PRE].
*)

(** The precondition of "int main(void){}"
    always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt nil gv
  POST [ tint ]
     PROP()
     LOCAL (
       temp ret_temp
            (Vint (Int.repr (1+2+3+4)))
     )
     SEP(
       (** trivially true
           spatial predicate *)
       TT
     ).

(** Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  (** [ltac] quotation *)
  ltac:(
    with_library
      prog [sumarray_spec; main_spec]
  ).


(** Proof that [f_sumarray],
    the body of the "sumarray()" function,
    satisfies [sumarray_spec],
    in the global context ([Vprog],[Gprog])
 *)
Lemma body_sumarray:
  semax_body (** Hoare triple of
                 the function body *)
    Vprog (** global variables context *)
    Gprog (** global functions context *)
    f_sumarray
    sumarray_spec.
Proof.
(** Always do this at the beginning of
    a semax_body proof *)
start_function.

(** The next two lines do forward
    symbolic execution through
    the first two executable statements
    of the function body *)
forward.  (* i = 0; *)
forward.  (* s = 0; *)
(** To do symbolic execution through
    a [while] loop, we must provide
    a loop invariant, so we use
    [forward_while] with the invariant
    as an argument .*)
forward_while
 (EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (
    temp _a a;
    temp _i (Vint (Int.repr i));
    temp _n (Vint (Int.repr size));
    temp _s (Vint (Int.repr
           (sum_Z (sublist 0 i contents))))
   )
   SEP (
     data_at
       sh
       (tarray tuint size)
       (map Vint (map Int.repr contents)) a
   )
 ).

(** [forward_while] leaves four subgoals *)

- (** Current precondition implies
      loop invariant *)
(* Instantiate the existential
   on the right-side of |-- *)
Exists 0.
(* Simplify this entailment *)
entailer!.
- (** loop invariant implies
      typechecking condition *)
entailer!.
- (** Prove postcondition of loop body
      implies loop invariant *)
Fail forward.
assert_PROP (Zlength contents = size). {
  entailer!. now rewrite !Zlength_map.
}
forward. (* x = a[i] *)
forward. (* s += x; *)
forward. (* i++; *)
(** Now we have reached the end of
    the loop body, and it's time to prove
    that the _current precondition_
    entails the loop invariant. *)
 Exists (i+1).
 entailer!.
 f_equal.
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite sum_Z_app, (sublist_one i) by lia.
 now simpl; rewrite Z.add_0_r.
- (** After the loop *)
forward.  (* return s; *)
(* postcondition of the function body
   entails the postcondition of funspec *)
entailer!.
autorewrite with sublist in *.
now autorewrite with sublist.
Qed.

(** Contents of the extern global
    initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:
  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call (*  s = sumarray(four,4); *)
  (gv _four, Ews,four_contents,4).
split3. auto. computable.
repeat constructor; computable.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_sumarray.
  semax_func_cons body_main.
Qed.


(** ==================================== *)


(**
What have we covered so far:
- The SSReflect proof language
- Elements of intuitionistic logic
- Curry-Howard correspondence
- Patterns of proofs by induction
- A bit of proof automation: lia (omega)
- The building blocks of the Mathcomp library:
  • Boolean reflection
  • Canonical Structures
  • Coercions, Notations
  • Phantom types
- Subtyping
- Commonly used axioms:
  • Axiom K
  • Proof irrelevance
  • Functional extensionality
- Totality
- Prop vs Type
- Hinted at Universe Polymorphism
- Inductive predicates
- A bit of tooling:
  • Program, Function builtin plugins
  • Equations plugin
  • QuickChick plugin
  • Typing Flags plugin
- Introduction to specification and verification of
  functional algorithms
- A survey of approaches to verifying of
  imperative heap manipulating programs
- Verification of C programs using VST
 *)


(** ==================================== *)


(**
What we did NOT cover in this course:
- We did not address logic and Calculus of Inductive
  Constructions formally
- Vanilla Coq tactics
- Coq Standard Library
- Ltac hacking and proof automation
  • Ltac2, Mtac/Mtac2, Rtac, coq-elpi
  • CoqHammer, SMTcoq
- Advanced dependently typed programming
- Module system
- Typeclasses
- Generalized rewriting
- SProp (proof irrelevant propositions)
  see "Definitional Proof-Irrelevance
  without K" by G. Gilbert et al.(2019)
  • Definition irrelevance
                 (A:SProp) (P:A -> Prop)
                 (x:A) (v:P x) (y:A)
                 : P y
     := v.
- Native binary integers
- More tooling:
  • Handling of projects (_CoqProject & coq_makefile)
  • coqdoc, coqdep, coqchk
  • SerAPI (Coq Protocol Playground with Se(xp)rialization of Internal Structures)
- Ecosystem in the large
 *)


(** ==================================== *)


(** Further directions to explore
- For mathematically inclined --
  explore the Mathcomp library further,
  read the associated papers
  (https://github.com/math-comp/math-comp.github.io)
- Type theoretic foundations of Coq
  (to track recent developments see papers
   by Sozeau, Tabareau, Gilbert, Pedrot)
- (Concurrent) separation logic
- PL (meta-)theory
- Hardware verification:
  Kami by A. Chlipala
- A great review of the area: the deep
  spec paper mentioned above
- Exercises/competition:
  • https://www21.in.tum.de/~wimmers/proofground/
  • https://competition.isabelle.systems/competitions
  • https://www.codewars.com [Coq tag]
- Books:
  • The manual: https://coq.inria.fr/distrib/current/refman/
  • Coq'art by Casteran and Bertot
    (a great reference)
  • Software Foundation series
    (PL theory mostly)
  • Programs and Proofs - I. Sergey
    (ssreflect, HTT)
  • Mathcomp book
    (architecture of Mathcomp)
*)
