Require Import Category.Core Category.Morphisms.
(* Require Import HoTT.Tactics Types.Record Trunc HProp Types.Sigma Equivalences. *)
(* Require Import Coq.Unicode.Utf8. *)

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section iso.
  Variable C : PreCategory.
  Variables x y z : C.

  Local Set Refine Instance Mode.
  Global Instance inverse_compose
        `(@IsIsomorphism C x y iso1)
        `(@IsIsomorphism C y z iso2) : IsIsomorphism (iso2 o iso1)
    := { morphism_inverse := morphism_inverse iso1 o morphism_inverse iso2
       (* ; left_inverse := _ *)
       (* ; right_inverse := _ *)
       }.
  Proof.
    { (* left_inverse *)
      rewrite <- associativity.
      iso_collapse_inverse.
      apply left_inverse.
    }
    { (* right_inverse *)
      rewrite <- associativity.
      iso_collapse_inverse.
      apply right_inverse.
    }
  Qed.
End iso.
