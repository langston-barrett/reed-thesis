(** * Universal objects *)
Require Import Category.Core Category.Morphisms.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Definition of "unique up to isomorphism" *)

Definition unique_up_to_isomorphism (C : PreCategory) (P : C -> Type) :=
  forall x (_ : P x) x' (_ : P x'), { c : morphism C x x' | IsIsomorphism c }.

Arguments unique_up_to_isomorphism [C] P.

(** ** Product objects *)
(** A product of objects A and B consists of:

     (i) an object P

     (ii) arrows π1 : P → A and π2 : P → B (called projections)

    satisfying the following condition: For any object X and arrows f : X → A
    and g : X → B, there is a unique arrow ⟨f,g⟩ : X → P such that the
    following diagram commutes:

      +------------- X ------------+
      |              |             |
      | f            | ⟨f,g⟩       | g
      |              |             |
      V      π1      V      π2     V
      A <----------- P ----------> B
*)
Notation IsProduct C a b p :=
  { projections : (morphism C p a * morphism C p b)
  | forall (x : object C) (f : morphism C x a) (g : morphism C x b),
      Contr { fg : morphism C x p
            | (fst projections) o fg = f & (snd projections) o fg = g}}.

(* Definition IsProduct (C : PreCategory) (a b p : C) *)
(*                      (proj1 : morphism C p a) *)
(*                      (proj2 : morphism C p b) : Type := *)
(*   forall (x : object C) (f : morphism C x a) (g : morphism C x b), *)
(*       Contr { fg : morphism C x p *)
(*             | proj1 o fg = f & proj2 o fg = g}. *)

Record ProductObject (C : PreCategory) :=
  {
    object_product :> C;
    factor1 : C;
    factor2 : C;
    proj1 : morphism C object_product factor1;
    proj2 : morphism C object_product factor2;
    isproduct_object_product :>
      IsProduct C factor1 factor2 object_product;
  }.

(** ** Initial and terminal objects are unique up to unique isomorphism *)
Section CategoryObjectsTheorems.
  Variable C : PreCategory.

  Definition sig_of_sig2 (A : Type) (P Q : A -> Type) (X : sig2 P Q) : sig P
    := exist P
            (let (a, _, _) := X in a)
            (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

  Definition proj3_sig (A : Type) (P Q : A -> Type) (e : sig2 P Q) :=
    let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.

  Theorem product_object_unique
    : forall (a b : C),
      unique_up_to_isomorphism (fun x => IsProduct C a b x).
  Proof.
    (* Break down relevant definitions and hypotheses *)
    intros a b.
    intros product1 isproduct1 product2 isproduct2.
    destruct isproduct1 as [[proj1a proj1b] universal1].
    destruct isproduct2 as [[proj2a proj2b] universal2].

    (* Construct a morphism ϕ : product1 → product2 *)
    unfold fst, snd in universal1, universal2.
    destruct (universal2 product1 proj1a proj1b)
      as [[phi proj2a_phi proj2b_phi] _]. (* We won't need uniqueness *)
    exists phi.

    (* Construct an inverse for phi *)
    destruct (universal1 product2 proj2a proj2b)
      as [[psi proj2a_psi proj2b_psi] _].
    (* destruct (universal1 product1 proj1a proj1b) *)
    (*   as [[identity' proj1a_id proj1b_id] id_uniq]. *)

    (* Prove that ϕ is an isomorphism *)
    refine ({| morphism_inverse := psi; left_inverse := _; right_inverse := _; |}).
    { (* psi o phi = 1 *)

      (* Construct the correct sig2 instances *)
      pose (construct_sig2 := exist2 (fun m => proj1a o m = proj1a)
                                     (fun m => proj1b o m = proj1b)).
      pose (exist_id := construct_sig2 1 (right_identity C _ _ _)
                                         (right_identity C _ _ _)).
      pose (exist_psi_phi :=
              construct_sig2
                (psi o phi)
                (transitivity
                  (associativity_sym _ _ _ _ _ phi psi proj1a)
                  (transitivity (ap (fun m => m o phi) proj2a_psi) proj2a_phi))
                (transitivity
                  (associativity_sym _ _ _ _ _ phi psi proj1b)
                  (transitivity (ap (fun m => m o phi) proj2b_psi) proj2b_phi))).

      assert (exist_id_pr1 : (pr1 (sig_of_sig2 exist_id)) = 1) by reflexivity.
      rewrite <- exist_id_pr1.
      assert (Heq : exist_id = exist_psi_phi).
      {
        transitivity (@center _ (universal1 product1 proj1a proj1b));
          try (apply contr); symmetry; apply contr.
      }
      rewrite Heq.
      reflexivity.
    }
    { (* phi o psi = 1 *)

      (* Construct the correct sig2 instances *)
      pose (construct_sig2 := exist2 (fun m => proj2a o m = proj2a)
                                     (fun m => proj2b o m = proj2b)).
      pose (exist_id := construct_sig2 1 (right_identity C _ _ _)
                                         (right_identity C _ _ _)).
      pose (exist_psi_phi :=
              construct_sig2
                (phi o psi)
                (transitivity
                  (associativity_sym _ _ _ _ _ psi phi proj2a)
                  (transitivity (ap (fun m => m o psi) proj2a_phi) proj2a_psi))
                (transitivity
                  (associativity_sym _ _ _ _ _ psi phi proj2b)
                  (transitivity (ap (fun m => m o psi) proj2b_phi) proj2b_psi))).

      assert (exist_id_pr1 : (pr1 (sig_of_sig2 exist_id)) = 1) by reflexivity.
      rewrite <- exist_id_pr1.
      assert (Heq : exist_id = exist_psi_phi).
      {
        transitivity (@center _ (universal2 product2 proj2a proj2b));
          try (apply contr); symmetry; apply contr.
      }
      rewrite Heq.
      reflexivity.
    }
  Qed.
End CategoryObjectsTheorems.