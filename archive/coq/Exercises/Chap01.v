Require Import HoTT.Basics.Overture.
Require Import Coq.Unicode.Utf8.

Global Set Universe Polymorphism.

(* ========================================= Exercise 1.1 *)

Definition 𝒰 := Type.

Definition comp {A B C : 𝒰} (f : A -> B) (g : B -> C) : (A -> C) :=
  fun x => g(f(x)).

Notation "g ∘ f" := (comp f g) (at level 51, right associativity).

Fact comp_assoc :
  forall {A B C D : 𝒰} (f : A -> B) (g : B -> C) (h : C -> D),
    h ∘ g ∘ f = h ∘ g ∘ f.
Proof.
  reflexivity.
Qed.

(* ========================================= Exercise 1.2 *)

(* ====== Product *)
Notation "A × B" := (A * B) (at level 52).
Section OneTwoProd.
  Require Import Init.Datatypes.
  Local Definition π1 {A B} := @fst A B.
  Local Definition π2 {A B} := @snd A B.

  Definition rec_prod {A B : 𝒰} (C : 𝒰) :  (A -> B -> C) -> (A × B) -> C :=
    fun f p => f (π1 p) (π2 p).

  Fact rec_prod_pr1 :
    ∀ {A B C : 𝒰}, @rec_prod A B A  (fun a b => a)  = π1.
  Proof. reflexivity. Qed.

  Fact rec_prod_pr2 :
    ∀ {A B C : 𝒰}, @rec_prod A B B  (fun a b => b)  = π2.
  Proof. reflexivity. Qed.

  Fact rec_def_eq : ∀ (A B C : 𝒰) (g : A → B → C) (p : A × B), 
      rec_prod C g p = g (π1 p) (π2 p).
  Proof. reflexivity. Qed.
End OneTwoProd.

(* ====== Coproduct *)
Section OneTwoSigma.
  Require Import Init.Datatypes.
  Local Definition Π1 {A P} := @proj1_sig A P.
  Local Definition Π2 {A P} := @proj2_sig A P.
  (* Definition 𝛱 := forall. *)
  Definition Σ A B := @sigT A B.

  Definition rec_sig {A : 𝒰} {B : A → 𝒰} (C : 𝒰) :
      (∀ x : A, B x → C) → Σ A B → C :=
    fun f p => f (Π1 p) (Π2 p).

  (* Define pr1, pr2 in terms of the recursor we just defined *)
  Local Definition sig_pr1 {A : 𝒰} {B : A → 𝒰} : Σ A B → A :=
    @rec_sig A B A (fun a b => a).

  (* Prove equivalence of the recursor-based definitions with the Coq ones *)
  Fact rec_sig_pr1 : ∀ {A : 𝒰} {B : A → 𝒰}, @sig_pr1 A = @Π1 A.
  Proof. reflexivity. Qed.

  (* From HoTT/HoTT/contrib/HoTTBookExercises.V *)
  (** NB: You cannot implement pr2 with only the recursor, so it is not possible
      to check its definitional equality as the exercise suggests. *)
  
  (* Local Definition sig_pr2 {A : 𝒰} {B : A → 𝒰} : ∀ {p : Σ A B}, B (Π1 p) := *)
  (*   fun p => (@rec_sig A B (B (Π1 p)) (fun a b => b)) p. *)

  (* Fact rec_sig_pr2 : ∀ {A : 𝒰} {B : A → 𝒰}, @sig_pr2 A = @Π2 A. *)
  (* Proof. reflexivity. Qed. *)

  Fact rec_sig_def_eq : ∀ {A : 𝒰} {B : A → 𝒰} {C : 𝒰}
                          (g : ∀ x : A, B x → C) (p : Σ A B),
      @rec_sig A B C g p = g (Π1 p) (Π2 p).
  Proof. reflexivity. Qed.
End OneTwoSigma.

(* ========================================= Exercise 1.3 *)


(* ========================================= Exercise 1.4 *)

Fixpoint iter {C : 𝒰} (c0 : C) (cs : C → C) (n : nat) : C :=
  match n with
    0 => c0
  | S m => cs (iter c0 cs m)
  end.

Definition cs_pair {C : 𝒰} (cs : nat → C → C) : (nat * C) → (nat * C) :=
  (fun pair => (S (π1 pair), cs (π1 pair) (π2 pair))).

Definition rec_nat {C : 𝒰} (c0 : C) (cs : nat → C → C) : nat → C :=
  π2 ∘ iter (0, c0) (cs_pair cs).

Lemma unfold_iter : ∀ C c0 cs n, @iter C c0 cs (S n) = cs (@iter C c0 cs n).
Proof. reflexivity. Qed.

Lemma apply_proj1 : ∀ A B (a : A) (b : B), π1 (a, b) = a.
Proof. reflexivity. Qed.

Lemma apply_proj2 : ∀ A B (a : A) (b : B), π2 (a, b) = b.
Proof. reflexivity. Qed.

Lemma proj1_iter_pair : ∀ C c0 cs n, π1 (@iter (nat × C) (0, c0) (cs_pair cs) n) = n.
Proof.
  induction n; try reflexivity.
  rewrite unfold_iter.
  unfold cs_pair at 1.
  rewrite IHn.
  reflexivity.
Qed.

Fact rec_nat_prop_eq : ∀ {C : 𝒰} (c0 : C) (cs : nat → C → C) (n : nat),
    rec_nat c0 cs (S n) = cs n (rec_nat c0 cs n).
Proof.
  induction n; try reflexivity.
  unfold rec_nat at 1, "∘".
  rewrite unfold_iter.
  unfold cs_pair at 1.
  rewrite apply_proj2.
  rewrite proj1_iter_pair.
  unfold rec_nat, "∘".
  reflexivity.
Qed.

(* ========================================= Exercise 1.5 *)

(* Unclear what it's asking for... What definitional equalities? *)

(* ========================================= Exercise 1.6 *)

(* Unclear what it's asking for... What definitional equalities? *)

(* ========================================= Exercise 1.7 *)

(* ========================================= Exercise 1.8 *)

Fixpoint rec_nat' (C : 𝒰) c0 cs (n : nat) : C :=
  match n with
    0 => c0
  | S m => cs m (rec_nat' C c0 cs m)
  end.

Definition add : nat → nat → nat :=
  rec_nat' (nat → nat) (fun m => m) (fun n g m => (S (g m))).

Definition mult : nat → nat → nat  :=
  rec_nat' (nat → nat) (fun m => 0) (fun n g m => add m (g m)).

Definition exp' : nat → nat → nat  :=
  rec_nat' (nat → nat) (fun m => 1) (fun n g m => mult m (g m)).

Definition flip {A B C : 𝒰} (f : A → B → C) : (B → A → C) :=
  fun b a => f a b.

Definition exp := flip exp'.

Notation "n ** m" := (exp' m n).

(* Definition of semiring from Wikipedia:

(R, +) is a commutative monoid with identity element 0:
    (a + b) + c = a + (b + c)
    0 + a = a + 0 = a
    a + b = b + a
(R, ⋅) is a monoid with identity element 1:
    (a⋅b)⋅c = a⋅(b⋅c)
    1⋅a = a⋅1 = a
Multiplication left and right distributes over addition:
    a⋅(b + c) = (a⋅b) + (a⋅c)
    (a + b)⋅c = (a⋅c) + (b⋅c)
Multiplication by 0 annihilates R:
    0⋅a = a⋅0 = 0 
*)

Lemma add_s_left: ∀ a b : nat, add (S a) b = S (add a b). reflexivity. Qed.
Lemma add_s_right : ∀ a b : nat, add a (S b) = S (add a b).
  induction a; intros b; try reflexivity.
  do 2 rewrite add_s_left.
  rewrite IHa.
  reflexivity.
Qed.

Fact plus_assoc : ∀ a b c : nat, (add a) (add b c) = add (add a b) c.
  induction a; try reflexivity.
  intros b c.
  do 3 rewrite add_s_left.
  rewrite IHa.
  reflexivity.
Qed.

Fact plus_unit_left : ∀ n : nat, add 0 n = n. reflexivity. Qed.

Fact plus_unit_right : ∀ n : nat, add n 0 = n.
  induction n; try reflexivity.
  rewrite add_s_left; rewrite IHn; reflexivity.
Qed.

Fact plus_commutative : ∀ a b : nat, add a b = add b a.
  induction a; intros b.
  {
    rewrite plus_unit_right; reflexivity.
  }
  {
    rewrite add_s_left, add_s_right.
    rewrite IHa.
    reflexivity.
  }
Qed.

Notation "x ⋅ y" := (mult x y) (at level 53).

Lemma mult_s_left : ∀ a b, (S a) ⋅ b = add b (a ⋅ b). reflexivity. Qed.
Lemma mult_s_right : ∀ a b, a ⋅ (S b) = add a (a ⋅ b).
  induction a; intros b; try reflexivity.
  do 2 rewrite mult_s_left.
  do 2 rewrite add_s_left.
  rewrite IHa.
  do 2 rewrite plus_assoc.
  assert (eqab : add b a = add a b) by (apply plus_commutative).
  rewrite eqab; reflexivity.
Qed.

Fact mult_annihilate_left : ∀ n, 0 ⋅ n = 0. reflexivity. Qed.
Fact mult_annihilate_right : ∀ n, n ⋅ 0 = 0.
  induction n; try reflexivity.
  rewrite mult_s_left.
  rewrite plus_unit_left.
  exact IHn.
Qed.

Fact mult_assoc : ∀ a b c : nat, a ⋅ (b ⋅ c) = (a ⋅ b) ⋅ c.
  induction a; try reflexivity.
  induction b.
  - intros c.
    rewrite mult_annihilate_left.
    rewrite mult_annihilate_right.
    rewrite mult_annihilate_left.
    reflexivity.
Admitted.

Fact mult_unit_left : ∀ n : nat, 1 ⋅ n = n. apply plus_unit_right. Qed.

Fact mult_unit_right : ∀ n : nat, n ⋅ 1 = n.
  induction n; try reflexivity.
  rewrite mult_s_left; rewrite IHn; reflexivity.
Qed.

(* ========================================= Exercise 1.9 *)
(* ========================================= Exercise 1.10 *)
(* ========================================= Exercise 1.11 *)
(* ========================================= Exercise 1.12 *)
(* ========================================= Exercise 1.13 *)
(* ========================================= Exercise 1.14 *)
(* ========================================= Exercise 1.15 *)
(* ========================================= Exercise 1.16 *)
(* ========================================= Exercise 1.17 *)