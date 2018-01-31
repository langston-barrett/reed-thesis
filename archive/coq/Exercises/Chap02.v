Require Import HoTT.Basics.Overture.
Require Import Coq.Unicode.Utf8.

Global Set Universe Polymorphism.

Definition 𝒰 := Type.

Definition concatenation1 : ∀ {A : 𝒰} (x y z : A), x = y → y = z → x = z.
  intros A x y z x_eq_y y_eq_z.
  induction x_eq_y.
  induction y_eq_z.
  reflexivity.
Defined.

Definition concatenation2 : ∀ {A : 𝒰} (x y z : A), x = y → y = z → x = z.
  intros A x y z x_eq_y y_eq_z.
  induction x_eq_y.
  exact y_eq_z.
Defined.

(* Definition straight from induction *)
Definition concatenation2' {A : 𝒰} : ∀ (x y : A), x = y → ∀ z : A, y = z → x = z :=
  @paths_ind' A (fun x y p => ∀ (z : A) (q : y = z), (x = z)) (fun x z q => q).

Definition concatenation2'' {A : 𝒰} (x y z : A) : x = y → y = z → x = z :=
  fun p q => concatenation2' x y p z q.

Definition concatenation3 : ∀ {A : 𝒰} (x y z : A), x = y → y = z → x = z.
  intros A x y z x_eq_y y_eq_z.
  induction y_eq_z.
  exact x_eq_y.
Defined.

(* TODO: Should I be using functional extensionality? *)
(* TODO: If so, we need concatenation123 to be functions of one or two arguments *)
Lemma concatenation1_eq_concatenation2 : `{Funext} → concatenation1 = concatenation2.
  intros fx.
  apply path_forall.
  intros x.
  unfold "==".
Admitted.