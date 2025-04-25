Require Import Utf8.
Require Import Syntax Semantics Consistency.
Require Import Binding.Lib.
Require Import Classes.RelationClasses.
Require Import Relation_Operators.

Inductive answer : Set :=
  | ans_const (b : constant)
  | ans_function.

Inductive eval {A : Set} : term A → answer → Prop :=
  | eval_const (M : term A) (b : constant) :
    M =ₜ v_const b →
    eval M (ans_const b)
  | eval_function (M : term A) (N : term (inc A)) :
    M =ₜ v_lam N →
    eval M (ans_function).

Lemma eval_partial {A : Set} (M : term A) :
  uniqueness (eval M).
Proof.
  unfold uniqueness.
  intros ans₁ ans₂ Heval₁ Heval₂.
  destruct ans₁ as [b₁ |], ans₂ as [b₂ |].
  + inversion Heval₁ as [? ? Heq₁ |]; subst.
    inversion Heval₂ as [? ? Heq₂ |]; subst.
    assert (Heqb: @v_const A b₁ =ₜ v_const b₂).
    { constructor 4 with (y := M).
      * constructor 3.
        apply Heq₁.
      * apply Heq₂. }
    apply consistency in Heqb.
    destruct Heqb as [L [HM Hb₁]].
    apply treds_const_inv in HM.
    subst L.
    apply treds_const_inv in Hb₁.
    inversion Hb₁. subst b₁.
    reflexivity.
  + inversion Heval₁ as [? ? Heq₁ |]; subst.
    inversion Heval₂ as [| ? ? Heq₂]; subst.
    assert (Heqb: v_const b₁ =ₜ v_lam N).
    { constructor 4 with (y := M).
      * constructor 3.
        apply Heq₁.
      * apply Heq₂. }
    apply consistency in Heqb.
    destruct Heqb as [L [Hb₁ Hlam]].
    apply treds_const_inv in Hb₁.
    subst L.
    apply treds_lam_inv in Hlam.
    destruct Hlam as [N' Heq].
    inversion Heq.
  + inversion Heval₁ as [| ? ? Heq₁]; subst.
    inversion Heval₂ as [? ? Heq₂ |]; subst.
    assert (Heqb: v_lam N =ₜ v_const b₂).
    { constructor 4 with (y := M).
      * constructor 3.
        apply Heq₁.
      * apply Heq₂. }
    apply consistency in Heqb.
    destruct Heqb as [L [Hlam Hb₂]].
    apply treds_const_inv in Hb₂.
    subst L.
    apply treds_lam_inv in Hlam.
    destruct Hlam as [N' Heq].
    inversion Heq.
  + reflexivity.
Qed.

(* ========================================================================== *)
(* TASK 1 *)
(* Nothing defined above is needed for this task. *)

Inductive answer1 : Set :=
  | ans1_const (b : constant)
  | ans1_function_1
  | ans1_function_plus.

Inductive eval1 {A : Set} : term A → answer1 → Prop :=
  | eval1_const (M : term A) (b : constant) :
    M =ₜ v_const b →
    eval1 M (ans1_const b)
  | eval1_function (M : term A) (N : term (inc A)) :
    (∀ K, N ≠ v_lam K) →
    M =ₜ v_lam N →
    eval1 M ans1_function_1
  | eval1_function_plus (M : term A) N:
    M =ₜ v_lam (v_lam N) →
    eval1 M ans1_function_plus.

Lemma eval1_partial {A : Set} (M : term A) ans₁ ans₂ :
  eval1 M ans₁
  → eval1 M ans₂
  → ans₁ = ans₂.
Proof.
Admitted.

Lemma eval1_not_partial :
  ∃ (A : Set) (M : term A) ans₁ ans₂,
    eval1 M ans₁
    ∧ eval1 M ans₂
    ∧ ans₁ ≠ ans₂.
Proof.
Admitted.
