Require Import Utf8.
Require Import Syntax Semantics.
Require Import Binding.Lib Binding.Product Binding.Set.
Require Import Relation_Operators.
Require Import List.
Import ListNotations.

(* There are no tasks here *)

Ltac Forall_ind H :=
  induction H as [| ? ? ? ? ? ? IHForall2 ]; [
    constructor
  | constructor; [| apply IHForall2 ]
  ].

Local Open Scope bind_scope.

Notation subst := (subst (Inc := inc)).

Lemma terms_values_prefix {A : Set} (ts : list (term A)) :
  ∃ (vs : list (value A)) (ts' : list (term A)), ts = vals_to_terms vs ++ ts'
    ∧ ∀ (V : value A), hd_error ts' ≠ Some (t_value V).
Proof.
  induction ts as [| M ].
  + exists [], []. split.
    - reflexivity.
    - intro V. discriminate.
  + destruct IHts as [vs [ts' [Hts Hhd]]].
    destruct M.
    - exists (V :: vs), ts'. split.
      * term_simpl. f_equal.
        apply Hts.
      * apply Hhd.
    - exists [], (t_app M1 M2 :: ts). split.
      * term_simpl. f_equal.
      * intro V. discriminate.
    - exists [], (t_op op ts0 :: ts). split.
      * term_simpl. f_equal.
      * intro V. discriminate.
Qed.

Definition nonvalue {A : Set} (M : term A) :=
  ∀ (V : value A), M ≠ V.

Lemma term_in_vals {A : Set} (vs : list (value A)) (M : term A) :
  nonvalue M →
  In M (vals_to_terms vs) →
  False.
Proof.
  intros HM HIn.
  induction vs as [| V].
  + inversion HIn.
  + inversion HIn.
    - unfold nonvalue in HM. specialize HM with V.
      symmetry in H. apply HM. apply H.
    - apply IHvs. apply H.
Qed.

Lemma vals_to_terms_inv {A : Set} (vs vs' : list (value A)) :
  vals_to_terms vs = vals_to_terms vs' →
  vs = vs'.
Proof.
  intro H.
  generalize dependent vs'.
  induction vs; intros vs' H.
  - destruct vs'; try discriminate. reflexivity.
  - destruct vs'; try discriminate. inversion H. f_equal.
    apply IHvs. apply H2.
Qed.

Definition has_unique_context {A : Set} (M : term A) :=
  (∃ (V : value A), M = V)
  ∨ (exists! (E : ectx A),
    (∃ (V₁ V₂ : value A), M = eplug E (t_app V₁ V₂))
    ∨ (∃ op (vs : list (value A)), M = eplug E (t_op op (vals_to_terms vs)))).

Fixpoint unique_context {A : Set} (M : term A) :
  has_unique_context M.
Proof.
  induction M.
  + left. exists V. reflexivity.
  + destruct IHM1 as [[V₁ HM₁] | [E₁ HE₁]], IHM2 as [[V₂ HM₂] | [E₂ HE₂]]; subst.
    - right. exists e_hole.
      unfold unique. split.
      * left. exists V₁, V₂. reflexivity.
      * intros E HE.
        destruct HE as [[V₁' [V₂' Hplug]] | [op [vs Hplug]]].
        ++ destruct E; try (inversion Hplug; destruct E; discriminate).
          reflexivity.
        ++ destruct E; inversion Hplug; destruct E; discriminate.
    - unfold unique in HE₂.
      right. exists (e_appr V₁ E₂).
      unfold unique. split.
      * destruct HE₂ as [[[U₁ [U₂ Hplug]] | [op [vs Hplug]]] HE]; subst.
        ++ left. exists U₁, U₂. reflexivity.
        ++ right. exists op, vs. reflexivity.
      * intros E' HE'.
        destruct HE₂ as [HE HuniqE].
        destruct HE' as [[U₁' [U₂' Hplug]] | [op [vs Hplug]]]; subst.
        ++ destruct E'; inversion Hplug; subst.
          -- destruct E₂; destruct HE as [[? [? ?]] | [? [? ?]]]; try discriminate.
          -- destruct E'; inversion Hplug; discriminate.
          -- f_equal. apply HuniqE. left. exists U₁', U₂'. reflexivity.
        ++ destruct E'; inversion Hplug; subst.
          -- destruct E'; discriminate.
          -- f_equal. apply HuniqE. right. exists op, vs. reflexivity.
    - unfold unique in HE₁.
      right. exists (e_appl E₁ V₂).
      unfold unique. split.
      * destruct HE₁ as [[[U₁ [U₂ Hplug]] | [op [vs Hplug]]] HE]; subst.
        ++ left. exists U₁, U₂. reflexivity.
        ++ right. exists op, vs. reflexivity.
      * intros E' HE'.
        destruct HE₁ as [HE HuniqE].
        destruct HE' as [[U₁' [U₂' Hplug]] | [op [vs Hplug]]]; subst.
        ++ destruct E'; inversion Hplug; subst.
          -- destruct E₁; destruct HE as [[? [? ?]] | [? [? ?]]]; try discriminate.
          -- f_equal. apply HuniqE. left. exists U₁', U₂'. reflexivity.
          -- destruct E'; inversion Hplug; discriminate.
        ++ destruct E'; inversion Hplug; subst.
          -- f_equal. apply HuniqE. right. exists op, vs. reflexivity.
          -- destruct E'; discriminate.
    - right. exists (e_appl E₁ M2).
      split.
      * destruct HE₁ as [[[U₁ [U₂ Hplug]] | [op [vs Hplug]]] HE]; subst.
        ++ left. exists U₁, U₂. reflexivity.
        ++ right. exists op, vs. reflexivity.
      * intros E' HE'.
        destruct HE₁ as [HE HuniqE].
        destruct HE' as [[U₁' [U₂' Hplug]] | [op [vs Hplug]]]; subst.
        ++ destruct E'; inversion Hplug; subst.
          -- destruct E₁; destruct HE as [[? [? ?]] | [? [? ?]]]; try discriminate.
          -- f_equal. apply HuniqE. left. exists U₁', U₂'. reflexivity.
          -- destruct E₁; destruct HE as [[? [? ?]] | [? [? ?]]]; try discriminate.
        ++ destruct E'; inversion Hplug; subst.
          -- f_equal. apply HuniqE. right. exists op, vs. reflexivity.
          -- destruct E₁; destruct HE as [[? [? ?]] | [? [? ?]]]; try discriminate.
  + pose proof (@terms_values_prefix A) as Hprefix.
    specialize Hprefix with ts.
    destruct Hprefix as [vs [ts' [Hts Hhd]]].
    destruct ts' as [| M ts'].
    - rewrite app_nil_r in Hts.
      right. exists e_hole. split.
      * right. exists op, vs. subst ts. reflexivity.
      * intros E HE.
        destruct HE as [[V₁ [V₂ Hplug]] | [op' [vs' Hplug]]]; subst.
        ++ destruct E; try discriminate. term_simpl in Hplug.
          inversion Hplug.
          exfalso. apply term_in_vals with (vs := vs) (M := eplug E (t_app V₁ V₂)).
          -- intro V. destruct E; discriminate.
          -- rewrite H1. apply in_or_app.
            right. constructor. reflexivity.
        ++ destruct E; try discriminate.
          -- reflexivity.
          -- term_simpl in Hplug. inversion Hplug.
            exfalso. apply term_in_vals with (vs := vs) (M := eplug E (t_op op' (vals_to_terms vs'))).
            ** intro V. destruct E; discriminate.
            ** rewrite H1. apply in_or_app.
              right. constructor. reflexivity.
    - term_simpl in Hhd.

      assert (IHall: Forall has_unique_context ts).
      { clear Hts.
        induction ts.
        + constructor.
        + constructor.
          - apply unique_context.
          - apply IHts. }
      assert (IHM: has_unique_context M).
      { subst ts.
        apply Forall_app in IHall as [_ IHl].
        inversion IHl; subst.
        apply H1. }

      destruct IHM as [[V HM] | [E [HE HuniqE]]].
      { specialize Hhd with V.
        apply (f_equal Some) in HM.
        apply Hhd in HM.
        destruct HM. }
      right. exists (e_op op vs E ts'). split.
      * destruct HE as [[V₁ [V₂ Hplug]] | [op' [vs' Hplug]]]; subst; clear HuniqE.
        ++ term_simpl. left. exists V₁, V₂. reflexivity.
        ++ term_simpl. right. exists op', vs'. reflexivity.
      * intros E' HE'.
        destruct HE' as [[V₁ [V₂ Hplug]] | [op' [vs' Hplug]]]; subst.
        ++ destruct E'; inversion Hplug; subst.
          -- apply app_eq_app in H1. destruct H1 as [L [[Hvs Htl] | [Hvs Htl]]].
            ** destruct L.
              +++ rewrite app_nil_r in Hvs. apply vals_to_terms_inv in Hvs. subst vs0.
                rewrite app_nil_l in Htl. inversion Htl; subst. f_equal.
                apply HuniqE. left. exists V₁, V₂. reflexivity.
              +++ term_simpl in Htl. inversion Htl.
                exfalso.
                apply term_in_vals with (vs := vs) (M := t).
                --- intro V. subst t. destruct E'; discriminate.
                --- rewrite Hvs. apply in_or_app. right.
                  constructor. reflexivity.
            ** destruct L.
              +++ rewrite app_nil_r in Hvs. apply vals_to_terms_inv in Hvs. subst vs0.
                rewrite app_nil_l in Htl. inversion Htl; subst. f_equal.
                apply HuniqE. left. exists V₁, V₂. reflexivity.
              +++ term_simpl in Htl. inversion Htl.
                exfalso.
                apply term_in_vals with (vs := vs0) (M := t).
                --- intro V. subst t. specialize Hhd with V. intro HM. apply Hhd. f_equal. apply HM.
                --- rewrite Hvs. apply in_or_app. right.
                  constructor. reflexivity.
        ++ destruct E'; inversion Hplug; subst.
          -- exfalso. apply term_in_vals with (vs := vs') (M := M).
            ** intro V. intro HM. apply (Hhd V). f_equal. apply HM.
            ** rewrite <- H1. apply in_or_app. right. constructor. reflexivity.
          -- apply app_eq_app in H1. destruct H1 as [L [[Hvs Htl] | [Hvs Htl]]].
            ** destruct L.
              +++ rewrite app_nil_r in Hvs. apply vals_to_terms_inv in Hvs. subst vs0.
                rewrite app_nil_l in Htl. inversion Htl; subst. f_equal.
                apply HuniqE. right. exists op', vs'. reflexivity.
              +++ term_simpl in Htl. inversion Htl.
                exfalso.
                apply term_in_vals with (vs := vs) (M := t).
                --- intro V. subst t. destruct E'; discriminate.
                --- rewrite Hvs. apply in_or_app. right.
                  constructor. reflexivity.
            ** destruct L.
              +++ rewrite app_nil_r in Hvs. apply vals_to_terms_inv in Hvs. subst vs0.
                rewrite app_nil_l in Htl. inversion Htl; subst. f_equal.
                apply HuniqE. right. exists op', vs'. reflexivity.
              +++ term_simpl in Htl. inversion Htl.
                exfalso.
                apply term_in_vals with (vs := vs0) (M := t).
                --- intro V. subst t. specialize Hhd with V. intro HM. apply Hhd. f_equal. apply HM.
                --- rewrite Hvs. apply in_or_app. right.
                  constructor. reflexivity.
Qed.

(* ========================================================================== *)
(* Weak head reduction *)

Reserved Notation "M₁ '→ₕₜ' M₂" (at level 50).

Inductive bdred {A : Set} : term A → term A → Prop :=
  | bdred_beta : ∀ M (V : value A),
    bdred (t_app (v_lam M) V) (subst M V)
  | bdred_delta : ∀ op bs V,
    δ op bs = Some V →
    bdred (t_op op (consts_to_terms bs)) (from_closed V).

Lemma bdred_red {A : Set} (M N : term A) :
  bdred M N →
  M →ₜ N.
Proof.
  intro Hbdred.
  inversion Hbdred.
  - constructor.
  - constructor. assumption.
Qed.

Inductive twh' {S : Set} : term S → term S → Prop :=
  | twhI : ∀ E M N,
    bdred M N →
    eplug E M →ₕₜ eplug E N

where "M₁ →ₕₜ M₂" := (@twh' _ M₁ M₂).

Definition twh {A : Set} M₁ M₂ := @clos_refl_trans (term A) twh' M₁ M₂.
Notation "M₁ '↠ₕₜ' M₂" := (clos_refl_trans _ twh' M₁ M₂) (at level 50).

(* -------------------------------------------------------------------------- *)
(* Properties of twh *)

(* -------------------------------------------------------------------------- *)

Lemma bdred_wh {A : Set} (M N : term A) :
  bdred M N →
  M →ₕₜ N.
Proof.
  intro Hbdred.
  apply twhI with (E := e_hole).
  apply Hbdred.
Qed.

Lemma twh_refl {A : Set} (M : term A) :
  M ↠ₕₜ M.
Proof. constructor 2. Qed.

Lemma twh_red' {A : Set} (M N : term A) :
  M →ₕₜ N →
  M →ₜ N.
Proof.
  intro Hwh.
  destruct Hwh.
  induction E; term_simpl.
  - apply bdred_red. apply H.
  - apply tred_app_L.
    apply IHE.
  - apply tred_app_R.
    apply IHE.
  - apply tred_op.
    apply IHE.
Qed.

Lemma twh_red {A : Set} (M N : term A) :
  M ↠ₕₜ N →
  M →*ₜ N.
Proof.
  intro Hwh.
  induction Hwh.
  + constructor. apply twh_red'. apply H.
  + constructor 2.
  + constructor 3 with (y := y).
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

Lemma twh_plug' {A : Set} E (M N : term A) :
  M →ₕₜ N →
  eplug E M →ₕₜ eplug E N.
Proof.
  intro Hwh.
  destruct Hwh; rewrite !eplug_plug_comp; constructor.
  + apply H.
Qed.

Lemma twh_plug {A : Set} E (M N : term A) :
  M ↠ₕₜ N →
  eplug E M ↠ₕₜ eplug E N.
Proof.
  intro Hwh.
  induction Hwh.
  + constructor. apply twh_plug'. apply H.
  + constructor 2.
  + constructor 3 with (y := eplug E y).
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

Lemma twh_app_L_cong {A : Set} (M M' N : term A) :
  M ↠ₕₜ M' →
  t_app M N ↠ₕₜ t_app M' N.
Proof.
  intro Hwh.
  apply twh_plug with (E := e_appl e_hole N).
  apply Hwh.
Qed.

Lemma twh_app_R_cong {A : Set} (V : value A) (N N' : term A) :
  N ↠ₕₜ N' →
  t_app V N ↠ₕₜ t_app V N'.
Proof.
  intro Hwh.
  apply twh_plug with (E := e_appr V e_hole).
  apply Hwh.
Qed.

Lemma twh_op_cong {A : Set} (vs : list (value A)) op (M M' : term A) (ts : list (term A)) :
  M ↠ₕₜ M' →
  t_op op (vals_to_terms vs ++ [M] ++ ts) ↠ₕₜ t_op op (vals_to_terms vs ++ [M'] ++ ts).
Proof.
  intro Hwh.
  apply twh_plug with (E := e_op op vs e_hole ts).
  apply Hwh.
Qed.

Lemma cons_app {A : Set} (x : A) (xs : list A) :
  x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* Standard and internal reductions *)

Reserved Notation "M₁ '↠ₛₜ' M₂" (at level 50).
Reserved Notation "M₁ '↠ᵢₜ' M₂" (at level 50).
Reserved Notation "V₁ '↠ᵢᵥ' V₂" (at level 50).

Lemma value_or_not {A : Set} (M : term A) :
  (∃ V, M = t_value V) ∨ nonvalue M.
Proof.
  destruct M.
  + left. exists V. reflexivity.
  + right. intro V. discriminate.
  + right. intro V. discriminate.
Qed.

Inductive tstd {S : Set} : term S → term S → Prop :=
  | tstdI : ∀ (M P N : term S),
    M ↠ₕₜ P →
    P ↠ᵢₜ N →
    M ↠ₛₜ N

with tint {S : Set} : term S → term S → Prop :=
  | tint_val : ∀ V V',
    V ↠ᵢᵥ V' →
    V ↠ᵢₜ V'
  | tint_app_nonvalue : ∀ M M' N N',
    nonvalue M →
    M ↠ᵢₜ M' →
    N ↠ₛₜ N' →
    t_app M N ↠ᵢₜ t_app M' N'
  | tint_app : ∀ V V' N N',
    V ↠ᵢᵥ V' →
    N ↠ᵢₜ N' →
    t_app V N ↠ᵢₜ t_app V' N'
  | tint_op_nonvalue : ∀ op (vs vs' : list (value S)) (M M' : term S) (ts ts' : list (term S)),
    Forall2 vint vs vs' →
    nonvalue M →
    M ↠ᵢₜ M' →
    Forall2 tstd ts ts' →
    t_op op (vals_to_terms vs ++ M :: ts) ↠ᵢₜ t_op op (vals_to_terms vs' ++ M' :: ts')
  | tint_op : ∀ op (vs vs' : list (value S)),
    Forall2 vint vs vs' →
    t_op op (vals_to_terms vs) ↠ᵢₜ t_op op (vals_to_terms vs')
with vint {S : Set} : value S → value S → Prop :=
  | vint_var : ∀ x,
    v_var x ↠ᵢᵥ v_var x
  | vint_const : ∀ b,
    v_const b ↠ᵢᵥ v_const b
  | vint_lam : ∀ M N,
    M ↠ₛₜ N →
    v_lam M ↠ᵢᵥ v_lam N

where "M₁ ↠ₛₜ M₂" := (@tstd _ M₁ M₂)
  and "M₁ ↠ᵢₜ M₂" := (@tint _ M₁ M₂)
  and "V₁ ↠ᵢᵥ V₂" := (@vint _ V₁ V₂).

(* -------------------------------------------------------------------------- *)

Lemma tint_red {A : Set} (M N : term A) :
  M ↠ᵢₜ N →
  M →*ₜ N
 with vint_red {A : Set} (V V' : value A) :
  V ↠ᵢᵥ V' →
  V →*ᵥ V'
 with tstd_red {A : Set} (M N : term A) :
  M ↠ₛₜ N →
  M →*ₜ N.
Proof.
(* tint_red *)
{
  intro Htint.
  induction Htint.
  + apply tred_value_cong. apply vint_red. apply H.
  + econstructor 3.
    - apply tred_appl_cong. apply IHHtint.
    - apply tred_appr_cong. apply tstd_red. apply H0.
  + econstructor 3.
    - apply tred_appl_cong.
      apply tred_value_cong.
      apply vint_red. apply H.
    - apply tred_appr_cong. apply IHHtint.
  + apply tred_op_cong.
    apply Forall2_app; [| constructor ].
    - induction H.
      * constructor.
      * constructor.
        ++ apply tred_value_cong. apply vint_red. apply H.
        ++ apply IHForall2.
    - apply IHHtint.
    - induction H1.
      * constructor.
      * constructor.
        ++ apply tstd_red. apply H1.
        ++ apply IHForall2.
  + apply tred_op_cong.
    - induction H.
      * constructor.
      * constructor.
        ++ apply tred_value_cong. apply vint_red. apply H.
        ++ apply IHForall2.
}
(* vint_red *)
{
  intro Hvint.
  induction Hvint.
  + constructor 2.
  + constructor 2.
  + apply vred_lam_cong.
    apply tstd_red.
    apply H.
}
(* tstd_red *)
{
  intro Hstd.
  inversion Hstd; subst.
  econstructor 3.
  + apply twh_red. apply H.
  + apply tint_red. apply H0.
}
Qed.

(* -------------------------------------------------------------------------- *)

Lemma tint_std {S : Set} : ∀ (M M' : term S),
  M ↠ᵢₜ M' →
  M ↠ₛₜ M'.
Proof.
  intros M M' Htint.
  constructor 1 with (P := M).
  - apply twh_refl.
  - apply Htint.
Qed.

Lemma value_vals_cons {A : Set} (V : value A) (vs : list (value A)) :
  t_value V :: vals_to_terms vs = vals_to_terms (V :: vs).
Proof. reflexivity. Qed.

Lemma vals_value_app {A : Set} (V : value A) (vs : list (value A)) :
  vals_to_terms vs ++ [t_value V] = vals_to_terms (vs ++ [V]).
Proof. unfold vals_to_terms. rewrite map_app. reflexivity. Qed.

Ltac list_forall2_ind xs :=
  induction xs as [| ? ? IHxs ]; [
    constructor
  | constructor; [| apply IHxs ]
  ].

Lemma tint_val_inv {A : Set} (V V' : value A) :
  V ↠ᵢₜ V' →
  V ↠ᵢᵥ V'.
Proof.
  intro Htint.
  inversion Htint; subst.
  apply H1.
Qed.

Lemma Forall2_vint_tstd {A : Set} (vs vs' : list (value A)) :
  Forall2 vint vs vs' →
  Forall2 tstd (vals_to_terms vs) (vals_to_terms vs').
Proof.
  intro Hvint.
  induction Hvint.
  + constructor.
  + constructor.
    - apply tint_std. constructor. apply H.
    - apply IHHvint.
Qed.

Lemma vals_cons_nonvalue_inv {A : Set} (vs vs' : list (value A)) M M' ts ts' :
  nonvalue M →
  nonvalue M' →
  vals_to_terms vs ++ M :: ts = vals_to_terms vs' ++ M' :: ts' →
  vs = vs' ∧ M = M' ∧ ts = ts'.
Proof.
  intros Hnonv Hnonv' Heq.
  apply app_eq_app in Heq.
  destruct Heq as [L [[Hvs Hts] | [Hvs Hts]]].
  + destruct L.
    - rewrite app_nil_r in Hvs.
      apply vals_to_terms_inv in Hvs. subst.
      inversion Hts. auto.
    - inversion Hts; subst.
      exfalso. apply term_in_vals with (vs := vs) (M := t).
      * apply Hnonv'.
      * rewrite Hvs. apply in_or_app. right.
        constructor. reflexivity.
  + destruct L.
    - rewrite app_nil_r in Hvs.
      apply vals_to_terms_inv in Hvs. subst.
      inversion Hts. auto.
    - inversion Hts; subst.
      exfalso. apply term_in_vals with (vs := vs') (M := t).
      * apply Hnonv.
      * rewrite Hvs. apply in_or_app. right.
        constructor. reflexivity.
Qed.

Lemma tint_nonvalue_inv_l {A : Set} (M M' : term A) :
  M ↠ᵢₜ M' →
  nonvalue M →
  nonvalue M'.
Proof.
  intros Htint Hnonv.
  inversion Htint.
  + subst M. unfold nonvalue in Hnonv. specialize Hnonv with V.
    exfalso. apply Hnonv. reflexivity.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
Qed.

Lemma tint_nonvalue_inv_r {A : Set} (M M' : term A) :
  M ↠ᵢₜ M' →
  nonvalue M' →
  nonvalue M.
Proof.
  intros Htint Hnonv.
  inversion Htint.
  + subst M M'. unfold nonvalue in Hnonv. specialize Hnonv with V'.
    exfalso. apply Hnonv. reflexivity.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
Qed.

Lemma tint_refl {S : Set} : ∀ (M : term S),
  M ↠ᵢₜ M
 with vint_refl {S : Set} : ∀ (V : value S),
  V ↠ᵢᵥ V.
Proof.
(* tint_refl *)
{
  intro M.
  induction M.
  + constructor. apply vint_refl.
  + destruct (value_or_not M1) as [[V HV] |]; subst.
    - apply tint_app.
      * inversion IHM1; subst.
        apply H1.
      * apply IHM2.
    - apply tint_app_nonvalue.
      * apply H.
      * apply IHM1.
      * apply tint_std. apply IHM2.
  + induction ts.
    - apply tint_op with (vs := []) (vs' := []).
      constructor.
    - inversion IHts; subst.
      * apply tint_nonvalue_inv_l in H4 as HnonM'; [| apply H3 ].
        apply vals_cons_nonvalue_inv in H1; [| assumption .. ].
        destruct H1 as [? [? ?]]. subst.
        destruct (value_or_not a) as [[V HV] |].
        ++ rewrite app_comm_cons. rewrite HV. rewrite value_vals_cons.
          apply tint_op_nonvalue with (M' := M).
          -- constructor.
            ** apply tint_val_inv. rewrite <- HV. apply tint_refl.
            ** apply H2.
          -- apply H3.
          -- apply H4.
          -- apply H5.
        ++ apply tint_op_nonvalue with (vs := []) (vs' := []) (M' := a).
          -- constructor.
          -- apply H.
          -- apply tint_refl.
          -- apply Forall2_app.
            ** apply Forall2_vint_tstd. apply H2.
            ** constructor.
              +++ apply tint_std. apply H4.
              +++ apply H5.
      * apply vals_to_terms_inv in H2. subst.
        pose proof (tint_refl _ a) as IHa.
        destruct (value_or_not a) as [[V HV] |]; subst.
        ++ apply tint_op with (vs := V :: vs) (vs' := V :: vs).
          constructor.
          -- inversion IHa; subst. apply H2.
          -- apply H0.
        ++ apply tint_op_nonvalue with (vs := []) (vs' := []).
          -- constructor.
          -- apply H.
          -- apply IHa.
          -- apply Forall2_vint_tstd. apply H0.
}
(* vint_refl *)
{
  intro V.
  induction V.
  + constructor.
  + constructor.
  + constructor. apply tint_std. apply tint_refl.
}
Qed.

Lemma twh_std {A : Set} (M M' : term A) :
  M ↠ₕₜ M' →
  M ↠ₛₜ M'.
Proof.
  intro Hwh.
  econstructor.
  + apply Hwh.
  + apply tint_refl.
Qed.

Lemma tstd_refl {S : Set} (M : term S) :
  M ↠ₛₜ M.
Proof.
  econstructor.
  - apply twh_refl.
  - apply tint_refl.
Qed.

Lemma Forall2_tstd_refl {A : Set} (ts : list (term A)) :
  Forall2 tstd ts ts.
Proof.
  induction ts.
  + constructor.
  + constructor.
    - apply tstd_refl.
    - apply IHts.
Qed.

Lemma tstd_app_L_cong {S : Set} (M M' N : term S) :
  M ↠ₛₜ M' →
  t_app M N ↠ₛₜ t_app M' N.
Proof.
  intro Hstd.
  inversion Hstd; subst.
  destruct (value_or_not P) as [[V HV] |]; subst.
  + inversion H0; subst.
    econstructor.
    - apply twh_app_L_cong. apply H.
    - apply tint_app.
      * apply H2.
      * apply tint_refl.
  + econstructor.
    - apply twh_app_L_cong.
      apply H.
    - apply tint_app_nonvalue.
      * apply H1.
      * apply H0.
      * apply tstd_refl.
Qed.

Lemma tstd_app_R_cong {S : Set} (M N N' : term S) :
  N ↠ₛₜ N' →
  t_app M N ↠ₛₜ t_app M N'.
Proof.
  intro Hstd.
  destruct (value_or_not M) as [[V HV] |]; subst.
  + inversion Hstd; subst.
    econstructor.
    apply twh_app_R_cong.
    - apply H.
    - apply tint_app.
      * apply vint_refl.
      * apply H0.
  + econstructor.
    - apply twh_refl.
    - apply tint_app_nonvalue.
      * apply H.
      * apply tint_refl.
      * apply Hstd.
Qed.

Lemma tstd_app {S : Set} (M₁ M₂ N₁ N₂ : term S) :
  M₁ ↠ₛₜ M₂ →
  N₁ ↠ₛₜ N₂ →
  t_app M₁ N₁ ↠ₛₜ t_app M₂ N₂.
Proof.
  intros Hstd₁ Hstd₂.
  inversion Hstd₁; subst.
  destruct (value_or_not P) as [[V HV] |]; subst.
  + inversion Hstd₂; subst.
    econstructor.
    - econstructor 3.
      * apply twh_app_L_cong.
        apply H.
      * apply twh_app_R_cong.
        apply H1.
    - inversion H0; subst.
      apply tint_app.
      * apply H4.
      * apply H2.
  + econstructor.
    - apply twh_app_L_cong. apply H.
    - apply tint_app_nonvalue.
      * apply H1.
      * apply H0.
      * apply Hstd₂.
Qed.

Lemma tstd_op {A : Set} op (ts ts' : list (term A)) :
  Forall2 tstd ts ts' →
  t_op op ts ↠ₛₜ t_op op ts'.
Proof.
  intro Hstd.
  assert (H:
    ∀ (vs vs' : list (value A)), Forall2 vint vs vs' →
    t_op op (vals_to_terms vs ++ ts) ↠ₛₜ t_op op (vals_to_terms vs' ++ ts')).
  { induction Hstd as [| M M' ]; intros vs vs' Hvint.
    + apply tint_std.
      rewrite !app_nil_r.
      apply tint_op.
      apply Hvint.
    + inversion H; subst.
      destruct (value_or_not P) as [[U HU] |]; subst.
      - inversion H1; subst.
        specialize IHHstd with (vs := vs ++ [U]) (vs' := vs' ++ [V']).
        assert (Hvint': Forall2 vint (vs ++ [U]) (vs' ++ [V'])).
        { apply Forall2_app; auto. }
        apply IHHstd in Hvint'.
        inversion Hvint'; subst.
        econstructor.
        * econstructor 3.
          ++ apply twh_op_cong.
            apply H0.
          ++ rewrite app_assoc. rewrite vals_value_app.
            apply H2.
        * rewrite cons_app. rewrite app_assoc. rewrite vals_value_app.
          apply H4.
    - econstructor.
      * apply twh_op_cong. apply H0.
      * apply tint_op_nonvalue.
        ++ apply Hvint.
        ++ apply H2.
        ++ apply H1.
        ++ apply Hstd.
  }

  apply H with (vs := []) (vs' := []).
  constructor.
Qed.

(* ========================================================================== *)
(* fmap lemmas - the relations are preserved under fmap *)

(* -------------------------------------------------------------------------- *)
(* Weah head map lemma *)

Lemma bdred_map {A B : Set} (φ : A [→] B) M M' :
  bdred M M' →
  bdred (fmap φ M) (fmap φ M').
Proof.
  intro Hbdred.
  inversion Hbdred; subst; term_simpl.
  - constructor.
  - rewrite fmap_closed_pure.
    rewrite fmap_consts_pure.
    constructor. apply H.
Qed.

Lemma twh_map' {A B : Set} (φ : A [→] B) M M' :
  M →ₕₜ M' →
  fmap φ M ↠ₕₜ fmap φ M'.
Proof.
  intro Hwh.
  induction Hwh; term_simpl.
  rewrite !eplug_fmap. term_simpl.
  constructor. constructor.
  apply bdred_map.
  apply H.
Qed.

Lemma twh_map {A B : Set} : ∀ (φ : A [→] B) M M',
  M ↠ₕₜ M' →
  fmap φ M ↠ₕₜ fmap φ M'.
Proof.
  intros φ M M' Hwh.
  induction Hwh as [ M₁ M₂ | M | M₁ M' M₂ ].
  + apply twh_map'. apply H.
  + apply twh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal map lemmas *)

Lemma nonvalue_fmap {A B : Set} (φ : A [→] B) M :
  nonvalue M →
  nonvalue (fmap φ M).
Proof.
  unfold nonvalue.
  intro Hnon.
  intro V.
  destruct M; try discriminate.
  specialize Hnon with V0.
  destruct Hnon. reflexivity.
Qed.

Lemma vals_map {A B : Set} (φ : A [→] B) (vs : list (value A)) :
  map (tmap φ) (vals_to_terms vs) = vals_to_terms (map (vmap φ) vs).
Proof.
  induction vs.
  + reflexivity.
  + term_simpl. f_equal.
    - apply IHvs.
Qed.

Lemma tint_map {A B : Set} (φ : A [→] B) (M₁ M₂ : term A) :
  M₁ ↠ᵢₜ M₂ →
  fmap φ M₁ ↠ᵢₜ fmap φ M₂
 with vint_map {A B : Set} (φ : A [→] B) (V₁ V₂ : value A) :
  V₁ ↠ᵢᵥ V₂ →
  fmap φ V₁ ↠ᵢᵥ fmap φ V₂

 with tstd_map {A B : Set} (φ : A [→] B) (M₁ M₂ : term A) :
  M₁ ↠ₛₜ M₂ →
  fmap φ M₁ ↠ₛₜ fmap φ M₂.
Proof.
(* tint_map *)
{
  intro Htint.
  induction Htint.
  + term_simpl. constructor. apply vint_map. apply H.
  + term_simpl. constructor.
    - apply nonvalue_fmap. apply H.
    - apply IHHtint.
    - apply tstd_map. apply H0.
  + term_simpl. apply tint_app.
    - apply vint_map. apply H.
    - apply IHHtint.
  + term_simpl. rewrite !map_app.
    rewrite !vals_map.
    constructor.
    - Forall_ind H. apply vint_map. apply H.
    - apply nonvalue_fmap. apply H0.
    - apply IHHtint.
    - Forall_ind H1. apply tstd_map. apply H1.
  + term_simpl.
    rewrite !vals_map.
    constructor.
    - Forall_ind H. apply vint_map. apply H.
}
(* vint_map *)
{
  intros Hvint.
  induction Hvint.
  + term_simpl. apply vint_refl.
  + term_simpl. apply vint_refl.
  + term_simpl. constructor. apply tstd_map. apply H.
}
(* tstd_map *)
{
  intros Hstd.
  inversion Hstd as [? P ? HM₁whP HPintM₂]; subst.
  + econstructor.
    - apply twh_map. apply HM₁whP.
    - apply tint_map. apply HPintM₂.
}
Qed.

(* ========================================================================== *)
(* Bind lemmas - the relations are preserved under bind *)

(* -------------------------------------------------------------------------- *)
(* Weak head bind lemma *)

Lemma bdred_bind {A B : Set} (φ : A [⇒] B) M M' :
  bdred M M' →
  bdred (bind φ M) (bind φ M').
Proof.
  intro Hbdred.
  inversion Hbdred; subst; term_simpl.
  - constructor.
  - rewrite bind_closed_pure.
    rewrite bind_consts_pure.
    constructor. apply H.
Qed.

Lemma twh_bind' {A B : Set} (φ : A [⇒] B) M M' :
  M →ₕₜ M' →
  bind φ M ↠ₕₜ bind φ M'.
Proof.
  intro Hwh.
  induction Hwh.
  rewrite <- !eplug_bind. term_simpl.
  constructor. constructor.
  apply bdred_bind.
  apply H.
Qed.

Lemma twh_bind {A B : Set} : ∀ (φ : A [⇒] B) M M',
  M ↠ₕₜ M' →
  bind φ M ↠ₕₜ bind φ M'.
Proof.
  intros φ M M' Hwh.
  induction Hwh.
  + apply twh_bind'. apply H.
  + apply twh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal bind lemmas *)
(* We use auxiliary definitions of standard reductions for substitutions *)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)
(* standard reduction of substitutions *)

Definition sstd {A B : Set} (φ φ' : A [⇒] B) :=
  ∀ x, φ x ↠ᵢᵥ φ' x.

Notation "φ₁ ↠ₛₛ φ₂" := (@sstd _ _ φ₁ φ₂) (at level 50).

Lemma sstd_refl {A B : Set} (φ : A [⇒] B) :
  φ ↠ₛₛ φ.
Proof.
  intro x. apply vint_refl.
Qed.

Lemma sstd_lift {A B : Set} (φ φ' : A [⇒] B) :
  φ ↠ₛₛ φ' →
  φ ↑ ↠ₛₛ φ' ↑.
Proof.
  intro Hsstd.
  intro x. destruct x as [| x].
  + term_simpl. apply vint_refl.
  + term_simpl. apply vint_map. apply Hsstd.
Qed.

Lemma nonvalue_bind {A B : Set} (φ : A [⇒] B) M :
  nonvalue M →
  nonvalue (bind φ M).
Proof.
  unfold nonvalue.
  intro Hnon.
  intro V.
  destruct M; try discriminate.
  specialize Hnon with V0.
  destruct Hnon. reflexivity.
Qed.

Lemma vals_bind {A B : Set} (φ : A [⇒] B) (vs : list (value A)) :
  map (tbind φ) (vals_to_terms vs) = vals_to_terms (map (vbind φ) vs).
Proof.
  induction vs.
  + reflexivity.
  + term_simpl. f_equal.
    - apply IHvs.
Qed.

Lemma tint_bind {A B : Set} : ∀ (φ φ' : A [⇒] B) M M',
  φ ↠ₛₛ φ' →
  M ↠ᵢₜ M' →
  bind φ M ↠ᵢₜ bind φ' M'
 with vint_bind {A B : Set} : ∀ (φ φ' : A [⇒] B) V V',
  φ ↠ₛₛ φ' →
  V ↠ᵢᵥ V' →
  vbind φ V ↠ᵢᵥ vbind φ' V'

 with tstd_bind {A B : Set} : ∀ (φ φ' : A [⇒] B) M M',
  φ ↠ₛₛ φ' →
  M ↠ₛₜ M' →
  bind φ M ↠ₛₜ bind φ' M'.
Proof.
(* tint_bind *)
{
  intros φ φ' M M' Hsstd Htint.
  induction Htint.
  + term_simpl. constructor. apply vint_bind; assumption.
  + term_simpl. constructor.
    - apply nonvalue_bind. apply H.
    - apply IHHtint. apply Hsstd.
    - apply tstd_bind; assumption.
  + term_simpl. apply tint_app.
    - apply vint_bind. apply Hsstd. apply H.
    - apply IHHtint. apply Hsstd.
  + term_simpl. rewrite !map_app.
    rewrite !vals_bind.
    constructor.
    - Forall_ind H. apply vint_bind; assumption.
    - apply nonvalue_bind. apply H0.
    - apply tint_bind; assumption.
    - Forall_ind H1. apply tstd_bind; assumption.
  + term_simpl.
    rewrite !vals_bind.
    constructor.
    - Forall_ind H. apply vint_bind; assumption.
}
(* vint_bind *)
{
  intros φ φ' V V' Hsstd Hvint.
  induction Hvint.
  + term_simpl. apply Hsstd.
  + term_simpl. apply vint_refl.
  + term_simpl. constructor. apply tstd_bind.
    - apply sstd_lift. apply Hsstd.
    - apply H.
}
(* tstd_bind *)
{
  intros φ φ' M M' Hsstd Hstd.
  inversion Hstd as [? P ? HMwhP HPintM']; subst.
  econstructor.
  + apply twh_bind. apply HMwhP.
  + apply tint_bind; assumption.
}
Qed.

Lemma mk_subst_sstd {S : Set} (V₁ V₂ : value S) :
  V₁ ↠ᵢᵥ V₂ →
  mk_subst V₁ ↠ₛₛ mk_subst V₂.
Proof.
  intros Hvint.
  intro x. destruct x as [| x].
  + term_simpl. apply Hvint.
  + term_simpl. apply vint_refl.
Qed.

(* ========================================================================== *)
(* standardisation lemma *)

(* -------------------------------------------------------------------------- *)
(* The original reduction can be standardised *)

Lemma twh_std' {S : Set} (M M' : term S) :
  M →ₕₜ M' →
  M ↠ₛₜ M'.
Proof.
  intro Hwh.
  econstructor.
  - constructor. apply Hwh.
  - apply tint_refl.
Qed.

Lemma tred_std {A : Set} : ∀ (M N : term A),
  M →ₜ N →
  M ↠ₛₜ N
 with vred_int {A : Set} : ∀ (V V' : value A),
  V →ᵥ V' →
  V ↠ᵢᵥ V'.
Proof.
(* tred_std *)
{
  intros M N Hred.
  induction Hred.
  + apply twh_std'. apply twhI with (E := e_hole). constructor.
  + apply twh_std'. apply twhI with (E := e_hole). constructor. apply H.
  + econstructor.
    - apply twh_refl.
    - constructor. apply vred_int. apply H.
  + apply tstd_app_L_cong.
    apply IHHred.
  + apply tstd_app_R_cong.
    apply IHHred.
  + apply tstd_op.
    repeat apply Forall2_app.
    - apply Forall2_tstd_refl.
    - auto.
    - apply Forall2_tstd_refl.
}
(* vred_int *)
{
  intros V V' Hred.
  induction Hred.
  + constructor. apply tred_std. apply H.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* standard reduction can be prepended by a weak head reduction *)

Lemma twh_std_std {S : Set} (M₁ M M₂ : term S) :
  M₁ ↠ₕₜ M  →
  M  ↠ₛₜ M₂ →
  M₁ ↠ₛₜ M₂.
Proof.
  intros Hwh Hstd.
  inversion Hstd as [? P ? HM HP]; subst.
  econstructor.
  + econstructor 3.
    - apply Hwh.
    - apply HM.
  + apply HP.
Qed.

(* -------------------------------------------------------------------------- *)
(* ↠ᵢ∙↠ₕ ⊆ ↠ₛ - composites of the form ↠ᵢ∙↠ₕ can be standardised *)

Lemma Forall2_vint_consts_inv {A : Set} (vs : list (value A)) (bs : list constant) :
  Forall2 vint vs (consts_to_vals bs) →
  vs = consts_to_vals bs.
Proof.
  intro Htint.
  generalize dependent bs.
  induction vs; intros bs Htint.
  + inversion Htint. reflexivity.
  + inversion Htint; subst.
    destruct bs; try discriminate.
    inversion H1; subst.
    inversion H2; subst.
    f_equal.
    apply IHvs. apply H3.
Qed.

Lemma tint_wh_std' {S : Set} (M₁ M M₂ : term S) :
  M₁ ↠ᵢₜ M  →
  M  →ₕₜ M₂ →
  M₁ ↠ₛₜ M₂.
Proof.
  intros Htint Hwh.
  inversion Hwh as [? N N' Hbdred]; subst.
  generalize dependent M₁.
  induction E; intros M₁ Htint; term_simpl in Htint; term_simpl.
  - inversion Hbdred; subst.
    + inversion Htint as [| N₁ ? N₂ ? Hnv HN₁ HN₂ | N₁ ? N₂ ? HN₁ HN₂ | |]; subst.
      { inversion HN₁ as [ V₁ ? HV₁ | | | |]; clear HN₁; subst.
        destruct Hnv with (V := V₁). reflexivity. }
      { inversion HN₁ as [| | M₁ ? HM₁ ]; clear HN₁; subst.
        inversion HN₂ as [ V₂ ? HV₂ | | | |]; subst.
        eapply twh_std_std.
        + constructor. apply twhI with (E := e_hole). constructor.
        + apply tstd_bind.
          - apply mk_subst_sstd.
            apply HV₂.
          - apply HM₁. }
    + inversion Htint as [| | | ? us us' M' N' rs rs' Hus Hnv HM' Hrs | ? rs rs' Hrs ]; subst.
      { exfalso. apply term_in_vals with (vs := consts_to_vals bs) (M := N').
        - apply tint_nonvalue_inv_l with (M := M').
          + apply HM'.
          + apply Hnv.
        - rewrite <- consts_to_terms_comp. rewrite <- H2.
          apply in_or_app. right.
          constructor. reflexivity. }
      { term_simpl.
        rewrite consts_to_terms_comp in H2.
        apply vals_to_terms_inv in H2. rewrite H2 in Hrs.
        apply Forall2_vint_consts_inv in Hrs. subst.
        rewrite <- consts_to_terms_comp.
        apply twh_std. constructor. apply twhI with (E := e_hole).
        constructor.
        apply H. }
    - inversion Htint as [| N₁ ? N₂ ? Hnv HN₁ HN₂ | N₁ ? N₂ ? HN₁ HN₂ | |]; subst.
      { term_simpl. apply tstd_app.
        - apply IHE.
          + constructor. apply Hbdred.
          + apply HN₁.
        - apply HN₂. }
      { destruct E; try discriminate. simpl eplug in *. subst N.
        apply tstd_app.
        - apply IHE.
          + apply bdred_wh. apply Hbdred.
          + constructor. apply HN₁.
        - apply tint_std. apply HN₂. }
    - inversion Htint as [| N₁ ? N₂ ? Hnv HN₁ HN₂ | N₁ ? N₂ ? HN₁ HN₂ | |]; subst.
      { inversion HN₂; subst.
        apply IHE in H0.
        + term_simpl. apply tstd_app.
          - apply tint_std. apply HN₁.
          - eapply twh_std_std.
            * apply H.
            * apply H0.
        + constructor. apply Hbdred. }
      { term_simpl. apply tstd_app.
        + apply tint_std. constructor. apply HN₁.
        + apply IHE.
          - constructor. apply Hbdred.
          - apply HN₂. }
    - inversion Htint as [| | | ? ws ws' M M' rs rs' Hws Hnv HM Hrs | ? rs rs' Hrs ]; subst.
      { apply tint_nonvalue_inv_l in HM as Hnv'; [| apply Hnv ].
        apply vals_cons_nonvalue_inv in H1; [| apply Hnv' |].
        - destruct H1 as [? [? ?]]; subst.
          apply tstd_op.
          apply Forall2_app; [| constructor ].
          + apply Forall2_vint_tstd. apply Hws.
          + apply IHE.
            * constructor. apply Hbdred.
            * apply HM.
          + apply Hrs.
        - destruct E; try discriminate.
          inversion Hbdred; subst; discriminate. }
      { exfalso. apply term_in_vals with (vs := rs') (M := eplug E N).
        - destruct E; try discriminate.
          inversion Hbdred; subst; discriminate.
        - rewrite H1.
          apply in_or_app. right.
          constructor. reflexivity. }
Qed.

Lemma tint_wh_std {S : Set} (M₁ M M₂ : term S) :
  M₁ ↠ᵢₜ M  →
  M  ↠ₕₜ M₂ →
  M₁ ↠ₛₜ M₂.
Proof.
  intros Htint Hwh.
  generalize dependent M₁.
  induction Hwh; intros M₁ Htint.
  + eapply tint_wh_std'.
    - apply Htint.
    - apply H.
  + apply tint_std. apply Htint.
  + apply IHHwh1 in Htint as Hstd.
    inversion Hstd as [ ? P ? HM₁ HP ]; subst.
    apply IHHwh2 in HP.
    eapply twh_std_std.
    - apply HM₁.
    - apply HP.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal reductions are transitive *)

Fixpoint tint_trans {S : Set} (M₁ M M₂ : term S)
  (Htint₁ : M₁ ↠ᵢₜ M )
  (Htint₂ : M  ↠ᵢₜ M₂) { struct Htint₂ } :
  M₁ ↠ᵢₜ M₂
 with vint_trans {S : Set} (V₁ V V₂ : value S)
  (Hvint₁ : V₁ ↠ᵢᵥ V )
  (Hvint₂ : V  ↠ᵢᵥ V₂) { struct Hvint₂ }:
  V₁ ↠ᵢᵥ V₂

 with tstd_trans {S : Set} (M₁ M M₂ : term S)
  (Hstd₁ : M₁ ↠ₛₜ M )
  (Hstd₂ : M  ↠ₛₜ M₂) { struct Hstd₂ }:
  M₁ ↠ₛₜ M₂.
Proof.
(* tint_trans *)
{
  (* intros Htint₁ Htint₂. *)
  induction Htint₂.
  + inversion Htint₁ as [ V₀ ? HV₀ | | | |]; subst.
    constructor.
    eapply vint_trans.
    - apply HV₀.
    - apply H.
  + inversion Htint₁ as [| M₀ ? N₀ ? Hnv HM₀ HN₀ | V₀ ? N₀ ? HV₀ HN₀ | |]; subst.
    { constructor.
      + apply Hnv.
      + apply IHHtint₂.
        apply HM₀.
      + eapply tstd_trans.
        - apply HN₀.
        - apply H0. }
    { apply tint_app_nonvalue.
      + eapply tint_nonvalue_inv_r.
        - constructor. apply HV₀.
        - apply H.
      + apply IHHtint₂. constructor. apply HV₀.
      + inversion H0; subst.
        apply tint_wh_std with (M₁ := N₀) in H1; [| apply HN₀ ].
        inversion H1; subst.
        apply tint_trans with (M₂ := N') in H4; [| apply H2 ].
        econstructor.
        - apply H3.
        - apply H4. }
  + inversion Htint₁ as [| M₀ ? N₀ ? Hnv HM₀ HN₀ | V₀ ? N₀ ? HV₀ HN₀ | |]; subst.
    { inversion HM₀; subst.
      destruct Hnv with (V := V0). reflexivity. }
    { apply tint_app.
      + apply vint_trans with (V := V); assumption.
      + apply IHHtint₂. apply HN₀. }
  + inversion Htint₁ as [| | | ? us us' L L' rs rs' Hus Hnv HL Hrs | ? rs rs' Hrs ]; subst.
    { apply tint_nonvalue_inv_l in HL as Hnv'; [| apply Hnv ].
      apply vals_cons_nonvalue_inv in H4; [| assumption .. ].
      destruct H4 as [? [? ?]]; subst.
      apply tint_op_nonvalue.
      { clear Htint₁.
        generalize dependent us.
        induction H; intros us Hus.
        + inversion Hus; subst. constructor.
        + inversion Hus; subst. constructor.
          - eapply vint_trans.
            * apply H6.
            * apply H.
          - apply IHForall2. apply H7. }
      { apply Hnv. }
      { apply IHHtint₂. apply HL. }
      { clear Htint₁.
        generalize dependent rs.
        induction H1; intros rs Hrs.
        + inversion Hrs; subst. constructor.
        + inversion Hrs; subst. constructor.
          - eapply tstd_trans.
            * apply H6.
            * apply H1.
          - apply IHForall2. apply H7. }
    }
    { exfalso. apply term_in_vals with (vs := rs') (M := M).
      - apply H0.
      - rewrite H4. 
        apply in_or_app. right.
        constructor. reflexivity. }
  + inversion Htint₁ as [| | | ? us us' L L' rs rs' Hus Hnv HL Hrs | ? rs rs' Hrs ]; subst.
    { exfalso. apply term_in_vals with (vs := vs) (M := L').
      - apply tint_nonvalue_inv_l with (M := L); assumption.
      - rewrite <- H2.
        apply in_or_app. right.
        constructor. reflexivity. }
    { constructor.
      clear Htint₁.
      apply vals_to_terms_inv in H2. subst.
      generalize dependent rs.
      induction H; intros rs Hrs.
      * apply Hrs.
      * inversion Hrs; subst. constructor.
        - apply vint_trans with (V := x); assumption.
        - apply IHForall2. assumption.
    }
}
(* vint_trans *)
{
  (* intros Hvint₁ Hvint₂. *)
  induction Hvint₂.
  + inversion Hvint₁; subst.
    apply vint_refl.
  + inversion Hvint₁; subst.
    apply vint_refl.
  + inversion Hvint₁; subst.
    constructor.
    eapply tstd_trans.
    - apply H2.
    - apply H.
}
(* tstd_trans *)
{
  (* intros Hstd₁ Hstd₂. *)
  destruct Hstd₁ as [ M₁ P₁ M HM₁ HP₁ ], Hstd₂ as [ M P₂ M₂ HM HP₂ ].
  pose proof (tint_wh_std _ _ _ HP₁ HM) as HstdP₁.
  inversion HstdP₁ as [? P ? HwhP₁ HP ]; subst.
  econstructor.
  + econstructor 3.
    - apply HM₁.
    - apply HwhP₁.
  + eapply tint_trans.
    - apply HP.
    - apply HP₂.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* Standardisation lemma *)

Lemma standardisation {S : Set} : ∀ (M N : term S),
  M →*ₜ N →
  M ↠ₛₜ N.
Proof.
  intros M N Hreds.
  induction Hreds.
  + apply tred_std. apply H.
  + apply tstd_refl.
  + eapply tstd_trans.
    - apply IHHreds1.
    - apply IHHreds2.
Qed.

Lemma tred_value_std {A : Set} (M : term A) (U : value A) :
  M →*ₜ U →
  ∃ (V : value A), M ↠ₕₜ V ∧ V ↠ᵢᵥ U.
Proof.
  intro Hreds.
  apply standardisation in Hreds.
  inversion Hreds; subst.
  inversion H0; subst.
  exists V. split.
  + apply H.
  + apply H3.
Qed.
