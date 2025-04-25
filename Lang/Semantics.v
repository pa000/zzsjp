Require Import Utf8.
Require Import Syntax.
Require Import Binding.Lib Binding.Set.
Require Import Relation_Operators.
Require Import List.
Require Import PeanoNat.
Import ListNotations.

Local Open Scope bind_scope.

Reserved Notation "M '→ₜ' M'" (at level 67).
Reserved Notation "V '→ᵥ' V'" (at level 67).

Parameter δ : operator → list constant → option (value ∅).

(* δ returns closed values so we need a way to lift it to any set *)
Lemma from_inct {A : Set} n (M : term (Nat.iter n inc ∅)) : term (Nat.iter n inc A)
 with from_incv {A : Set} n (V : value (Nat.iter n inc ∅)) : value (Nat.iter n inc A).
Proof.
{
  destruct M.
  - constructor. apply from_incv. apply V.
  - constructor 2.
    * apply from_inct. apply M1.
    * apply from_inct. apply M2.
  - constructor 3.
    * apply op.
    * induction ts.
      + apply nil.
      + apply cons.
        -- apply from_inct. apply a.
        -- apply IHts.
}
{
  destruct V.
  - constructor.
    induction n.
    * destruct x.
    * term_simpl in x. term_simpl.
      destruct x.
      + apply VZ.
      + apply VS. apply IHn. apply i.
  - constructor 2. apply b.
  - constructor 3.
    replace (inc (Nat.iter n inc A)) with (Nat.iter (S n) inc A) by reflexivity.
    apply from_inct. apply M.
}
Defined.

Lemma from_closed {A : Set} (V : value ∅) : value A.
Proof.
  apply from_incv with (n := 0). apply V.
Defined.

Notation subst := (subst (Inc := inc)).

Inductive tred {S : Set} : term S → term S → Prop :=
  | tred_beta : ∀ M (V : value S),
    t_app (v_lam M) V →ₜ subst M V
  | tred_delta : ∀ op (bs : list constant) V,
    δ op bs = Some V →
    t_op op (consts_to_terms bs) →ₜ from_closed V

  | tred_value : ∀ V V',
    V →ᵥ V' →
    V →ₜ V'
  | tred_app_L : ∀ M M' N,
    M →ₜ M' →
    t_app M N →ₜ t_app M' N
  | tred_app_R : ∀ M N N',
    N →ₜ N' →
    t_app M N →ₜ t_app M N'
  | tred_op : ∀ op ts M M' ts',
    M →ₜ M' →
    t_op op (ts ++ [M] ++ ts') →ₜ t_op op (ts ++ [M'] ++ ts')

with vred {S : Set} : value S → value S → Prop :=
  | vred_lam : ∀ M M',
    M →ₜ M' →
    v_lam M →ᵥ v_lam M'

where "M →ₜ M'" := (tred M M')
  and "V →ᵥ V'" := (vred V V').

Notation tred_tc M₁ M₂ := (clos_trans_1n _ tred M₁ M₂).
Notation vred_tc V₁ V₂ := (clos_trans_1n _ vred V₁ V₂).

Notation "M →+ₜ M'" := (tred_tc M M') (at level 100).
Notation "V →+ᵥ V'" := (vred_tc V V') (at level 100).

Definition tred_rtc {A : Set} M₁ M₂ := (clos_refl_trans (term A) tred M₁ M₂).
Definition vred_rtc {A : Set} V₁ V₂ := (clos_refl_trans (value A) vred V₁ V₂).

Notation "M '→*ₜ' M'" := (clos_refl_trans _ tred M M') (at level 50).
Notation "V '→*ᵥ' V'" := (clos_refl_trans _ vred V V') (at level 50).

Notation tred_symc M₁ M₂ := (clos_refl_sym_trans _ tred M₁ M₂).
Notation vred_symc V₁ V₂ := (clos_refl_sym_trans _ vred V₁ V₂).

Notation "M '=ₜ' M'" := (tred_symc M M') (at level 50).
Notation "V '=ᵥ' V'" := (vred_symc V V') (at level 50).

(* -------------------------------------------------------------------------- *)
(* → and →* are preserved under fmap. *)

Ltac cong H :=
  induction H; [
    constructor; constructor; assumption
  | constructor 2
  | econstructor 3; [
      eassumption
    | assumption ]
  ].

Lemma tred_value_cong {S : Set} : ∀ (V V' : value S),
  V →*ᵥ V' →
  V →*ₜ V'.
Proof.
  intros V V' Hreds.
  cong Hreds.
Qed.

Lemma tred_appl_cong {S : Set} : ∀ (M M' N : term S),
  M →*ₜ M' →
  t_app M N →*ₜ t_app M' N.
Proof.
  intros M M' N Hreds.
  cong Hreds.
Qed.

Lemma tred_appr_cong {S : Set} : ∀ (M N N' : term S),
  N →*ₜ N' →
  t_app M N →*ₜ t_app M N'.
Proof.
  intros M M' N Hreds.
  cong Hreds.
Qed.

Lemma tred_op_cong' {S : Set} : ∀ op (ts ts' : list (term S)) M M',
  M →*ₜ M' →
  t_op op (ts ++ [M] ++ ts') →*ₜ t_op op (ts ++ [M'] ++ ts').
Proof.
  intros op ts ts' M M' Hreds.
  cong Hreds.
Qed.

Lemma tred_op_cong {S : Set} : ∀ op (ts ts' : list (term S)),
  Forall2 tred_rtc ts ts' →
  t_op op ts →*ₜ t_op op ts'.
Proof.
  intros op ts ts' Hforall.
  assert (∀ rs, t_op op (rs ++ ts) →*ₜ t_op op (rs ++ ts')).
  generalize dependent ts'.
  induction ts; intros ts' Hall rs.
  - apply Forall2_length in Hall.
    destruct ts'; try discriminate.
    constructor 2.
  - apply Forall2_length in Hall as Hlen.
    destruct ts'; try discriminate.
    apply Forall2_cons_iff in Hall.
    destruct Hall as [Hpar Hforall].
    constructor 3 with (y := t_op op (rs ++ t :: ts)).
    { apply tred_op_cong' with (ts := rs) (M := a) (ts' := ts).
      apply Hpar. }
    replace (t :: ts) with ([t] ++ ts) by reflexivity.
    replace (t :: ts') with ([t] ++ ts') by reflexivity.
    rewrite !app_assoc.
    apply IHts.
    apply Hforall.
  - apply H with (rs := []).
Qed.

Lemma vred_lam_cong {S : Set} : ∀ (M M' : term (inc S)),
  M →*ₜ M' →
  v_lam M →*ᵥ v_lam M'.
Proof.
  intros M M' Hreds.
  cong Hreds.
Qed.

Lemma fmap_consts_pure {A B : Set} (φ : A [→] B) (bs : list constant) :
  map (fmap φ) (consts_to_terms bs) = consts_to_terms bs.
Proof.
  induction bs.
  - term_simpl. reflexivity.
  - term_simpl. f_equal.
    apply IHbs.
Qed.

Lemma fmap_delta_liftt {A B : Set} n (φ : A [→] B) (M : term (Nat.iter n inc ∅)) :
  fmap (liftn n φ) (from_inct n M) = from_inct n M
 with fmap_delta_liftv {A B : Set} n (φ : A [→] B) (V : value (Nat.iter n inc ∅)) :
  fmap (liftn n φ) (from_incv n V) = from_incv n V.
Proof.
{
  destruct M.
  + term_simpl. f_equal. apply fmap_delta_liftv.
  + term_simpl. f_equal.
    - apply fmap_delta_liftt.
    - apply fmap_delta_liftt.
  + term_simpl. f_equal.
    list_ind ts.
    apply fmap_delta_liftt.
}
{
  destruct V.
  + induction n.
    - destruct x.
    - destruct x as [| x].
      * term_simpl. reflexivity.
      * term_simpl. term_simpl in IHn.
        specialize IHn with x.
        inversion IHn. rewrite H0.
        reflexivity.
  + term_simpl. reflexivity.
  + term_simpl.
    f_equal.
    replace (liftn n φ ↑) with (liftn (S n) φ) by reflexivity.
    pose proof (fmap_delta_liftt A B (S n) φ M) as IH.
    apply IH.
}
Qed.

Fixpoint fmap_closed_pure {A B : Set} (φ : A [→] B) M :
  fmap φ (from_closed M) = from_closed M.
Proof.
  unfold from_closed.
  apply fmap_delta_liftv with (n := 0).
Qed.

Lemma tred_map {S T : Set} : ∀ (M M' : term S) (φ : S [→] T),
  M →ₜ M' →
  fmap φ M →ₜ fmap φ M'
with vred_map {S T : Set} : ∀ (V V' : value S) (φ : S [→] T),
  V →ᵥ V' →
  fmap φ V →ᵥ fmap φ V'.
Proof.
(* tred_map *)
{
  intros M M' φ Hred.
  induction Hred.
  + term_simpl.
    constructor.
  + term_simpl.
    rewrite fmap_consts_pure. rewrite fmap_closed_pure.
    constructor. apply H.
  + term_simpl. constructor. apply vred_map. apply H.
  + term_simpl. constructor. apply IHHred.
  + term_simpl. constructor. apply IHHred.
  + term_simpl. rewrite !map_app. term_simpl.
    constructor. apply IHHred.
}
(* vred_map *)
{
  intros V V' φ Hred.
  induction Hred.
  term_simpl. constructor. apply tred_map. apply H.
}
Qed.

Lemma treds_map {S T : Set} : ∀ (M M' : term S) (φ : S [→] T),
  M →*ₜ M' →
  fmap φ M →*ₜ fmap φ M'
with vreds_map {S T : Set} : ∀ (V V' : value S) (φ : S [→] T),
  V →*ᵥ V' →
  fmap φ V →*ᵥ fmap φ V'.
Proof.
(* treds_map *)
{
  intros M M' φ Hreds.
  induction Hreds.
  + constructor. apply tred_map. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* vreds_map *)
{
  intros M M' φ Hreds.
  induction Hreds.
  + constructor. apply vred_map. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
Qed.

Lemma bind_delta_liftt {A B : Set} n (φ : A [⇒] B) (M : term (Nat.iter n inc ∅)) :
  bind (liftn n φ) (from_inct n M) = from_inct n M
 with bind_delta_liftv {A B : Set} n (φ : A [⇒] B) (V : value (Nat.iter n inc ∅)) :
  bind (liftn n φ) (from_incv n V) = from_incv n V.
Proof.
{
  destruct M.
  + term_simpl. f_equal. apply bind_delta_liftv.
  + term_simpl. f_equal.
    - apply bind_delta_liftt.
    - apply bind_delta_liftt.
  + term_simpl. f_equal.
    list_ind ts.
    apply bind_delta_liftt.
}
{
  destruct V.
  + induction n.
    - destruct x.
    - destruct x as [| x].
      * term_simpl. reflexivity.
      * term_simpl. term_simpl in IHn.
        specialize IHn with x.
        inversion IHn. rewrite H0.
        reflexivity.
  + term_simpl. reflexivity.
  + term_simpl.
    f_equal.
    replace (liftn n φ ↑) with (liftn (S n) φ) by reflexivity.
    pose proof (bind_delta_liftt A B (S n) φ M) as IH.
    apply IH.
}
Qed.

Fixpoint bind_closed_pure {A B : Set} (φ : A [⇒] B) M :
  bind φ (from_closed M) = from_closed M.
Proof.
  unfold from_closed.
  apply bind_delta_liftv with (n := 0).
Qed.

Lemma bind_consts_pure {A B : Set} (φ : A [⇒] B) (bs : list constant) :
  map (bind φ) (consts_to_terms bs) = consts_to_terms bs.
Proof.
  induction bs.
  - term_simpl. reflexivity.
  - term_simpl. f_equal.
    apply IHbs.
Qed.

Fixpoint treds_const_inv {A : Set} (M : term A) (b : constant)
  (Hreds: v_const b →*ₜ M) :
  M = v_const b.
Proof.
  inversion Hreds; subst.
  + inversion H; subst.
    inversion H1; subst.
  + reflexivity.
  + apply treds_const_inv in H.
    subst y.
    apply treds_const_inv in H0.
    apply H0.
Qed.

Fixpoint treds_lam_inv {A : Set} (M : term A) N
  (Hreds: v_lam N →*ₜ M) :
  ∃ N', M = v_lam N'.
Proof.
  inversion Hreds; subst.
  + inversion H; subst.
    inversion H1; subst.
    exists M'. reflexivity.
  + exists N. reflexivity.
  + apply treds_lam_inv in H.
    destruct H as [N' Hy].
    subst y.
    apply treds_lam_inv in H0.
    apply H0.
Qed.