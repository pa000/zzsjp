Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import Syntax Semantics.
Require Import Relation_Operators.
Require Import List.
Import ListNotations.

Local Open Scope bind_scope.

Reserved Notation "M '⇉ₜ' M'" (at level 67).
Reserved Notation "V '⇉ᵥ' V'" (at level 67).

(* We prove confluence in the typical way by defining a parallel reduction relation ⇉.
  It corresponds to reducing many redexes in a term simultaneously. We then show that:
    - ⇉ is confluent (by defining a complete development),
    - ⇉ ⊆ →* ⊆ ⇉*,
  which implies that the original reduction is confluent. *)
Inductive tpar {S : Set} : term S → term S → Prop :=
  | tpar_beta : ∀ M M' (V V' : value S),
    M ⇉ₜ M' →
    V ⇉ᵥ V' →
    t_app (v_lam M) V ⇉ₜ subst M' V'
  | tpar_delta : ∀ op (bs : list constant) V,
    δ op bs = Some V →
    t_op op (consts_to_terms bs) ⇉ₜ from_closed V

  | tpar_value : ∀ V V',
    V ⇉ᵥ V' →
    V ⇉ₜ V'
  | tpar_app : ∀ M M' N N',
    M ⇉ₜ M' →
    N ⇉ₜ N' →
    t_app M N ⇉ₜ t_app M' N'
  | tpar_op : ∀ op (ts ts' : list (term S)),
    Forall2 tpar ts ts' →
    t_op op ts ⇉ₜ t_op op ts'
with vpar {S : Set} : value S → value S → Prop :=
  | vpar_var : ∀ x,
    v_var x ⇉ᵥ v_var x
  | vpar_const : ∀ b,
    v_const b ⇉ᵥ v_const b
  | vpar_lam : ∀ M M',
    M ⇉ₜ M' →
    v_lam M ⇉ᵥ v_lam M'

where "M ⇉ₜ M'" := (tpar M M')
  and "V ⇉ᵥ V'" := (vpar V V').

Notation tpar_rtc M₁ M₂ := (clos_refl_trans _ tpar M₁ M₂).
Notation vpar_rtc V₁ V₂ := (clos_refl_trans _ vpar V₁ V₂).

Notation "M '⇉*ₜ' M'" := (tpar_rtc M M') (at level 50).
Notation "V '⇉*ᵥ' V'" := (vpar_rtc V V') (at level 50).

Lemma tpar_lam_invert {A : Set} (M M' : term (inc A)) :
  v_lam M ⇉ₜ v_lam M' →
  M ⇉ₜ M'.
Proof.
  intro Hpar.
  inversion Hpar; subst.
  inversion H1; subst.
  apply H2.
Qed.

Lemma tpar_value_invert {A : Set} (V V' : value A) :
  V ⇉ₜ V' →
  V ⇉ᵥ V'.
Proof.
  intro Hpar. inversion Hpar; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ is reflexive. *)

Lemma tpar_refl {S : Set} : ∀ (M : term S),
  M ⇉ₜ M
with vpar_refl {S : Set} : ∀ (V : value S),
  V ⇉ᵥ V.
Proof.
(* tpar_refl *)
{
  induction M.
  + constructor. apply vpar_refl.
  + constructor.
    - apply IHM1.
    - apply IHM2.
  + constructor.
    induction ts.
    - constructor.
    - constructor.
      * apply tpar_refl.
      * apply IHts.
}
(* vpar_refl *)
{
  induction V.
  + constructor.
  + constructor.
  + constructor. apply tpar_refl.
}
Qed.

Lemma Forall2_tpar_refl {A : Set} (ts : list (term A)) :
  Forall2 tpar ts ts.
Proof.
  induction ts.
  + constructor.
  + constructor.
    - apply tpar_refl.
    - apply IHts.
Qed.

(* -------------------------------------------------------------------------- *)
(* → ⊆ ⇉ and →* ⊆ ⇉*. *)

Lemma tred_par {S : Set} : ∀ (M N : term S),
  M →ₜ N →
  M ⇉ₜ N
with vred_par {S : Set} : ∀ (V V' : value S),
  V →ᵥ V' →
  V ⇉ᵥ V'.
Proof.
(* tred_par *)
{
  intros M N Hred.
  induction Hred.
  + constructor 1 with (V' := V).
    - apply tpar_refl.
    - apply vpar_refl.
  + constructor. apply H.
  + constructor. apply vred_par. apply H.
  + constructor.
    - apply IHHred.
    - apply tpar_refl.
  + constructor.
    - apply tpar_refl.
    - apply IHHred.
  + constructor.
    repeat apply Forall2_app.
    - apply Forall2_tpar_refl.
    - constructor; [ apply IHHred | auto ].
    - apply Forall2_tpar_refl.
}
(* vred_par *)
{
  intros V V' Hred.
  induction Hred.
  constructor.
  apply tred_par. apply H.
}
Qed.

Lemma treds_pars {S : Set} : ∀ (M N : term S),
  M →*ₜ N →
  M ⇉*ₜ N
with vreds_pars {S : Set} : ∀ (V V' : value S),
  V →*ᵥ V' →
  V ⇉*ᵥ V'.
Proof.
(* treds_pars *)
{
  intros M N Hreds.
  induction Hreds.
  + constructor. apply tred_par. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* vreds_pars *)
{
  intros V V' Hreds.
  induction Hreds.
  + constructor. apply vred_par. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ ⊆ →* and ⇉* ⊆ →*. *)

Lemma tpar_reds {S : Set} (M N : term S) :
  M ⇉ₜ N →
  M →*ₜ N
with vpar_reds {S : Set} (V V' : value S) :
  V ⇉ᵥ V' →
  V →*ᵥ V'.
Proof.
(* tpar_reds *)
{
  intro Hpar.
  induction Hpar.
  + (* TASK 2.1: Prove this case *) admit.
  + constructor. constructor. apply H.
  + apply tred_value_cong.
    apply vpar_reds.
    apply H.
  + constructor 3 with (y := t_app M' N).
    - apply tred_appl_cong.
      apply IHHpar1.
    - apply tred_appr_cong.
      apply IHHpar2.
  + apply tred_op_cong.
    induction H.
    - constructor.
    - constructor.
      * apply tpar_reds. apply H.
      * apply IHForall2.
}
(* vpar_reds *)
{
  intro Hpar.
  induction Hpar.
  + constructor 2.
  + constructor 2.
  + apply vred_lam_cong.
    apply tpar_reds.
    apply H.
}
Admitted.

Lemma tpars_reds {S : Set} (M N : term S) :
  M ⇉*ₜ N →
  M →*ₜ N
with vpars_reds {S : Set} (V V' : value S) :
  V ⇉*ᵥ V' →
  V →*ᵥ V'.
Proof.
all: (
  intros Hpar;
  induction Hpar; [
    apply tpar_reds || apply vpar_reds; apply H
  | constructor 2
  | econstructor 3; [
      apply IHHpar1
    | apply IHHpar2 ]]).
Qed.

(* -------------------------------------------------------------------------- *)
(* complete development *)

(* If `ts` consists only of constants, return the list of constants
  else return None *)
Fixpoint extract_constants {A : Set} (ts : list (term A)) : option (list constant) :=
  match ts with
  | [] => Some []
  | t_value (v_const b) :: ts =>
    match extract_constants ts with
    | None => None
    | Some bs => Some (b :: bs)
    end
  | _ => None
  end.

Lemma extract_constants_correct {A : Set} (ts : list (term A)) (bs : list constant) :
  extract_constants ts = Some bs →
  ts = consts_to_terms bs.
Proof.
  generalize dependent bs.
  induction ts as [| M ts ]; intros bs Hts.
  + term_simpl in Hts. inversion Hts; subst.
   reflexivity.
  + term_simpl in Hts.
    destruct M; inversion Hts; subst.
    destruct V; inversion Hts; subst.
    destruct (extract_constants ts) as [bs' |]; inversion Hts; subst.
    term_simpl. f_equal.
    apply IHts. reflexivity.
Qed.

Lemma extract_constants_correct2 {A : Set} (ts : list (term A)) (bs : list constant) :
  ts = consts_to_terms bs →
  extract_constants ts = Some bs.
Proof.
  intro Hts.
  generalize dependent bs.
  induction ts; intros bs Hts.
  + destruct bs; try discriminate.
    reflexivity.
  + destruct bs; try discriminate.
    inversion Hts; subst.
    term_simpl.
    specialize IHts with bs.
    rewrite IHts; reflexivity.
Qed.

Lemma extract_constants_consts {A : Set} (bs : list constant) :
  @extract_constants A (consts_to_terms bs) = Some bs.
Proof.
  apply extract_constants_correct2.
  reflexivity.
Qed.

(* The complete development is obtained by contracting all redexes of a term. *)
Fixpoint tcd {S : Set} (M : term S) { struct M } : term S :=
  match M with
  | t_value V   => t_value (vcd V)
  | t_app (v_lam M₁) (t_value V₂) => subst (tcd M₁) (vcd V₂)
  | t_app M₁ M₂ => t_app (tcd M₁) (tcd M₂)
  | t_op op ts  =>
    match extract_constants ts with
    | None => t_op op (map tcd ts)
    | Some bs =>
      match δ op bs with
      | None => t_op op ts (* in this case it won't reduce further so that's the cd *)
      | Some V => from_closed V
      end
    end
  end
with vcd {S : Set} (V : value S) { struct V } : value S :=
  match V with
  | v_var x   => v_var x
  | v_const b => v_const b
  | v_lam M   => v_lam (tcd M)
  end.

(* -------------------------------------------------------------------------- *)
(* every term parallel-reduces to its complete development. *)

Lemma tpar_cd {S : Set} (M : term S) :
  M ⇉ₜ tcd M
with vpar_cd {S : Set} (V : value S) :
  V ⇉ᵥ vcd V.
Proof.
(* treds_cd *)
{
  induction M as [ ? V | A M₁ IHM₁ M₂ |].
  + term_simpl. constructor. apply vpar_cd.
  + (* TASK 2.2: Prove this case *) admit.
  + term_simpl.
    destruct (extract_constants ts) as [bs |] eqn:Hts.
    - destruct (δ op bs) as [V |] eqn:Hδ.
      * apply extract_constants_correct in Hts.
        rewrite Hts.
        constructor. apply Hδ.
      * constructor. apply Forall2_tpar_refl.
    - constructor.
      clear Hts.
      induction ts.
      * constructor.
      * constructor.
        ++ apply tpar_cd.
        ++ apply IHts.
}
(* vpar_cd *)
{
  induction V.
  + term_simpl. apply vpar_refl.
  + term_simpl. apply vpar_refl.
  + term_simpl. constructor.
    apply tpar_cd.
}
Admitted.

(* -------------------------------------------------------------------------- *)
(* ⇉ is preserved under fmap. *)

Ltac Forall_ind H :=
  induction H as [| ? ? ? ? ? ? IHForall2 ]; [
    constructor
  | constructor; [| apply IHForall2 ]
  ].

Lemma tpar_map {S T : Set} (φ : S [→] T) (M M' : term S) :
  M ⇉ₜ M' →
  fmap φ M ⇉ₜ fmap φ M'
 with vpar_map {S T : Set} (φ : S [→] T) (V V' : value S) :
  V ⇉ᵥ V' →
  fmap φ V ⇉ᵥ fmap φ V'.
Proof.
(* tpar_map *)
{
  intros Hpar.
  generalize dependent T.
  induction Hpar; intros T φ;
    try (term_simpl; constructor; auto).
  + term_simpl.
    rewrite fmap_closed_pure.
    rewrite fmap_consts_pure.
    constructor. apply H.
  + Forall_ind H.
    apply tpar_map. apply H.
}
(* vpar_map *)
{
  intros Hpar.
  induction Hpar;
    try (term_simpl; constructor; auto).
}
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ is preserved under bind (substitution).
   We use an auxiliary definition of parallel reduction for substitutions. *)

Definition spar {S T : Set} (φ φ' : S [⇒] T) :=
  ∀ x, φ x ⇉ᵥ φ' x.
Notation "φ ⇉ₛ φ'" := (spar φ φ') (at level 67).

Lemma spar_lift {S T : Set} (φ φ' : S [⇒] T) :
  φ ⇉ₛ φ' →
  φ ↑ ⇉ₛ φ' ↑.
Proof.
  intros Hpar.
  intro x. destruct x as [| x].
  + term_simpl. apply vpar_refl.
  + term_simpl. apply vpar_map. apply Hpar.
Qed.

Lemma tpar_bind {S T : Set} (M M' : term S) (φ φ' : S [⇒] T) :
  φ ⇉ₛ φ' →
  M ⇉ₜ M' →
  bind φ M ⇉ₜ bind φ' M'
 with vpar_bind {S T : Set} (V V' : value S) (φ φ' : S [⇒] T) :
  φ ⇉ₛ φ' →
  V ⇉ᵥ V' →
  bind φ V ⇉ᵥ bind φ' V'.
Proof.
(* tpar_bind *)
{
  intros Hφ Hpar.
  generalize dependent T.
  induction Hpar; intros T φ φ' Hφ.
  + term_simpl. constructor.
    - apply IHHpar. apply spar_lift. apply Hφ.
    - apply vpar_bind.
      * apply Hφ.
      * apply H.
  + term_simpl.
    rewrite bind_closed_pure. rewrite bind_consts_pure.
    constructor. apply H.
  + term_simpl. constructor.
    apply vpar_bind.
    - apply Hφ.
    - apply H.
  + term_simpl. constructor.
    - apply IHHpar1. apply Hφ.
    - apply IHHpar2. apply Hφ.
  + term_simpl. constructor.
    Forall_ind H.
    apply tpar_bind.
    - apply Hφ.
    - apply H.
}
(* vpar_bind *)
{
  intros Hφ Hpar.
  induction Hpar.
  + term_simpl. apply Hφ.
  + term_simpl. apply vpar_refl.
  + term_simpl. constructor.
    apply tpar_bind.
    - apply spar_lift. apply Hφ.
    - apply H.
}
Qed.

Lemma spar_mk_subst_value {S : Set} (V V' : value S) :
  V ⇉ᵥ V' →
  mk_subst V ⇉ₛ mk_subst V'.
Proof.
  intros Hpar.
  intro x. destruct x as [| x].
  + term_simpl. apply Hpar.
  + term_simpl. apply vpar_refl.
Qed.

Lemma tpar_subst {S : Set} (M M' : term (inc S)) V V' :
  M ⇉ₜ M' →
  V ⇉ᵥ V' →
  subst M V ⇉ₜ subst M' V'.
Proof.
  intros HparM HparV.
  apply tpar_bind.
  + apply spar_mk_subst_value. apply HparV.
  + apply HparM.
Qed.

(* -------------------------------------------------------------------------- *)
(* triangle lemma:
   if M ⇉ M', then M' ⇉ tcd M.
      M
     /|
    / |
   M' |
    \ |
     \|
    tcd M
*)

Lemma Forall2_tpar_consts_inv {A : Set} (bs : list constant) (ts : list (term A)) :
  Forall2 tpar (consts_to_terms bs) ts →
  ts = consts_to_terms bs.
Proof.
  intro Hall.
  generalize dependent bs.
  induction ts; intros bs Hall.
  - inversion Hall. reflexivity.
  - inversion Hall; subst.
    destruct bs; try discriminate.
    term_simpl in H. inversion H; subst.
    inversion H2; subst.
    inversion H1; subst.
    f_equal.
    apply IHts. apply H3.
Qed.

Fixpoint tcd_complete {S : Set} (M M' : term S) { struct M }:
  M ⇉ₜ M' →
  M' ⇉ₜ tcd M
 with vcd_complete {S : Set} (V V' : value S) { struct V }:
  V ⇉ᵥ V' →
  V' ⇉ᵥ vcd V.
Proof.
(* tcd_complete *)
{
  intro Hpar.
  induction M as [ ? V | ? M₁ IHM₁ M₂ | ? op ts ].
  (* t_value V *)
  + term_simpl. inversion Hpar as [| | ? V' Hparᵥ | |]; subst.
    constructor. apply vcd_complete. apply Hparᵥ.
  (* t_app M₁ M₂ *)
  + (* TASK 2.3: Prove this case *) admit.
  (* t_op op ts *)
  + inversion Hpar as [| ? bs ? Hδ | | |]; subst.
    (* t_op op (consts_to_terms bs) *)
    - term_simpl. rewrite extract_constants_consts.
      rewrite Hδ. apply tpar_refl.
    (* t_op op ts' *)
    - term_simpl. destruct (extract_constants ts) as [bs |] eqn:Hts.
      * destruct (δ op bs) as [V |] eqn:Hδ.
        ++ apply extract_constants_correct in Hts. subst ts.
          apply Forall2_tpar_consts_inv in H. subst ts'.
          constructor. apply Hδ.
        ++ constructor.
          apply extract_constants_correct in Hts. subst ts.
          apply Forall2_tpar_consts_inv in H. subst ts'.
          clear Hpar Hδ.
          induction bs.
          -- constructor.
          -- constructor.
            ** term_simpl. apply tpar_refl.
            ** apply IHbs.
      * constructor.
        clear Hpar Hts.
        generalize dependent ts'.
        induction ts; intros ts' Hall.
        ++ inversion Hall. constructor.
        ++ inversion Hall; subst.
          constructor.
          -- apply tcd_complete. apply H1.
          -- apply IHts. apply H3.
}
(* vcd_complete *)
{

  intro Hpar.
  induction V.
  + inversion Hpar; subst.
    term_simpl. apply Hpar.
  + inversion Hpar; subst.
    term_simpl. apply Hpar.
  + inversion Hpar; subst.
    term_simpl. constructor.
    apply tcd_complete. apply H0.
}
Admitted.

(* -------------------------------------------------------------------------- *)
(* Finally: ⇉, ⇉* and →* are confluent. *)

Lemma tpar_confluence {S : Set} (M M₁ M₂ : term S) :
  M ⇉ₜ M₁ →
  M ⇉ₜ M₂ →
  ∃ M', M₁ ⇉ₜ M' ∧ M₂ ⇉ₜ M'
 with vpar_confluence {S : Set} (V V₁ V₂ : value S) :
  V ⇉ᵥ V₁ →
  V ⇉ᵥ V₂ →
  ∃ V', V₁ ⇉ᵥ V' ∧ V₂ ⇉ᵥ V'.
Proof.
(* tpar_confluence *)
{
  intros Hpar₁ Hpar₂.
  exists (tcd M).
  split; apply tcd_complete; assumption.
}
(* vpar_confluence *)
{
  intros Hpar₁ Hpar₂.
  exists (vcd V).
  split; apply vcd_complete; assumption.
}
Qed.

(* Auxiliary strip lemma:
        M
       / \
      /   *
     /     \
    M₁     M₂
     \    /
      *  /
       \/
       M'
*)

Lemma tpars_strip {S : Set} (M M₁ M₂ : term S) :
  M ⇉ₜ M₁ →
  M ⇉*ₜ M₂ →
  ∃ M', M₁ ⇉*ₜ M' ∧ M₂ ⇉ₜ M'
 with vpars_strip {S : Set} (V V₁ V₂ : value S) :
  V ⇉ᵥ V₁ →
  V ⇉*ᵥ V₂ →
  ∃ V', V₁ ⇉*ᵥ V' ∧ V₂ ⇉ᵥ V'.
Proof.
(* tpars_strip *)
{
  intros Hpar₁ Hpars₂.
  generalize dependent M₁.
  induction Hpars₂; intros M₁ Hpar₁.
  + exists (tcd x).
    split.
    - constructor. apply tcd_complete. apply Hpar₁.
    - apply tcd_complete. apply H.
  + exists (tcd x).
    split.
    - constructor. apply tcd_complete. apply Hpar₁.
    - apply tpar_cd.
  + apply IHHpars₂1 in Hpar₁.
    destruct Hpar₁ as [tcd₁ [HM₁ Hy]].
    apply IHHpars₂2 in Hy.
    destruct Hy as [tcd₂ [Htcd₁ Hz]].
    exists (tcd₂).
    split.
    - constructor 3 with (y := tcd₁).
      * apply HM₁.
      * apply Htcd₁.
    - apply Hz.
}
(* vpars_strip *)
{
  intros Hpar₁ Hpars₂.
  generalize dependent V₁.
  induction Hpars₂; intros V₁ Hpar₁.
  + exists (vcd x).
    split.
    - constructor. apply vcd_complete. apply Hpar₁.
    - apply vcd_complete. apply H.
  + exists (vcd x).
    split.
    - constructor. apply vcd_complete. apply Hpar₁.
    - apply vpar_cd.
  + apply IHHpars₂1 in Hpar₁.
    destruct Hpar₁ as [vcd₁ [HM₁ Hy]].
    apply IHHpars₂2 in Hy.
    destruct Hy as [vcd₂ [Hvcd₁ Hz]].
    exists (vcd₂).
    split.
    - constructor 3 with (y := vcd₁).
      * apply HM₁.
      * apply Hvcd₁.
    - apply Hz.
}
Qed.

Lemma tpars_confluence {S : Set} (M M₁ M₂ : term S) :
  M ⇉*ₜ M₁ →
  M ⇉*ₜ M₂ →
  ∃ M', M₁ ⇉*ₜ M' ∧ M₂ ⇉*ₜ M'
 with vpars_confluence {S : Set} (V V₁ V₂ : value S) :
  V ⇉*ᵥ V₁ →
  V ⇉*ᵥ V₂ →
  ∃ V', V₁ ⇉*ᵥ V' ∧ V₂ ⇉*ᵥ V'.
Proof.
(* tpars_confluence *)
{
  intros Hpar₁ Hpar₂.
  generalize dependent M₂.
  induction Hpar₁; intros M₂ Hpar₂.
  + pose proof (tpars_strip _ _ _ H Hpar₂) as Hstrip.
    destruct Hstrip as [Mtcd [Hy HM₂]].
    exists Mtcd.
    split.
    - apply Hy.
    - constructor. apply HM₂.
  + assert (Hpar₁: x ⇉ₜ x) by (apply tpar_refl).
    pose proof (tpars_strip _ _ _ Hpar₁ Hpar₂) as Hstrip.
    destruct Hstrip as [Mtcd [Hx HM₂]].
    exists Mtcd.
    split.
    - apply Hx.
    - constructor. apply HM₂.
  + apply IHHpar₁1 in Hpar₂.
    destruct Hpar₂ as [Mtcd₁ [Hy HM₂]].
    apply IHHpar₁2 in Hy.
    destruct Hy as [Mtcd₂ [Hz HMtcd₁]].
    exists Mtcd₂.
    split.
    - apply Hz.
    - constructor 3 with (y := Mtcd₁).
      * apply HM₂.
      * apply HMtcd₁.
}
(* vpars_confluence *)
{
  intros Hpar₁ Hpar₂.
  generalize dependent V₂.
  induction Hpar₁; intros V₂ Hpar₂.
  + pose proof (vpars_strip _ _ _ H Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hy HV₂]].
    exists Vvcd.
    split.
    - apply Hy.
    - constructor. apply HV₂.
  + assert (Hpar₁: x ⇉ᵥ x) by (apply vpar_refl).
    pose proof (vpars_strip _ _ _ Hpar₁ Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hx HV₂]].
    exists Vvcd.
    split.
    - apply Hx.
    - constructor. apply HV₂.
  + apply IHHpar₁1 in Hpar₂.
    destruct Hpar₂ as [Vvcd₁ [Hy HV₂]].
    apply IHHpar₁2 in Hy.
    destruct Hy as [Vvcd₂ [Hz HVvcd₁]].
    exists Vvcd₂.
    split.
    - apply Hz.
    - constructor 3 with (y := Vvcd₁).
      * apply HV₂.
      * apply HVvcd₁.
}
Qed.

Lemma treds_confluence {S : Set} (M M₁ M₂ : term S) :
  M →*ₜ M₁ →
  M →*ₜ M₂ →
  ∃ M', M₁ →*ₜ M' ∧ M₂ →*ₜ M'
 with vreds_confluence {S : Set} (V V₁ V₂ : value S) :
  V →*ᵥ V₁ →
  V →*ᵥ V₂ →
  ∃ V', V₁ →*ᵥ V' ∧ V₂ →*ᵥ V'.
Proof.
(* treds_confluence *)
{
  intros Hreds₁ Hreds₂.
  apply treds_pars in Hreds₁.
  apply treds_pars in Hreds₂.
  pose proof (tpars_confluence _ _ _ Hreds₁ Hreds₂) as Hpar_conf.
  destruct Hpar_conf as [M' [HM₁ HM₂]].
  apply tpars_reds in HM₁.
  apply tpars_reds in HM₂.
  exists M'.
  split; assumption.
}
(* vreds_confluence*)
{
  intros Hreds₁ Hreds₂.
  apply vreds_pars in Hreds₁.
  apply vreds_pars in Hreds₂.
  pose proof (vpars_confluence _ _ _ Hreds₁ Hreds₂) as Hpar_conf.
  destruct Hpar_conf as [M' [HM₁ HM₂]].
  apply vpars_reds in HM₁.
  apply vpars_reds in HM₂.
  exists M'.
  split; assumption.
}
Qed.