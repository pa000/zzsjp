Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import List.
Import ListNotations.

Notation map_id := Core.map_id.

Parameter constant : Set.
Parameter operator : Set.

Inductive term (A : Set) : Type :=
  | t_value (V : value A)
  | t_app   (M₁ M₂ : term A)
  | t_op    (op : operator) (ts : list (term A))
with value (A : Set) : Type :=
  | v_var   (x : A)
  | v_const (b : constant)
  | v_lam   (M : term (inc A)).

Coercion t_value : value >-> term.

Arguments t_value {A}.
Arguments t_app   {A}.
Arguments t_op    {A}.

Arguments v_var   {A}.
Arguments v_lam   {A}.
Arguments v_const {A}.

Inductive ectx (A : Set) : Set :=
  | e_hole : ectx A
  | e_appl (E : ectx A) (M : term A)
  | e_appr (V : value A) (E : ectx A)
  | e_op   (op : operator) (vs : list (value A)) (E : ectx A) (ts : list (term A)).

Arguments e_hole  {A}.
Arguments e_appl  {A}.
Arguments e_appr  {A}.
Arguments e_op    {A}.

Definition vals_to_terms {A : Set} (l : list (value A)) : list (term A) :=
  map (fun n => t_value n) l.

Definition consts_to_terms {A : Set} (l : list constant) : list (term A) :=
  map (fun b => t_value (v_const b)) l.

Definition consts_to_vals {A : Set} (l : list constant) : list (value A) :=
  map (fun b => v_const b) l.

Lemma consts_to_terms_comp {A : Set} (bs : list constant) :
  @consts_to_terms A bs = vals_to_terms (consts_to_vals bs).
Proof.
  symmetry.
  apply map_map.
Qed.

Fixpoint eplug {A : Set} (E : ectx A) (M : term A) : term A :=
  match E with
  | e_hole          => M
  | e_appl E M'     => t_app (eplug E M) M'
  | e_appr V E      => t_app V (eplug E M)
  | e_op op vs E ts => t_op op (vals_to_terms vs ++ [eplug E M] ++ ts)
  end.

(* Composition of evaluation contexts: (ecomp E1 E2)[M] = E1[E2[M]] *)
Fixpoint ecomp {A : Set} (E1 : ectx A) (E2 : ectx A) : ectx A :=
  match E1 with
  | e_hole           => E2
  | e_appl E1 M      => e_appl (ecomp E1 E2) M
  | e_appr V E1      => e_appr V (ecomp E1 E2)
  | e_op op vs E1 ts => e_op op vs (ecomp E1 E2) ts
  end.

Lemma ecomp_assoc {A : Set} (E₁ E₂ E₃ : ectx A) :
  ecomp E₃ (ecomp E₂ E₁) = ecomp (ecomp E₃ E₂) E₁.
Proof.
  induction E₃.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply IHE₃.
  + term_simpl. f_equal.
    apply IHE₃.
  + term_simpl. f_equal.
    apply IHE₃.
Qed.

(* ========================================================================= *)
(* Mapping, i.e. variable renaming *)

Fixpoint tmap {A B : Set} (φ : A [→] B) (t : term A) : term B :=
  match t with
  | t_value v   => vmap φ v
  | t_app t₁ t₂ => t_app (tmap φ t₁) (tmap φ t₂)
  | t_op op ts  => t_op op (map (tmap φ) ts)
  end
with vmap {A B : Set} (φ : A [→] B) (v : value A) : value B :=
  match v with
  | v_var x   => v_var (φ x)
  | v_lam t   => v_lam (tmap (lift φ) t)
  | v_const b => v_const b
  end.

Instance FMap_term  : FunctorCore term  := @tmap.
Instance FMap_value : FunctorCore value := @vmap.

Local Open Scope bind_scope.

Lemma tmap_id {A : Set} (φ : A [→] A) M (EQ : φ ≡ ı) : tmap φ M = M
with  vmap_id {A : Set} (φ : A [→] A) V (EQ : φ ≡ ı) : vmap φ V = V.
Proof.
(* tmap_id *)
{
  induction M.
  + term_simpl. f_equal. apply vmap_id. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    induction ts.
    - term_simpl. reflexivity.
    - term_simpl. f_equal.
      * apply tmap_id. apply EQ.
      * apply IHts.
}
(* vmap_id *)
{
  induction V.
  + term_simpl. f_equal. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply tmap_id.
    apply lift_id.
    apply EQ.
}
Qed.

Lemma tmap_map_comp {S T U : Set} (φ₂ : T [→] U) (φ₁ : S [→] T) φ M (EQ : φ₂ ∘ φ₁ ≡ φ) :
  tmap φ₂ (fmap φ₁ M) = fmap φ M
with vmap_map_comp {S T U : Set} (φ₂ : T [→] U) (φ₁ : S [→] T) φ V (EQ : φ₂ ∘ φ₁ ≡ φ) :
  vmap φ₂ (fmap φ₁ V) = fmap φ V.
Proof.
(* tmap_map_comp *)
{
  induction M.
  + term_simpl. f_equal. apply vmap_map_comp. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    induction ts.
    - term_simpl. reflexivity.
    - term_simpl. f_equal.
      * apply tmap_map_comp. apply EQ.
      * apply IHts.
}
(* vmap_map_comp *)
{
  induction V.
  + term_simpl. f_equal. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply tmap_map_comp.
    apply lift_comp.
    apply EQ.
}
Qed.

Instance Functor_term  : Functor term  := {| map_id := @tmap_id; map_map_comp := @tmap_map_comp |}.
Instance Functor_value : Functor value := {| map_id := @vmap_id; map_map_comp := @vmap_map_comp |}.

Fixpoint emap {A B : Set} (φ : A [→] B) (E : ectx A) : ectx B :=
  match E with
  | e_hole     => e_hole
  | e_appl E M => e_appl (emap φ E) (tmap φ M)
  | e_appr V E => e_appr (vmap φ V) (emap φ E)
  | e_op op vs E ts => e_op op (map (vmap φ) vs) (emap φ E) (map (tmap φ) ts)
  end.

Instance FMap_ectx : FunctorCore ectx := @emap.

Ltac list_ind xs :=
  induction xs; term_simpl; [
    constructor
  | f_equal; [
    | assumption
    ]
  ].

Lemma emap_id {A : Set} (φ : A [→] A) E (EQ : φ ≡ ı) : emap φ E = E.
Proof.
  induction E; term_simpl; f_equal; try apply map_id; try assumption.
  + list_ind vs. apply map_id. apply EQ.
  + list_ind ts. apply map_id. apply EQ.
Qed.

Lemma emap_map_comp {S T U : Set} (φ₂ : T [→] U) (φ₁ : S [→] T) φ E (EQ : φ₂ ∘ φ₁ ≡ φ) :
  emap φ₂ (fmap φ₁ E) = fmap φ E.
Proof.
  induction E; term_simpl; f_equal; try apply map_map_comp; try assumption.
  + list_ind vs. apply map_map_comp. apply EQ.
  + list_ind ts. apply map_map_comp. apply EQ.
Qed.

Instance Functor_etcx : Functor ectx := {| map_id := @emap_id; map_map_comp := @emap_map_comp |}.

Lemma emap_plug_comm {S T : Set} (E : ectx S) (M : term S) (φ : S [→] T) :
  fmap φ (eplug E M) = eplug (fmap φ E) (fmap φ M).
Proof.
  induction E; term_simpl; f_equal; try assumption.
  induction vs.
  - term_simpl. f_equal. apply IHE.
  - term_simpl. f_equal. apply IHvs.
Qed.

Lemma ecomp_pure {S : Set} (E : ectx S) :
  ecomp E e_hole = E.
Proof.
  induction E; term_simpl; f_equal; assumption.
Qed.

(* ========================================================================= *)
(* Binding, i.e. simultaneous subsitution *)

Instance SetPureCore_value : SetPureCore value := { set_pure := λ _, v_var }.

Fixpoint tbind {A B : Set} (φ : A [⇒] B) (t : term A) : term B :=
  match t with
  | t_value v   => vbind φ v
  | t_app t₁ t₂ => t_app (tbind φ t₁) (tbind φ t₂)
  | t_op op ts  => t_op op (map (tbind φ) ts)
  end
with vbind {A B : Set} (φ : A [⇒] B) (v : value A) : value B :=
  match v with
  | v_var x   => φ x
  | v_lam t   => v_lam (tbind (φ ↑) t)
  | v_const b => v_const b
  end.

Instance BindCore_term  : BindCore term  := @tbind.
Instance BindCore_value : BindCore value := @vbind.

Fixpoint ebind {A B : Set} (φ : A [⇒] B) (E : ectx A) : ectx B :=
  match E with
  | e_hole          => e_hole
  | e_appl E t      => e_appl (ebind φ E) (tbind φ t)
  | e_appr v E      => e_appr (vbind φ v) (ebind φ E)
  | e_op op vs E ts => e_op op (map (vbind φ) vs) (ebind φ E) (map (tbind φ) ts)
  end.

Instance BindCore_ectx : BindCore ectx := @ebind.

Instance SubstitutableCore_value : SubstitutableCore Sub value inc :=
  { mk_subst := λ A v,
    {| apply_sub := λ (x : (inc A)),
        match x with
        | VZ   => v
        | VS y => v_var y
        end
    |}
  }.

Program Instance SetPure_value : SetPure value.

Lemma tbind_map {S T : Set} (φ : S [→] T) ψ (M : term S) (EQ : φ ̂ ≡ ψ) :
  fmap φ M = bind ψ M
 with vbind_map {S T : Set} (φ : S [→] T) ψ (V : value S) (EQ : φ ̂ ≡ ψ) :
  fmap φ V = bind ψ V.
Proof.
(* tbind_map *)
{
  induction M.
  + term_simpl. f_equal. apply vbind_map. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    list_ind ts. apply tbind_map. apply EQ.
}
(* vbind_map *)
{
  induction V.
  + term_simpl. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply tbind_map.
    apply lift_of.
    apply EQ.
}
Qed.

Instance BindMapPure_term  : BindMapPure term  := { bind_map := @tbind_map }.
Instance BindMapPure_value : BindMapPure value := { bind_map := @vbind_map }.

Lemma ebind_map {S T : Set} (φ : S [→] T) ψ (E : ectx S) (EQ : φ ̂ ≡ ψ) :
  fmap φ E = bind ψ E.
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_map. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_map. apply EQ.
    - apply IHE.
  + term_simpl. f_equal.
    - list_ind vs. apply bind_map. apply EQ.
    - apply IHE.
    - list_ind ts. apply bind_map. apply EQ.
Qed.

Instance BindMapPure_ectx : BindMapPure ectx := { bind_map := @ebind_map }.

Lemma ecomp_fmap {S T : Set} (E1 : ectx S) (E2 : ectx S) (φ : S [→] T) :
  ecomp (fmap φ E1) (fmap φ E2) = fmap φ (ecomp E1 E2).
Proof.
  induction E1.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply IHE1.
  + term_simpl. f_equal.
    apply IHE1.
  + term_simpl. f_equal.
    apply IHE1.
Qed.

Lemma ecomp_kshift {S : Set} (E1 : ectx S) (E2 : ectx S) :
  ecomp (shift E1) (shift E2) = shift (ecomp E1 E2).
Proof.
  apply ecomp_fmap.
Qed.

Lemma ecomp_vshift {S : Set} (E1 : ectx S) (E2 : ectx S) :
  ecomp (shift E1) (shift E2) = fmap mk_shift (ecomp E1 E2).
Proof.
  apply ecomp_fmap.
Qed.

Lemma tbind_map_comm {S T₁ T₂ U : Set} (φ₁ : T₁ [→] U) (φ₂ : S [→] T₂) (ψ₁ : S [⇒] T₁) ψ₂ (M : term S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ M) = fmap φ₁ (bind ψ₁ M)
 with vbind_map_comm {S T₁ T₂ U : Set} (φ₁ : T₁ [→] U) (φ₂ : S [→] T₂) (ψ₁ : S [⇒] T₁) ψ₂ (V : value S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ V) = fmap φ₁ (bind ψ₁ V).
Proof.
(* tbind_map_comm *)
{
  induction M.
  + term_simpl. f_equal. apply vbind_map_comm. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    list_ind ts. apply tbind_map_comm. apply EQ.
}
(* vbind_map_comm *)
{
  induction V.
  + term_simpl.
    term_simpl in EQ.
    unfold "≡" in EQ.
    unfold SubEqC in EQ.
    specialize EQ with x.
    term_simpl in EQ.

    rewrite <- map_to_bind in EQ.
    apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply tbind_map_comm.
    apply lift_comm.
    apply EQ.
}
Qed.

Instance BindMapComm_term  : BindMapComm term  := { bind_map_comm := @tbind_map_comm }.
Instance BindMapComm_value : BindMapComm value := { bind_map_comm := @vbind_map_comm }.

Lemma ebind_map_comm {S T₁ T₂ U : Set} (φ₁ : T₁ [→] U) (φ₂ : S [→] T₂) (ψ₁ : S [⇒] T₁) ψ₂ (E : ectx S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ E) = fmap φ₁ (bind ψ₁ E).
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_map_comm. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_map_comm. apply EQ.
    - apply IHE.
  + term_simpl. f_equal.
    - list_ind vs. apply bind_map_comm. apply EQ.
    - apply IHE.
    - list_ind ts. apply bind_map_comm. apply EQ.
Qed.

Instance BindMapComm_ectx : BindMapComm ectx := { bind_map_comm := @ebind_map_comm }.

Lemma tbind_pure {A : Set} (φ : A [⇒] A) (M : term A) (EQ : φ ≡ ı) :
  bind φ M = M
 with vbind_pure {A : Set} (φ : A [⇒] A) (V : value A) (EQ : φ ≡ ı) :
  bind φ V = V.
Proof.
(* tbind_pure *)
{
  induction M.
  + term_simpl. f_equal. apply vbind_pure. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    list_ind ts. apply tbind_pure. apply EQ.
}
(* vbind_pure *)
{
  induction V.
  + term_simpl. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal. apply tbind_pure. apply lift_id. apply EQ.
}
Qed.

Ltac ectx_ind E :=
  induction E as [| | | ? vs ]; term_simpl; f_equal; try assumption;
    induction vs; term_simpl; f_equal; assumption.

Lemma eplug_fmap {A B : Set} (φ : A [→] B) (E : ectx A) (M : term A) :
  fmap φ (eplug E M) = eplug (fmap φ E) (fmap φ M).
Proof.
  ectx_ind E.
Qed.

Lemma eplug_bind {A B : Set} (φ : A [⇒] B) (E : ectx A) M :
  eplug (bind φ E) (bind φ M) = bind φ (eplug E M).
Proof.
  ectx_ind E.
Qed.

Lemma eplug_plug_comp {A : Set} (E₂ E₁ : ectx A) (M : term A) :
  eplug E₂ (eplug E₁ M) = eplug (ecomp E₂ E₁) M.
Proof.
  ectx_ind E₂.
Qed.

Lemma tbind_bind_comp {A B C : Set} (φ₂ : B [⇒] C) (φ₁ : A [⇒] B) ψ (M : term A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ M) = bind ψ M
 with vbind_bind_comp {A B C : Set} (φ₂ : B [⇒] C) (φ₁ : A [⇒] B) ψ (V : value A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ V) = bind ψ V.
Proof.
(* tbind_bind_comp *)
{
  induction M as [ A V | A M₁ IHM₁ M₂ | A J].
  + term_simpl. f_equal. apply vbind_bind_comp. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal.
    list_ind ts. apply tbind_bind_comp. apply EQ.
}
(* vbind_bind_comp *)
{
  induction V.
  + term_simpl. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal. apply tbind_bind_comp. apply lift_comp. apply EQ.
}
Qed.

Instance Bind_term  : Bind term  := { bind_pure := @tbind_pure; bind_bind_comp := @tbind_bind_comp }.
Instance Bind_value : Bind value := { bind_pure := @vbind_pure; bind_bind_comp := @vbind_bind_comp }.

Lemma ebind_pure {A : Set} (φ : A [⇒] A) (E : ectx A) (EQ : φ ≡ ı) :
  bind φ E = E.
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_pure. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_pure. apply EQ.
    - apply IHE.
  + term_simpl. f_equal.
    - list_ind vs. apply bind_pure. apply EQ.
    - apply IHE.
    - list_ind ts. apply bind_pure. apply EQ.
Qed.

Lemma ebind_bind_comp {A B C : Set} (φ₂ : B [⇒] C) (φ₁ : A [⇒] B) ψ (E : ectx A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ E) = bind ψ E.
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_bind_comp. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_bind_comp. apply EQ.
    - apply IHE.
  + term_simpl. f_equal.
    - list_ind vs. apply bind_bind_comp. apply EQ.
    - apply IHE.
    - list_ind ts. apply bind_bind_comp. apply EQ.
Qed.

Instance Bind_ectx : Bind ectx := { bind_pure := @ebind_pure; bind_bind_comp := @ebind_bind_comp }.

Lemma ecomp_bind {S T : Set} (E1 : ectx S) (E2 : ectx S) (φ : S [⇒] T) :
  ecomp (bind φ E1) (bind φ E2) = bind φ (ecomp E1 E2).
Proof.
  ectx_ind E1.
Qed.

Lemma tbind_eq {A B : Set} (φ ψ : A [⇒] B) (M : term A) :
  φ ≡ ψ →
  bind φ M = bind ψ M
 with vbind_eq {A B : Set} (φ ψ : A [⇒] B) (V : value A) :
  φ ≡ ψ →
  bind φ V = bind ψ V.
Proof.
(* tbind_eq *)
{
  intro EQ.
  induction M.
  + term_simpl. f_equal. apply vbind_eq. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    list_ind ts. apply tbind_eq. apply EQ.
}
(* vbind_eq *)
{
  intro EQ.
  induction V.
  + term_simpl. apply EQ.
  + term_simpl. reflexivity.
  + term_simpl. f_equal. apply tbind_eq. apply lift_proper. apply EQ.
}
Qed.

Lemma ebind_eq {A B : Set} (φ ψ : A [⇒] B) (E : ectx A) :
  φ ≡ ψ →
  bind φ E = bind ψ E.
Proof.
  intro EQ.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_eq. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_eq. apply EQ.
    - apply IHE.
  + term_simpl. f_equal.
    - list_ind vs. apply vbind_eq. apply EQ.
    - apply IHE.
    - list_ind ts. apply tbind_eq. apply EQ.
Qed.
