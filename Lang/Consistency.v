Require Import Utf8.
Require Import Syntax Semantics Confluence.

Lemma consistency {A : Set} (M N : term A) :
  M =ₜ N →
  ∃ L, M →*ₜ L ∧ N →*ₜ L.
Proof.
  intro Heq.
  induction Heq.
  + exists y.
    split.
    - constructor. apply H.
    - constructor 2.
  + exists x.
    split; constructor 2.
  + destruct IHHeq as [L [Hx Hy]].
    exists L.
    split.
    - apply Hy.
    - apply Hx.
  + destruct IHHeq1 as [L₁ [Hx₁ Hy₁]].
    destruct IHHeq2 as [L₂ [Hy₂ Hz₂]].
    pose proof (@treds_confluence A) as Hconf.
    specialize Hconf with y L₁ L₂.
    destruct Hconf as [L [HL₁ HL₂]]; [ assumption .. | ].
    exists L.
    split.
    - constructor 3 with (y := L₁); assumption.
    - constructor 3 with (y := L₂); assumption.
Qed.
