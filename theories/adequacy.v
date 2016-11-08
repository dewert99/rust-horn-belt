From iris.program_logic Require Export hoare adequacy.
From lrust Require Export heap.
From iris.algebra Require Import auth.
From lrust Require Import proofmode notation.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> irisPreG lrust_lang Σ;
  heap_preG_heap :> inG Σ (authR heapUR);
  heap_preG_heap_freeable :> inG Σ (authR heap_freeableUR)
}.

Definition heapΣ : gFunctors :=
  #[irisΣ state;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR))].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [? [?%subG_inG ?%subG_inG]%subG_inv]%subG_inv. split; apply _. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, {{ heap_ctx }} e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ). iIntros (?) "Hσ".
  iMod (own_alloc (● to_heap σ)) as (vγ) "Hvγ".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ"; first done.
  set (Hheap := HeapG _ _ _ _ vγ fγ).
  iMod (inv_alloc heapN _ heap_inv with "[-]"); [iNext; iExists σ, ∅; by iFrame|].
  iApply (Hwp _). by rewrite /heap_ctx.
Qed.