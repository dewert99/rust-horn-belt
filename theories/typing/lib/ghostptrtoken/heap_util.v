From lrust.typing Require Import type.

Section defs.
Context `{!typeG Σ}.

Lemma no_duplicate_heap_mapsto l v1 v2:
(l ↦ v1) -∗ (l ↦ v2) -∗ False.
Proof.
    iIntros "↦0 ↦1".
    iCombine "↦0 ↦1" as "tofalse".
    iDestruct (heap_mapsto_agree with "tofalse") as %<-.
    rewrite -heap_mapsto_fractional - heap_mapsto_vec_singleton heap_mapsto_vec_combine; [|done].
    iDestruct (own_valid with "tofalse") as "%tofalse". iPureIntro.
    rewrite auth.auth_frag_valid in tofalse.
    rewrite big_opL_singleton in tofalse.
    rewrite gmap.singleton_valid 2! pair_valid frac.frac_valid in tofalse.
    destruct tofalse as [[tofalse _] _].
    by vm_compute.
Qed.

Lemma no_duplicate_heap_mapsto_own {𝔄} (ty: type 𝔄) l (aπ aπ': proph 𝔄) d d' tid tid':
(ty.(ty_size) > 0) → (l ↦∗: ty.(ty_own) aπ d tid) -∗ (l ↦∗: ty.(ty_own) aπ' d' tid') -∗ False.
Proof.
    iIntros (?) "↦0 ↦1".
    rewrite 2! heap_mapsto_ty_own.
    iDestruct "↦0" as "(%vl0 & ↦0 & _)".
    iDestruct "↦1" as "(%vl1 & ↦1 & _)".
    destruct vl0 as [|v0 vl0]; [done|]. 
    destruct vl1 as [|v1 vl1]; [done|].
    do 2 rewrite vec_to_list_cons heap_mapsto_vec_cons.
    iDestruct "↦0" as "(↦0 & _)".
    iDestruct "↦1" as "(↦1 & _)".
    iApply (no_duplicate_heap_mapsto with "↦0 ↦1").
Qed.

Lemma no_duplicate_freeable l n m: †{1}l…n -∗ †{1}l…m -∗ False.
Proof.
    iIntros "† †'". iCombine "† †'" as "tofalse".
    rewrite heap_freeable_eq /heap_freeable_def -own_op -auth.auth_frag_op gmap.singleton_op -pair_op frac.frac_op.
    iDestruct (own_valid with "tofalse") as "%tofalse". iPureIntro.
    rewrite auth.auth_frag_valid gmap.singleton_valid pair_valid frac.frac_valid in tofalse.
    destruct tofalse as [tofalse _]. by vm_compute in tofalse.
Qed.


Lemma plain_entails_r {P Q: iProp Σ} `{Plain _ Q} :
((P -∗ Q) → (P -∗ (P ∗ Q))).
Proof.
    rewrite -(plain_plainly Q).
    apply plainly_entails_r.
Qed.

End defs.
