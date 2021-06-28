From lrust.typing Require Export type.
From lrust.typing Require Import array_util uniq_util typing.
From lrust.typing.lib.slice Require Import uniq_slice.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section slice_len.
  Context `{!typeG Σ}.

  Definition slice_len: val :=
    fn: ["bv"] :=
      let: "v" := !"bv" in delete [ #1; "bv"];;
      letalloc: "r" <- !("v" +ₗ #1) in
      return: ["r"].

  Lemma slice_len_type {𝔄} (ty: type 𝔄) :
    typed_val slice_len (fn<(α, β)>(∅; &shr{β} (uniq_slice α ty)) → int)
      (λ post '-[v], post (length v)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.

    iIntros (?[?[]]?) "LFT _ _ _ E Na L C /=[bv _] #Obs".
    rewrite tctx_hasty_val. iDestruct "bv" as ([|d]) "[⧖ box]"=>//.
    case b as [[]|]=>//=. rewrite split_mt_ptr.
    case d as [|d]; first by iDestruct "box" as "[>[] _]".
    iDestruct "box" as "[(%& >↦bv  & slice) †bv]". wp_read. wp_let.
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_apply (wp_delete with "[$↦bv $†bv]"); [done|]. iIntros "_". wp_seq.
    case d as [|]=>//. iDestruct "slice" as (???? [Hsl ?]) "[Bor _]".
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor β") as (?) "[(↦₀ & ↦₁ & ↦₂) Toα]"; [done|].
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let. wp_op. wp_read.
    rewrite heap_mapsto_vec_singleton. wp_write. do 2 wp_seq.
    iMod ("Toα" with "[$↦₀ $↦₁ $↦₂]") as "β". iMod ("ToL" with "β L") as "L".
    rewrite cctx_interp_singleton. iApply ("C" $! [# #_] -[_] with "Na L [-] []").
    - rewrite/= right_id (tctx_hasty_val #_) -freeable_sz_full. iExists _.
      iFrame "⧖ †r". iNext. iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "↦r". by iExists _.
    - iApply proph_obs_eq; [|done]=>/= π. f_equal.
      rewrite -(map_length fst). move: (equal_f Hsl π) => /= ->.
      by rewrite -vec_to_list_apply vec_to_list_length.
  Qed.
End slice_len.
