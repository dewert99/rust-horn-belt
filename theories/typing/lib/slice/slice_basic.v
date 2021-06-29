From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util.
From lrust.typing.lib.slice Require Import uniq_slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section slice_basic.
  Context `{!typeG Σ}.

  Global Instance uniq_slice_type_contractive {𝔄} κ :
    TypeContractive (uniq_slice (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=> > EqSz EqLft */=. f_equiv.
      + apply equiv_dist. iDestruct EqLft as "#[??]".
        iSplit; iIntros "#In"; (iApply lft_incl_trans; [iApply "In"|done]).
      + rewrite EqSz /uniq_own. do 23 (f_contractive || f_equiv). by simpl in *.
    - move=> > EqSz */=. rewrite EqSz. do 17 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance uniq_slice_send {𝔄} κ (ty: type 𝔄) : Send ty → Send (uniq_slice κ ty).
  Proof. move=> >/=. rewrite /uniq_own. by do 24 f_equiv. Qed.

  Global Instance uniq_slice_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (uniq_slice κ ty).
  Proof. move=> >/=. by do 17 f_equiv. Qed.

  Lemma uniq_slice_resolve {𝔄} κ (ty: type 𝔄) E L :
    lctx_lft_alive E L κ →
    resolve E L (uniq_slice κ ty) (λ pl, lforall (λ '(a, a'), a' = a) pl).
  Proof.
    iIntros "%* LFT PROPH E L (In &%&%&%& %aπξil &(->&->&%)& uniqs)".
    iMod (resolve_big_sepL_uniq_own with "LFT PROPH In E L uniqs") as "Upd"; [done..|].
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >[? $]". iApply proph_obs_impl; [|done]=>/= ?.
    elim aπξil; [done|]. move=> [??]/=?? IH [??]. split; by [|apply IH].
  Qed.

  Lemma uniq_slice_real {𝔄 𝔅} κ (ty: type 𝔄) E L (f: _ → 𝔅) :
    lctx_lft_alive E L κ → real E L ty f →
    real (𝔅:=listₛ _) E L (uniq_slice κ ty) (map (f ∘ fst)).
  Proof.
    move=> ??. split.
    - iIntros "*% LFT E L ($&%&%&%& %aπξil &(->&->&%)& uniqs)".
      iMod (real_big_sepL_uniq_own with "LFT E L uniqs") as "Upd"; [done..|].
      iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
      iIntros "!> >([%bl %Eq] &$& uniqs) !>". iSplit.
      { iPureIntro. exists (bl: list _). fun_ext=> π. move: (equal_f Eq π)=>/= <-.
        clear. elim aπξil; [done|]. by move=> [??]/=??->. }
      iExists _, _, _, _. by iFrame.
    - iIntros (??? d) "*% LFT E L big". case d; [done|]=> ?.
      iDestruct "big" as (?? aπl ? [Eq ?]) "(Bor↦ & Borξl & tys)". iIntros "!>!>!>".
      iDestruct (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand _ _ (S _) with "Upd").
      iIntros ">([%bl %Eq'] &$& tys) !>". iSplit.
      { iPureIntro. exists (bl: list _). fun_ext=>/= π. rewrite -map_map.
        move: (equal_f Eq π) (equal_f Eq' π)=>/= -><-. by elim aπl=>//= ???->. }
      iExists _, _, _, _. by iFrame.
  Qed.

  Lemma uniq_slice_subtype {𝔄} κ κ' (ty ty': type 𝔄) E L :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    subtype E L (uniq_slice κ ty) (uniq_slice κ' ty') id.
  Proof.
    move=> In /eqtype_id_unfold Eqt ?. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iSplit; [done|]. iDestruct ("Eqt" with "E") as (EqSz) "[[??][#EqOwn #EqShr]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit; iModIntro=>/=.
    - iIntros "* (#?&%&%&%&%&(->&->&%)& uniqs)". iSplitR.
      { iApply lft_incl_trans; [|done]. by iApply lft_incl_trans. }
      iExists _, _, _, _. iSplit; [done|]. rewrite -EqSz.
      iApply (incl_big_sepL_uniq_own with "In EqOwn uniqs").
    - iIntros (?[|?]???); [by iIntros|]. iDestruct 1 as (?????) "(?&?& tys)".
      iExists _, _, _, _. do 3 (iSplit; [done|]). iNext.
      rewrite !(big_sepL_forall (λ _ (_: proph _), _)) -EqSz. iIntros (???).
      iApply "EqShr". by iApply "tys".
  Qed.
  Lemma uniq_slice_eqtype {𝔄} κ κ' (ty ty': type 𝔄) E L :
    lctx_lft_eq E L κ' κ → eqtype E L ty ty' id id →
    eqtype E L (uniq_slice κ ty) (uniq_slice κ' ty') id id.
  Proof. move=> [??][??]. split; (apply uniq_slice_subtype; by [|split]). Qed.

  Definition slice_len: val :=
    fn: ["bv"] :=
      let: "v" := !"bv" in delete [ #1; "bv"];;
      letalloc: "r" <- !("v" +ₗ #1) in
      return: ["r"].

  Lemma uniq_slice_len_type {𝔄} (ty: type 𝔄) :
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
End slice_basic.

Global Hint Resolve uniq_slice_resolve uniq_slice_real
  uniq_slice_subtype uniq_slice_eqtype : lrust_typing.
