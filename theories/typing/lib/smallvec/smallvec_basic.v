From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.smallvec Require Import smallvec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_basic.
  Context `{!typeG Σ}.

  Global Instance smallvec_type_ne 𝔄 n : TypeNonExpansive (smallvec (𝔄:=𝔄) n).
  Proof.
    split.
    - by apply type_lft_morphism_id_like.
    - by move=> ??/=->.
    - move=>/= > ->*. by do 21 f_equiv; [f_equiv|].
    - move=>/= > ->*. by do 16 f_equiv.
  Qed.

  Global Instance smallvec_send {𝔄} n (ty: type 𝔄) : Send ty → Send (smallvec n ty).
  Proof. move=> ?>/=. by do 21 f_equiv; [f_equiv|]. Qed.

  Global Instance smallvec_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (smallvec n ty).
  Proof. move=> ?>/=. by do 16 f_equiv. Qed.

  Lemma smallvec_resolve {𝔄} n (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (smallvec n ty) (lforall Φ).
  Proof.
    iIntros "%* LFT PROPH E L". iDestruct 1 as (b ?????(->&?&->)) "big". case b=>/=.
    - iDestruct "big" as (???) "tys".
      by iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys").
    - iDestruct "big" as "[↦tys _]". rewrite trans_big_sepL_mt_ty_own.
      iDestruct "↦tys" as (?) "[↦ tys]".
      iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). by iIntros "!> ?".
  Qed.

  Lemma smallvec_resolve_just {𝔄} n (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (smallvec n ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma smallvec_real {𝔄 𝔅} n (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (smallvec n ty) (map f).
  Proof.
    move=> Rl. split; iIntros "*% LFT E L svec".
    - iDestruct "svec" as (b ?????(->&?&->)) "big". case b=>/=.
      + iDestruct "big" as (???) "tys".
        iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
        iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq&$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists true, _, _, _, _, _. iSplit; [done|]. iExists _, _. by iFrame.
      + iDestruct "big" as "[↦tys ex†]".
        rewrite trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
        iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
        iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists false, _, _, _, _, _. iFrame "ex†". iSplit; [done|].
        rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame.
    - iDestruct "svec" as (b ????->) "[Bor tys]". case b=>/=.
      + iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
        iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
        iIntros ">(%Eq &$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists true, _, _, _, _. by iFrame.
      + iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
        iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
        iIntros ">(%Eq &$& tys) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists false, _, _, _, _. by iFrame.
  Qed.

  Lemma smallvec_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) n ty ty' E L :
    subtype E L ty ty' f → subtype E L (smallvec n ty) (smallvec n ty') (map f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz &?&#?&#?)".
    have Eq: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    iSplit. { iPureIntro. rewrite/=. lia. } iSplit; [done|].
    iSplit; iModIntro.
    - iDestruct 1 as (b ?????(->&?&->)) "big". iExists b, _, _, _, _, _. case b=>/=.
      + iDestruct "big" as (???) "?". rewrite Eq -EqSz. iSplit; [done|].
        iExists _, _. iSplit; [done|]. by iApply incl_big_sepL_ty_own.
      + iDestruct "big" as "[↦tys ex†]". rewrite !trans_big_sepL_mt_ty_own Eq -EqSz.
        iSplit; [done|]. iFrame "ex†". iDestruct "↦tys" as (?) "[↦ ?]".
        iExists _. iFrame "↦". by iApply incl_big_sepL_ty_own.
    - iDestruct 1 as (b ????->) "[↦ big]". iExists b, _, _, _, _. rewrite Eq.
      iSplit; [done|]. iFrame "↦". case b=>/=; by iApply incl_big_sepL_ty_shr.
  Qed.
  Lemma smallvec_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g n ty ty' E L :
    eqtype E L ty ty' f g →
    eqtype E L (smallvec n ty) (smallvec n ty') (map f) (map g).
  Proof. move=> [??]. split; by apply smallvec_subtype. Qed.

  Definition smallvec_new {𝔄} n (ty: type 𝔄): val :=
    fn: [] :=
      let: "r" := new [ #((4 + n * ty.(ty_size))%nat)] in
      "r" <- #true;; "r" +ₗ #1 <- #any_loc;;
      "r" +ₗ #2 <- #0;; "r" +ₗ #3 <- #0;;
      return: ["r"].

  Lemma smallvec_new_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_new n ty) (fn(∅) → smallvec n ty) (λ post _, post []).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs".
    iMod persistent_time_receipt_0 as "⧖". wp_bind (new _).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (r).
    rewrite !Nat2Z.id/= !heap_mapsto_vec_cons !shift_loc_assoc.
    iIntros "[† (↦₀ & ↦₁ & ↦₂ & ↦₃ & ↦ex)] ⧖". wp_seq. wp_write.
    do 3 (wp_op; wp_write). do 2 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full.
    iFrame "†". iNext. iExists (_::_::_::_::_).
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc. iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦ex".
    iExists true, _, 0, 0, (repeat _ _), [#]. rewrite/= repeat_length.
    iSplit; [done|]. by iExists [#], _=>/=.
  Qed.

  Definition smallvec_delete {𝔄} n (ty: type 𝔄) : val :=
    fn: ["v"] :=
      if: !"v" then
        delete [ #((4 + n * ty.(ty_size))%nat); "v"];;
        return: [new [ #0]]
      else
        delete [(!("v" +ₗ #2) + !("v" +ₗ #3)) * #ty.(ty_size); !("v" +ₗ #1)];;
        delete [ #((4 + n * ty.(ty_size))%nat); "v"];;
        return: [new [ #0]].

  Lemma smallvec_delete_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_delete n ty) (fn(∅; smallvec n ty) → ()) (λ post _, post ()).
  Proof.
    eapply type_fn; [apply _|]=> _ ??[v[]]. simpl_subst.
    iIntros (?[?[]]?) "_ TIME _ _ _ Na L C [v _] Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|?]) "[_ bsvec]"=>//.
    case v as [[]|]=>//=. rewrite split_mt_smallvec.
    iDestruct "bsvec" as "[(%b &%&%&%& big) †]".
    iMod (bi.later_exist_except_0 with "big") as (?) "(>-> & >↦ & big)".
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)". case b=>/=; wp_read; wp_case.
    - rewrite trans_big_sepL_mt_ty_own.
      iDestruct "big" as "[(%wll & ↦ar & tys) (%wl' & -> & ↦ex)]".
      iDestruct (big_sepL_ty_own_length with "tys") as %<-. rewrite -app_length.
      wp_bind (delete _).
      iApply (wp_delete (_::_::_::_::_) with "[↦₀ ↦₁ ↦₂ ↦₃ ↦ar ↦ex †]"); [done|..].
      { rewrite !heap_mapsto_vec_cons heap_mapsto_vec_app !shift_loc_assoc
          freeable_sz_full. iFrame. }
      iIntros "!>_". wp_seq. iMod persistent_time_receipt_0 as "⧖".
      wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
      wp_seq. iIntros "⧖". wp_seq. wp_bind (new _). iApply wp_new; [done..|].
      iIntros "!>" (?) "[† ↦]". rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[const ()] with "Na L [-Obs] Obs"). iSplit; [|done].
      rewrite tctx_hasty_val. iExists _. iFrame "⧖". iSplit; [|done]. iNext.
      iExists _. iFrame "↦". by rewrite unit_ty_own.
    - rewrite trans_big_sepL_mt_ty_own.
      iDestruct "big" as "((%&<-& ↦tl) & (%& ↦ar & tys) & (%& %Eq & ↦ex) & †')".
      iDestruct (big_sepL_ty_own_length with "tys") as %Eq'.
      do 2 (wp_op; wp_read). do 3 wp_op. wp_read.
      rewrite -Nat2Z.inj_add -Nat2Z.inj_mul !Nat.mul_add_distr_r -Eq -Eq' -app_length.
      wp_bind (delete _). iApply (wp_delete (_++_) with "[↦ar ↦ex †']"); [done|..].
      { rewrite heap_mapsto_vec_app. iFrame. }
      iIntros "!>_". wp_seq. wp_bind (delete _).
      iApply (wp_delete (_::_::_::_::_) with "[↦₀ ↦₁ ↦₂ ↦₃ ↦tl †]"); [done| |].
      { rewrite !heap_mapsto_vec_cons !shift_loc_assoc freeable_sz_full. iFrame. }
      iIntros "!>_". wp_seq. iMod persistent_time_receipt_0 as "⧖".
      wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
      wp_seq. iIntros "⧖". wp_seq. wp_bind (new _). iApply wp_new; [done..|].
      iIntros "!>" (?) "[† ↦]". rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[const ()] with "Na L [-Obs] Obs"). iSplit; [|done].
      rewrite tctx_hasty_val. iExists _. iFrame "⧖". iSplit; [|done]. iNext.
      iExists _. iFrame "↦". by rewrite unit_ty_own.
  Qed.

  Definition smallvec_len: val :=
    fn: ["bv"] :=
      let: "v" := !"bv" in delete [ #1; "bv"];;
      letalloc: "r" <- !("v" +ₗ #2) in
      return: ["r"].

  Lemma smallvec_len_type {𝔄} n (ty: type 𝔄) :
    typed_val smallvec_len (fn<α>(∅; &shr{α} (smallvec n ty)) → int)
      (λ post '-[v], post (length v)).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[bv[]]. simpl_subst.
    iIntros (?[?[]]?) "LFT _ _ _ E Na L C /=[bv _] #Obs".
    rewrite tctx_hasty_val. iDestruct "bv" as ([|d]) "[⧖ box]"=>//.
    case bv as [[]|]=>//=. rewrite split_mt_ptr.
    case d as [|d]; first by iDestruct "box" as "[>[] _]".
    iDestruct "box" as "[(%& >↦bv & svec) †bv]". wp_read.
    iDestruct "svec" as (?????->) "[Bor _]". wp_let.
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_apply (wp_delete with "[$↦bv $†bv]"); [done|]. iIntros "_". wp_seq.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor α") as (?) "[↦ Toα]"; [done|].
    rewrite !heap_mapsto_vec_cons !heap_mapsto_vec_nil shift_loc_assoc.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)".
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let. wp_op. wp_read.
    rewrite heap_mapsto_vec_singleton. wp_write. do 2 wp_seq.
    iMod ("Toα" with "[$↦₀ $↦₁ $↦₂ $↦₃]") as "α". iMod ("ToL" with "α L") as "L".
    rewrite cctx_interp_singleton. iApply ("C" $! [# #_] -[_] with "Na L [-] []").
    - rewrite/= right_id (tctx_hasty_val #_) -freeable_sz_full. iExists _.
      iFrame "⧖ †r". iNext. iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "↦r". by iExists _.
    - iApply proph_obs_eq; [|done]=>/= ?. f_equal.
      by rewrite -vec_to_list_apply vec_to_list_length.
  Qed.
End smallvec_basic.

Global Hint Resolve smallvec_resolve | 5 : lrust_typing.
Global Hint Resolve smallvec_resolve_just smallvec_subtype smallvec_eqtype : lrust_typing.
