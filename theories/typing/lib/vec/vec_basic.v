From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.vec Require Import vec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec_basic.
  Context `{!typeG Σ}.

  Global Instance vec_type_contractive 𝔄 : TypeContractive (vec_ty (𝔄:=𝔄)).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 19 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > ->*. do 16 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance vec_send {𝔄} (ty: type 𝔄) : Send ty → Send (vec_ty ty).
  Proof. move=> ?>/=. by do 19 f_equiv. Qed.

  Global Instance vec_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (vec_ty ty).
  Proof. move=> ?>/=. by do 16 f_equiv. Qed.

  Lemma vec_leak {𝔄} (ty: type 𝔄) Φ E L :
    leak E L ty Φ → leak E L (vec_ty ty) (lforall Φ).
  Proof.
    iIntros (????[|]???) "#LFT #PROPH #E L vec //=".
    iDestruct "vec" as (????[->->]) "[↦tys _]". iIntros "!>!>!>".
    rewrite trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
    iMod (leak_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). by iIntros "!> ?".
  Qed.

  Lemma vec_leak_just {𝔄} (ty: type 𝔄) E L :
    leak E L ty (const True) → leak E L (vec_ty ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma vec_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (vec_ty ty) (map f).
  Proof.
    move=> Rl. split; iIntros (???[|]) "*% LFT E L vec //=".
    - iDestruct "vec" as (????[->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
      rewrite trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first.
      { iExists _, _, _, _. iFrame "ex †". iSplit; [done|]. iNext.
        rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame. }
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map.
    - iDestruct "vec" as (????->) "[Bor tys]". iIntros "!>!>!>".
      iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%Eq &$& tys) !>". iSplit; [|iExists _, _, _, _; by iFrame].
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map.
  Qed.

  Lemma vec_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (vec_ty ty) (vec_ty ty') (map f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz &?&#?&#?)".
    have Eq: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    do 2 (iSplit; [done|]). iSplit; iIntros "!>" (?[|]) "* vec //=".
    - iDestruct "vec" as (????[->->]) "(↦tys & ex & †)". iExists _, _, _, _.
      rewrite !trans_big_sepL_mt_ty_own Eq EqSz. iSplit; [done|]. iFrame "ex †".
      iNext. iDestruct "↦tys" as (?) "[↦ ?]". iExists _. iFrame "↦".
      by iApply incl_big_sepL_ty_own.
    - iDestruct "vec" as (????->) "[↦ ?]". iExists _, _, _, _. rewrite Eq.
      iSplit; [done|]. iFrame "↦". iNext. by iApply incl_big_sepL_ty_shr.
  Qed.
  Lemma vec_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (vec_ty ty) (vec_ty ty') (map f) (map g).
  Proof. move=> [??]. split; by apply vec_subtype. Qed.

  Definition vec_new: val :=
    fn: [] :=
      let: "r" := new [ #3] in
      "r" <- new [ #0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
      return: ["r"].

  Lemma vec_new_type {𝔄} (ty: type 𝔄) :
    typed_val vec_new (fn(∅) → vec_ty ty) (λ post _, post []).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs".
    wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>" (r).
    rewrite !heap_mapsto_vec_cons shift_loc_assoc. iIntros "[† (↦₀ & ↦₁ & ↦₂ &_)]".
    wp_seq. iMod persistent_time_receipt_0 as "⧖". wp_bind (new _).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[†' _] ⧖". wp_bind (_ <- _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_write.
    iIntros "⧖". wp_seq. wp_op. wp_write. wp_op. wp_write. do 2 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full.
    iFrame "†". iNext. iExists [_; _; _].
    rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil.
    iFrame "↦₀ ↦₁ ↦₂". iExists l, 0, 0, [#]. iSplit; [done|]. iFrame "†'".
    iSplit; [by iNext|]. iExists []. by rewrite heap_mapsto_vec_nil.
  Qed.

  Definition vec_delete {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      delete [(!("v" +ₗ #1) + !("v" +ₗ #2)) * #ty.(ty_size); !"v"];;
      delete [ #3; "v"];;
      return: [new [ #0]].

  Lemma vec_delete_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_delete ty) (fn(∅; vec_ty ty) → ()) (λ post _, post ()).
  Proof.
    eapply type_fn; [apply _|]=> _ ??[v[]]. simpl_subst.
    iIntros (?[?[]]?) "_ TIME _ _ _ Na L C [v _] Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|d]) "[_ bvec]"=>//.
    case v as [[]|]=>//=. rewrite split_mt_vec.
    case d; [by iDestruct "bvec" as "[>[] _]"|]=> ?.
    iDestruct "bvec" as "[(%&%&%& big) †]".
    iMod (bi.later_exist_except_0 with "big") as (?) "(>-> & >↦₀ & >↦₁ & >↦₂ & big)".
    do 2 (wp_op; wp_read). do 2 wp_op. wp_read. rewrite trans_big_sepL_mt_ty_own.
    iDestruct "big" as "((%& ↦old & tys) & (%& %Eq & ↦ex) & †')".
    iDestruct (big_sepL_ty_own_length with "tys") as %Eq'.
    wp_bind (delete _). iApply (wp_delete (_++_) with "[↦old ↦ex †']").
    { rewrite app_length -Nat2Z.inj_add -Nat2Z.inj_mul Nat.mul_add_distr_r.
      by do 2 f_equal. }
    { rewrite heap_mapsto_vec_app /freeable_sz' app_length
        -Nat2Z.inj_add -Nat2Z.inj_mul Nat.mul_add_distr_r Eq Eq'. iFrame. }
    iIntros "!>_". wp_seq. wp_bind (delete _).
    iApply (wp_delete [_;_;_] with "[↦₀ ↦₁ ↦₂ †]"); [done| |].
    { rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil
        freeable_sz_full. iFrame. }
    iIntros "!>_". wp_seq. iMod persistent_time_receipt_0 as "⧖".
    wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    wp_seq. iIntros "⧖". wp_seq. wp_bind (new _). iApply wp_new; [done..|].
    iIntros "!>" (?) "[† ↦]". rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const ()] with "Na L [-Obs] Obs"). iSplit; [|done].
    rewrite tctx_hasty_val. iExists _. iFrame "⧖". iSplit; [|done]. iNext.
    iExists _. iFrame "↦". by rewrite unit_ty_own.
  Qed.
End vec_basic.

Global Hint Resolve vec_leak | 5 : lrust_typing.
Global Hint Resolve vec_leak_just vec_subtype vec_eqtype : lrust_typing.
