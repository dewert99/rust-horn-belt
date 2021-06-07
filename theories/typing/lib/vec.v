From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec.
  Context `{!typeG Σ}.

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0⌝.

  Lemma split_vec_mt {𝔄} l' q d alπ Φ :
    (l' ↦∗{q}: (λ vl, [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #len; #ex; #l] ∧ alπ = lapply aπl⌝ ∗ Φ d' len ex l aπl))%I ⊣⊢
    [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗
      l' ↦{q} #len ∗ (l' +ₗ 1) ↦{q} #ex ∗ (l' +ₗ 2) ↦{q} #l ∗ Φ d' len ex l aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (????[->->]) "Φ".
      iExists _, _, _, _. iSplit; [done|]. iFrame "Φ".
      rewrite !heap_mapsto_vec_cons shift_loc_assoc. iDestruct "↦" as "($&$&$&_)".
    - iIntros "big". case d=>// ?. iDestruct "big" as (????->) "(↦ & ↦' & ↦'' & ?)".
      iExists [_;_;_]. rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil.
      iFrame "↦ ↦' ↦''". iExists _, _, _, _. by iFrame.
  Qed.

  Program Definition vec_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #len; #ex; #l] ∧ alπ = lapply aπl⌝ ∗
        ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
        (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
        freeable_sz' ((len + ex) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗
        &frac{κ} (λ q, l' ↦{q} #len ∗ (l' +ₗ 1) ↦{q} #ex ∗ (l' +ₗ 2) ↦{q} #l) ∗
        ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros (???[]??) "vec //". by iDestruct "vec" as (????[-> _]) "?".
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 17 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 14 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&?& All)".
    iExists _, _, _, _. iSplit; [done|]. iSplit; [by iApply frac_bor_shorten|].
    rewrite !big_sepL_forall. iIntros "!> **".
    iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (???? d ? l' tid q ?) "#LFT In Bor κ". rewrite split_vec_mt. case d.
    { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    move=> ?. do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_exists_tok with "LFT Bor κ") as (aπl) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    do 2 rewrite assoc. iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    rewrite -assoc. iMod (bor_fracture (λ q', _ ↦{q'} _ ∗ _ ↦{q'} _ ∗ _ ↦{q'} _)%I
      with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|].
    iIntros "/=!>!>!>". iMod "Borκ" as "[Bor κ]".
    iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] tid ?? q ?) "LFT In vec κ //=".
    iDestruct "vec" as (??? aπl[->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_mt_big_sepL_v with "LFT In ↦tys κ") as "To↦tys"; [done|].
    iApply (step_fupdN_wand with "To↦tys"). iIntros "!> >(%&%&%& ξl & To↦tys) !>".
    iExists _, _. iSplit.
    { iPureIntro. rewrite lapply_vapply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("To↦tys" with "ξl") as "[?$]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] κ ? l' κ' q ?) "LFT In In' vec κ' //=".
    iDestruct "vec" as (?? l aπl ->) "[? tys]". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepL_v with "LFT In In' tys κ'") as "Totys"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Totys").
    iIntros ">(%&%&%& ξl & Totys)!>". iExists _, _. iSplit.
    { iPureIntro. rewrite lapply_vapply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[?$]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.

  Global Instance vec_ty_ne {𝔄} : NonExpansive (@vec_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance vec_type_contractive 𝔄 : TypeContractive (@vec_ty 𝔄).
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
    iIntros (Lk ? q ?[|]???) "#LFT #PROPH #E L vec //=".
    iDestruct "vec" as (?? l aπl[->->]) "[↦tys _]". iIntros "!>!>!>".
    iInduction aπl as [|] "IH" forall (q l)=>/=.
    { iApply step_fupdN_full_intro. iFrame. by iApply proph_obs_true. }
    iDestruct "↦tys" as "[(%&_& ty) ↦tys]". iDestruct "L" as "[L L₊]".
    iMod (Lk with "LFT PROPH E L ty") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ ↦tys") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "!>[>[#? $] >[#? $]]". by iApply proph_obs_and.
  Qed.

  Lemma vec_leak_just {𝔄} (ty: type 𝔄) E L :
    leak E L ty (const True) → leak E L (vec_ty ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma vec_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (vec_ty ty) (vec_ty ty') (map f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz & #? & #InOwn & #InShr)".
    have Eq: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    do 2 (iSplit; [done|]). iSplit; iIntros "!>" (?[|]) "* vec //=".
    - iDestruct "vec" as (?? l aπl [->->]) "(↦tys & ex & †)".
      iExists _, _, _, _. rewrite Eq EqSz. iSplit; [done|]. iFrame "ex †".
      iNext. iInduction aπl as [|] "IH" forall (l)=>/=; [done|].
      iDestruct "↦tys" as "[(%& ↦ & ty) ↦tys]". setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "↦tys") as "$". iExists _. iFrame "↦". by iApply "InOwn".
    - iDestruct "vec" as (?? l' ?->) "(↦ & tys)". iExists _, _, _, _.
      rewrite Eq EqSz. iSplit; [done|]. iFrame "↦". iNext.
      iInduction aπl as [|] "IH" forall (l')=>/=; [done|].
      iDestruct "tys" as "[ty tys]". setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "tys") as "$". by iApply "InShr".
  Qed.
  Lemma vec_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (vec_ty ty) (vec_ty ty') (map f) (map g).
  Proof. move=> [??]. split; by apply vec_subtype. Qed.

  Definition vec_new: val :=
    fn: [] :=
      let: "r" := new [ #3] in let: "l" := new [ #0] in
      "r" <- #0;; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- "l";;
      return: ["r"].

  Lemma vec_new_type {𝔄} (ty: type 𝔄) :
    typed_val vec_new (fn(∅) → vec_ty ty) (λ post _, post []).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs".
    wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>" (r).
    rewrite !heap_mapsto_vec_cons shift_loc_assoc. iIntros "[† (↦ & ↦' & ↦'' &_)]".
    wp_seq. wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>" (l) "[†' _]".
    wp_seq. iMod persistent_time_receipt_0 as "⧖". wp_bind (_ <- _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_write.
    iIntros "⧖". wp_seq. do 2 (wp_op; wp_write). wp_bind Skip.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_seq.
    iIntros "⧖". wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full.
    iFrame "†". iNext. iExists [_; _; _].
    rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil.
    iFrame "↦ ↦' ↦''". iExists 0, 0, l, [#]. iSplit; [done|]. iFrame "†'".
    iSplit; [by iNext|]. iExists []. by rewrite heap_mapsto_vec_nil.
  Qed.

  Definition vec_delete {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      let: "len" := !"v" in let: "ex" := !("v" +ₗ #1) in let: "l" := !("v" +ₗ #2) in
      let: "sz" := "len" + "ex" in
      delete [ "sz" * #ty.(ty_size); "l"];; delete [ #3; "v"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma vec_delete_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_delete ty) (fn(∅; vec_ty ty) → ()) (λ post _, post ()).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[v[]]. simpl_subst.
    iIntros (?[?[]]?) "_ TIME _ _ _ Na L C [v _] Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|d]) "[_ bvec]"=>//.
    case v as [[]|]=>//=. rewrite split_vec_mt.
    case d; [by iDestruct "bvec" as "[>[] _]"|]=> ?.
    iDestruct "bvec" as "[(%&%&%& big) †]".
    iMod (bi.later_exist_except_0 with "big") as (?) "(>-> & >↦ & >↦' & >↦'' & big)".
    wp_read. wp_seq. do 2 (wp_op; wp_read; wp_seq). wp_op. wp_let. wp_op.
    rewrite leak_mt_big_sepL.
    iDestruct "big" as "((%& %Eq & ↦len) & (%& %Eq' & ↦ex) & †')".
    wp_bind (delete _). iApply (wp_delete _ _ _ (_ ++ _) with "[↦len ↦ex †']").
    { rewrite app_length -Nat2Z.inj_add -Nat2Z.inj_mul Nat.mul_add_distr_r.
      by do 2 f_equal. }
    { rewrite heap_mapsto_vec_app /freeable_sz' app_length
        -Nat2Z.inj_add -Nat2Z.inj_mul Nat.mul_add_distr_r Eq Eq'. iFrame. }
    iIntros "!>_". wp_seq. wp_bind (delete _).
    iApply (wp_delete _ _ _ [_;_;_] with "[↦ ↦' ↦'' †]"); [done| |].
    { rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil
        freeable_sz_full. iFrame. }
    iIntros "!>_". wp_seq. wp_bind (new _). iApply wp_new; [done..|].
    iIntros "!>" (?) "[† ↦]". wp_seq. iMod persistent_time_receipt_0 as "⧖".
    wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    wp_seq. iIntros "⧖". wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const ()] with "Na L [-Obs] Obs"). iSplit; [|done].
    rewrite tctx_hasty_val. iExists _. iFrame "⧖". iSplit; [|done]. iNext.
    iExists _. iFrame "↦". by rewrite unit_ty_own.
  Qed.
End vec.

Global Hint Resolve vec_leak | 5 : lrust_typing.
Global Hint Resolve vec_leak_just vec_subtype vec_eqtype : lrust_typing.
