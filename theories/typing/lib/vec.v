From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec.
  Context `{!typeG Σ}.

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0%Z⌝.

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
    iMod (ty_own_proph_big_sepL_mt_v with "LFT In ↦tys κ") as "To↦tys"; [done|].
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
      let: "r" := new [ #3] in
      "r" <- #0;; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- new [ #0];;
      return: ["r"].

  Lemma vec_new_type {𝔄} (ty: type 𝔄) :
    typed_val vec_new (fn(∅) → vec_ty ty) (λ post _, post []).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs".
    wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>" (r).
    rewrite !heap_mapsto_vec_cons shift_loc_assoc. iIntros "[† (↦ & ↦' & ↦'' &_)]".
    wp_seq. iMod persistent_time_receipt_0 as "⧖". wp_bind (_ <- _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_write.
    iIntros "⧖". wp_seq. wp_op. wp_write. wp_op. wp_bind (new _).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[†' _] ?". wp_write.
    do 2 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full.
    iFrame "†". iNext. iExists [_; _; _].
    rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil.
    iFrame "↦ ↦' ↦''". iExists 0, 0, l, [#]. iSplit; [done|]. iFrame "†'".
    iSplit; [by iNext|]. iExists []. by rewrite heap_mapsto_vec_nil.
  Qed.

  Definition vec_delete {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      delete [(!"v" + !("v" +ₗ #1)) * #ty.(ty_size); !("v" +ₗ #2)];;
      delete [ #3; "v"];;
      return: [new [ #0]].

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
    wp_read. wp_op. wp_read. do 3 wp_op. wp_read. rewrite leak_big_sepL_mt_ty_own.
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
    iIntros "!>_". wp_seq. iMod persistent_time_receipt_0 as "⧖".
    wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    wp_seq. iIntros "⧖". wp_seq. wp_bind (new _). iApply wp_new; [done..|].
    iIntros "!>" (?) "[† ↦]". rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const ()] with "Na L [-Obs] Obs"). iSplit; [|done].
    rewrite tctx_hasty_val. iExists _. iFrame "⧖". iSplit; [|done]. iNext.
    iExists _. iFrame "↦". by rewrite unit_ty_own.
  Qed.

  Definition vec_index_shr {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "i"] :=
      letalloc: "r" <- !(!"v" +ₗ #2) +ₗ !"i" * #ty.(ty_size) in
      delete [ #1; "v"];; delete [ #1; "i"];;
      return: ["r"].

  (* The precondition requires that the index is within bounds of the list *)
  Lemma vec_index_shr_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_index_shr ty) (fn<α>(∅; &shr{α} (vec_ty ty), int) → &shr{α} ty)
      (λ post '-[al; z], ∃(i: nat) (a: 𝔄), z = i ∧ al !! i = Some a ∧ post a).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[v[i[]]]. simpl_subst.
    iIntros (?(?&?&[])?) "LFT TIME PROPH _ E Na L C (v & i & _) #Obs".
    rewrite !tctx_hasty_val.
    iDestruct "v" as ([|d]) "[⧖ v]"=>//. case v as [[|v|]|]=>//=.
    iDestruct "i" as ([|]) "[_ i]"=>//. case i as [[|i|]|]=>//=.
    wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>% [†r ↦r]".
    iDestruct "v" as "[(%vl & ↦v & vec) †v]". move: d=> [|d]//=.
    case vl as [|[[]|][]]=>//=. move: d=> [|d]//=.
    iDestruct "vec" as (??? aπl ->) "[Bor tys]".
    iDestruct "i" as "[(%& ↦i & (%&->&->)) †i]"=>/=.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor α") as (?) "[(↦ & ↦' & ↦'') Toα]"; [done|].
    rewrite !heap_mapsto_vec_singleton.
    wp_let. wp_read. wp_op. wp_read. wp_read. do 2 wp_op. wp_write.
    iMod ("Toα" with "[$↦ $↦' $↦'']") as "α". iMod ("ToL" with "α L") as "L".
    do 2 rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_bind (delete _). iApply (wp_delete with "[$↦v $†v]"); [done|].
    iIntros "!> _". wp_seq. wp_bind (delete _).
    iApply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "!> _". do 3 wp_seq.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &?&->& Lkup &_); [done|].
    move: Lkup. rewrite lapply_vapply -vlookup_lookup'. move=> [In _].
    set ifin := nat_to_fin In. have iEq: inat = ifin by rewrite fin_to_nat_to_fin.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[aπl !!! ifin] with "Na L [-] []").
    - iSplit; [|done]. rewrite tctx_hasty_val. iExists (S (S d)).
      iSplit. { iApply persistent_time_receipt_mono; [|done]. lia. }
      rewrite/= freeable_sz_full. iFrame "†r". iNext. iExists [_].
      rewrite heap_mapsto_vec_singleton. iFrame "↦r".
      rewrite/= -Nat2Z.inj_mul iEq. iApply (big_sepL_vlookup with "tys").
    - iApply proph_obs_impl; [|done]=>/= ?[?[?[/Nat2Z.inj <-[++]]]].
      by rewrite iEq -vlookup_lookup -vapply_lookup=> <-.
  Qed.

  Definition vec_push {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "x"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !"v'" in let: "ex" := !("v'" +ₗ #1) in "v'" <- "len";;
      "v'" <- "len" + #1;;
      withcont: "push":
        if: "ex" ≤ #0 then
          "v'" +ₗ #1 <- "len";; let: "l" := !("v'" +ₗ #2) in
          let: "l'" := new [(#2 * "len" + #1) * #ty.(ty_size)] in
          memcpy ["l'"; "len" * #ty.(ty_size); "l"];;
          delete ["len" * #ty.(ty_size); "l"];;
          "v'" +ₗ #2 <- "l'";; "push" []
        else
          "v'" +ₗ #1 <- "ex" - #1;; "push" []
      cont: "push" [] :=
        !("v'" +ₗ #2) +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x";;
        delete [ #ty.(ty_size); "x"];;
        let: "r" := new [ #0] in return: ["r"].

  Lemma vec_push_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_push ty) (fn<α>(∅; &uniq{α} (vec_ty ty), ty) → ())
      (λ post '-[(al, al'); a], al' = al ++ [a] → post ()).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[v[x[]]]. simpl_subst.
    iIntros (tid(vπ & aπ &[])?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(v & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "v" as ([|dv]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//.
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_persistent_time_receipt with "TIME ⧖x"); [done|].
    iApply (wp_delete _ with "[$↦ $†]"); [done|]. iIntros "!>_ ⧖x".
    iDestruct "uniq" as (du i [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ i=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ↦vec & ⧖u & Pc) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_vec_mt. case du as [|du]=>//.
    iDestruct "↦vec" as (len ex ? aπl Eq1) "(↦₀ & ↦₁ & ↦₂ & ↦tys & (%wl &%& ↦ex) & †)".
    wp_read. wp_let. wp_op. wp_read. wp_let. wp_write. wp_op. wp_write.
    have ->: (len + 1)%Z = S len by lia.
    iCombine "⧖u ⧖x" as "#⧖"=>/=. set d := du `max` dx.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    set push := (rec: "push" _ := _)%E.
    iAssert (
      (∃(ex: nat) (l: loc), v' ↦ #(S len) ∗ (v' +ₗ 1) ↦ #ex ∗ (v' +ₗ 2) ↦ #l ∗
        ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ du tid) ∗
        (l +ₗ[ty] len) ↦∗len (S ex * ty.(ty_size)) ∗
        freeable_sz' ((S len + ex) * ty.(ty_size)) l) -∗
      WP push [] {{ _, cont_postcondition }})%I
      with "[L ToL Na C Vo Pc ToBor x]" as "push".
    { iIntros "/=(%ex' &%& ↦₀ & ↦₁ & ↦₂ & ↦tys & (%vl & %Len & ↦ex) & †)".
      rewrite /push. wp_rec. wp_op. wp_read. do 2 wp_op. wp_bind (_ <-{_} !_)%E.
      move: {Len}(app_length_ex vl _ _ Len)=> [vl'[?[->[Len ?]]]].
      rewrite heap_mapsto_vec_app shift_loc_assoc_nat Len -Nat2Z.inj_mul.
      iDestruct "↦ex" as "[↦ ↦ex]". iDestruct "x" as "[(%& ↦x & ty) †x]".
      iDestruct (ty_size_eq with "ty") as %Sz. rewrite freeable_sz_full.
      iApply (wp_memcpy with "[$↦ $↦x]"); [lia..|]. iIntros "!> [↦ ↦x]". wp_seq.
      wp_bind (delete _). iApply (wp_delete with "[$↦x †x]"); [lia|by rewrite Sz|].
      iIntros "!>_". wp_seq. set vπ' := λ π, (lapply (vsnoc aπl aπ) π, π ξ).
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦ ty ↦ex † Pc]") as "[Bor α]".
      { iNext. iExists _, _. rewrite split_vec_mt. iFrame "⧖ Pc".
        iExists _, _, _, (vsnoc aπl _). iFrame "↦₀ ↦₁ ↦₂ †". iSplit; [done|].
        iSplitR "↦ex"; last first. { iExists _. rewrite/= plus_comm. by iFrame. }
        iNext. rewrite vsnoc_list big_sepL_app. iSplitL "↦tys".
        { iClear "#". iStopProof. do 6 f_equiv. apply ty_own_depth_mono. lia. }
        rewrite/= right_id. iExists _. rewrite vec_to_list_length Nat.add_0_r.
        iFrame "↦". iApply ty_own_depth_mono; [|done]. lia. }
      iMod ("ToL" with "α L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty)] -[vπ']
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= right_id (tctx_hasty_val #_). iExists _.
        iFrame "⧖ LftIn". iExists _, _.
        rewrite (proof_irrel (@prval_to_inh' (listₛ 𝔄) vπ')
          (@prval_to_inh' (listₛ 𝔄) vπ)). by iFrame.
      - iApply proph_obs_impl; [|done]=> π.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (vπ π)=>/= ??->-> Imp Eq.
        apply Imp. move: Eq. by rewrite vsnoc_list lapply_app. }
    rewrite /push. wp_let. wp_op. wp_case. case ex as [|ex']=>/=; last first.
    { do 2 wp_op. have ->: (S ex' - 1)%Z = ex' by lia. wp_write.
      iApply "push". iExists _, _. iFrame "↦tys ↦₀ ↦₁ ↦₂".
      iSplitL "↦ex". { iExists _. iFrame. iPureIntro. lia. }
      iClear "#". iStopProof. f_equiv. lia. }
    wp_op. wp_write. wp_op. wp_read. wp_let. do 3 wp_op. wp_bind (new _).
    iApply wp_new; [lia|done|]. iIntros "!>" (?) "[†' ↦']". wp_let. wp_op.
    have ->: ∀sz: nat, ((2 * len + 1) * sz)%Z = (len + S len) * sz by lia.
    rewrite split_big_sepL_mt_ty_own plus_0_r Nat2Z.id Nat.mul_add_distr_r
      repeat_app heap_mapsto_vec_app.
    iDestruct "↦tys" as (?) "[↦ tys]". iDestruct "↦'" as "[↦' ↦ex']".
    iDestruct (big_sepL_ty_own_length with "tys") as %Len. wp_bind (memcpy _).
    iApply (wp_memcpy with "[$↦' $↦]"); [rewrite repeat_length; lia|lia|].
    iIntros "!>[↦' ↦]". wp_seq. wp_op. rewrite -Nat2Z.inj_mul. wp_bind (delete _).
    iApply (wp_delete with "[$↦ †]"); [lia|by rewrite Len|]. iIntros "!>_".
    wp_seq. wp_op. wp_write. iApply "push". iExists _, _. iFrame "↦₀ ↦₁ ↦₂".
    iSplitL "↦' tys". { rewrite split_big_sepL_mt_ty_own. iExists _. iFrame. }
    iSplitR "†'".
    - iExists _. rewrite repeat_length. iFrame "↦ex'". by rewrite repeat_length.
    - by have <-: ∀sz, sz + (len + len) * sz = len * sz + (sz + len * sz) by lia.
  Qed.

  Local Lemma lapply_app_vinitlast {A B n} (fl: vec (B → A) (S n)) x al a :
    lapply fl x = al ++ [a] → al = lapply (vinit fl) x ∧ a = vlast fl x.
  Proof.
    inv_vec fl=>/= f fl. move: al f. elim: fl=>/= [|??? IH] al ? Eq;
    move/(f_equal length): (Eq); rewrite last_length; case al as [|a' al]=>// _.
    { by move: Eq=> [=?]. } { by move: Eq=>/= [=->/IH[<-<-]]. }
  Qed.

  Definition vec_pop {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !"v'" in let: "ex" := !("v'" +ₗ #1) in
      let: "len'" := "len" - #1 in
      "v'" <- "len'";; "v'" +ₗ #1 <- "ex" + #1;;
      letalloc: "r" <-{ty.(ty_size)} ! !("v'" +ₗ #2) +ₗ "len'" * #ty.(ty_size) in
      return: ["r"].

  (* The precondition requires that the input list has a positive length *)
  Lemma vec_pop_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_pop ty) (fn<α>(∅; &uniq{α} (vec_ty ty)) → ty)
      (λ post '-[(al, al')],
        ∃alᵢ (a: 𝔄), al = alᵢ ++ [a] ∧ (al' = alᵢ → post a)).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[v[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[v _] #Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete _ with "[$↦ $†]"); [done|]. iIntros "!>_".
    iDestruct "uniq" as (d i [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ i=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ↦vec & #⧖ & Pc) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_vec_mt. case d=>// ?.
    iDestruct "↦vec" as (? ex ? aπl Eq1) "(↦₀ & ↦₁ & ↦₂ & ↦tys & (%wl &%& ↦ex) & †)".
    wp_read. wp_let. wp_op. wp_read. wp_let. wp_op. wp_let. wp_write.
    do 2 wp_op. wp_write. wp_bind (new _). iApply wp_new; [lia|done|].
    iIntros "!>" (r) "[†r ↦r]". rewrite Nat2Z.id. wp_let. wp_op. wp_read. do 2 wp_op.
    iMod (proph_obs_sat with "PROPH Obs") as %[π' Obs]; [done|].
    move: Obs (equal_f Eq1 π')=>/=. case (vπ π')=>/= ??[?[?[-> _]]] /(f_equal length).
    rewrite last_length. case aπl as [|aπ len' aπl]=>// _.
    iDestruct (big_sepL_vinitlast with "↦tys") as "[↦tys (%vl & ↦last & ty)]".
    set aπl' := vinit' aπ aπl. set vπ' := λ π, (lapply aπl' π, π ξ).
    iDestruct (ty_size_eq with "ty") as %Eqvl. have ->: (S len' - 1)%Z = len' by lia.
    rewrite -Nat2Z.inj_mul. wp_bind (_ <-{_} !_)%E.
    iApply (wp_memcpy with "[$↦r $↦last]"); [by rewrite repeat_length|lia|].
    iIntros "!>[↦r ↦last]". wp_seq.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦last ↦ex † ⧖ Pc]") as "(Bor & α)".
    { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_vec_mt.
      have ->: ∀sz, sz + (len' + ex) * sz = (len' + S ex) * sz by lia.
      have ->: (ex + 1)%Z = S ex by lia. iExists _, _, _, _.
      iFrame "↦₀ ↦₁ ↦₂ ↦tys †". iSplit; [done|]. iExists (vl ++ wl).
      rewrite app_length heap_mapsto_vec_app shift_loc_assoc_nat plus_comm Eqvl.
      iSplit; [iPureIntro; lia|]. iFrame. }
    iMod ("ToL" with "α L") as "L".
    iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty); #r ◁ box ty]
      -[vπ'; _] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_) right_id. iSplitL "Vo Bor".
      + iExists _. iFrame "⧖ LftIn". iExists _, _.
        rewrite (proof_irrel (@prval_to_inh' (listₛ 𝔄) vπ')
          (@prval_to_inh' (listₛ 𝔄) vπ)). by iFrame.
      + iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r". iNext. iExists _.
        iFrame "↦r". iApply ty_own_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=> π. move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=.
      case (vπ π)=>/= ??->->[?[?[Eq +]]]+. apply (lapply_app_vinitlast (_:::_)) in Eq.
      move: Eq=> [->->] Imp ?. by apply Imp.
  Qed.
End vec.

Global Hint Resolve vec_leak | 5 : lrust_typing.
Global Hint Resolve vec_leak_just vec_subtype vec_eqtype : lrust_typing.
