From iris.proofmode Require Import tactics.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section cell.
  Context `{!typeG Σ}.

  Lemma split_mt_cell {A} l q (Φπ: proph A) (Ψ: A → _) :
    (l ↦∗{q}: λ vl, ∃Φ, ⌜Φπ = const Φ⌝ ∗ Ψ Φ vl)%I ⊣⊢
    ∃Φ, ⌜Φπ = const Φ⌝ ∗ l ↦∗{q}: Ψ Φ.
  Proof.
    iSplit.
    - iIntros "(%&?&%&%&?)". iExists _. iSplit; [done|]. iExists _. iFrame.
    - iIntros "(%&%&%& ↦ &?)". iExists _. iFrame "↦". iExists _. by iFrame.
  Qed.

  Program Definition cell {𝔄} (ty: type 𝔄) : type (𝔄 → Propₛ) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own Φπ _ tid vl := ∃Φ, ⌜Φπ = const Φ⌝ ∗
      ∃(vπ: proph 𝔄) d, ⟨π, Φ (vπ π)⟩ ∗ ⧖d ∗ ty.(ty_own) vπ d tid vl;
    ty_shr Φπ _ κ tid l := ∃Φ, ⌜Φπ = const Φ⌝ ∗
      &na{κ, tid, shrN.@l}
        (∃(vπ: proph 𝔄) d, ⟨π, Φ (vπ π)⟩ ∗ ⧖d ∗ l ↦∗: ty.(ty_own) vπ d tid)
  |}%I.
  Next Obligation. iIntros "* (%&%&%&%&_&_& ty)". by rewrite ty_size_eq. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "* In (%&%&?)". iExists _. iSplit; [done|].
    by iApply (na_bor_shorten with "In").
  Qed.
  Next Obligation.
    iIntros "* % #LFT In Bor κ !>". iApply step_fupdN_full_intro.
    rewrite split_mt_cell. iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>% & Bor & $)"; [done|].
    iExists _. iSplitR; [done|]. iApply bor_na; [done|].
    iApply (bor_iff with "[] Bor"). iIntros "!>!>". iSplit.
    - iIntros "(%&?&%&%&?&?&?)". iExists _, _. iFrame. iExists _. iFrame.
    - iIntros "(%&%&?&?&%&?&?)". iExists _. iFrame. iExists _, _. iFrame.
  Qed.
  Next Obligation.
    iIntros "* _ _ _ (%&->&?) $ !>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _. by iSplit.
  Qed.
  Next Obligation.
    iIntros "* _ _ _ _ (%&->&?) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _. by iSplit.
  Qed.

  Global Instance cell_ne {𝔄} : NonExpansive (@cell 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance cell_type_ne {𝔄} : TypeNonExpansive (@cell 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=> */=. by do 9 f_equiv.
    - move=> */=. do 13 (f_contractive || f_equiv). by simpl in *.
  Qed.

  (* In order to prove [cell_leak] with a non-trivial postcondition,
    we need to modify the model of [leak] to use [⧖d] inside [ty_own] *)
  Lemma cell_leak_just {𝔄} (ty: type 𝔄) E L :
    leak E L ty (const True) → leak E L (cell ty) (const True).
  Proof. move=> _. apply leak_just. Qed.

  Global Instance cell_copy {𝔄} (ty: type 𝔄) : Copy ty → Copy (cell ty).
  Proof.
    move=> ?. split; [apply _|]=>/= *. iIntros "#LFT (%&%& Bor) Na κ".
    iExists 1%Qp.
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    case (ty_size ty) as [|?] eqn:EqSz; simpl in *.
    { iMod (na_bor_acc with "LFT Bor κ Na") as "(Big & Na & ToNa)"; [solve_ndisj..|].
      iMod (bi.later_exist_except_0 with "Big") as (??) "(>#?&>#?& %vl & >↦ & #ty)".
      iDestruct (ty_size_eq with "ty") as "#>%EqLen". move: EqLen.
      rewrite EqSz. case vl; [|done]=> _. rewrite difference_empty_L.
      iMod ("ToNa" with "[↦] Na") as "[$$]".
      { iNext. iExists _, _. do 2 (iSplit; [done|]). iExists _. by iFrame. }
      iModIntro. iExists []. rewrite heap_mapsto_vec_nil. iSplit; [done|].
      iSplit; [|by iIntros]. iNext. iExists _. iSplit; [done|]. iExists _, _.
      by iSplit; [|iSplit]. }
    (* Now we are in the non-0 case. *)
    iMod (na_bor_acc with "LFT Bor κ Na") as "(Big & Na & ToNa)"; [solve_ndisj..|].
    iMod (bi.later_exist_except_0 with "Big") as (??) "(>#?&>#?&%& >↦ & #ty)".
    iExists _. iDestruct (na_own_acc with "Na") as "[$ ToNa']"; [set_solver+|].
    iIntros "!>{$↦}". iSplitR.
    { iNext. iExists _. iSplit; [done|]. iExists _, _. by iSplit; [|iSplit]. }
    iIntros "Na ↦". iDestruct ("ToNa'" with "Na") as "Na".
    iMod ("ToNa" with "[↦] Na") as "[$$]"; [|done]. iNext. iExists _, _.
    do 2 (iSplit; [done|]). iExists _. by iFrame.
  Qed.

  Global Instance cell_send {𝔄} (ty: type 𝔄) : Send ty → Send (cell ty).
  Proof. move=> ?>/=. by do 9 f_equiv. Qed.

  Lemma cell_subtype {𝔄 𝔅} E L ty ty' f g `{!@Iso 𝔄 𝔅 f g} :
    eqtype E L ty ty' f g → subtype E L (cell ty) (cell ty') (.∘ g).
  Proof.
    move=> /eqtype_unfold Eq. iIntros (?) "L".
    iDestruct (Eq with "L") as "#Eq". iIntros "!> #E".
    iDestruct ("Eq" with "E") as "(%&[_?]& #EqOwn & #EqShr)".
    do 2 (iSplit; [done|]). iSplit; iModIntro.
    - iIntros "* (%&->& %vπ &%&?&?& ty)". iExists _. iSplit; [done|].
      iExists (f ∘ vπ), _=>/=. iSplit.
      { iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'. }
      iSplit; [done|]. by iApply "EqOwn".
    - iIntros "* (%&->& Bor)". iExists _. iSplit; [done|]=>/=.
      iApply (na_bor_iff with "[] Bor"). iIntros "!>!>".
      iSplit; iIntros "(%vπ &%&?& ⧖ &%& ↦ &?)".
      + iExists (f ∘ vπ), _. iFrame "⧖". iSplit.
        { iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'. }
        iExists _. iFrame "↦". by iApply "EqOwn".
      + iExists (g ∘ vπ), _. iFrame "⧖". iSplit; [done|]. iExists _.
        iFrame "↦". iApply "EqOwn". by rewrite compose_assoc semi_iso.
  Qed.
  Lemma cell_eqtype {𝔄 𝔅} E L ty ty' f g `{!@Iso 𝔄 𝔅 f g} :
    eqtype E L ty ty' f g → eqtype E L (cell ty) (cell ty') (.∘ g) (.∘ f).
  Proof.
    move=> [??]. split; (eapply cell_subtype; [|by split]; split; apply _).
  Qed.

(*
  (** The next couple functions essentially show owned-type equalities, as they
      are all different types for the identity function. *)
  (* Constructing a cell. *)
  Definition cell_new : val := fn: ["x"] := return: ["x"].

  Lemma cell_new_type ty : typed_val cell_new (fn(∅; ty) → cell ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_jump; [solve_typing..|].
    iIntros (??) "#LFT _ $ Hty".
    rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    iDestruct "Hty" as ([|depth]) "[#? H]"=>//=. iExists _. iFrame "#".
    destruct x as [[]|]=>//. iDestruct "H" as "[H $]".
    iDestruct "H" as (?) "[??]". iExists _. iFrame. iExists _. iFrame "#".
    iApply ty_own_depth_mono; [|done]. lia.
  Qed.

  (* The other direction: getting ownership out of a cell. *)
  Definition cell_into_inner : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma cell_into_inner_type ty :
    typed_val cell_into_inner (fn(∅; cell ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL HC HT".
    rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    iDestruct "HT" as (depth) "[_ H]". destruct depth as [|depth]; [done|].
    destruct x as [[]|]=>//=. iDestruct "H" as "[H ?]".
    iDestruct "H" as (vl) "[? H]". iDestruct "H" as (depth') "[>Hdepth' ?]".
    wp_bind Skip. iApply (wp_persistent_time_receipt with "TIME Hdepth'"); [done|].
    wp_let. iIntros "Hdepth'". wp_let.
    rewrite cctx_interp_singleton /=. iApply ("HC" $! [# #l] with "Hna HL").
    rewrite tctx_interp_singleton tctx_hasty_val. iExists _. iFrame. iExists _. iFrame.
  Qed.

  Definition cell_get_mut : val :=
    fn: ["x"] := Skip ;; Skip ;; return: ["x"].

  Lemma cell_get_mut_type ty :
    typed_val cell_get_mut (fn(∀ α, ∅; &uniq{α} (cell ty)) → &uniq{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL HC HT".
    rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    iDestruct "HT" as ([|depth]) "[? H]"=>//=. destruct x as [[]|]=>//=.
    iDestruct "H" as "[H >H†]". iDestruct "H" as (vl) "(>H↦ & #Hout & H)".
    destruct vl as [|[[]|] []], depth as [|depth]; try by iDestruct "H" as ">[]".
    iDestruct "H" as (depth' γ) "(>% & _ & Hbor)".
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_let. iIntros "H⧗1". wp_let.
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_let. iIntros "H⧗2". wp_let.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Htok & HL & Hclose1)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[H Hclose]"; [done|].
    iDestruct "H" as (depth2') "(>H● & >Hdepth2' & H)". iDestruct "H" as (vl) "[>H↦' H]".
    iDestruct "H" as (depth'') "[>Hdepth'' H]".
    iMod (cumulative_persistent_time_receipt with "TIME H⧗1 Hdepth''") as "Hdepth''"; [done|].
    iMod (cumulative_persistent_time_receipt with "TIME H⧗2 Hdepth''") as "#Hdepth''"; [done|].
    iMod (own_alloc (●E _ ⋅ ◯E _)) as (γ') "[H●' H◯']"; [by apply excl_auth_valid|].
    iMod ("Hclose" with "[H● Hdepth2'] [H●' H↦' H]") as "[Hbor Htok]"; last first.
    - iMod ("Hclose1" with "Htok HL") as "HL".
      rewrite cctx_interp_singleton /=. iApply ("HC" $! [# #l] with "Hna HL").
      rewrite tctx_interp_singleton tctx_hasty_val. iExists (S (S depth'')).
      iFrame "H† Hdepth''". iExists _. iFrame "∗ Hout". iExists depth''. auto with iFrame.
    - iExists _. iFrame "H●'".
      iDestruct (persistent_time_receipt_mono with "Hdepth''") as "$"; [lia|].
      iExists _. iFrame.
    - iIntros "!> H". iExists _. iFrame "H● ∗".
      iDestruct "H" as (?) "(_ & >Hd & Ho)". iDestruct "Ho" as (vl') "[>? ?]".
      iExists vl'. iFrame. iExists _. iFrame.
      iApply (persistent_time_receipt_mono with "Hd"). lia.
  Qed.

  Definition cell_from_mut : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma cell_from_mut_type ty :
    typed_val cell_from_mut (fn(∀ α, ∅; &uniq{α} ty) → &uniq{α} (cell ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL HC HT".
    rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    iDestruct "HT" as ([|depth]) "[#Hdepth H]"=>//=. destruct x as [[]|]=>//=.
    iDestruct "H" as "[H >H†]". iDestruct "H" as (vl) "(>H↦ & #Hout & H)".
    destruct vl as [|[[]|] []], depth as [|depth]; try by iDestruct "H" as ">[]".
    iDestruct "H" as (depth' γ) "(>% & H◯ & Hbor)".
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_let. iIntros "H⧗". wp_let.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Htok & HL & Hclose1)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[H Hclose]"; [done|].
    iDestruct "H" as (?) "(>H● & _ & H)". iDestruct "H" as (vl) "[>H↦' H]".
    iDestruct (own_valid_2 with "H● H◯") as %->%excl_auth_agree_L.
    iMod (own_alloc (●E _ ⋅ ◯E _)) as (γ') "[H●' H◯']"; [by apply excl_auth_valid|].
    iMod ("Hclose" with "[H● H◯ H⧗] [H●' H↦' H]") as "[Hbor Htok]"; last first.
    - iMod ("Hclose1" with "Htok HL") as "HL".
      rewrite cctx_interp_singleton /=. iApply ("HC" $! [# #l] with "Hna HL").
      rewrite tctx_interp_singleton tctx_hasty_val. iExists (S (S depth)).
      iFrame "Hdepth H†". iExists _. iFrame "H↦ Hout". iExists depth, γ'.
      by iFrame.
    - iExists _. iFrame. iSplitR; [iApply persistent_time_receipt_mono; [|done]; lia|].
      iExists _. iFrame. iExists _. iFrame.
      iApply persistent_time_receipt_mono; [|done]. lia.
    - iIntros "!> H". iDestruct "H" as (?) "(_ & _ & Ho)".
      iDestruct "Ho" as (vl') "[>? Ho]". iDestruct "Ho" as (?) "[>Hdepth0 Ho]".
      iMod (own_update_2 with "H● H◯") as "[H● _]"; [by apply excl_auth_update|].
      iExists _. iFrame.
      iMod (cumulative_persistent_time_receipt with "TIME H⧗ Hdepth0") as "$"; [solve_ndisj|].
      iExists vl'. by iFrame.
  Qed.

  Definition cell_into_box : val :=
    fn: ["x"] := Skip ;; Skip ;; return: ["x"].

  Lemma cell_into_box_type ty :
    typed_val cell_into_box (fn(∅;box (cell ty)) → box ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL HC HT".
    rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    destruct x as [[]|]; iDestruct "HT" as ([|depth]) "[_ H]"=>//=.
    iDestruct "H" as "[Ho >H†]". iDestruct "Ho" as (vl) "[>H↦ Ho]".
    destruct vl as [|[[]|] []], depth as [|depth]=>//; try by iDestruct "Ho" as ">[]".
    iDestruct "Ho" as "[Ho ?]". iDestruct "Ho" as (?) "[H↦' Ho]".
    iDestruct "Ho" as (depth') "[Hdepth' Ho]".
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_let. iIntros "H⧗1". wp_let.
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_let. iIntros "H⧗2". wp_let.
    iMod (cumulative_persistent_time_receipt with "TIME H⧗1 Hdepth'") as "Hdepth'"; [done|].
    iMod (cumulative_persistent_time_receipt with "TIME H⧗2 Hdepth'") as "#Hdepth'"; [done|].
    rewrite cctx_interp_singleton /=. iApply ("HC" $! [# #l] with "Hna HL").
    rewrite tctx_interp_singleton tctx_hasty_val. iExists (S (S depth')).
    iFrame "H† Hdepth'". iExists _. iFrame "∗∗". auto with iFrame.
  Qed.

  Definition cell_from_box : val :=
    fn: ["x"] := return: ["x"].

  Lemma cell_from_box_type ty :
    typed_val cell_from_box (fn(∅; box ty) → box (cell ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_jump; [solve_typing..|].
    iIntros (??) "#LFT _ $ Hty". rewrite !tctx_interp_singleton /= !tctx_hasty_val.
    iDestruct "Hty" as (depth) "[#Hdepth Ho]". iExists depth. iFrame "Hdepth".
    destruct x as [[]|], depth as [|depth]=>//=. iDestruct "Ho" as "[Ho $]".
    iDestruct "Ho" as (vl) "[H↦ Ho]". iExists _. iFrame.
    destruct vl as [|[[]|] []], depth as [|depth]=>//=.
    iDestruct "Ho" as "[Ho $]". iDestruct "Ho" as (vl) "[H↦ Ho]".
    iExists _. iFrame. iExists _. iFrame.
    iApply persistent_time_receipt_mono; [|done]. lia.
  Qed.

  (** Reading from a cell *)
  Definition cell_get ty : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      letalloc: "r" <-{ty.(ty_size)} !"x'" in
      let: "cell_into_inner" := cell_into_inner in
      letcall: "r" := "cell_into_inner" ["r"]%E in
      delete [ #1; "x"];;
      return: ["r"].

  (* Interestingly, this is syntactically well-typed: we do not need
     to enter the model. *)
  Lemma cell_get_type ty `(!Copy ty) :
    typed_val (cell_get ty) (fn(∀ α, ∅; &shr{α} (cell ty)) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply (type_letalloc_n (cell ty)); [solve_typing..|].
    iIntros (r); simpl_subst.
    iApply type_let; [iApply cell_into_inner_type|solve_typing|].
    iIntros (cell_into_inner_type'). simpl_subst.
    iApply (type_letcall ()); [solve_typing..|]. iIntros (r'). simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (** Writing to a cell *)
  Definition cell_replace ty : val :=
    fn: ["c"; "x"] :=
      let: "c'" := !"c" in
      letalloc: "r" <-{ty.(ty_size)} !"c'" in
      "c'" <-{ty.(ty_size)} !"x";;
      delete [ #1; "c"] ;; delete [ #ty.(ty_size); "x"] ;; return: ["r"].

  Lemma cell_replace_type ty :
    typed_val (cell_replace ty) (fn(∀ α, ∅; &shr{α}(cell ty), ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>c x. simpl_subst.
    iApply type_deref; [solve_typing..|].
    iIntros (c'); simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (r); simpl_subst.
    (* Drop to Iris level. *)
    iIntros (tid) "#LFT #TIME #HE Htl HL HC".
    rewrite 3!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iIntros "(Hr & Hc & #Hc' & Hx)".
    iDestruct "Hc'" as (depthc') "[Hdepthc' Hc']"; destruct c' as [[|c'|]|]=>//=.
    iDestruct "Hx" as ([|depthx]) "[#Hdepthx Hx]"; destruct x as [[|x|]|]=>//=.
    iDestruct "Hr" as ([|depthr]) "[#Hdepthr Hr]"; destruct r as [[|r|]|]=>//=.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q') "(Htok & HL & Hclose1)"; [solve_typing..|].
    iMod (na_bor_acc with "LFT Hc' Htok Htl") as "(H & Htl & Hclose2)"; [solve_ndisj..|].
    iDestruct "H" as (depth) "[>Hdepth Hc'↦]". iDestruct "Hc'↦" as (vc') "[>Hc'↦ Hc'own]".
    iDestruct (ty_size_eq with "Hc'own") as "#>%".
    iDestruct "Hr" as "[Hr↦ Hr†]". iDestruct "Hr↦" as (vr) "[>Hr↦ >Heq]".
    iDestruct "Heq" as %Heq.
    (* FIXME: Changing the order of $Hr↦ $Hc'↦ breaks applying...?? *)
    wp_bind (_ <-{ty_size ty} !_)%E.
    iApply (wp_persistent_time_receipt with "TIME Hdepth"); [done|].
    wp_apply (wp_memcpy with "[$Hr↦ $Hc'↦]"); [lia..|].
    iIntros "[Hr↦ Hc'↦] #Hdepth". wp_seq.
    iDestruct "Hx" as "[Hx↦ Hx†]". iDestruct "Hx↦" as (vx) "[Hx↦ Hxown]".
    iDestruct (ty_size_eq with "Hxown") as "#%".
    wp_apply (wp_memcpy with "[$Hc'↦ $Hx↦]"); try by f_equal.
    iIntros "[Hc'↦ Hx↦]". wp_seq.
    iMod ("Hclose2" with "[Hc'↦ Hxown] Htl") as "[Htok Htl]".
    { iExists depthx.
      iSplitR; [iApply (persistent_time_receipt_mono with "Hdepthx"); lia|].
      auto with iFrame. }
    iMod ("Hclose1" with "Htok HL") as "HL".
    (* Now go back to typing level. *)
    iApply (type_type _ _ _
           [c ◁ box (&shr{α}(cell ty)); #x ◁ box (uninit ty.(ty_size)); #r ◁ box ty]
    with "[] LFT TIME HE Htl HL HC"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
      iFrame "Hc". rewrite !tctx_hasty_val' //. iSplitL "Hx↦ Hx†".
      - iExists (S depthx). iFrame "Hdepthx Hx†". iExists _. iFrame.
        iApply uninit_own. done.
      - iExists (S depth). auto with iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (** Create a shared cell from a mutable borrow.
      Called alias::one in Rust.
      This is really just [cell_from_mut] followed by sharing. *)
  Definition fake_shared_cell : val :=
    fn: ["x"] :=
      let: "cell_from_mut" := cell_from_mut in
      letcall: "r" := "cell_from_mut" ["x"]%E in
      let: "r'" := !"r" in
      delete [ #1; "r"];;
      Share;;
      letalloc: "r" <- "r'" in
      return: ["r"].

  Lemma fake_shared_cell_type ty :
    typed_val fake_shared_cell (fn(∀ α, ∅; &uniq{α} ty) → &shr{α}(cell ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_let; [apply cell_from_mut_type|solve_typing|]. iIntros (f). simpl_subst.
    iApply type_letcall; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (r'). simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply (type_share r'); [solve_typing..|].
    iApply type_letalloc_1; [solve_typing..|]. iIntros (r''). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
*)
End cell.

Global Hint Resolve cell_leak_just cell_subtype cell_eqtype : lrust_typing.
