From iris.proofmode Require Import tactics.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section cell.
  Context `{!typeG Σ}.

  Program Definition cell (ty : type) :=
    {| ty_size := ty.(ty_size); ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own _ tid vl := (∃ depth, ⧖depth ∗ ty.(ty_own) depth tid vl)%I;
       ty_shr κ tid l :=
         (* Depth is frozen by shargin *)
         (&na{κ, tid, shrN.@l}(∃ depth, ⧖depth ∗ l ↦∗: ty.(ty_own) depth tid))%I
    |}.
  Next Obligation. intros. iDestruct 1 as (?) "[_ ?]". by iApply ty_size_eq. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (ty E depth κ l tid q ?) "#LFT #Hout Hown Htok !>".
    iApply step_fupdN_intro; [done|]. iModIntro. iFrame. iApply bor_na; [done|].
    iApply (bor_iff with "[] Hown"). iIntros "!> !>". iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[? H]". iDestruct "H" as (depth') "[??]".
      iExists _. iFrame. iExists _. iFrame.
    - iDestruct "H" as (depth') "[? H]". iDestruct "H" as (vl) "[??]".
      iExists _. iFrame. iExists _. iFrame.
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#H⊑ H". by iApply (na_bor_shorten with "H⊑").
  Qed.

  Global Instance cell_type_ne : TypeNonExpansive cell.
  Proof.
    split=>//.
    - apply (type_lft_morphism_add _ static [] []).
      + intros. rewrite left_id. iApply lft_equiv_refl.
      + intros. by rewrite /elctx_interp /= left_id right_id.
    - intros. simpl. do 3 (f_contractive || f_equiv). done.
    - intros. simpl. do 7 (f_contractive || f_equiv). simpl in *. done.
  Qed.

  Global Instance cell_ne : NonExpansive cell.
  Proof. solve_ne_type. Qed.

  Global Instance cell_mono E L : Proper (eqtype E L ==> subtype E L) cell.
  Proof.
    move=>?? /eqtype_unfold EQ. iIntros (?) "HL".
    iDestruct (EQ with "HL") as "#EQ". iIntros "!> #HE".
    iDestruct ("EQ" with "HE") as "(% & #[Hout1 Hout2] & #Hown & #Hshr)".
    iSplit; [done|iSplit; [done|iSplit; iIntros "!> * H"]].
    - iDestruct "H" as (depth') "[? H]". iExists _. iFrame. iApply ("Hown" with "H").
    - iApply na_bor_iff; last done. iNext; iModIntro; iSplit; iIntros "H";
      iDestruct "H" as (depth) "[? H]"; iExists depth; iFrame;
      iDestruct "H" as (vl) "[??]"; iExists vl; iFrame; by iApply "Hown".
  Qed.
  Lemma cell_mono' E L ty1 ty2 : eqtype E L ty1 ty2 → subtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_mono. Qed.
  Global Instance cell_proper E L : Proper (eqtype E L ==> eqtype E L) cell.
  Proof. by split; apply cell_mono. Qed.
  Lemma cell_proper' E L ty1 ty2 : eqtype E L ty1 ty2 → eqtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_proper. Qed.

  Global Instance cell_copy ty :
    Copy ty → Copy (cell ty).
  Proof.
    intros Hcopy. split; first by intros; simpl; unfold ty_own; apply _.
    iIntros (depth κ tid E F l q ??) "#LFT #Hshr Htl Htok". iExists 1%Qp. simpl in *.
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    destruct (ty_size ty) as [|sz] eqn:Hsz; simpl in *.
    { iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(Hown & Htl & Hclose)";
        [solve_ndisj..|].
      iDestruct "Hown" as (depth') "[#Hdepth' Hown]". iDestruct "Hown" as (vl) "[H↦ #Hown]".
      assert (F ∖ ∅ = F) as -> by set_solver+.
      iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
      iMod ("Hclose" with "[H↦] Htl") as "[$ $]".
      { iExists depth'. iFrame "Hdepth'". iExists vl. by iFrame. }
      iModIntro. iExists vl. iSplitL "".
      { destruct vl; last done. by iApply heap_mapsto_vec_nil. }
      iSplit; [by eauto|]. by iIntros "$ _". }
    (* Now we are in the non-0 case. *)
    iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(H & Htl & Hclose)"; [solve_ndisj..|].
    iDestruct "H" as (depth') "[#Hdepth' H]". iDestruct "H" as (vl) "[>Hvl #Hown]".
    iExists vl. iDestruct (na_own_acc with "Htl") as "($ & Hclose')"; first by set_solver.
    iIntros "{$Hvl}". iSplitR; [by eauto|]. iIntros " !> Htl Hvl".
    iPoseProof ("Hclose'" with "Htl") as "Htl".
    iMod ("Hclose" with "[Hvl] Htl") as "[$ $]"=>//. iExists depth'. iFrame "Hdepth'".
    iExists vl; auto.
  Qed.

  Global Instance cell_send ty :
    Send ty → Send (cell ty).
  Proof. rewrite /cell /Send /=. intros H12 **. do 3 f_equiv. apply H12. Qed.
End cell.

Section typing.
  Context `{!typeG Σ}.

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
End typing.

Global Hint Resolve cell_mono' cell_proper' : lrust_typing.
