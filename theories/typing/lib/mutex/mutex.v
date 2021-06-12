From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition mutexN := lrustN .@ "mutex".

Section mutex.
  Context `{!typeG Σ}.

  (*
    pub struct Mutex<T: ?Sized> {
      // Note that this mutex is in a *box*, not inlined into the struct itself.
      // Once a native mutex has been used once, its address can never change (it
      // can't be moved). This mutex type can be safely moved at any time, so to
      // ensure that the native mutex is used correctly we box the inner lock to
      // give it a constant address.
      inner: Box<sys::Mutex>,
      poison: poison::Flag,
      data: UnsafeCell<T>,
    }
  *)

  Program Definition mutex {𝔄} (ty: type 𝔄) : type (predₛ 𝔄) := {|
      ty_size := 1 + ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
      ty_own Φπ _ tid vl := ∃vπ d (b: bool) vl' Φ,
        ⌜vl = #b :: vl' ∧ Φπ = const Φ⌝ ∗
        ⧖(S d) ∗ ty.(ty_own) vπ d tid vl' ∗ ⟨π, Φ (vπ π)⟩;
      ty_shr Φπ _ κ tid l := ∃Φ κ', ⌜Φπ = const Φ⌝ ∗ κ ⊑ κ' ∗ κ' ⊑ ty.(ty_lft) ∗
        &at{κ, mutexN} $ lock_proto l $
          &{κ'} (∃vπ d, (l +ₗ 1) ↦∗: ty.(ty_own) vπ d tid ∗ ⧖(S d) ∗ ⟨π, Φ (vπ π)⟩);
    |}%I.
  Next Obligation.
    iIntros "* (%&%&%&%&%&[->_]&_& ty &_) /=". rewrite ty_size_eq.
    by iDestruct "ty" as %->.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "* #? (%&%&%&#?&?&?)". iExists _, _. iSplit; [done|].
    iSplit; [|iSplit; [done|]]; by [iApply lft_incl_trans|iApply at_bor_shorten].
  Qed.
  Next Obligation.
    iIntros "*% #LFT #In Bor κ !>". iApply step_fupdN_full_intro.
    iMod (bor_acc_cons with "LFT Bor κ") as "[(%& >↦ & big) ToBor]"; [done|].
    iMod (bi.later_exist_except_0 with "big") as (?????) "(>[->->] & >⧖ & ty & Obs)".
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[↦b ↦]".
    iMod ("ToBor" $! ((∃b: bool, l ↦ #b) ∗
        ∃vπ d, (l +ₗ 1) ↦∗: ty.(ty_own) vπ d tid ∗ ⧖(S d) ∗ ⟨π, Φ (vπ π)⟩)%I
      with "[] [↦b ↦ ty ⧖ Obs]") as "[Bor κ]".
    { iIntros "!> big !>!>". iDestruct "big" as "[[% ↦b] (%&%&(%& ↦ &?)&?&?)]".
      iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame "↦b ↦".
      iExists _, _, _, _, _. by iFrame. }
    { iNext. iSplitL "↦b"; [by iExists _|]. iExists _, _. iFrame "⧖ Obs".
      iExists _. iFrame. }
    iMod (bor_sep with "LFT Bor") as "[Borb Borty]"; [done|]. clear b.
    iMod (bor_acc_cons with "LFT Borb κ") as "[>(%b & ↦b) ToBorb]"; [done|].
    iMod (lock_proto_create with "↦b [Borty]") as "Proto".
    { case b; [done|]. by iExact "Borty". }
    iMod ("ToBorb" with "[] Proto") as "[Bor $]".
    { iIntros "!> Proto !>!>".
      iDestruct (lock_proto_destroy with "Proto") as (?) "[? _]". by iExists _. }
    iExists _, _. iMod (bor_share with "Bor") as "$"; [solve_ndisj|].
    iFrame "In". iSplitR; [done|]. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros "*% _ _ (%&%&%&%&%&[->->]& big) $ !>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _, _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "*% _ _ _ (%&%&->& big) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _, _. by iFrame.
  Qed.

  Global Instance mutex_ne {𝔄} : NonExpansive (@mutex 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance mutex_type_ne {𝔄} : TypeNonExpansive (@mutex 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|by move=>/= ??->|..].
    - move=>/= *. by do 13 f_equiv.
    - move=>/= *. do 7 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      do 11 (f_contractive || f_equiv). simpl in *. by apply dist_S.
  Qed.

  Global Instance mutex_send {𝔄} (ty: type 𝔄) : Send ty → Send (mutex ty).
  Proof. move=> ?>/=. by do 13 f_equiv. Qed.

  Global Instance mutex_sync {𝔄} (ty: type 𝔄) : Send ty → Sync (mutex ty).
  Proof. move=> ?>/=. by do 18 f_equiv. Qed.

  (* In order to prove [mutex_leak] with a non-trivial postcondition,
    we need to modify the model of [leak] to use [⧖d] inside [ty_own] *)
  Lemma mutex_leak {𝔄} (ty: type 𝔄) E L : leak E L (mutex ty) (const True).
  Proof. apply leak_just. Qed.

  Lemma mutex_real {𝔄} (ty: type 𝔄) E L : real E L (mutex ty) id.
  Proof.
    split.
    - iIntros "*% _ _ $ (%&%&%&%&%&[->->]&?)". iApply step_fupdN_full_intro.
      iSplitR; [by iExists _|]. iExists _, _, _, _, _. by iFrame.
    - iIntros "*% _ _ $ (%&%&->&?)!>!>!>". iApply step_fupdN_full_intro.
      iSplitR; [by iExists _|]. iExists _, _. by iFrame.
  Qed.

  Lemma mutex_subtype {𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    eqtype E L ty ty' f g → subtype E L (mutex ty) (mutex ty') (.∘ g).
  Proof.
    move=> /eqtype_unfold Eq ?. iIntros "L". iDestruct (Eq with "L") as "#Eq".
    iIntros "!> E". iDestruct ("Eq" with "E") as "(%EqSz & [#? #?] & #EqOwn &_)".
    iSplit; [by rewrite/= EqSz|]. iSplit; [done|]. iSplit; iIntros "!> *".
    - iDestruct 1 as (?????[->->]) "(⧖ & ty &?)". iExists (f ∘ _), _, _, _, _.
      iSplit; [done|]. iFrame "⧖". iSplitL "ty"; [by iApply "EqOwn"|].
      iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'.
    - iDestruct 1 as (??->) "(In & #In' & At)". iExists _, _. iSplit; [done|].
      iFrame "In". iSplit; [by iApply lft_incl_trans|].
      iApply (at_bor_iff with "[] At"). iNext. iApply lock_proto_iff_proper.
      iApply bor_iff_proper. iIntros "!>!>".
      iSplit; iIntros "(%&%& (%& ↦ & ty) & ⧖ & Obs)".
      + iExists (f ∘ _), _. iFrame "⧖".
        iSplitR "Obs". { iExists _. iFrame "↦". by iApply "EqOwn". }
        iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'.
      + iExists (g ∘ _), _. iFrame "⧖ Obs". iExists _. iFrame "↦".
        iApply "EqOwn". by rewrite compose_assoc semi_iso.
  Qed.
  Lemma mutex_eqtype {𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (mutex ty) (mutex ty') (.∘ g) (.∘ f).
  Proof. move=> [??]. split; by (eapply mutex_subtype; [split; apply _|]). Qed.

(*
  Definition mutex_new ty : val :=
    fn: ["x"] :=
      let: "m" := new [ #(mutex ty).(ty_size) ] in
      "m" +ₗ #1 <-{ty.(ty_size)} !"x";;
      mklock_unlocked ["m" +ₗ #0];;
      delete [ #ty.(ty_size); "x"];; return: ["m"].

  Lemma mutex_new_type ty :
    typed_val (mutex_new ty) (fn(∅; ty) → mutex ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    (* FIXME: It should be possible to infer the `S ty.(ty_size)` here.
       This should be done in the @eq external hints added in lft_contexts.v. *)
    iApply (type_new (S ty.(ty_size))); [solve_typing..|]; iIntros (m); simpl_subst.
    (* FIXME: The following should work.  We could then go into Iris later.
    iApply (type_memcpy ty); [solve_typing..|]. *)
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hm [Hx _]]".
    rewrite !tctx_hasty_val /=.
    iDestruct (ownptr_uninit_own with "Hm") as (lm vlm) "(% & Hm & Hm†)".
    subst m. inv_vec vlm=>m vlm. simpl. iDestruct (heap_mapsto_vec_cons with "Hm") as "[Hm0 Hm]".
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct (heap_mapsto_ty_own with "Hx") as (vl) "[>Hx Hxown]".
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. wp_apply (wp_memcpy with "[$Hm $Hx]"); [by rewrite vec_to_list_length..|].
    iIntros "[Hm Hx]". wp_seq. wp_op. rewrite shift_loc_0. wp_lam.
    wp_write.
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ #lx ◁ box (uninit ty.(ty_size)); #lm ◁ box (mutex ty)]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val' // tctx_hasty_val' //.
      iFrame. iSplitL "Hx".
      - iExists _. iFrame. by rewrite uninit_own vec_to_list_length.
      - iExists (#false :: vl). rewrite heap_mapsto_vec_cons. iFrame; eauto. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutex_into_inner ty : val :=
    fn: ["m"] :=
      let: "x" := new [ #ty.(ty_size) ] in
      "x" <-{ty.(ty_size)} !("m" +ₗ #1);;
      delete [ #(mutex ty).(ty_size); "m"];; return: ["x"].

  Lemma mutex_into_inner_type ty :
    typed_val (mutex_into_inner ty) (fn(∅; mutex ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>m. simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|]; iIntros (x); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hm _]]".
    rewrite !tctx_hasty_val /=.
    iDestruct (ownptr_uninit_own with "Hx") as (lx vlx) "(% & Hx & Hx†)".
    subst x. simpl.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as "[Hm Hm†]".
    iDestruct (heap_mapsto_ty_own with "Hm") as (vlm) "[>Hm Hvlm]".
    inv_vec vlm=>m vlm. destruct m as [[|m|]|]; try by iDestruct "Hvlm" as ">[]".
    simpl. iDestruct (heap_mapsto_vec_cons with "Hm") as "[Hm0 Hm]".
    iDestruct "Hvlm" as "[_ Hvlm]".
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. wp_apply (wp_memcpy with "[$Hx $Hm]"); [by rewrite vec_to_list_length..|].
    (* FIXME: Swapping the order of $Hx and $Hm breaks. *)
    iIntros "[Hx Hm]". wp_seq.
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ #lx ◁ box ty; #lm ◁ box (uninit (mutex ty).(ty_size))]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val' // tctx_hasty_val' //.
      iFrame. iSplitR "Hm0 Hm".
      - iExists _. iFrame.
      - iExists (_ :: _). rewrite heap_mapsto_vec_cons. iFrame.
        rewrite uninit_own. rewrite /= vec_to_list_length. eauto. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutex_get_mut : val :=
    fn: ["m"] :=
      let: "m'" := !"m" in
      "m" <- ("m'" +ₗ #1);;
      return: ["m"].

  Lemma mutex_get_mut_type ty :
    typed_val mutex_get_mut (fn(∀ α, ∅; &uniq{α}(mutex ty)) → &uniq{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg); inv_vec arg=>m; simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m'); simpl_subst.
    (* Go to Iris *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hm [Hm' _]]".
    rewrite !tctx_hasty_val [[m]]lock.
    iDestruct "Hm'" as "[#? Hm']".
    destruct m' as [[|lm'|]|]=>//=.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose1)";
      [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hm' Hα") as "[Hm' Hclose2]"; first done.
    wp_op. iDestruct "Hm'" as (vl) "[H↦ Hm']".
    destruct vl as [|[[|m'|]|] vl]; try done. simpl.
    iDestruct (heap_mapsto_vec_cons with "H↦") as "[H↦1 H↦2]".
    iDestruct "Hm'" as "[% Hvl]".
    iMod ("Hclose2" $! ((lm' +ₗ 1) ↦∗: ty_own ty tid)%I with "[H↦1] [H↦2 Hvl]") as "[Hbor Hα]".
    { iIntros "!> Hlm' !>". iNext. clear vl. iDestruct "Hlm'" as (vl) "[H↦ Hlm']".
      iExists (_ :: _). rewrite heap_mapsto_vec_cons. do 2 iFrame. done. }
    { iExists vl. iFrame. }
    iMod ("Hclose1" with "Hα HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ m ◁ own_ptr _ _; #(lm' +ₗ 1) ◁ &uniq{α} ty]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. by iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
*)
End mutex.

Global Hint Resolve mutex_leak mutex_real mutex_subtype mutex_eqtype
  : lrust_typing.
