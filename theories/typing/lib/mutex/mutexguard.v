From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option mutex.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mutexguard.
  Context `{!typeG Σ}.

  (*
    pub struct MutexGuard<'a, T: ?Sized + 'a> {
      // funny underscores due to how Deref/DerefMut currently work (they
      // disregard field privacy).
      __lock: &'a Mutex<T>,
      __poison: poison::Guard,
    }
  *)
  Context `{!BiFUpd PROP}.
Implicit Type P Q R: PROP.

  Program Definition mutexguard {𝔄} (κ: lft) (ty: type 𝔄) : type (predₛ 𝔄) := {|
    ty_size := 1;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    (* One logical step is required for [ty_share] *)
    ty_own Φπ d tid vl := ⌜d > 0⌝ ∗ [loc[l] := vl] ∃Φ κ',
      ⌜Φπ = const Φ⌝ ∗ κ ⊑ κ' ∗ κ' ⊑ ty.(ty_lft) ∗
      &at{κ, mutexN} (lock_proto l (mutex_body ty Φ κ' l tid)) ∗
      mutex_body ty Φ κ' l tid;
    ty_shr Φπ _ κ' tid l := ∃Φ (l': loc) κᵢ (vπ: proph 𝔄) d,
      ⌜Φπ = const Φ⌝ ∗ κ' ⊑ κᵢ ∗ κᵢ ⊑ ty.(ty_lft) ∗
      &frac{κ'}(λ q', l ↦{q'} #l') ∗ ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗
      □ ∀E q, ⌜↑lftN ∪ ↑shrN ⊆ E⌝ -∗ q.[κᵢ]
        ={E,E∖↑shrN}=∗ |={E∖↑shrN}▷=>^(S d) |={E∖↑shrN,E}=>
          ty.(ty_shr) vπ d κᵢ tid (l' +ₗ 1) ∗ q.[κᵢ];
  |}%I.
  Next Obligation. iIntros (??????[|[[]|][]]) "[%?] //". Qed.
  Next Obligation. iIntros "*% [%$] !%". lia. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "%%* #Inκ' (%&%&%&%&%&->& ⊑κᵢ & κᵢ⊑ & Bor & big)".
    iExists _, _, _, _, _. iFrame "κᵢ⊑ big". iSplit; [done|].
    iSplit; [|by iApply frac_bor_shorten]. by iApply lft_incl_trans.
  Qed.
  Next Obligation.
    iIntros (????? d κ') "*% #LFT #In Bor κ' //".
    iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>% & Bor & κ')"; [done|].
    case d as [|]; [done|]. case vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent with "LFT Bor κ'") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Bor↦") as "#Bor↦"; [done|].
    iMod (bor_exists with "LFT Bor") as (Φ) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (κ'') "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>-> & Bor & κ')"; [done|].
    do 2 (iMod (bor_sep_persistent with "LFT Bor κ'") as "(#? & Bor & κ')"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. iIntros "/=!>!>!>!>".
    iApply step_fupdN_full_intro. iMod "Bor". set κᵢ := κ'' ⊓ κ'.
    iAssert (κ' ⊑ κᵢ)%I as "κ'⊑κᵢ".
    { iApply lft_incl_glb; [|iApply lft_incl_refl]. iApply lft_incl_trans; [|done].
      iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    iMod (lft_incl_acc with "κ'⊑κᵢ κ'") as (?) "[κᵢ Toκ']"; [done|].
    do 2 (iMod (bor_exists_tok with "LFT Bor κᵢ") as (?) "[Bor κᵢ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κᵢ") as "(>Obs & Bor & κᵢ)"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κᵢ") as "(>⧖ & Bor & κᵢ)"; [done|].
    iMod ("Toκ'" with "κᵢ") as "κ'".
    iMod (inv_alloc shrN _ (_ ∨ ty.(ty_shr) _ _ _ _ _)%I with "[Bor]") as "#inv".
    { iLeft. iNext. iExact "Bor". }
    iModIntro. iFrame "κ'". iExists _, _, κᵢ, _, _. iSplit; [done|].
    iFrame "Bor↦ Obs ⧖ κ'⊑κᵢ". iAssert (κᵢ ⊑ ty.(ty_lft))%I as "#?".
    { iApply lft_incl_trans; [iApply lft_intersect_incl_l|done]. }
    iSplit; [done|]. iIntros "!>" (???) "κᵢ".
    iInv shrN as "[Bor|#ty]" "Close"; iIntros "/=!>!>!>"; last first.
    { iApply step_fupdN_full_intro. iModIntro. iFrame "κᵢ".
      iMod ("Close" with "[]"); by [iRight|]. }
    iMod (ty_share with "LFT [] Bor κᵢ") as "Upd"; [solve_ndisj|done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[#ty $]".
    iMod ("Close" with "[]"); by [iRight|].
  Qed.
  Next Obligation.
    iIntros (???????[|[[]|][]]) "*% _ _ [% big] //". iDestruct "big" as (??->) "?".
    iIntros "$ !>". iApply step_fupdN_full_intro. iModIntro. iExists [], 1%Qp.
    do 2 (iSplit; [done|]). iIntros "_!>". iSplit; [done|]. iExists _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "*% _ _ _ (%&%&%&%&%&->&?) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplit; [done|]). iIntros "_!>".
    iExists _, _, _, _, _. by iFrame.
  Qed.

  Global Instance mutexguard_ne {𝔄} κ : NonExpansive (mutexguard (𝔄:=𝔄) κ).
  Proof. rewrite /mutexguard /mutex_body. solve_ne_type. Qed.

  Global Instance mutexguard_type_contractive {𝔄} κ :
    TypeContractive (mutexguard (𝔄:=𝔄) κ).
  Proof.
    split; [by eapply type_lft_morphism_add_one|done| |].
    - move=>/= *. do 10 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      rewrite /mutex_body.
      f_equiv; [do 2 f_equiv|]; f_contractive; do 9 f_equiv; by simpl in *.
    - move=>/= *. do 13 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      do 17 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance mutexguard_sync {𝔄} κ (ty: type 𝔄) :
    Sync ty → Sync (mutexguard κ ty).
  Proof. move=> ?>/=. by do 30 f_equiv. Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for MutexGuard. We can
     prove this for our spinlock implementation, however. *)
  Global Instance mutexguard_send {𝔄} κ (ty: type 𝔄) :
    Send ty → Send (mutexguard κ ty).
  Proof.
    move=> ?>/=. rewrite /mutex_body. do 21 f_equiv; [|done]. by do 2 f_equiv.
  Qed.

  (* In order to prove [mutexguard_leak] with a non-trivial postcondition,
    we need to modify the model of [leak] to use [⧖d] inside [ty_own] *)
  Lemma mutexguard_leak {𝔄} κ (ty: type 𝔄) E L :
    leak E L (mutexguard κ ty) (const True).
  Proof. apply leak_just. Qed.

  Lemma mutexguard_real {𝔄} κ (ty: type 𝔄) E L : real E L (mutexguard κ ty) id.
  Proof.
    split.
    - iIntros (????? vl) "*% _ _ $ (%& big) !>". case vl as [|[[]|][]]=>//.
      iDestruct "big" as (??->) "?". iApply step_fupdN_full_intro. iModIntro.
      iSplit; [by iExists _|]. iSplit; [done|]. iExists _, _. by iFrame.
    - iIntros "*% _ _ $ (%&%&%&%&%&->&?) !>!>!>". iApply step_fupdN_full_intro.
      iModIntro. iSplit; [by iExists _|]. iExists _, _, _, _, _. by iFrame.
  Qed.

  Lemma mutexguard_subtype {𝔄 𝔅} κ κ' f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' f g →
    subtype E L (mutexguard κ ty) (mutexguard κ' ty') (.∘ g).
  Proof.
    move=> Lft /eqtype_unfold Eq ?. iIntros "L".
    iDestruct (Lft with "L") as "#Toκ'⊑κ". iDestruct (Eq with "L") as "#ToEq".
    iIntros "!> E". iDestruct ("Toκ'⊑κ" with "E") as "#κ'⊑κ".
    iDestruct ("ToEq" with "E") as "(%&[#?#?]& #InOwn & #InShr)". iSplit; [done|].
    iSplit; [by iApply lft_intersect_mono|]. iSplit; iModIntro.
    - iIntros (???[|[[]|][]]) "[% big] //".
      iDestruct "big" as (? κ''->) "(#?&#?& At & Mut)". iSplit; [done|]. iExists _, κ''.
      iSplit; [done|]. do 2 (iSplit; [by iApply lft_incl_trans|]).
      iDestruct (mutex_body_iff with "InOwn") as "Iff". iSplit; [|by iApply "Iff"].
      iApply at_bor_shorten; [done|]. iApply (at_bor_iff with "[] At"). iNext.
      by iApply lock_proto_iff_proper.
    - iIntros "* (%&%& %κᵢ &%&%&->&#?&#?&#?&#?&#?& #big)".
      iExists _, _, κᵢ, (f ∘ _), _. do 2 (iSplit; [done|]).
      iSplit; [by iApply lft_incl_trans|]. iSplit; [done|].
      iSplit. { iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'. }
      iSplit; [done|]. iIntros "!>" (???) "κᵢ". iMod ("big" with "[//] κᵢ") as "Upd".
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >[?$] !>". by iApply "InShr".
  Qed.
  Lemma mutexguard_eqtype {𝔄 𝔅} κ κ' f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    lctx_lft_eq E L κ' κ → eqtype E L ty ty' f g →
    eqtype E L (mutexguard κ ty) (mutexguard κ' ty') (.∘ g) (.∘ f).
  Proof.
    move=> [??][??]. split; by (eapply mutexguard_subtype; [split; apply _|..]).
  Qed.

(*
  Lemma mutex_acc E l ty tid q α κ :
    ↑lftN ⊆ E → ↑mutexN ⊆ E →
    let R := (&{κ}((l +ₗ 1) ↦∗: ty_own ty tid))%I in
    lft_ctx -∗ &at{α,mutexN}(lock_proto l R) -∗ α ⊑ κ -∗
    □ ((q).[α] ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ (q).[α])).
  Proof.
    (* FIXME: This should work: iIntros (?? R). *) intros ?? R.
    iIntros "#LFT #Hshr #Hlincl !> Htok".
    iMod (at_bor_acc_tok with "LFT Hshr Htok") as "[Hproto Hclose1]"; [done..|].
    iMod (fupd_intro_mask') as "Hclose2"; last iModIntro; first solve_ndisj.
    iFrame. iIntros "Hproto". iMod "Hclose2" as "_".
    iMod ("Hclose1" with "Hproto") as "$". done.
  Qed.

  Definition mutex_lock : val :=
    fn: ["mutex"] :=
      let: "m" := !"mutex" in
      let: "guard" := new [ #1 ] in
      acquire ["m"];;
      "guard" +ₗ #0 <- "m";;
      delete [ #1; "mutex" ];; return: ["guard"].

  Lemma mutex_lock_type ty :
    typed_val mutex_lock (fn(∀ α, ∅; &shr{α}(mutex ty)) → mutexguard α ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m); simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (g); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hx [Hm _]]]".
    rewrite !tctx_hasty_val [[x]]lock /=.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as (κ') "(#Hακ' & #? & #Hshr)".
    iDestruct (ownptr_uninit_own with "Hg") as (lg vlg) "(% & Hg & Hg†)".
    subst g. inv_vec vlg=>g. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    wp_apply (acquire_spec with "[] Hα"); first by iApply (mutex_acc with "LFT Hshr Hακ'").
    iIntros "[Hcont Htok]". wp_seq. wp_op. rewrite shift_loc_0. wp_write.
    iMod ("Hclose1" with "Htok HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ x ◁ own_ptr _ _; #lg ◁ box (mutexguard α ty)]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hg".
      iExists _. iFrame "#∗". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
*)

  Definition mutexguard_deref: val :=
    fn: ["g"] :=
      let: "g'" := !"g" in let: "m" := !"g'" in
      letalloc: "r" <- ("m" +ₗ #1) in
      delete [ #1; "g"];; return: ["r"].

(*
  Lemma mutexguard_derefmut_type ty :
    typed_val mutexguard_derefmut
              (fn(∀ '(α, β), ∅; &uniq{α}(mutexguard β ty)) → &uniq{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>g. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (g'); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hg' _]]".
    rewrite !tctx_hasty_val [[g]]lock /=.
    iDestruct "Hg'" as "[#? Hg']".
    destruct g' as [[|lg|]|]; try done. simpl.
    iMod (bor_exists with "LFT Hg'") as (vl) "Hbor"; first done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hprot]"; first done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose1)";
      [solve_typing..|].
    destruct vl as [|[[|lm|]|] [|]]; simpl;
      try by iMod (bor_persistent with "LFT Hprot Hα") as "[>[] _]".
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT Hprot") as (κ) "Hprot"; first done.
    iMod (bor_sep with "LFT Hprot") as "[Hβκ Hprot]"; first done.
    iMod (bor_sep with "LFT Hprot") as "[Hκty Hprot]"; first done.
    iMod (bor_sep with "LFT Hprot") as "[_ Hlm]"; first done.
    iMod (bor_persistent with "LFT Hβκ Hα") as "[#Hβκ Hα]"; first done.
    iMod (bor_persistent with "LFT Hκty Hα") as "[#Hκty Hα]"; first done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hclose2]"; first done.
    wp_bind (!_)%E. iMod (bor_unnest with "LFT Hlm") as "Hlm"; first done.
    wp_read. wp_let. iMod "Hlm".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iMod ("Hclose2" with "H↦") as "[_ Hα]".
    iMod ("Hclose1" with "Hα HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ g ◁ own_ptr _ _; #lm +ₗ #1 ◁ &uniq{α} ty ]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iSplitR.
      - iApply lft_incl_trans; [done|]. by iApply lft_incl_trans.
      - iApply bor_shorten; last done.
        iApply lft_incl_glb; last by iApply lft_incl_refl.
        iApply lft_incl_trans; done. }
    iApply type_letalloc_1; [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
*)

  Lemma mutexguard_deref_shr_type {𝔄} (ty: type 𝔄) :
    typed_val mutexguard_deref
      (fn<(α, β)>(∅; &shr{α} (mutexguard β ty)) → &shr{α} ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [solve_typing|]=>/= αβ ??[g[]]. case αβ=> α β. simpl_subst.
    iIntros (?[?[]]?) "LFT #TIME _ _ #E Na L C /=[g _] Obs". rewrite tctx_hasty_val.
    iDestruct "g" as ([|d]) "[_ box]"=>//. case g as [[|g|]|]=>//.
    iDestruct "box" as "[(%vl & >↦g & guard) †g]".
    case d as [|]; try by iDestruct "guard" as ">[]".
    case vl as [|[[|l|]|][]]; try by iDestruct "guard" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    iDestruct "guard" as (?????->) "(#⊑κᵢ &?& Bor↦ & Obs' & #⧖ & #Upd)".
    iCombine "Obs Obs'" as "#?".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor↦ α") as (?) "[>↦l Toα]"; [done|].
    wp_read. wp_let. iMod ("Toα" with "↦l") as "α".
    iMod (lft_incl_acc with "⊑κᵢ α") as (?) "[κᵢ Toα]"; [done|].
    wp_bind (new _). iSpecialize ("Upd" $! ⊤ with "[//] κᵢ").
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done|done| |].
    { iApply step_fupdN_with_emp. rewrite difference_empty_L.
      iApply (step_fupdN_nmono (S _)); [|done]. lia. }
    iApply wp_new; [done..|]. iIntros "!>% [†r ↦r] [ty κᵢ] !>". wp_let.
    iMod ("Toα" with "κᵢ") as "α". iMod ("ToL" with "α L") as "L".
    rewrite heap_mapsto_vec_singleton. wp_op. wp_write. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iClear "⧖".
    iApply (wp_delete with "[$↦g $†g]"); [done|]. iIntros "!>_ #⧖".
    do 3 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[_] with "Na L [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp. }
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iSplit; [done|].
    rewrite/= freeable_sz_full. iFrame "†r". iNext. iExists [_].
    rewrite heap_mapsto_vec_singleton. iFrame "↦r". by iApply ty_shr_lft_mono.
  Qed.

(*
  Definition mutexguard_drop : val :=
    fn: ["g"] :=
      let: "m" := !"g" in
      release ["m"];;
      delete [ #1; "g" ];;
      let: "r" := new [ #0 ] in return: ["r"].

  Lemma mutexguard_drop_type ty :
    typed_val mutexguard_drop (fn(∀ α, ∅; mutexguard α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>g. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hm _]]".
    rewrite !tctx_hasty_val [[g]]lock /=.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as (β) "(#Hαβ & #Hβty & #Hshr & Hcnt)".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    wp_apply (release_spec with "[] [Hα Hcnt]");
      [by iApply (mutex_acc with "LFT Hshr Hαβ")|by iFrame|].
    iIntros "Htok". wp_seq. iMod ("Hclose1" with "Htok HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ g ◁ own_ptr _ _ ]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val. unlock. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* TODO: Should we do try_lock? *)
*)
End mutexguard.

Global Hint Resolve mutexguard_leak mutexguard_real
  mutexguard_subtype mutexguard_eqtype : lrust_typing.
