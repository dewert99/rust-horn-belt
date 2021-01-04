From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing util option mutex.
Set Default Proof Using "Type".

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mguard.
  Context `{!typeG Σ}.

  (*
    pub struct MutexGuard<'a, T: ?Sized + 'a> {
      // funny underscores due to how Deref/DerefMut currently work (they
      // disregard field privacy).
      __lock: &'a Mutex<T>,
      __poison: poison::Guard,
    }
  *)

  Program Definition mutexguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_lfts := α :: ty.(ty_lfts); ty_E := ty.(ty_E) ++ ty_outlives_E ty α;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ β, α ⊑ β ∗ β ⊑ ty.(ty_lft) ∗
             &at{α, mutexN} (lock_proto l (&{β} ((l +ₗ 1) ↦∗: ty.(ty_own) tid))) ∗
             &{β} ((l +ₗ 1) ↦∗: ty.(ty_own) tid)
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l':loc), &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α⊓κ]
                ={F}[F∖↑shrN]▷=∗ ty.(ty_shr) (α⊓κ) tid (l' +ₗ 1) ∗ q.[α⊓κ]
    |}%I.
  Next Obligation. by iIntros (? ty tid [|[[]|][]]) "H". Qed.
  (* This is to a large extend copy-pasted from RWLock's write guard. *)
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT #? Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT Hb") as (β) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ H]"; first done.
    iMod (bor_sep with "LFT H") as "[Hβty H]"; first done.
    iMod (bor_sep with "LFT H") as "[_ H]"; first done.
    iMod (bor_persistent with "LFT Hβty Htok") as "[#Hβty Htok]"; [done|].
    iMod (bor_persistent with "LFT Hαβ Htok") as "[#Hαβ $]"; first done.
    iExists _. iFrame "H↦". iApply delay_sharing_nested; try done.
    { iNext. iApply lft_incl_trans; [|done]. iApply lft_intersect_incl_l. }
    iApply (bor_shorten with "[] H"). iApply lft_intersect_incl_r.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (l') "[#Hf #H]".
    iExists _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance mutexguard_type_contractive α : TypeContractive (mutexguard α).
  Proof.
    split.
    - apply (type_lft_morphism_add _ α [α] []) => ?.
      + iApply lft_equiv_refl.
      + by rewrite elctx_interp_app elctx_interp_ty_outlives_E /elctx_interp /=
                   left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid [|[[]|][]]=>//=.
      repeat (apply equiv_dist, lft_incl_equiv_proper_r, Hl ||
              apply Ho || apply dist_S, Ho || f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. simpl.
      repeat (apply Hs || f_contractive || f_equiv).
  Qed.

  Global Instance mutexguard_ne α : NonExpansive (mutexguard α).
  Proof. solve_ne_type. Qed.

  Global Instance mutexguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) mutexguard.
  Proof.
    intros α1 α2 Hα ty1 ty2 Hty. generalize Hty. rewrite eqtype_unfold.
    iIntros (Hty' q) "HL". iDestruct (Hty' with "HL") as "#Hty".
    clear Hty'. iDestruct (Hα with "HL") as "#Hα".
    iIntros "!# #HE". iDestruct ("Hα" with "HE") as "{Hα} Hα".
    iDestruct ("Hty" with "HE") as "(%&[Hl1 Hl2]&#Ho&#Hs) {HE Hty}".
    iSplit; [done|iSplit; [|iSplit; iModIntro]].
    - by iApply lft_intersect_mono.
    - iIntros (tid [|[[]|][]]) "H //=".
      iDestruct "H" as (β) "(#H⊑ & #Hl & #Hinv & Hown)".
      iExists β. iSplit; [|iSplit; [|iSplit]].
      + by iApply lft_incl_trans.
      + by iApply lft_incl_trans.
      + iApply (at_bor_shorten with "Hα").
        iApply (at_bor_iff with "[] Hinv"). iNext.
        iApply lock_proto_iff_proper. iApply bor_iff_proper. iNext.
        iApply heap_mapsto_pred_iff_proper.
        iModIntro; iIntros; iSplit; iIntros; by iApply "Ho".
      + iApply bor_iff; last done. iNext.
        iApply heap_mapsto_pred_iff_proper.
        iModIntro; iIntros; iSplit; iIntros; by iApply "Ho".
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "H". iExists l'.
      iDestruct "H" as "[$ #H]". iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. done. iApply lft_incl_refl. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. done. iApply lft_incl_refl.
      by iApply "Hs".
  Qed.

  Global Instance mutexguard_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E  L) mutexguard.
  Proof. intros ??[]???. split; by apply mutexguard_mono. Qed.

  Global Instance mutexguard_sync α ty :
    Sync ty → Sync (mutexguard α ty).
  Proof.
    move=>?????/=. apply bi.exist_mono=>?. do 7 f_equiv.
    by rewrite sync_change_tid.
  Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for MutexGuard. We can
     prove this for our spinlock implementation, however. *)
  Global Instance mutexguard_send α ty :
    Send ty → Send (mutexguard α ty).
  Proof.
    iIntros (??? [|[[]|][]]) "H"; try done. simpl. iRevert "H".
    iApply bi.exist_mono. iIntros (κ); simpl. apply bi.equiv_spec.
    repeat match goal with
           | |- (ty_own _ _ _) ≡ (ty_own _ _ _) => by apply send_change_tid'
           | |- _ => f_equiv
           end.
  Qed.
End mguard.

Section code.
  Context `{!typeG Σ}.

  Lemma mutex_acc E l ty tid q α κ :
    ↑lftN ⊆ E → ↑mutexN ⊆ E →
    let R := (&{κ}((l +ₗ 1) ↦∗: ty_own ty tid))%I in
    lft_ctx -∗ &at{α,mutexN}(lock_proto l R) -∗ α ⊑ κ -∗
    □ ((q).[α] ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ (q).[α])).
  Proof.
    (* FIXME: This should work: iIntros (?? R). *) intros ?? R.
    iIntros "#LFT #Hshr #Hlincl !# Htok".
    iMod (at_bor_acc_tok with "LFT Hshr Htok") as "[Hproto Hclose1]"; [done..|].
    iMod (fupd_intro_mask') as "Hclose2"; last iModIntro; first solve_ndisj.
    iFrame. iIntros "Hproto". iMod "Hclose2" as "_".
    iMod ("Hclose1" with "Hproto") as "$". done.
  Qed.

  Definition mutex_lock : val :=
    funrec: <> ["mutex"] :=
      let: "m" := !"mutex" in
      let: "guard" := new [ #1 ] in
      acquire ["m"];;
      "guard" +ₗ #0 <- "m";;
      delete [ #1; "mutex" ];; return: ["guard"].

  Lemma mutex_lock_type ty :
    typed_val mutex_lock (fn(∀ α, ∅; &shr{α}(mutex ty)) → mutexguard α ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
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

  Definition mutexguard_derefmut : val :=
    funrec: <> ["g"] :=
      let: "g'" := !"g" in
      let: "m" := !"g'" in
      letalloc: "r" <- ("m" +ₗ #1) in
      delete [ #1; "g"];; return: ["r"].

  Lemma mutexguard_derefmut_type ty :
    typed_val mutexguard_derefmut
              (fn(∀ '(α, β), ∅; &uniq{α}(mutexguard β ty)) → &uniq{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
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

  Definition mutexguard_deref : val := mutexguard_derefmut.

  Lemma mutexguard_deref_type ty :
    typed_val mutexguard_derefmut
              (fn(∀ '(α, β), ∅; &shr{α}(mutexguard β ty)) → &shr{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>g. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (g'); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hg' _]]".
    rewrite !tctx_hasty_val [[g]]lock /=.
    destruct g' as [[|lg|]|]; try done. simpl.
    iDestruct "Hg'" as (lm) "[Hlg Hshr]".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hlg Hα1") as (qlx') "[H↦ Hclose2]"; first done.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose3)";
      [solve_typing..|].
    iDestruct (lft_intersect_acc with "Hβ Hα2") as (qβα) "[Hα2β Hclose4]".
    wp_bind (!_)%E. iApply (wp_step_fupd with "[Hshr Hα2β]");
         [|by iApply ("Hshr" with "[] Hα2β")|]; first done.
    wp_read. iIntros "[#Hshr Hα2β] !>". wp_let.
    iDestruct ("Hclose4" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hclose3" with "Hβ HL") as "HL".
    iMod ("Hclose2" with "H↦") as "Hα1".
    iMod ("Hclose1" with "[$] HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ g ◁ own_ptr _ _; #lm +ₗ #1 ◁ &shr{α} ty ]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iApply ty_shr_mono; last done.
      iApply lft_incl_glb; last by iApply lft_incl_refl. done. }
    iApply type_letalloc_1; [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutexguard_drop : val :=
    funrec: <> ["g"] :=
      let: "m" := !"g" in
      release ["m"];;
      delete [ #1; "g" ];;
      let: "r" := new [ #0 ] in return: ["r"].

  Lemma mutexguard_drop_type ty :
    typed_val mutexguard_drop (fn(∀ α, ∅; mutexguard α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
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
End code.
