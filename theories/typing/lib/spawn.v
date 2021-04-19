From iris.proofmode Require Import tactics.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition spawnN := lrustN .@ "spawn".

Section join_handle.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition join_inv (ty : type) (v : val) :=
    (∀ tid, tctx_elt_interp tid (v ◁ box ty))%I.

  Program Definition join_handle (ty : type) :=
    {| ty_size := 1; ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own _ _ vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => lang.lib.spawn.join_handle spawnN l (join_inv ty)
         | _ => False
         end%I;
       ty_shr κ _ l := True%I |}.
  Next Obligation. by iIntros (ty depth tid [|[[]|][]]) "H". Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "* _ _ _ _ ? !>". iApply step_fupdN_intro; [done|by iFrame].
  Qed.
  Next Obligation. iIntros (?) "**"; auto. Qed.

  Lemma join_handle_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (join_handle ty1) (join_handle ty2).
  Proof.
    iIntros "#Hincl". iSplit; first done. iSplit; [|iSplit; iModIntro].
    - iDestruct "Hincl" as "[_ [Hout _]]". by iApply "Hout".
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      simpl. iApply (join_handle_impl with "[] Hvl"). clear tid.
      iIntros "!> * Hown" (tid). iSpecialize ("Hown" $! tid).
      rewrite /tctx_elt_interp /=. iDestruct "Hown" as (??) "(?&?&?)".
      iExists _, _. iFrame.
      iDestruct (box_type_incl with "Hincl") as "{Hincl} (_ & _ & Hincl & _)".
      iApply "Hincl". done.
    - iIntros "* _". auto.
  Qed.

  Global Instance join_handle_mono E L :
    Proper (subtype E L ==> subtype E L) join_handle.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!> #HE". iApply join_handle_subtype. iApply "Hsub"; done.
  Qed.
  Global Instance join_handle_proper E L :
    Proper (eqtype E L ==> eqtype E L) join_handle.
  Proof. intros ??[]. by split; apply join_handle_mono. Qed.

  Global Instance join_handle_type_contractive : TypeContractive join_handle.
  Proof.
    split=>//.
    - apply (type_lft_morphism_add _ static [] [])=>?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /elctx_interp /= left_id right_id.
    - move=> ??? Hsz ?? Ho ??? [|[[|l|]|] []] //=.
      rewrite /join_inv /tctx_elt_interp /box /own_ptr
              ![X in X {| ty_own := _ |}]/ty_own Hsz.
      repeat (apply Ho || f_contractive || f_equiv).
  Qed.

  Global Instance join_handle_ne : NonExpansive join_handle.
  Proof.
    intros n ty1 ty2 Hty12. constructor; [done|apply Hty12..| |done].
    intros depth tid vs.
    rewrite /join_handle /join_inv /tctx_elt_interp /box /own_ptr
            ![X in X {| ty_own := _ |}]/ty_own.
    repeat (apply Hty12 || f_equiv).
  Qed.

  Global Instance join_handle_send ty :
    Send (join_handle ty).
  Proof. iIntros (????) "$ //". Qed.
  Global Instance join_handle_sync ty : Sync (join_handle ty).
  Proof. iIntros (????) "_ //". Qed.
End join_handle.

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition spawn (call_once : val) : val :=
    funrec: <> ["f"] :=
      let: "call_once" := call_once in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "call_once" ["f":expr] in
                            finish ["c"; "r"]] in
      letalloc: "r" <- "join" in
      return: ["r"].

  Lemma spawn_type fty retty call_once `(!Send fty, !Send retty) :
    typed_val call_once (fn(∅; fty) → retty) → (* fty : FnOnce() -> retty, as witnessed by the impl call_once *)
    let E ϝ := ty_outlv_E fty static ++ ty_outlv_E retty static in
    typed_val (spawn call_once) (fn(E; fty) → join_handle retty).
  Proof.
    intros Hf ? E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>env. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (f'). simpl_subst.
    iApply (type_let _ _ _ _ ([f' ◁ _; env ◁ _])
                     (λ j, [j ◁ join_handle retty])); try solve_typing; [|].
    { (* The core of the proof: showing that spawn is safe. *)
      iIntros (tid) "#LFT #TIME #HE $ $ [Hf' [Henv _]]". rewrite !tctx_hasty_val [fn _]lock.
      iApply wp_fupd. iApply (spawn_spec _ (join_inv retty) with "[-]"); last first.
      { iIntros "!> *". rewrite tctx_interp_singleton tctx_hasty_val.
        iIntros "?". iExists 0%nat. iMod persistent_time_receipt_0 as "$". by iFrame. }
      simpl_subst. iIntros (c) "Hfin". iMod na_alloc as (tid') "Htl". wp_let. wp_let.
      iDestruct "Hf'" as (?) "[_ Hf']".
      unlock. iApply (type_call_iris _ [] () [_] with "LFT TIME HE Htl [] Hf' [Henv]");
      (* The `solve_typing` here shows that, because we assume that `fty` and `retty`
         outlive `static`, the implicit requirmeents made by `call_once` are satisifed. *)
        [solve_typing|iApply (lft_tok_static 1%Qp)| |].
      - iDestruct "Henv" as (?) "?".
        rewrite big_sepL_singleton tctx_hasty_val send_change_tid. eauto.
      - iIntros (r depth') "Htl _ #Hdepth' Hret".
        wp_rec. iApply (finish_spec with "[$Hfin Hret]"); last auto.
        iIntros (?). rewrite tctx_hasty_val. iExists _. iFrame "Hdepth'".
        by iApply @send_change_tid. }
    iIntros (v). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition join : val :=
    funrec: <> ["c"] :=
      let: "c'" := !"c" in
      let: "r" := spawn.join ["c'"] in
      delete [ #1; "c"];; return: ["r"].

  Lemma join_type retty :
    typed_val join (fn(∅; join_handle retty) → retty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>c. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (c'); simpl_subst.
    iApply (type_let _ _ _ _ ([c' ◁ _])
                             (λ r, [r ◁ box retty])); try solve_typing; [|].
    { iIntros (tid) "#LFT #TIME _ $ $".
      rewrite tctx_interp_singleton tctx_hasty_val. iIntros "Hc".
      iDestruct "Hc" as (depth) "[Hdepth Hc]".
      destruct c' as [[|c'|]|]; try done.
      iApply (join_spec with "Hc"). iNext. iIntros "* Hret".
      by rewrite tctx_interp_singleton. }
    iIntros (r); simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End spawn.
