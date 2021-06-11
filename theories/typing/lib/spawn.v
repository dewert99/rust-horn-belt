From iris.proofmode Require Import tactics.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition spawnN := lrustN .@ "spawn".

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition join_future {𝔄} (ty: type 𝔄) (Φ: pred' 𝔄) (v: val) : iProp Σ :=
    ∀tid, ∃vπ d, ⧖d ∗ (box ty).(ty_own) vπ d tid [v] ∗ ⟨π, Φ (vπ π)⟩.

  Program Definition join_handle {𝔄} (ty: type 𝔄) : type (predₛ 𝔄) := {|
    ty_size := 1;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own Φπ _ _ vl := [loc[l] := vl] ∃Φ, ⌜Φπ = const Φ⌝ ∗
      join_handle spawnN l (join_future ty Φ);
    ty_shr Φπ _ _ _ _ := ∃Φ, ⌜Φπ = const Φ⌝;
  |}%I.
  Next Obligation. iIntros (?????[|[[]|][]]) "* ? //". Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation.
    iIntros "*% LFT _ Bor κ !>". iApply step_fupdN_full_intro.
    setoid_rewrite by_just_loc_ex.
    iMod (bor_acc with "LFT Bor κ") as "[(%& ↦ &%&>->&%&>->& join) ToBor]"; [done|].
    iMod ("ToBor" with "[↦ join]") as "[_ $]"; [|by iExists _]. iNext.
    iExists _. iFrame "↦". iExists _. iSplitR; [done|]. iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (??????[|[[]|][]]) "*% _ _ join //". iIntros "$".
    iDestruct "join" as (?->) "join". iApply step_fupdN_full_intro.
    iIntros "!>!>". iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "* _ _ _ _ (%&->) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros. by iExists _.
  Qed.

  Global Instance join_handle_ne {𝔄} : NonExpansive (@join_handle 𝔄).
  Proof. rewrite /join_handle /join_future. solve_ne_type. Qed.

  Global Instance join_handle_type_contractive {𝔄} : TypeContractive (@join_handle 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |done]=>/= *.
    rewrite /join_future. Opaque box. do 15 f_equiv. by apply box_type_contractive.
  Qed.

  Global Instance join_handle_send {𝔄} (ty: type 𝔄) : Send (join_handle ty).
  Proof. done. Qed.
  Global Instance join_handle_sync {𝔄} (ty: type 𝔄) : Sync (join_handle ty).
  Proof. done. Qed.

  Lemma join_handle_leak {𝔄} (ty: type 𝔄) E L : leak E L (join_handle ty) (const True).
  Proof. apply leak_just. Qed.

  Lemma join_handle_real {𝔄} (ty: type 𝔄) E L : real E L (join_handle ty) id.
  Proof.
    split.
    - iIntros (?????[|[[]|][]]) "_ _ _ L join //". iFrame "L".
      iDestruct "join" as (?->) "join". iApply step_fupdN_full_intro.
      iIntros "!>!>". iSplitR; [by iExists _|]. iExists _. by iFrame.
    - iIntros "*% _ _ $ % !>!>!>". by iApply step_fupdN_full_intro.
  Qed.

  Definition forward_pred {A B} (f: A → B) (Φ: pred' A) (b: B) : Prop :=
    ∃a, b = f a ∧ Φ a.

  Lemma join_handle_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f →
    subtype E L (join_handle ty) (join_handle ty') (forward_pred f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "#Incl". iPoseProof "Incl" as "#(%&?&_)".
    do 2 (iSplit; [done|]). iSplit; iModIntro; last first.
    { iIntros "* (%&->)". iExists _. iPureIntro. by fun_ext=>/=. }
    iIntros (?? tid' [|[[]|][]]) "join //". iDestruct "join" as (?->) "join".
    iExists _. iSplit. { iPureIntro. by fun_ext=>/=. }
    iApply (join_handle_impl with "[] join"). iIntros "!>% fut %tid".
    iDestruct ("fut" $! tid) as (??) "(⧖ & box & #Obs)". iExists _, _.
    iFrame "⧖". iSplitL.
    { iDestruct (box_type_incl with "Incl") as "(_&_& InO &_)". by iApply "InO". }
    iApply proph_obs_impl; [|done]=>/= ??. by eexists _.
  Qed.

  Lemma join_handle_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g →
    eqtype E L (join_handle ty) (join_handle ty') (forward_pred f) (forward_pred g).
  Proof. move=> [??]. split; by apply join_handle_subtype. Qed.

(*
  Definition spawn (call_once : val) : val :=
    fn: ["f"] :=
      let: "call_once" := call_once in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "call_once" ["f":expr] in
                            finish ["c"; "r"]] in
      letalloc: "r" <- "join" in
      return: ["r"].

  Lemma spawn_type fty retty call_once `(!Send fty, !Send retty) :
    typed_val call_once (fn(∅; fty) → retty) → (* fty : FnOnce() -> retty, as witnessed by the impl call_once *)
    let E ϝ := ty_outlives_E fty static ++ ty_outlives_E retty static in
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
    fn: ["c"] :=
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
*)
End spawn.

Global Hint Resolve join_handle_leak join_handle_real
  join_handle_subtype join_handle_eqtype : lrust_typing.
