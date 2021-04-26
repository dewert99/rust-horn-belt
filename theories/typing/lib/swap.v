From iris.proofmode Require Import tactics.
From lrust.lang.lib Require Import swap.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section swap.
  Context `{!typeG Σ}.

  Definition swap ty : val :=
    funrec: <> ["p1"; "p2"] :=
      let: "p1'" := !"p1" in
      let: "p2'" := !"p2" in
      swap ["p1'"; "p2'"; #ty.(ty_size)];;
      delete [ #1; "p1"];; delete [ #1; "p2"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma swap_type τ :
    typed_val (swap τ) (fn(∀ α, ∅; &uniq{α} τ, &uniq{α} τ) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret p).
      inv_vec p=>p1 p2. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (p1'). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (p2'). simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL Hk (H2 & H2' & H1 & H1' & _)".
    rewrite !tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose)";
      [solve_typing..|].
    iDestruct "H1" as (depth1) "[#Hdepth1 H1]".
    iDestruct "H1'" as ([|depth1']) "[#Hdepth1' H1']"; try iDestruct "H1'" as "[_ []]".
    iDestruct "H2" as (depth2) "[#Hdepth2 H2]".
    iDestruct "H2'" as ([|depth2']) "[#Hdepth2' H2']"; try iDestruct "H2'" as "[_ []]".
    iDestruct (uniq_is_ptr with "H1'") as (l1) "#H1eq". iDestruct "H1eq" as %[=->].
    iDestruct "H1'" as "[#H1o H1']". iDestruct "H1'" as (depth1'' γ1 ?) "[H◯1 H1']".
    iMod (bor_acc with "LFT H1' Hα1") as "[H1' Hclose1]"=>//.
    iDestruct "H1'" as (depth1''0) "(>H●1 & >#Hdepth1'' & H1')". iDestruct "H1'" as (vl1) "[>H↦1 H1']".
    iDestruct (τ.(ty_size_eq) with "H1'") as "#>%".
    iDestruct (uniq_is_ptr with "H2'") as (l2) "#H2eq". iDestruct "H2eq" as %[=->].
    iDestruct "H2'" as "[#H2o H2']". iDestruct "H2'" as (depth2'' γ2 ?) "[H◯2 H2']".
    iMod (bor_acc with "LFT H2' Hα2") as "[H2' Hclose2]"=>//.
    iDestruct "H2'" as (depth2''0) "(>H●2 & >#Hdepth2'' & H2')". iDestruct "H2'" as (vl2) "[>H↦2 H2']".
    iDestruct (τ.(ty_size_eq) with "H2'") as "#>%".
    wp_apply (wp_swap with "[$H↦1 $H↦2]"); try lia. iIntros "[H↦1 H↦2]". wp_seq.
    iDestruct (own_valid_2 with "H●1 H◯1") as %->%excl_auth_agree_L.
    iDestruct (own_valid_2 with "H●2 H◯2") as %->%excl_auth_agree_L.
    iMod (own_update_2 with "H●1 H◯1") as "[H●1 H◯1]"; [by apply excl_auth_update|].
    iMod (own_update_2 with "H●2 H◯2") as "[H●2 H◯2]"; [by apply excl_auth_update|].
    iMod ("Hclose" with "[>-Hna HL H1 H2 Hk] HL") as "HL".
    { iMod ("Hclose1" with "[H2' H↦1 H●1]") as "[_ $]".
      { iExists depth2''. iFrame "∗#". by iExists _; iFrame. }
      iMod ("Hclose2" with "[H1' H↦2 H●2]") as "[_ $]".
      { iExists depth1''. iFrame "∗#". by iExists _; iFrame. }
      done. }
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ p1 ◁ box (uninit 1); p2 ◁ box (uninit 1) ]
      with "[] LFT TIME HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
      iSplitL "H1"; auto with iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply (type_new _); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End swap.
