From iris.proofmode Require Import tactics.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
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
      ∃(vπ: proph 𝔄) d, ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ ty.(ty_own) vπ d tid vl;
    ty_shr Φπ _ κ tid l := ∃Φ, ⌜Φπ = const Φ⌝ ∗
      &na{κ, tid, shrN.@l}
        (∃(vπ: proph 𝔄) d, ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ l ↦∗: ty.(ty_own) vπ d tid)
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

  (** The next couple functions essentially show owned-type equalities, as they
      are all different types for the identity function. *)

  (** Constructing a cell. *)

  Lemma tctx_cell_new {𝔄 𝔅l} Φ (ty: type 𝔄) n p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ own_ptr n ty +:: T) (p ◁ own_ptr n (cell ty) +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (Φ -:: bl)).
  Proof.
    split. { move=>/= ???[??]/=. by f_equiv. }
    iIntros (??[??]?) "_ _ _ _ $ /=[p T] ? !>". iExists (const Φ -:: _).
    iFrame "T". iSplit; [|by iApply proph_obs_impl; [|done]=> ?[_?]].
    iDestruct "p" as ([[]|][|]?) "[? own]"=>//. iExists _, _.
    do 2 (iSplit; [done|]). iDestruct "own" as "[(%& ↦ & ty) $]". iNext.
    iExists _. iFrame "↦". iExists _. iSplit; [done|]. iExists _, _.
    iSplit; [by iApply proph_obs_impl; [|done]=> ?[? _]|]. iFrame.
  Qed.

  Definition cell_new: val := fn: ["x"] := return: ["x"].

  Lemma cell_new_type {𝔄} Φ (ty: type 𝔄) :
    typed_val cell_new (fn(∅; ty) → cell ty) (λ post '-[a], Φ a ∧ post Φ).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_jump; [solve_typing| |].
      { eapply tctx_extract_ctx_elt; [apply tctx_cell_new|solve_typing]. }
      solve_typing. }
    by move=> ?[?[]]?/=.
  Qed.

  (** The Other Direction: Getting Ownership out of a Cell. *)

  Lemma tctx_cell_into_inner {𝔄 𝔅l} (ty: type 𝔄) n p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ own_ptr n (cell ty) +:: T) (p ◁ own_ptr n ty +:: T)
      (λ post '(Φ -:: bl), ∀a: 𝔄, Φ a → post (a -:: bl)).
  Proof.
    split. { move=>/= ?? Eq [??]/=. by do 2 (apply forall_proper=> ?). }
    iIntros (??[??]?) "_ _ _ _ $ /=[p T] Obs".
    iDestruct "p" as ([[]|][|]?) "[? own]"=>//.
    iDestruct "own" as "[(%& ↦ & (%&>->& Big)) †]".
    iMod (bi.later_exist_except_0 with "Big") as (vπ ?) "(>Obs' &>?& ?)".
    iCombine "Obs Obs'" as "Obs". iModIntro. iExists (vπ -:: _). iFrame "T".
    iSplit; last first. { iApply proph_obs_impl; [|done]=>/= ? [Imp ?]. by apply Imp. }
    iExists _, _. do 2 (iSplit; [done|]). iFrame "†". iNext. iExists _. iFrame.
  Qed.

  Definition cell_into_inner: val := fn: ["x"] := return: ["x"].

  Lemma cell_into_inner_type {𝔄} (ty: type 𝔄) :
    typed_val cell_into_inner (fn(∅; cell ty) → ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_jump; [solve_typing| |].
      { eapply tctx_extract_ctx_elt; [apply tctx_cell_into_inner|solve_typing]. }
      solve_typing. }
    by move=> ?[?[]]?/=.
  Qed.

  (** Conversion under [box] *)

  Lemma tctx_cell_from_box {𝔄 𝔅l} Φ (ty: type 𝔄) n p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ own_ptr n (box ty) +:: T) (p ◁ own_ptr n (box (cell ty)) +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (Φ -:: bl)).
  Proof.
    split. { move=>/= ???[??]/=. by f_equiv. }
    iIntros (??[??]?) "_ _ _ _ $ /=[p T] ? !>". iExists (const Φ -:: _).
    iFrame "T". iSplit; [|by iApply proph_obs_impl; [|done]=> ?[_?]].
    iDestruct "p" as ([[]|][|d]?) "[? obox]"=>//.
    iExists _, _. do 2 (iSplit; [done|]). iDestruct "obox" as "[(%vl & ↦ & box) $]".
    iNext. iExists _. iFrame "↦". case d as [|]=>//. case vl as [|[[]|][]]=>//.
    iDestruct "box" as "[(%& ↦ & ty) $]". iNext. iExists _. iFrame "↦".
    iExists _. iSplit; [done|]. iExists _, _.
    iSplit; [by iApply proph_obs_impl; [|done]=> ?[? _]|]. iFrame "ty".
    iApply persistent_time_receipt_mono; [|done]. lia.
  Qed.

  Definition cell_from_box: val := fn: ["x"] := return: ["x"].

  Lemma cell_from_box_type {𝔄} Φ (ty: type 𝔄) :
    typed_val cell_from_box (fn(∅; box ty) → box (cell ty))
      (λ post '-[a], Φ a ∧ post Φ).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_jump; [solve_typing| |].
      { eapply tctx_extract_ctx_elt; [apply tctx_cell_from_box|solve_typing]. }
      solve_typing. }
    by move=> ?[?[]]?/=.
  Qed.

  Definition cell_into_box: val := fn: ["x"] := Skip;; return: ["x"].

  Lemma cell_into_box_type {𝔄} (ty: type 𝔄) :
    typed_val cell_into_box (fn(∅; box (cell ty)) → box ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[x[]]. simpl_subst.
    iIntros (?[?[]]?) "LFT #TIME PROPH UNIQ E Na L C /=[p _] Obs".
    rewrite tctx_hasty_val.  iDestruct "p" as ([|d]) "[_ bbox]"=>//.
    case x as [[|l|]|]=>//. iDestruct "bbox" as "[(%vl & ↦ & box) †]".
    wp_bind Skip. iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    wp_seq. iIntros "⧗". wp_seq. case d=>// ?. case vl as [|[[]|][]]=>//=.
    iDestruct "box" as "[(%& >↦' &%&>->& Big) †']".
    iMod (bi.later_exist_except_0 with "Big") as (??) "(>Obs' & >⧖ & ty)".
    iCombine "Obs Obs'" as "#?".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖") as "#⧖"; [done|].
    iApply (type_type +[#l ◁ box (box ty)] -[_] with
      "[] LFT TIME PROPH UNIQ E Na L C [↦ † ↦' †' ty] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplit; [|done]. rewrite (tctx_hasty_val #l). iExists _. iFrame "⧖".
      iFrame "†". iNext. iExists _. iFrame "↦ †'". iNext. iExists _. iFrame.
    - iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  (** Conversion under [&uniq{α}] *)

  Definition cell_from_uniq: val := fn: ["x"] := Skip;; return: ["x"].

  (* In this rule, we lose the prophecy information of the input.
    We need a stronger model of prophecy to know that
    the prophetic value of the input satisfies [Φ']. *)
  Lemma cell_from_uniq_type {𝔄} (Φ: pred' 𝔄) ty :
    typed_val cell_from_uniq (fn<α>(∅; &uniq{α} ty) → &uniq{α} (cell ty))
      (λ post '-[(a, _)], Φ a ∧ ∀Φ': pred' 𝔄, post (Φ, Φ')).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[x[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT _ #PROPH #UNIQ E Na L C /=[x _] #?".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    rewrite tctx_hasty_val. iDestruct "x" as ([|]) "[#⧖ box]"=>//.
    case x as [[|x|]|]=>//. iDestruct "box" as "[(%vl & >↦ & [#? uniq]) †]".
    do 2 wp_seq. case vl as [|[[]|][]]=>//=.
    iDestruct "uniq" as (? i [? _]) "[Vo Bor]". set ξ := PrVar _ i.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as
      "[(%&%&(%& >↦' & ty)& >#⧖' & Pc) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iMod (uniq_intro (const (Φ: predₛ 𝔄)) with "PROPH UNIQ") as
      (j) "[Vo' Pc']"; [done|]. set ζ := PrVar _ j.
    iMod ("ToBor" with "[Vo Pc] [↦' ty Pc']") as "[Bor α]"; last first.
    - iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton. do 2 wp_seq.
      iApply ("C" $! [# #x] -[λ π, (_, π ζ)] with "Na L [↦ † Vo' Bor] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= π. by case (vπ π)=> ? _[_ ?]. }
      iSplit; [|done]. rewrite tctx_hasty_val. iExists _. iFrame "⧖ †".
      iNext. iExists _. iFrame "↦". iSplit; [done|]. iExists _, _. by iFrame.
    - iNext. iExists _, _. iFrame "⧖' Pc'". iExists _. iFrame "↦'".
      iExists _. iSplit; [done|]. iExists _, _. iFrame "ty ⧖'".
      iApply proph_obs_impl; [|done]=>/= π. by case (vπ π)=>/= ??[? _].
    - iIntros "!> (%&%&(%&?&(%&>->&%&%&_& ⧖'' &?))&_&_)". iExists _, _.
      iFrame "⧖''". iSplitR "Vo Pc"; [iExists _; by iFrame|].
      iMod (uniq_update with "UNIQ Vo Pc") as "[_ $]"; [solve_ndisj|done].
  Qed.

  Definition cell_get_uniq: val := fn: ["x"] := Skip;; return: ["x"].

  (* The final invariant of [&uniq{α} (cell ty)] should be trivial,
    because [&uniq{α} ty] does not restrict the target value *)
  Lemma cell_get_uniq_type {𝔄} (ty: type 𝔄) :
    typed_val cell_get_uniq (fn<α>(∅; &uniq{α} (cell ty)) → &uniq{α} ty)
      (λ post '-[(Φ, Φ')], ∀a a': 𝔄, Φ a → Φ' = const True → post (a, a')).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[x[]]. simpl_subst.
    iIntros (?[vπ[]]?) "LFT #TIME #PROPH #UNIQ E Na L C /=[x _] Obs".
    rewrite tctx_hasty_val. iDestruct "x" as ([|]) "[_ box]"=>//. case x as [[|x|]|]=>//.
    iDestruct "box" as "[(%vl & ↦ & [#? uniq]) †]". wp_bind Skip.
    iApply (wp_cumulative_time_receipt with "TIME"); [done|]. wp_seq.
    iIntros "⧗". wp_seq. case vl as [|[[]|][]]=>//.
    iDestruct "uniq" as (??[? Eq]) "[Vo Bor]". set ξ := PrVar _ i.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as
      "[(%&%&(%& >↦' &%&>->& Big)&_& Pc) ToBor]"; [done|].
    iMod (bi.later_exist_except_0 with "Big") as (aπ ?) "(>Obs' & >#⧖ & ty)".
    iCombine "Obs Obs'" as "Obs".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖") as "#⧖S"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (Eq' <-) "[Vo Pc]".
    iMod (uniq_preresolve ξ [] (const (const True)) 1%Qp with "PROPH Vo Pc []")
      as "(Obs' &_& ToPc)"; [done..|]. iCombine "Obs' Obs" as "#?".
    iMod (uniq_intro aπ with "PROPH UNIQ") as (j) "[Vo' Pc']"; [done|].
    set ζ := PrVar _ j. have ?: Inhabited 𝔄 := populate (aπ inhabitant).
    iMod ("ToBor" with "[ToPc] [↦' ty Pc']") as "[Bor α]"; last first.
    - iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton. do 2 wp_seq.
      iApply ("C" $! [# #x] -[λ π, (_, π ζ)] with "Na L [↦ † Vo' Bor] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π) (equal_f Eq' π)=>/=.
        case (vπ π)=>/= ??<-->[->[Imp ?]]. by apply Imp. }
      iSplit; [|done]. rewrite tctx_hasty_val. iExists _. iFrame "⧖S †". iNext.
      iExists _. iFrame "↦". iSplit; [done|]. iExists _, _. iSplit; [done|]. iFrame.
    - iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame.
    - iIntros "!> (%&%&((%& ↦ & ty)& #⧖' & Pc')) !>!>". iExists _, _.
      iFrame "⧖'". iSplitR "ToPc"; [|iApply "ToPc"; by iApply proph_eqz_eq].
      iExists _. iFrame "↦". iExists _. iSplit; [done|]. iExists _, _.
      iFrame "⧖' ty". by iApply proph_obs_true.
  Qed.

  (** Updating the Invariant *)

  Lemma tctx_cell_set_inv {𝔄 𝔅l} (Φ: pred' 𝔄) ty n p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ own_ptr n (cell ty) +:: T) (p ◁ own_ptr n (cell ty) +:: T)
      (λ post '(Φ' -:: bl), (∀a: 𝔄, Φ' a → Φ a) ∧ post (Φ -:: bl)).
  Proof.
    eapply tctx_incl_impl.
    - eapply tctx_incl_trans; [apply tctx_cell_into_inner|apply (tctx_cell_new Φ)].
    - move=> ?[??][Imp ?]??. split; by [apply Imp|].
    - move=>/= ???[??]. by f_equiv.
  Qed.

  Definition cell_set_inv: val :=
    fn: ["x"] := let: "r" := new [ #0] in delete [ #1; "x"];; return: ["r"].

  Lemma cell_set_inv_type {𝔄} (Φ: pred' 𝔄) ty :
    typed_val cell_set_inv (fn<α>(∅; &uniq{α} (cell ty)) → ())
      (λ post '-[(Φ', Φ'')], (∀a: 𝔄, Φ' a → Φ a) ∧ (Φ'' = Φ → post ())).
  Proof.
    eapply type_fn; [solve_typing|]=> α ??[x[]]. simpl_subst.
    iIntros (?[vπ[]]?) "LFT _ PROPH UNIQ E Na L C /=[x _] Obs".
    rewrite tctx_hasty_val. iDestruct "x" as ([|]) "[_ box]"=>//. case x as [[|x|]|]=>//.
    iDestruct "box" as "[(%& ↦x & [_ uniq]) †x]".
    wp_bind (new _). iApply wp_new; [done..|]. iIntros "!>" (?) "[†r ↦r]". wp_seq.
    case vl as [|[[]|][]]=>//.
    iDestruct "uniq" as (? i [? Eq']) "[Vo Bor]". set ξ := PrVar _ i.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[Big Toα]"; [done|].
    wp_bind (delete _). iApply (wp_delete with "[$↦x †x]");
      [done|by rewrite freeable_sz_full|].
    iIntros "!> _". do 3 wp_seq.
    iDestruct "Big" as (??) "((%& ↦ &(%&->&(%&%&(Obs' & #⧖ & ty))))&_& Pc)".
    iDestruct (uniq_agree with "Vo Pc") as %[Eq <-].
    iMod (uniq_update ξ (const Φ) with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod (uniq_resolve _ [] 1%Qp with "PROPH Vo Pc []") as "(Obs'' & Pc &_)"; [done..|].
    iCombine "Obs Obs'" as "Obs". iCombine "Obs'' Obs" as "#?".
    iMod ("Toα" with "[↦ ty Pc]") as "[_ α]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame "↦". iExists _.
      iSplit; [done|]. iExists _, _. iFrame "⧖ ty". iApply proph_obs_impl; [|done]=>/= π.
      move: (equal_f Eq π)=>/=. case (vπ π)=>/= ??->[_[[Imp _]?]]. by apply Imp. }
    iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const ()] with "Na L [↦r †r] []").
    - iSplit; [|done]. rewrite tctx_hasty_val -freeable_sz_full. iExists _.
      iFrame "⧖ †r". iNext. iExists _. iFrame "↦r". by iExists (const -[]).
    - iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π) (equal_f Eq' π)=>/=.
      case (vπ π)=>/= ??->->[->[[_ Imp]_]]. by apply Imp.
  Qed.

  (** Reading from a Cell *)

  Definition cell_get {𝔄} (ty: type 𝔄) : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      letalloc: "r" <-{ty.(ty_size)} !"x'" in
      delete [ #1; "x"];; return: ["r"].

  (* Interestingly, this is syntactically well-typed: we do not need
     to enter the model. *)
  Lemma cell_get_type {𝔄} (ty: type 𝔄) `{!Copy ty} :
    typed_val (cell_get ty) (fn<α>(∅; &shr{α} (cell ty)) → ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [solve_typing|]=> ???[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
      iApply (type_letalloc_n (cell ty)); [solve_extract|solve_typing|].
      intro_subst. iApply typed_body_tctx_incl; [apply tctx_cell_into_inner|].
      iApply type_delete; [solve_extract|done|done|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[?[]]/=.
  Qed.

  (** Writing to a Cell *)

  Definition cell_replace {𝔄} (ty: type 𝔄) : val :=
    fn: ["c"; "x"] :=
      let: "c'" := !"c" in
      letalloc: "r" <-{ty.(ty_size)} !"c'" in
      "c'" <-{ty.(ty_size)} !"x";;
      delete [ #1; "c"];; delete [ #ty.(ty_size); "x"];; return: ["r"].

  Lemma cell_replace_type {𝔄} (ty: type 𝔄) :
    typed_val (cell_replace ty) (fn<α>(∅; &shr{α} (cell ty), ty) → ty)
      (λ post '-[Φ; a], Φ a ∧ ∀a': 𝔄, Φ a' → post a').
  Proof.
    eapply type_fn; [solve_typing|]=>/= α ϝ k[c[x[]]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst_as c'.
      iApply type_new; [lia|]. intro_subst_as r. rewrite Nat2Z.id.
      iApply (type_with_tr [_;predₛ _;_;_]
        (λ post '-[_; Φ; _; a], Φ a ∧ ∀a': 𝔄, Φ a' → post a')%type).
      (* Drop to Iris level. *)
      iIntros (?(?&?&?&?&[])?)
        "/= #LFT TIME PROPH UNIQ #E Na L C (r & c' & c & x &_) Obs".
      rewrite !tctx_hasty_val.
      iDestruct "c'" as ([|]) "[_ cell]"; case c' as [[|c'|]|]=>//.
      iDestruct "cell" as (?->) "Bor".
      iDestruct "x" as ([|]) "[#⧖ bty]"; case x as [[|x|]|]=>//.
      iDestruct "bty" as "[(%& >↦x & ty) †x]".
      iDestruct (ty_size_eq with "ty") as "#>%".
      iDestruct "r" as ([|]) "[_ own]"; case r as [[|r|]|]=>//.
      iDestruct "own" as "[(%& >↦r &>(%&_& %)) †r]".
      iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
      iMod (na_bor_acc with "LFT Bor α Na") as "(Big & Na & Toα)"; [solve_ndisj..|].
      iMod (bi.later_exist_except_0 with "Big") as
        (??) "(>Obs' & >#⧖' &(%& >↦c & ty'))".
      iCombine "Obs Obs'" as "#Obs". iDestruct (ty_size_eq with "ty'") as "#>%".
      wp_bind (_ <-{_} !_)%E. wp_apply (wp_memcpy with "[$↦r $↦c]"); [lia..|].
      iIntros "[↦r ↦c]". wp_seq. wp_apply (wp_memcpy with "[$↦c $↦x]"); [by f_equal..|].
      iIntros "[↦c ↦x]". wp_seq. iMod ("Toα" with "[↦c ty] Na") as "[α Na]".
      { iNext. iExists _, _. iSplit; [by iApply proph_obs_impl; [|done]=> ?[[? _]_]|].
        iFrame "⧖". iExists _. iFrame. }
      iMod ("ToL" with "α L") as "L".
      (* Now go back to typing level. *)
      iApply (type_type
        +[c ◁ box (&shr{α} (cell ty)); #x ◁ box (↯ ty.(ty_size)); #r ◁ box ty]
        -[_;_;_] with "[] LFT TIME PROPH UNIQ E Na L C [ty' c ↦x †x ↦r †r] []").
      - do 2 (iApply type_delete; [solve_extract|done|done|]).
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= tctx_hasty_val right_id. iFrame "c".
        have Eq: ∀l: loc, (#l)%E = (#l)%V by done. rewrite !Eq !tctx_hasty_val.
        iSplitL "↦x †x"; iExists _; iFrame "⧖'"; iFrame; iNext; iExists _; iFrame.
        iPureIntro. by exists ().
      - iApply proph_obs_impl; [|done]=>/= ?[[_ Imp]?]. by apply Imp. }
    by move=> ?[?[?[]]]/=.
  Qed.

  (** Create a shared cell from a unique borrow.
      Called alias::one in Rust.
      This is really just [cell_from_uniq] followed by sharing. *)

  Definition fake_shared_cell: val :=
    fn: ["x"] :=
      let: "cell_from_uniq" := cell_from_uniq in
      letcall: "c" := "cell_from_uniq" ["x"]%E in let: "c'" := !"c" in
      Share;; letalloc: "r" <- "c'" in
      delete [ #1; "c"];; return: ["r"].

  (* In this rule, we lose the prophecy information *)
  Lemma fake_shared_cell_type {𝔄} Φ (ty: type 𝔄) :
    typed_val fake_shared_cell (fn<α>(∅; &uniq{α} ty) → &shr{α} (cell ty))
      (λ post '-[(a, _)], Φ a ∧ post Φ).
  Proof.
    eapply type_fn; [solve_typing|]=> ???[?[]]. simpl_subst. via_tr_impl.
    { iApply type_let; [apply (cell_from_uniq_type Φ)|solve_extract|done|].
      intro_subst. iApply type_letcall; [solve_typing|solve_extract|solve_typing|].
      intro_subst. iApply type_deref; [solve_extract|solve_typing|done|].
      intro_subst. iApply type_share; [solve_extract|solve_typing|].
      iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
      iApply type_delete; [solve_extract|done|done|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[[??][]][??]/=.
  Qed.
End cell.

Global Hint Resolve cell_leak_just cell_subtype cell_eqtype : lrust_typing.
