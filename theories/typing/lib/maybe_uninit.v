From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section maybe_uninit.
  Context `{!typeG Σ}.

  Local Lemma maybe_uninit_mt {𝔄} (ty: type 𝔄) vπ d tid l q :
    (l ↦∗{q}: λ vl, ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl) ⊣⊢
    ⌜vπ = const None⌝ ∗ l ↦∗{q}: (λ vl, ⌜length vl = ty.(ty_size)⌝) ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ l ↦∗{q}: ty.(ty_own) vπ' d tid.
  Proof.
    iSplit.
    - iIntros "(%vl &?&[[%%]|(%vπ' &%&?)])".
      { iLeft. iSplit; [done|]. iExists vl. by iFrame. }
      iRight. iExists vπ'. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "[(%& %vl & ↦ &%)|(%vπ' &%& %vl & ↦ &?)]"; iExists vl;
        iFrame "↦"; [by iLeft|].
      iRight. iExists vπ'. by iSplit.
  Qed.

  (* Rust's mem::MaybeUninit<T> *)
  Program Definition maybe_uninit {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl :=
      ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ': proph 𝔄, ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l :=
      ⌜vπ = const None⌝ ∗ uninit_shr κ l ty.(ty_size) 0 ∨
      ∃vπ': proph 𝔄, ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_shr) vπ' d κ tid l;
  |}%I.
  Next Obligation. iIntros "* [[_$]|(%&_&?)]". by rewrite ty_size_eq. Qed.
  Next Obligation.
    move=> *. iIntros "[?|(%vπ &?&?)]"; [by iLeft|iRight]. iExists vπ.
    iSplit; [done|]. by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "[?|(%vπ &?&?)]"; [by iLeft|iRight]. iExists vπ.
    iSplit; [done|]. by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> ? ty *. iIntros "#? [[-> ?]|(%vπ &?&?)]"; [iLeft|iRight].
    { iSplit; [done|]. by iApply uninit_shr_shorten. }
    iExists vπ. iSplit; [done|]. by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT In Bor κ". rewrite maybe_uninit_mt.
    iMod (bor_or with "LFT Bor") as "[Bor|Bor]"; first done.
    { iApply step_fupdN_full_intro.
      iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
      iMod (bor_to_uninit_shr with "LFT Bor κ") as "[?$]"; by [|iLeft; iFrame]. }
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>->& Bor & κ)"; [done|].
    iMod (ty_share with "LFT In Bor κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[?$] !>". iRight.
    iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In [[->%]|(%vπ &->& ty)] κ".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "κ". by iLeft. }
    iMod (ty_own_proph with "LFT In ty κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%ξl & %q &%& ξl & Toty) !>".
    iExists ξl, q. iSplit; [iPureIntro; by apply proph_dep_constr|].
    iIntros "{$ξl}ξl". iMod ("Toty" with "ξl") as "[?$]".
    iRight. iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In In' [[-> ?]|(%vπ &->& ty)] κ".
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). by iIntros. }
    iMod (ty_shr_proph with "LFT In In' ty κ") as "Upd"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξl&%q&%& ξl & Toκ) !>". iExists ξl, q.
    iSplit; [iPureIntro; by apply proph_dep_constr|]. iIntros "{$ξl}ξl".
    by iMod ("Toκ" with "ξl").
  Qed.

  Global Instance maybe_uninit_ne {𝔄} : NonExpansive (@maybe_uninit 𝔄).
  Proof. solve_ne_type. Qed.
End maybe_uninit.

Notation "?" := maybe_uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance maybe_uninit_type_ne {𝔄} : TypeNonExpansive (maybe_uninit (𝔄:=𝔄)).
  Proof.
    constructor; [by apply type_lft_morphism_id_like|done| |];
    move=>/= > ->*; by do 4 f_equiv.
  Qed.

  Global Instance maybe_uninit_copy {𝔄} (ty: type 𝔄) : Copy ty → Copy (? ty).
  Proof.
    move=> ?. split; [apply _|]=> *. iIntros "LFT [[-> shr]|(%&->& ty)] Na κ".
    - iMod (uninit_shr_acc with "LFT shr κ") as (???) "[↦ Toκ]"; [solve_ndisj|].
      iModIntro. iExists _, _.
      iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [set_solver+|]. iFrame "↦".
      iSplit; [by iLeft|]. iIntros "Na". by iDestruct ("ToNa" with "Na") as "$".
    - iMod (copy_shr_acc with "LFT ty Na κ") as (??) "($& ↦ &?& Toκ)"; [done..|].
      iModIntro. iExists _, _. iFrame "↦ Toκ". iNext. iRight. iExists _. by iFrame.
  Qed.

  Global Instance maybe_uninit_send {𝔄} (ty: type 𝔄) : Send ty → Send (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.
  Global Instance maybe_uninit_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.

  Lemma maybe_uninit_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ →
    resolve E L (? ty) (λ o, match o with None => True | Some a => Φ a end).
  Proof.
    move=> Rslv > ?. iIntros "LFT PROPH E L [[-> _]|(%&->& ty)]".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
      by iApply proph_obs_true. }
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). by iIntros "!> >[$$]".
  Qed.

  Lemma maybe_uninit_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (? ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma maybe_uninit_real {𝔄 𝔅} ty E L (f: 𝔄 → 𝔅) :
    real E L ty f → real (𝔅:=optionₛ _) E L (? ty) (option_map f).
  Proof.
    move=> [Rlo Rls]. split.
    - iIntros "*% LFT E L [[->%]|(%&->& ty)]".
      { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
        iSplit; by [iExists _|iLeft]. }
      iMod (Rlo with "LFT E L ty") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first. { iRight. iExists _. by iFrame. }
      iPureIntro. move: Eq=> [b Eq]. exists (Some b). fun_ext=>/= π.
      by move: (equal_f Eq π)=>/= <-.
    - iIntros "*% LFT E L [[-> ?]|(%&->& ty)]".
      { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iFrame "L".
        iSplit; by [iExists _|iLeft; iFrame]. }
      iMod (Rls with "LFT E L ty") as "Upd"; [done|]. iIntros "!>!>".
      iApply (step_fupdN_wand with "Upd"). iIntros ">(%Eq &$&?) !>".
      iSplit; last first. { iRight. iExists _. by iFrame. }
      iPureIntro. move: Eq=> [b Eq]. exists (Some b). fun_ext=>/= π.
      by move: (equal_f Eq π)=>/= <-.
  Qed.

  Lemma maybe_uninit_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (? ty) (? ty') (option_map f).
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%EqSz &?& #InOwn & #InShr)".
    do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InOwn".
    - iIntros "[[-> ?]|(%vπ' &->&?)]".
      + iLeft. rewrite EqSz. by iFrame.
      + iRight. iExists (f ∘ vπ'). iSplit; [done|]. by iApply "InShr".
  Qed.
  Lemma maybe_uninit_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (? ty) (? ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply maybe_uninit_subtype. Qed.

  (* Rust's MaybeUninit::new *)
  Lemma uninit_to_maybe_uninit {𝔄} (ty: type 𝔄) E L :
    subtype E L (↯ ty.(ty_size)) (? ty) (const None).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_static|].
    iSplit; iIntros "!>** /="; iLeft; by iSplit.
  Qed.

  (* Rust's MaybeUninit::uninit *)
  Lemma into_maybe_uninit {𝔄} (ty: type 𝔄) E L : subtype E L ty (? ty) Some.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*?/="; iRight; iExists vπ; by iFrame.
  Qed.

  Lemma maybe_uninit_join {𝔄} (ty: type 𝔄) E L :
    subtype E L (? (? ty)) (? ty) (option_join 𝔄).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%&->&[[->->]|(%vπ'' &->&?)])]"; [by iLeft..|].
      iRight. iExists vπ''. by iFrame.
    - iIntros "[[->?]|(%&->&[[->?]|(%vπ'' &->&?)])]"; [iLeft; by iFrame..|].
      iRight. iExists vπ''. by iFrame.
  Qed.

  (* Rust's MaybeUninit::assume_uninit *)
  Lemma tctx_unwrap_maybe_uninit {𝔄 𝔅l} (ty: type 𝔄) E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ ? ty +:: T) (p ◁ ty +:: T)
      (λ post '(o -:: bl), match o with
        Some a => post (a -:: bl) | None => False end).
  Proof.
    split. { by move=> ???[[?|]?]. }
    iIntros (??[oπ ?]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %[??]; [done|].
    iDestruct "p" as (???) "[? [[->_]|(%&->&?)]]"=>//. iModIntro.
    iExists (_-::_). iFrame "T Obs". iExists _, _. by iFrame.
  Qed.

  Lemma tctx_unwrap_own_maybe_uninit {𝔄 𝔅l} (ty: type 𝔄) n E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ own_ptr n (? ty) +:: T) (p ◁ own_ptr n ty +:: T)
      (λ post '(o -:: bl), match o with
        Some a => post (a -:: bl) | None => False end).
  Proof.
    split. { by move=> ???[[?|]?]. }
    iIntros (??[oπ ?]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %[??]; [done|].
    iDestruct "p" as ([[]|][|]?) "[⧖ own]"=>//.
    iDestruct "own" as "[(%& ↦ & [[>->_]|big]) †]"=>//.
    iMod (bi.later_exist_except_0 with "big") as (?) "[>-> ty]". iModIntro.
    iExists (_-::_). iFrame "T Obs". iExists _, _. iSplit; [done|].
    iFrame "⧖ †". iNext. iExists _. iFrame.
  Qed.

  (* Rust's MaybeUninit::assume_uninit_ref *)
  Lemma tctx_unwrap_shr_maybe_uninit {𝔄 𝔅l} (ty: type 𝔄) κ E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ &shr{κ} (? ty) +:: T) (p ◁ &shr{κ} ty +:: T)
      (λ post '(o -:: bl), match o with
        Some a => post (a -:: bl) | None => False end).
  Proof.
    split. { by move=> ???[[?|]?]. }
    iIntros (??[oπ ?]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %[??]; [done|]. iModIntro.
    iDestruct "p" as ([[]|][|]?) "[⧖ ty]"=>//.
    iDestruct "ty" as "[[-> _]|(%&->&?)]"=>//. iExists (_-::_). iFrame "T Obs".
    iExists _, _. iSplit; [done|]. by iFrame "⧖".
  Qed.

  (* Rust's MaybeUninit::assume_uninit_mut *)
  Lemma tctx_unwrap_uniq_maybe_uninit {𝔄 𝔅l} (ty: type 𝔄) κ E L (T: tctx 𝔅l) p :
    lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (? ty) +:: T) (p ◁ &uniq{κ} ty +:: T)
      (λ post '((o, o') -:: bl), match o with
        | Some a => ∀a': 𝔄, o' = Some a' → post ((a, a') -:: bl)
        | None => False
        end).
  Proof.
    move=> Alv. split.
    { move=> ???[[[?|]?]?]; [|done]. by do 2 (apply forall_proper=> ?). }
    iIntros (??[vπ ?]?) "LFT #PROPH UNIQ E L /=[p T] #Obs".
    iDestruct "p" as ([[]|]??) "(_ &#?& uniq)"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[Vo Bor]". move: Eq. set ξ := PrVar _ ξi=> Eq.
    iMod (lctx_lft_alive_tok with "E L") as (?) "(κ & L & ToL)"; [done..|].
    iMod (bor_acc_cons with "LFT Bor κ") as "[big ToBor]"; [done|].
    iMod (bi.later_exist_except_0 with "big") as (oπ ?) "(>#⧖ & Pc &%& >↦ & uty)".
    iMod (uniq_strip_later with "Vo Pc") as (Eq' <-) "[Vo Pc]".
    have ->: vπ = λ π, (oπ π, π ξ). { by rewrite [vπ]surjective_pairing_fun Eq Eq'. }
    iMod (proph_obs_sat with "PROPH Obs") as %[??]; [done|].
    iDestruct "uty" as "[[>-> _]|big]"=>//.
    iMod (bi.later_exist_except_0 with "big") as (aπ) "[>-> ty]"=>/=.
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζj) "[Vo' Pc']" ; [done|].
    set ζ := PrVar _ ζj. iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ & Pc')".
    iMod (uniq_preresolve ξ [ζ] (Some ∘ (.$ ζ)) with "PROPH Vo Pc [$ζ //]")
      as "(Obs' & [ζ _] & ToPc)"; [done|apply proph_dep_constr, proph_dep_one|].
    iSpecialize ("Pc'" with "ζ"). iCombine "Obs' Obs" as "#?". iClear "Obs".
    iMod ("ToBor" with "[ToPc] [↦ ty Pc']") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ L") as "$". iModIntro.
      iExists ((λ π, (aπ π, π ζ)) -:: _). iFrame "T". iSplit; last first.
      { iApply proph_obs_impl; [|done]=>/= ?[-> Imp]. by apply Imp. }
      iExists _, _. iSplit; [done|]. iFrame "⧖". iSplit; [done|]. iExists _, _.
      by iFrame.
    - iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame.
    - iIntros "!> big !>!>". iDestruct "big" as (??) "(⧖' & Pc' &%& ↦ & ty)".
      iExists _, _. iFrame "⧖'".
      iDestruct (proph_ctrl_eqz with "PROPH Pc'") as "Eqz".
      iSplitL "Eqz ToPc". { iApply "ToPc". by iApply proph_eqz_constr. }
      iExists _. iFrame "↦". iRight. iExists _. by iFrame.
  Qed.
End typing.

Global Hint Resolve maybe_uninit_resolve | 5 : lrust_typing.
Global Hint Resolve maybe_uninit_resolve_just maybe_uninit_real
  maybe_uninit_subtype maybe_uninit_eqtype : lrust_typing.
