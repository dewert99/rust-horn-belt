From lrust.util Require Import basic.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context own shr_bor.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section obs_def.
Context `{!invGS Σ, !prophG Σ}.

Definition proph_obs_s (φπ: proph Prop) : iProp Σ :=
  proph_obs φπ ∗ ∃π, ⌜φπ π⌝.
End obs_def.

Notation ".⟨ φπ ⟩S" := (proph_obs_s φπ%type%stdpp)
  (at level 1, format ".⟨ φπ ⟩S") : bi_scope.
Notation "⟨ π , φ ⟩S" := (proph_obs_s (λ π, φ%type%stdpp))
  (at level 1, format "⟨ π ,  φ ⟩S") : bi_scope.

Section obs.
Context `{!invGS Σ, !prophG Σ}.
Global Instance proph_obs_s_persistent φπ : Persistent .⟨φπ⟩S := _.
Global Instance proph_obs_s_timeless φπ : Timeless .⟨φπ⟩S := _.
Global Instance proph_obs_s_proper :
  Proper (pointwise_relation _ (↔) ==> (⊣⊢)) proph_obs_s.
Proof. solve_proper. Qed.
Global Instance proph_obs_s_mono :
  Proper (pointwise_relation _ impl ==> (⊢)) proph_obs_s.
Proof. solve_proper. Qed.

Lemma proph_obs_s_impl (φπ ψπ: proph Prop) : (∀π, φπ π → ψπ π) → .⟨φπ⟩S -∗ .⟨ψπ⟩S.
Proof. move=> Imp. do 2 f_equiv. move=> ?. by apply Imp. Qed.

Lemma proph_obs_s_true (φπ: proph Prop) : (∀π, φπ π) → ⊢ .⟨φπ⟩S.
Proof. iIntros. iSplit. by iApply proph_obs_true. iExists inhabitant. iPureIntro. done. Qed.

Lemma proph_obs_upgrade E (φπ: proph Prop): ↑prophN ⊆ E → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ .⟨φπ⟩S.
Proof. 
  iIntros (?) "PROPH #Obs". iMod (proph_obs_sat with "PROPH Obs") as "%"; [done|]. 
  iModIntro. iFrame "Obs". done.
Qed.
End obs.

Section refined.
  Context `{!typeG Σ}.

  Lemma split_mt_refined {𝔄} Φ (ty: type 𝔄) vπ d tid l :
    (l ↦∗: λ vl, ⟨π, Φ (vπ π)⟩S ∗ ty.(ty_own) vπ d tid vl) ⊣⊢
    ⟨π, Φ (vπ π)⟩S ∗ l ↦∗: ty.(ty_own) vπ d tid.
  Proof. iSplit; [|iIntros "[$$]"]. iIntros "(%&?&$&?)". iExists _. iFrame. Qed.

  Program Definition refined {𝔄} (Φ: pred' 𝔄) (ty: type 𝔄) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_proph vπ ξl := ty.(ty_proph) vπ ξl /\ exists π, Φ (vπ π);
    ty_own vπ d tid vl := ⟨π, Φ (vπ π)⟩S ∗ ty.(ty_own) vπ d tid vl;
    ty_shr vπ d κ tid l := ⟨π, Φ (vπ π)⟩S ∗ ty.(ty_shr) vπ d κ tid l;
  |}%I.
  Next Obligation. iIntros "* [_ ?]". by rewrite ty_size_eq. Qed.
  Next Obligation. iIntros "*% [$?]". by iApply ty_own_depth_mono. Qed.
  Next Obligation. iIntros "*% [$?]". by iApply ty_shr_depth_mono. Qed.
  Next Obligation. iIntros "* #? [$?]". by iApply ty_shr_lft_mono. Qed.
  Next Obligation.
    iIntros "*% #LFT In Bor κ". rewrite split_mt_refined.
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>$& Bor & κ)"; [done|].
    by iApply (ty_share with "LFT In Bor κ").
  Qed.
  Next Obligation.
    iIntros "*% LFT In [#Obs ty] κ". iFrame "Obs". iDestruct "Obs" as "(_&%)".
    assert (∀ ξl, (ty.(ty_proph) vπ ξl /\ exists π, Φ (vπ π)) ↔ ty.(ty_proph) vπ ξl). intuition.
    setoid_rewrite H1. by iApply (ty_own_proph with "LFT In ty κ").
  Qed.
  Next Obligation.
    iIntros "*% LFT In In' [[_ %] ty] κ".
    assert (∀ ξl, (ty.(ty_proph) vπ ξl /\ exists π, Φ (vπ π)) ↔ ty.(ty_proph) vπ ξl). intuition.
    setoid_rewrite H1. by iApply (ty_shr_proph with "LFT In In' ty κ").
  Qed.
  Next Obligation. move=> ?????[??]. by eapply ty_proph_weaken. Qed.

  Global Instance refined_ne {𝔄} (Φ: 𝔄 → _) : NonExpansive (refined Φ).
  Proof. solve_ne_type. Qed.
End refined.

Notation "!{ Φ }" := (refined Φ) (format "!{ Φ }"): lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance refined_type_ne {𝔄} (Φ: 𝔄 → _) : TypeNonExpansive !{Φ}%T.
  Proof.
    split; [|split|..]=>/= *; [done| by apply type_lft_morphism_id_like|by f_equiv| |by f_equiv..].
    eexists [_], [_]. intuition. by constructor. by inversion_clear H1.
  Qed.

  Global Instance refined_send {𝔄} (Φ: 𝔄 → _) ty : Send ty → Send (!{Φ} ty).
  Proof. move=> ?>/=. by f_equiv. Qed.

  Global Instance refined_sync {𝔄} (Φ: 𝔄 → _) ty : Sync ty → Sync (!{Φ} ty).
  Proof. move=> ?>/=. by f_equiv. Qed.

  Lemma refined_resolve {𝔄} (Φ: 𝔄 → _) ty Ψ E L :
    resolve E L ty Ψ → resolve E L (!{Φ} ty) Ψ.
  Proof.
    iIntros (Rslv) "* LFT PROPH E L [_ ty]". by iApply (Rslv with "LFT PROPH E L ty").
  Qed.

  Lemma refined_real {𝔄 𝔅} Φ (f: 𝔄 → 𝔅) ty E L :
    real E L ty f → real E L (!{Φ} ty) f.
  Proof.
    move=> [Rlo Rls]. split; iIntros "*% LFT E L [$ ty]";
    by [iApply (Rlo with "LFT E L ty")|iApply (Rls with "LFT E L ty")].
  Qed.

  Lemma refined_subtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → (∀a, Φ a → Ψ (f a)) →
    subtype E L (!{Φ} ty) (!{Ψ} ty') f.
  Proof.
    iIntros (Sub Imp ?) "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "((%&%)&?& #InOwn & #InShr)".
    iSplit. iPureIntro. split; [done|].
    intros ??(?&?&?). split. intuition. exists x. by apply Imp.
    iSplit; [done|].
    iSplit; iIntros "!>*[??]"; iSplit; [|by iApply "InOwn"| |by iApply "InShr"];
    (iApply proph_obs_s_impl; [|done]=>/= ?; apply Imp).
  Qed.
  Lemma refined_eqtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → (∀a, Φ a → Ψ (f a)) → (∀a, Ψ a → Φ (g a)) →
    eqtype E L (!{Φ} ty) (!{Ψ} ty') f g.
  Proof. move=> [??]??. split; by apply refined_subtype. Qed.

  Lemma refined_forget {𝔄} (Φ: 𝔄 → _) ty E L : subtype E L (!{Φ} ty) ty id.
  Proof.
    iIntros "% _!>_". iSplit. iPureIntro. split; [done|].
    intros ??(?&?&?). done.
    iSplit; [by iApply lft_incl_refl|]. iSplit; iIntros "!>* [_$]".
  Qed.

  (* Lemma refined_blocked_subtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) ty ty' :
    blocked_subtype ty ty' f →
    blocked_subtype (!{Φ} ty) (!{Ψ} ty') f.
  Proof. done. Qed.
  Lemma refined_blocked_eqtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) g ty ty' :
    blocked_eqtype ty ty' f g → (∀a, Φ a → Ψ (f a)) → (∀a, Ψ a → Φ (g a)) →
    blocked_eqtype (!{Φ} ty) (!{Ψ} ty') f g.
  Proof. done. Qed.
  Lemma refined_blocked_forget {𝔄} (Φ: 𝔄 → _) ty : blocked_eqtype (!{Φ} ty) ty id id.
  Proof. apply blocked_eqtype_unfold. apply _. done. Qed. *)

  Lemma tctx_refined_in {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ !{Φ} ty +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by f_equiv. }
    iIntros (??[??]?) "_ PROPH _ _ $ /=[(%&%&%& ⧖ & ty) T] #Obs".
    iMod (proph_obs_upgrade with "PROPH Obs") as "ObsS"; [done|]. iModIntro.
    iExists (_-::_). iFrame "T". iSplit; last first.
    { by iApply proph_obs_impl; [|done]=>/= ?[_ ?]. }
    iExists _, _. iSplit; [done|]. iFrame "⧖ ty".
    by iApply proph_obs_s_impl; [|done]=>/= ?[? _].
  Qed.

  Lemma tctx_refined_out {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ !{Φ} ty +:: T) (p ◁ ty +:: T)
      (λ post '(a -:: bl), Φ a → post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by apply forall_proper=> ?. }
    iIntros (??[??]?) "_ _ _ _ $ /=[(%&%&%&?& [Obs _] &?) T] Obs' !>".
    iCombine "Obs Obs'" as "Obs". iExists (_-::_). iFrame "T".
    iSplit. { iExists _, _. by iFrame. }
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma tctx_own_refined_in {𝔄 𝔅l} (Φ: 𝔄 → _) ty n E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ own_ptr n ty +:: T) (p ◁ own_ptr n (!{Φ} ty) +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by f_equiv. }
    iIntros (??[??]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_upgrade with "PROPH Obs") as "ObsS"; [done|].
    iDestruct "p" as ([[]|][|]?) "[⧖ own]"=>//. iDestruct "own" as "[(%& >↦ & ty) †]".
    iModIntro. iExists (_-::_). iFrame "T". iSplit; last first.
    { by iApply proph_obs_impl; [|done]=>/= ?[_ ?]. }
    iExists _, _. iSplit; [done|]. iFrame "⧖ †". iNext. iExists _.
    iFrame "↦ ty". by iApply proph_obs_s_impl; [|done]=>/= ?[? _].
  Qed.

  Lemma tctx_own_refined_out {𝔄 𝔅l} (Φ: 𝔄 → _) ty n E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ own_ptr n (!{Φ} ty) +:: T) (p ◁ own_ptr n ty +:: T)
      (λ post '(a -:: bl), Φ a → post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by apply forall_proper=> ?. }
    iIntros (??[??]?) "_ _ _ _ $ /=[p T] Obs'".
    iDestruct "p" as ([[]|][|]?) "[⧖ own]"=>//.
    iDestruct "own" as "[(%& >↦ & >[Obs _] & ty) †]". iCombine "Obs Obs'" as "Obs".
    iModIntro. iExists (_-::_). iFrame "T". iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp. }
    iExists _, _. iSplit; [done|]. iFrame "⧖ †". iNext. iExists _. iFrame.
  Qed.

  Lemma tctx_shr_refined_in {𝔄 𝔅l} (Φ: 𝔄 → _) ty κ E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ &shr{κ} ty +:: T) (p ◁ &shr{κ} (!{Φ} ty) +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by f_equiv. }
    iIntros (??[??]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_upgrade with "PROPH Obs") as "ObsS"; [done|].
    iDestruct "p" as ([[]|][|]?) "[⧖ ty]"=>//. iModIntro. iExists (_-::_).
    iFrame "T". iSplit; last first. { by iApply proph_obs_impl; [|done]=>/= ?[_ ?]. }
    iExists _, _. iSplit; [done|]. iFrame "⧖ ty".
    by iApply proph_obs_s_impl; [|done]=>/= ?[? _].
  Qed.

  Lemma tctx_shr_refined_out {𝔄 𝔅l} (Φ: 𝔄 → _) ty κ E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ &shr{κ} (!{Φ} ty) +:: T) (p ◁ &shr{κ} ty +:: T)
      (λ post '(a -:: bl), Φ a → post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by apply forall_proper=> ?. }
    iIntros (??[??]?) "_ _ _ _ $ /=[p T] Obs'".
    iDestruct "p" as ([[]|][|]?) "[⧖ shr]"=>//. iDestruct "shr" as "[[Obs _] ty]".
    iCombine "Obs Obs'" as "Obs". iModIntro. iExists (_-::_). iFrame "T".
    iSplit. { iExists _, _. iSplit; [done|]. by iFrame. }
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.
End typing.

Global Hint Resolve refined_resolve refined_real refined_subtype refined_eqtype
  : lrust_typing.
