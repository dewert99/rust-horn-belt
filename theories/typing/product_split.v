From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context lft_contexts product own uniq_bor.
From lrust.typing Require Import shr_bor mod_ty uninit.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l ℭl: syn_typel).

Section product_split.
  Context `{!typeG Σ}.

  (** * General Split/Merger for Plain Pointer Types *)

  Fixpoint hasty_ptr_offsets {𝔄l} (ptr: ∀𝔄, type 𝔄 → type 𝔄) (p: path)
    (tyl: typel 𝔄l) (off: nat) : tctx 𝔄l :=
    match tyl with +[] => +[] | ty +:: tyl' =>
      p +ₗ #off ◁ ptr _ ty +:: hasty_ptr_offsets ptr p tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_offset {𝔄l} ptr p (tyl: _ 𝔄l) (off: nat) (l: loc) tid vπl :
    eval_path p = Some #l →
    tctx_interp tid (hasty_ptr_offsets ptr (p +ₗ #off) tyl 0) vπl ⊣⊢
    tctx_interp tid (hasty_ptr_offsets ptr p tyl off) vπl.
  Proof.
    move=> ?. rewrite -{2}(Nat.add_0_r off). move: off 0%nat.
    induction tyl, vπl; [done|]=>/= ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc Nat2Z.inj_add.
  Qed.

  Definition ptr_homo_sub (ptr: ∀𝔄, type 𝔄 → type 𝔄) : Prop :=
    ∀E L 𝔄 𝔅 (ty: _ 𝔄) (ty': _ 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr _ ty) (ptr _ ty') f.

  Definition ptr_just_loc (ptr: ∀𝔄, type 𝔄 → type 𝔄) : Prop :=
    ∀𝔄 (ty: _ 𝔄) vπ d tid vl,
      (ptr _ ty).(ty_own) vπ d tid vl -∗ ⌜∃l: loc, vl = [ #l]⌝.

  Lemma tctx_split_ptr_xprod {𝔄l} ptr (tyl: _ 𝔄l) E L :
    ptr_homo_sub ptr → ptr_just_loc ptr →
    (∀p 𝔄 𝔅 (ty: _ 𝔄) (ty': _ 𝔅), tctx_incl E L +[p ◁ ptr _ (ty * ty')%T]
      +[p ◁ ptr _ ty; p +ₗ #ty.(ty_size) ◁ ptr _ ty']
      (λ post '-[(a, b)], post -[a; b])) →
    ∀p, tctx_incl E L +[p ◁ ptr _ (Π! tyl)%T] (hasty_ptr_offsets ptr p tyl 0)
      (λ post '-[al], post al).
  Proof.
    move=> HSub JLoc In. elim: tyl. { move=>/= ?. by eapply tctx_incl_eq;
    [apply tctx_incl_leak_head|]=>/= ?[[][]]. } move=>/= 𝔄 𝔅l ty tyl IH p.
    eapply tctx_incl_eq. { eapply tctx_incl_trans;
    [by eapply subtype_tctx_incl, HSub, mod_ty_out, _|].
    eapply (tctx_incl_trans _ [𝔄; Π!%ST 𝔅l] (𝔄 :: 𝔅l)
      _ (λ post '-[a; bl], post (a -:: bl))); [apply In|]=>/=.
    iIntros (?? (aπ &?&[]) postπ)
      "LFT PROPH UNIQ E L ((%&%& %Ev & ? & ptr) & p' & _) Obs".
    iDestruct (JLoc with "ptr") as %[?[=->]].
    iMod (IH _ _ _ -[_] (λ π bl, postπ π (aπ π -:: bl)) with
      "LFT PROPH UNIQ E L [$p'] Obs") as (?) "($ & T & Obs)". iModIntro.
    rewrite hasty_ptr_offsets_offset; [|done]. iExists (_-::_).
    iFrame "Obs T". iExists _, _. iSplit; [by rewrite/= Ev|].
    rewrite shift_loc_0. iFrame. } by move=>/= ?[[??][]].
  Qed.

  Lemma tctx_merge_ptr_xprod {𝔄l} ptr (tyl: _ 𝔄l) E L :
    ptr_homo_sub ptr → ptr_just_loc ptr →
    (∀p 𝔄 𝔅 (ty: _ 𝔄) (ty': _ 𝔅), tctx_incl E L
      +[p ◁ ptr _ ty; p +ₗ #ty.(ty_size) ◁ ptr _ ty'] +[p ◁ ptr _ (ty * ty')]
      (λ post '-[a; b], post -[(a, b)])) →
    𝔄l ≠ [] → ∀p, tctx_incl E L (hasty_ptr_offsets ptr p tyl 0)
      +[p ◁ ptr _ (Π! tyl)%T] (λ post al, post -[al]).
  Proof.
    move=> HSub JLoc In. elim: tyl; [done|]=>/= 𝔄 ? ty. case.
    { have Sub: subtype E L (ptr _ ty) (ptr _ (Π!%T +[ty])) (λ a, -[a]).
      { apply HSub. eapply subtype_eq. { eapply subtype_trans;
        [|apply mod_ty_in]. eapply subtype_trans; [apply prod_ty_right_id|].
        apply prod_subtype, mod_ty_in. solve_typing. } done. }
      iIntros (_ _ p ??[?[]]?) "_ _ _ E L [(%&%& %Ev & ⧖ & ptr) _] Obs !>".
      iDestruct (Sub with "L E") as "#(_&_& #In &_)". iExists -[_].
      iFrame "L Obs". iSplit; [|done]. iExists _, _. iFrame "⧖".
      iSplit; [|by iApply "In"]. move: Ev=>/=. case (eval_path p)=>//.
      (do 2 case=>//)=> ?. by rewrite shift_loc_0=> [=->]. }
    move=> 𝔅 𝔅l' ?? IH _ p. set 𝔅l := 𝔅 :: 𝔅l'. eapply tctx_incl_eq. {
    eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, HSub, mod_ty_in].
    eapply (tctx_incl_trans (𝔄 :: 𝔅l) [𝔄; Π!%ST 𝔅l] _
      (λ post '(a -:: bl), post -[a; bl])); [|by apply In].
    rewrite [hasty_ptr_offsets]lock. iIntros (?? (aπ &?&?) postπ)
      "LFT PROPH UNIQ E L /= [(%&%& %Ev & ⧖ & ptr) T] Obs".
    have Ne: 𝔅l ≠ [] by done. iDestruct (JLoc with "ptr") as %[l[=->]].
    have ?: eval_path p = Some #l. { move: Ev=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_0=> [=->]. }
    iMod (IH Ne _ _ _ (_-::_) (λ π '-[bl], postπ π -[aπ π; bl]) with
    "LFT PROPH UNIQ E L [T] Obs") as ([?[]]) "($ & T & Obs)". { unlock.
    by rewrite -hasty_ptr_offsets_offset. } iModIntro. iExists -[_; _].
    iFrame "Obs T". iExists _, _. by iFrame. } by move=> ?[?[??]].
  Qed.

End product_split.

Global Hint Unfold ptr_homo_sub : lrust_typing.
Notation hasty_own_offsets n :=
  (hasty_ptr_offsets (λ 𝔄, @own_ptr _ _ 𝔄 n)).
Notation hasty_shr_offsets κ :=
  (hasty_ptr_offsets (λ 𝔄, @shr_bor _ _ 𝔄 κ)).

Section product_split.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Lemma tctx_split_own_prod {𝔄 𝔅} n (ty: _ 𝔄) (ty': _ 𝔅) p E L :
    tctx_incl E L +[p ◁ own_ptr n (ty * ty')]
      +[p ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      (λ post '-[(a, b)], post -[a; b]).
  Proof.
    iIntros (??[abπ[]]?) "_ _ _ _ $ [p _] Obs".
    iDestruct "p" as ([[]|][|]Ev) "[#? own]"=>//.
    iDestruct "own" as "[(% & >↦ & (%&%&>->& ty & ty')) †]".
    rewrite heap_mapsto_vec_app -freeable_sz_split.
    iDestruct (ty_size_eq with "ty") as "#>->".
    iDestruct "↦" as "[↦ ↦']". iDestruct "†" as "[† †']". iModIntro.
    iExists -[fst ∘ abπ; snd ∘ abπ]. iSplitR "Obs"; last first.
    { iApply proph_obs_eq; [|done]=>/= π. by case (abπ π). }
    iSplitL "ty ↦ †"; [|iSplitL; [|done]]; iExists _, _.
    - do 2 (iSplit; [done|]). iFrame "†". iNext. iExists _. iFrame.
    - iSplit; [by rewrite/= Ev|]. iSplit; [done|]. iFrame "†'". iNext.
      iExists _. iFrame.
  Qed.

  Lemma tctx_merge_own_prod {𝔄 𝔅} n (ty: _ 𝔄) (ty': _ 𝔅) p E L :
    tctx_incl E L +[p ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      +[p ◁ own_ptr n (ty * ty')] (λ post '-[a; b], post -[(a, b)]).
  Proof.
    iIntros (??(?&?&[])?) "_ _ _ _ $ (p & p' &_) Obs".
    iDestruct "p" as ([[]|][|]Ev) "[⧖ own]"=>//.
    iDestruct "p'" as ([[]|][|]Ev') "[⧖' own']"=>//.
    move: Ev'. rewrite/= Ev. move=> [=<-]. iCombine "⧖ ⧖'" as "?".
    iDestruct "own" as "[(% & >↦ & ty) †]".
    iDestruct "own'" as "[(% & >↦' & ty') †']". iModIntro.
    iExists -[_]. iFrame "Obs". iSplitL; [|done]. iExists _, _.
    do 2 (iSplit; [done|]). rewrite/= -freeable_sz_split. iFrame "† †'".
    iNext. iExists (_ ++ _). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "ty") as %->. iFrame "↦ ↦'". iExists _, _.
    iSplit; [done|]. iSplitL "ty"; (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Local Lemma own_just_loc n : ptr_just_loc (λ _, own_ptr n).
  Proof. iIntros (???[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma tctx_split_own_xprod {𝔄l} n (tyl: _ 𝔄l) p E L :
    tctx_incl E L +[p ◁ own_ptr n (Π! tyl)]
      (hasty_own_offsets n p tyl 0) (λ post '-[al], post al).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, own_ptr n));
    [solve_typing|apply own_just_loc|move=> *; apply tctx_split_own_prod].
  Qed.

  Lemma tctx_merge_own_xprod {𝔄 𝔄l} n (tyl: _ (𝔄 :: 𝔄l)) p E L :
    tctx_incl E L (hasty_own_offsets n p tyl 0)
      +[p ◁ own_ptr n (Π! tyl)] (λ post al, post -[al]).
  Proof.
    apply (tctx_merge_ptr_xprod (λ _, own_ptr n));
    [solve_typing|apply own_just_loc|move=> *; apply tctx_merge_own_prod|done].
  Qed.

  (** * Shared References *)

  Lemma tctx_split_shr_prod {𝔄 𝔅} κ (ty: _ 𝔄) (ty': _ 𝔅) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (ty * ty')]
      +[p ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty']
      (λ post '-[(a, b)], post -[a; b]).
  Proof.
    iIntros (??[abπ[]]?) "_ _ _ _ $ [p _] Obs !>".
    iDestruct "p" as ([[]|][|]Ev) "[#? own]"=>//. iDestruct "own" as "[ty ty']".
    iExists -[fst ∘ abπ; snd ∘ abπ]. iSplitR "Obs"; last first.
    { iApply proph_obs_eq; [|done]=>/= π. by case (abπ π). }
    iSplitL "ty"; [|iSplitL; [|done]]; iExists _, _.
    { by do 2 (iSplit; [done|]). } { iSplit; [by rewrite/= Ev|]. by iSplit. }
  Qed.

  Lemma tctx_merge_shr_prod {𝔄 𝔅} κ (ty: _ 𝔄) (ty': _ 𝔅) p E L :
    tctx_incl E L +[p ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty']
      +[p ◁ &shr{κ} (ty * ty')] (λ post '-[a; b], post -[(a, b)]).
  Proof.
    iIntros (??(?&?&[])?) "_ _ _ _ $ (p & p' &_) Obs !>".
    iDestruct "p" as ([[]|][|]Ev) "[⧖ ty]"=>//.
    iDestruct "p'" as ([[]|][|]Ev') "[⧖' ty']"=>//.
    move: Ev'. rewrite/= Ev. move=> [=<-]. iCombine "⧖ ⧖'" as "?".
    iExists -[_]. iFrame "Obs". iSplitL; [|done]. iExists _, _.
    do 2 (iSplit; [done|])=>/=.
    iSplit; (iApply ty_shr_depth_mono; [|done]); lia.
  Qed.

  Local Lemma shr_just_loc κ : ptr_just_loc (λ _, &shr{κ}%T).
  Proof. iIntros (???[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma tctx_split_shr_xprod {𝔄l} κ (tyl: _ 𝔄l) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (Π! tyl)]
      (hasty_shr_offsets κ p tyl 0) (λ post '-[al], post al).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, &shr{κ}%T));
    [solve_typing|apply shr_just_loc|move=> *; apply tctx_split_shr_prod].
  Qed.

  Lemma tctx_merge_shr_xprod {𝔄 𝔄l} κ (tyl: _ (𝔄 :: 𝔄l)) p E L :
    tctx_incl E L (hasty_shr_offsets κ p tyl 0)
      +[p ◁ &shr{κ} (Π! tyl)] (λ post al, post -[al]).
  Proof.
    apply (tctx_merge_ptr_xprod (λ _, &shr{κ}%T));
    [solve_typing|apply shr_just_loc|move=> *; apply tctx_merge_shr_prod|done].
  Qed.

  (** * Unique References *)

  Lemma tctx_split_uniq_prod {𝔄 𝔅} κ (ty: _ 𝔄) (ty': _ 𝔅) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (ty * ty')]
      +[p ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty']
      (λ post '-[((a, b), (a', b'))], post -[(a, a'); (b, b')]).
  Proof.
    iIntros (Alv ??[vπ[]]?) "#LFT #PROPH #UNIQ E L [p _] Obs".
    set aπ: proph 𝔄 := λ π, (vπ π).1.1. set bπ: proph 𝔅 := λ π, (vπ π).1.2.
    have ?: Inhabited 𝔄 := populate (aπ inhabitant).
    have ?: Inhabited 𝔅 := populate (bπ inhabitant).
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iDestruct "p" as ([[]|]? Ev) "[_ [#In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo ξBor]".
    move: Eq. (set ξ := PrVar _ ξi)=> Eq.
    iMod (bor_acc_cons with "LFT ξBor κ") as "[(%&%& ↦ty & >#⧖ & ξPc) ToBor]"; [done|].
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    iMod (uniq_intro bπ with "PROPH UNIQ") as (ζ'i) "[ζ'Vo ζ'Pc]"; [done|].
    set ζ := PrVar _ ζi. set ζ' := PrVar _ ζ'i.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ζPc)".
    iDestruct (uniq_proph_tok with "ζ'Vo ζ'Pc") as "(ζ'Vo & ζ' & ζ'Pc)".
    iMod (uniq_preresolve ξ [ζ; ζ'] (λ π, (π ζ, π ζ')) with
      "PROPH ξVo ξPc [$ζ $ζ']") as "(Obs' & (ζ & ζ' &_) & ToξPc)"; [done| |done|].
    { apply (proph_dep_pair [_] [_]); apply proph_dep_one. }
    iCombine "Obs Obs'" as "#Obs".
    iSpecialize ("ζPc" with "ζ"). iSpecialize ("ζ'Pc" with "ζ'").
    iMod ("ToBor" with "[ToξPc] [↦ty ζPc ζ'Pc]") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ") as "$".
      iMod (bor_sep with "LFT Bor") as "[Bor Bor']"; [done|]. iModIntro.
      iExists -[λ π, (aπ π, π ζ); λ π, (bπ π, π ζ')]. iSplitL; last first.
      { iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π).
        rewrite/= /aπ /bπ. case (vπ π). by (do 2 (case=>/= ??))=> <- [?[=<-<-]]. }
      rewrite lft_intersect_list_app.
      iSplitL "ζVo Bor"; [|iSplit; [|done]]; iExists _, _; iFrame "⧖".
      + iSplit; [done|]. iSplit; [by iApply lft_incl_trans;
        [|iApply lft_intersect_incl_l]|]. iExists _, _. by iFrame.
      + iSplit; [by rewrite/= Ev|]. iSplit; [by iApply lft_incl_trans;
      [|iApply lft_intersect_incl_r]|]. iExists _, _. by iFrame.
    - iNext. iDestruct "↦ty" as (?) "[↦ (%&%&->& ty & ty')]".
      rewrite heap_mapsto_vec_app. iDestruct "↦" as "[↦ ↦']".
      iDestruct (ty_size_eq with "ty") as %->. iSplitL "↦ ty ζPc"; iExists _, _;
      iFrame "⧖"; [iFrame "ζPc"|iFrame "ζ'Pc"]; iExists _; iFrame.
    - iClear "⧖". iIntros "!> [(%&%& ↦ty & ⧖ & ζPc) (%&%& ↦ty' & ⧖' & ζ'Pc)] !>!>".
      iCombine "⧖ ⧖'" as "⧖"=>/=. iExists (pair ∘ _ ⊛ _), _. iFrame "⧖".
      iSplitL "↦ty ↦ty'"; last first.
      { iApply "ToξPc". iApply (proph_eqz_constr2 with "[ζPc] [ζ'Pc]");
        [iApply (proph_ctrl_eqz with "PROPH ζPc")|
         iApply (proph_ctrl_eqz with "PROPH ζ'Pc")]. }
      iDestruct "↦ty" as (?) "[↦ ty]". iDestruct "↦ty'" as (?) "[↦' ty']".
      iExists (_ ++ _). rewrite heap_mapsto_vec_app.
      iDestruct (ty_size_eq with "ty") as %->. iFrame "↦ ↦'". iExists _, _.
      iSplit; [done|]. iSplitL "ty"; (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  (** Merging mutable references is not supported. *)

  Fixpoint hasty_uniq_offsets {𝔄l} (κ: lft) (p: path)
    (tyl: typel 𝔄l) (off: nat) : tctx (map (λ 𝔄, 𝔄 * 𝔄)%ST 𝔄l) :=
    match tyl with +[] => +[] | ty +:: tyl' =>
      p +ₗ #off ◁ &uniq{κ} ty +:: hasty_uniq_offsets κ p tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_uniq_offsets_offset {𝔄l} κ p (tyl: _ 𝔄l) (off: nat) (l: loc) tid vπl :
    eval_path p = Some #l →
    tctx_interp tid (hasty_uniq_offsets κ (p +ₗ #off) tyl 0) vπl ⊣⊢
    tctx_interp tid (hasty_uniq_offsets κ p tyl off) vπl.
  Proof.
    move=> ?. rewrite -{2}(Nat.add_0_r off). move: off 0%nat.
    induction tyl, vπl; [done|]=>/= ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc Nat2Z.inj_add.
  Qed.

  Lemma tctx_split_uniq_xprod {𝔄l} κ (tyl: _ 𝔄l) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (Π! tyl)%T] (hasty_uniq_offsets κ p tyl 0)
      (λ post '-[(al, al')], post (ptrans (pzip al al'))).
  Proof.
    move=> ?. move: p. elim: tyl. { move=>/= ?. by eapply tctx_incl_eq;
    [apply tctx_incl_leak_head|]=>/= ?[[][]]_[]. } move=>/= 𝔄 𝔅l ty tyl IH p.
    eapply tctx_incl_eq. { eapply tctx_incl_trans; [apply tctx_uniq_mod_ty_out;
    by [apply _|]|]. eapply (tctx_incl_trans _ [𝔄 * 𝔄; Π! 𝔅l * Π! 𝔅l]%ST
      (𝔄 * 𝔄 :: map (λ 𝔄, 𝔄 * 𝔄) 𝔅l)%ST _ (λ post '-[aa'; (bl, bl')],
        post (aa' -:: ptrans (pzip bl bl')))); [by apply tctx_split_uniq_prod|].
    iIntros (??(aa'π &?&[])?) "LFT PROPH UNIQ E L (p & p' &_) Obs".
    iDestruct "p" as ([[]|]? Ev) "[⧖ [In uniq]]"=>//.
    iMod (IH _ _ _ -[_] (λ π bl, postπ π (aa'π π -:: bl)) with
      "LFT PROPH UNIQ E L [$p'] Obs") as (?) "($ & T & Obs)". iModIntro.
    rewrite hasty_uniq_offsets_offset; [|done]. iExists (_-::_).
    iFrame "Obs T". iExists _, _. iSplit; [by rewrite/= Ev|].
    rewrite shift_loc_0. iFrame. } by move=>/= ?[[[??][??]][]].
  Qed.

  (** * Splitting with [tctx_extract_elt]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)
  Lemma tctx_extract_split_own_xprod {𝔄 𝔄l 𝔅l ℭl} (t: _ 𝔄) n (tyl: _ 𝔄l)
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_offsets n p tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_own_xprod|]. } move=>/= ?[??].
    rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

  Lemma tctx_extract_split_shr_xprod {𝔄 𝔄l 𝔅l ℭl} (t: _ 𝔄) κ (tyl: _ 𝔄l)
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_shr_offsets κ p tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_shr_xprod|]. } move=>/= ?[??].
    rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

  Lemma tctx_extract_split_uniq_xprod {𝔄 𝔄l 𝔅l ℭl} (t: _ 𝔄) κ (tyl: _ 𝔄l)
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_offsets κ p tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} (Π! tyl) +:: T) (T' h++ T)
      (λ post '((al, al') -:: bl),
        tr (λ '(a -:: cl), post (a -:: cl -++ bl)) (ptrans (pzip al al'))).
  Proof.
    move=> ??. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_uniq_xprod|]. }
    move=>/= ?[[??]?]. rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

  (** * Merging with [tctx_extract_elt]. *)

  Lemma tctx_extract_merge_own_xprod {𝔄 𝔄l 𝔅l ℭl} n (tyl: _ (𝔄 :: 𝔄l))
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_own_offsets n p tyl 0) T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr n (Π! tyl)) T T'
      (λ post, tr (λ acl, let '(al, cl) := psep acl in post (al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply tctx_incl_trans; [done|].
    apply (tctx_incl_frame_r _ +[_]), tctx_merge_own_xprod. } done.
  Qed.

  Lemma tctx_extract_merge_shr_xprod {𝔄 𝔄l 𝔅l ℭl} κ (tyl: _ (𝔄 :: 𝔄l))
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_shr_offsets κ p tyl 0) T T' tr →
    tctx_extract_elt E L (p ◁ &shr{κ} (Π! tyl)) T T'
      (λ post, tr (λ acl, let '(al, cl) := psep acl in post (al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply tctx_incl_trans; [done|].
    apply (tctx_incl_frame_r _ +[_]), tctx_merge_shr_xprod. } done.
  Qed.

End product_split.

(* We do not want unification to try to unify the definition of these
   types with anything in order to try splitting or merging. *)
Global Hint Opaque tctx_extract_elt : lrust_typing_merge.

(* We make sure that splitting is tried before borrowing, so that not
   the entire product is borrowed when only a part is needed. *)
Global Hint Resolve tctx_extract_split_own_xprod
  tctx_extract_split_shr_xprod tctx_extract_split_uniq_xprod | 5 : lrust_typing.

(* Merging is also tried after everything, except
   [tctx_extract_hasty_further]. Moreover, it is placed in a
   difference hint db. The reason is that it can make the proof search
   diverge if the type is an evar.

   Unfortunately, priorities are not taken into account accross hint
   databases with [typeclasses eauto], so this is useless, and some
   solve_typing get slow because of that. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5304
*)
Global Hint Resolve tctx_extract_merge_own_xprod tctx_extract_merge_shr_xprod
  | 40 : lrust_typing_merge.
