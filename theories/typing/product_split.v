From iris.algebra Require Import numbers.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context
  mod_ty uninit product own uniq_bor shr_bor.
Set Default Proof Using "Type".

(** * General Split/Merger for Plain Pointer Types *)
Section product_split.
  Context `{!typeG Σ}.

  Fixpoint hasty_ptr_offsets {𝔄l} (ptr: ∀𝔄, type 𝔄 → type 𝔄) (p: path)
    (tyl: typel 𝔄l) (off: nat) : tctx 𝔄l :=
    match tyl with +[] => +[] | ty +:: tyl' =>
      p +ₗ #off ◁ ptr _ ty +:: hasty_ptr_offsets ptr p tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_offset {𝔄l}
    (off: nat) p ptr (l: loc) (tyl: _ 𝔄l) tid vπl :
    eval_path p = Some #l →
    tctx_interp tid (hasty_ptr_offsets ptr (p +ₗ #off) tyl 0) vπl ⊣⊢
    tctx_interp tid (hasty_ptr_offsets ptr p tyl off) vπl.
  Proof.
    move=> ?. rewrite -{2}(Nat.add_0_r off). move: off 0.
    induction tyl, vπl; [done|]=>/= ??. f_equiv; [|by rewrite IHtyl assoc_L].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc Nat2Z.inj_add.
  Qed.

  Definition ptr_homo_sub (ptr: ∀𝔄, type 𝔄 → type 𝔄) : Prop :=
    ∀E L 𝔄 𝔅 (ty: _ 𝔄) (ty': _ 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr _ ty) (ptr _ ty') f.
  Hint Unfold ptr_homo_sub : lrust_typing.

  Definition ptr_just_loc (ptr: ∀𝔄, type 𝔄 → type 𝔄) : Prop :=
    ∀𝔄 (ty: _ 𝔄) vπ d tid vl,
      (ptr _ ty).(ty_own) vπ d tid vl -∗ ⌜∃l: loc, vl = [ #l]⌝.

  Lemma tctx_split_ptr_xprod {𝔄l} ptr (tyl: _ 𝔄l) E L :
    ptr_homo_sub ptr → ptr_just_loc ptr →
    (∀p 𝔄 𝔅 (ty: _ 𝔄) (ty': _ 𝔅), tctx_incl E L +[p ◁ ptr _ (ty * ty')%T]
      +[p ◁ ptr _ ty; p +ₗ #ty.(ty_size) ◁ ptr _ ty'] (λ post '-[(a, b)], post -[a; b])) →
    ∀p, tctx_incl E L +[p ◁ ptr _ (Π! tyl)%T] (hasty_ptr_offsets ptr p tyl 0)
      (λ post '-[al], post al).
  Proof.
    move=> HSub JLoc In. elim: tyl. { move=>/= ?. by eapply tctx_incl_eq;
    [apply tctx_incl_leak_head|]=>/= ?[[][]]. } move=>/= 𝔄 𝔅l ty tyl IH p.
    eapply tctx_incl_eq. { eapply tctx_incl_trans;
    [by eapply subtype_tctx_incl, HSub, mod_ty_out, _|].
    set tr := (λ post '-[a; bl], post (a -:: bl)) :
      predl (𝔄 :: 𝔅l) → predl [𝔄; Π!%ST 𝔅l].
    eapply (tctx_incl_trans _ _ _ _ tr); [apply In|]=>/=.
    iIntros (??(aπ &?&[])postπ)
      "LFT PROPH UNIQ E L ((%&%& %Ev & ? & ptr) & p' & _) Obs".
    iDestruct (JLoc with "ptr") as %[?[=->]].
    iMod (IH _ _ _ -[_] (λ π bl, postπ π (aπ π -:: bl)) with
      "LFT PROPH UNIQ E L [$p'] Obs") as (?) "($ & T & Obs)". iModIntro.
    rewrite hasty_ptr_offsets_offset; [|done]. iExists (_ -:: _).
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
      { apply HSub. eapply subtype_eq. { eapply subtype_trans; [|apply mod_ty_in].
        eapply subtype_trans; [apply prod_ty_right_id|].
        apply prod_subtype, mod_ty_in. solve_typing. } done. }
      iIntros (_ _ p ??[?[]]?) "_ _ _ E L [(%&%& %Ev & ⧖ & ptr) _] Obs !>".
      iDestruct (Sub with "L E") as "#(_&_& #In &_)". iExists -[_].
      iFrame "L Obs". iSplit; [|done]. iExists _, _. iFrame "⧖".
      iSplit; [|by iApply "In"]. move: Ev=>/=. case (eval_path p)=>//.
      (do 2 case=>//)=> ?. by rewrite shift_loc_0=> [=->]. }
    move=> 𝔅 𝔅l' ?? IH _ p. eapply tctx_incl_eq. {
    eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, HSub, mod_ty_in].
    set tr := (λ post '(a -:: bl), post -[a; bl]) :
      predl [𝔄; Π!%ST (𝔅 :: 𝔅l')] → predl (𝔄 :: 𝔅 :: 𝔅l').
    eapply (tctx_incl_trans _ _ _ tr); [|by apply In]. rewrite [hasty_ptr_offsets]lock.
    iIntros (??(aπ&?&?)postπ) "LFT PROPH UNIQ E L /= [(%&%& %Ev & ⧖ & ptr) T] Obs".
    have Ne: 𝔅 :: 𝔅l' ≠ [] by done. iDestruct (JLoc with "ptr") as %[l[=->]].
    have ?: eval_path p = Some #l. { move: Ev=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_0=> [=->]. }
    iMod (IH Ne _ _ _ (_ -:: _) (λ π '-[bl], postπ π -[aπ π; bl]) with
      "LFT PROPH UNIQ E L [T] Obs") as ([?[]]) "($ & T & Obs)".
    { unlock. by rewrite -hasty_ptr_offsets_offset. } iModIntro. iExists -[_; _].
    iFrame "Obs T". iExists _, _. by iFrame. } by move=> ?[?[??]].
  Qed.

  (** * Owned pointers *)

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
    iIntros (??(aπ&bπ&[])?) "_ _ _ _ $ (p & p' &_) Obs".
    iDestruct "p" as ([[]|][|]Ev) "[⧖ own]"=>//.
    iDestruct "p'" as ([[]|][|]Ev') "[⧖' own']"=>//.
    move: Ev'. rewrite/= Ev. move=> [=<-]. iCombine "⧖ ⧖'" as "?".
    iDestruct "own" as "[(% & >↦ & ty) †]".
    iDestruct "own'" as "[(% & >↦' & ty') †']". iModIntro.
    iExists -[pair ∘ aπ ⊛ bπ]. iFrame "Obs". iSplitL; [|done]. iExists _, _.
    do 2 (iSplit; [done|]). rewrite/= -freeable_sz_split. iFrame "† †'".
    iNext. iExists (_ ++ _). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "ty") as %->. iFrame "↦ ↦'". iExists _, _.
    iSplit; [done|]. iSplitL "ty"; (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Definition hasty_own_offsets {𝔄l} n := @hasty_ptr_offsets 𝔄l (λ _, own_ptr n).

  Local Lemma own_just_loc n : ptr_just_loc (λ _, own_ptr n).
  Proof. iIntros (???[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma tctx_split_own_xprod {𝔄l} n (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ own_ptr n (Π! tyl)]
      (hasty_own_offsets n p tyl 0) (λ post '-[al], post al).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, own_ptr n));
    [solve_typing|apply own_just_loc|move=> *; apply tctx_split_own_prod].
  Qed.

  Lemma tctx_merge_own_xprod {𝔄 𝔄l} n (tyl: typel (𝔄 :: 𝔄l)) p E L :
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
    iIntros (??(aπ&bπ&[])?) "_ _ _ _ $ (p & p' &_) Obs !>".
    iDestruct "p" as ([[]|][|]Ev) "[⧖ ty]"=>//.
    iDestruct "p'" as ([[]|][|]Ev') "[⧖' ty']"=>//.
    move: Ev'. rewrite/= Ev. move=> [=<-]. iCombine "⧖ ⧖'" as "?".
    iExists -[pair ∘ aπ ⊛ bπ]. iFrame "Obs". iSplitL; [|done]. iExists _, _.
    do 2 (iSplit; [done|])=>/=.
    iSplit; (iApply ty_shr_depth_mono; [|done]); lia.
  Qed.

  Definition hasty_shr_offsets {𝔄l} κ := @hasty_ptr_offsets 𝔄l (λ _, &shr{κ}%T).

  Local Lemma shr_just_loc κ : ptr_just_loc (λ _, &shr{κ}%T).
  Proof. iIntros (???[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma tctx_split_shr_xprod {𝔄l} κ (tyl: typel 𝔄l) p E L :
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

(*
  (** Unique borrows *)
  Lemma tctx_split_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ}(product2 ty1 ty2)]
                  [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2].
  Proof.
    iIntros (tid q) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|] [|depth]) "(#Hdepth & Hp & #Hout & H)"=>//.
    iDestruct "Hp" as %Hp. setoid_rewrite split_prod_mt.
    iDestruct "H" as (depth' γ ?) "[H◯ Hbor]".
    iMod (own_alloc (●E depth' ⋅ ◯E depth')) as (γ1) "[H●1 H◯1]";
      [by apply excl_auth_valid|].
    iMod (own_alloc (●E depth' ⋅ ◯E depth')) as (γ2) "[H●2 H◯2]";
      [by apply excl_auth_valid|].
    rewrite lft_intersect_list_app.
    iAssert (κ ⊑ ty_lft ty1)%I as "Hout1".
    { by iApply lft_incl_trans; [|iApply lft_intersect_incl_l]. }
    iAssert (κ ⊑ ty_lft ty2)%I as "Hout2".
    { by iApply lft_incl_trans; [|iApply lft_intersect_incl_r]. }
    iMod (bor_acc_atomic_cons with "LFT Hbor") as "[[H Hclose]|[#H† Hclose]]";
      [done|..]; last first.
    { iMod "Hclose" as "_". iSplitL "H◯1".
      - iExists _, _. iFrame "%#". iExists _, _. iFrame "∗%". by iApply bor_fake.
      - iExists _, _. iFrame "%#". rewrite /= Hp. iSplitR; [done|].
        iExists _, _. iFrame "∗%". by iApply bor_fake. }
    iDestruct "H" as (?) "(>H● & _ & H1 & H2)".
    iDestruct (own_valid_2 with "H● H◯") as %->%excl_auth_agree_L.
    iMod ("Hclose" with "[H● H◯] [H●1 H●2 H1 H2]") as "Hbor"; last first.
    - iMod (bor_sep with "LFT Hbor") as "[Hbor1 Hbor2]"; [done|].
      iSplitL "H◯1 Hbor1".
      + iExists _, _. iFrame "#%". auto with iFrame.
      + iExists _, _. iFrame "#". rewrite /= Hp. iSplitR; [done|]. auto with iFrame.
    - rewrite -!(bi.exist_intro depth'). iFrame.
      iSplit; iApply (persist_time_rcpt_mono with "Hdepth"); lia.
    - iIntros "!> [H1 H2]".
      iDestruct "H1" as (depth1) "(_ & >Hdepth1 & H1)".
      iDestruct "H2" as (depth2) "(_ & >Hdepth2 & H2)".
      iCombine "Hdepth1 Hdepth2" as "Hdepth12".
      rewrite -persist_time_rcpt_sep -Max.succ_max_distr.
      iExists _. iFrame "Hdepth12".
      iMod (own_update_2 with "H● H◯") as "[$ _]"; [by apply excl_auth_update|].
      iSplitL "H1"; (iApply ty_own_mt_depth_mono; [|done]); lia.
  Qed.

  Lemma tctx_merge_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2]
                  [p ◁ &uniq{κ}(product2 ty1 ty2)].
  Proof.
    iIntros (tid q) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]".
    iDestruct "H1" as ([[]|] [|depth1]) "(Hdepth1 & Hp1 & #Hout1 & H1)"=>//. iDestruct "Hp1" as %Hp1.
    rewrite /tctx_elt_interp /= Hp1.
    iDestruct "H2" as (v2 [|depth2]) "(Hdepth2 & Hp2 & #Hout2 & H2)"=>//. iDestruct "Hp2" as %[=<-].
    iExists _, _. iCombine "Hdepth1 Hdepth2" as "Hdepth".
    rewrite -persist_time_rcpt_sep -Max.succ_max_distr. iFrame "Hdepth".
    iSplitR; [done|]. iSplitR.
    { rewrite lft_intersect_list_app. by iApply lft_incl_glb. }
    iDestruct "H1" as (depth1' γ1 ?) "[H◯1 H1]".
    iDestruct "H2" as (depth2' γ2 ?) "[H◯2 H2]".
    iMod (own_alloc (●E _ ⋅ ◯E _)) as (γ) "[H● H◯]";
      [by apply excl_auth_valid|].
    iExists _, _. iSplitR; [iPureIntro; apply Nat.max_le_compat; eassumption|].
    iFrame "H◯". iMod (bor_combine with "LFT H1 H2") as "H"; first solve_ndisj.
    setoid_rewrite split_prod_mt.
    iMod (bor_acc_atomic_cons with "LFT H") as "[[[H1 H2] Hclose]|[H† Hclose]]";
      [done|..]; first last.
    { iMod "Hclose" as "_". by iApply bor_fake. }
    iDestruct "H1" as (depth1'') "(>H●1 & >Hdepth1' & H1)".
    iDestruct "H2" as (depth2'') "(>H●2 & >Hdepth2' & H2)".
    iDestruct (own_valid_2 with "H●1 H◯1") as %->%excl_auth_agree_L.
    iDestruct (own_valid_2 with "H●2 H◯2") as %->%excl_auth_agree_L.
    iCombine "Hdepth1' Hdepth2'" as "Hdepth".
    rewrite -persist_time_rcpt_sep -Max.succ_max_distr.
    iApply ("Hclose" with "[H◯1 H◯2 H●1 H●2]").
    - iIntros "!> H". iDestruct "H" as (depth') "(_ & >#Hdepth' & H1 & H2)".
      rewrite -!(bi.exist_intro depth'). iFrame "∗#".
      iMod (own_update_2 with "H●1 H◯1") as "[$ _]"; [by apply excl_auth_update|].
      iMod (own_update_2 with "H●2 H◯2") as "[$ _]"; [by apply excl_auth_update|].
      done.
    - iExists _. iFrame "H● Hdepth". iNext.
      iSplitL "H1"; (iApply ty_own_mt_depth_mono; [|done]); lia.
  Qed.

  Lemma uniq_is_ptr κ ty depth tid (vl : list val) :
    ty_own (&uniq{κ}ty) depth tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof. iIntros "[? H]". destruct vl as [|[[]|][]], depth; eauto. Qed.

  Lemma tctx_split_uniq_prod E L κ tyl p :
    tctx_incl E L [p ◁ &uniq{κ}(product tyl)]
                  (hasty_ptr_offsets p (uniq_bor κ) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.

  Lemma tctx_merge_uniq_prod E L κ tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (uniq_bor κ) tyl 0)
                   [p ◁ &uniq{κ}(product tyl)].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.
*)

  (** * Splitting with [tctx_extract_elt]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)
  Lemma tctx_extract_split_own_prod {𝔄 𝔄l 𝔅l ℭl} (t: _ 𝔄) n (tyl: _ 𝔄l)
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_offsets n p tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq. {
    eapply (tctx_incl_frame_r +[_] (_ +:: _)). eapply tctx_incl_trans;
    [apply tctx_split_own_xprod|done]. } move=>/= ?[??].
    rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

  Lemma tctx_extract_split_shr_prod {𝔄 𝔄l 𝔅l ℭl} (t: _ 𝔄) κ (tyl: _ 𝔄l)
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_shr_offsets κ p tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq. {
    eapply (tctx_incl_frame_r +[_] (_ +:: _)). eapply tctx_incl_trans;
    [apply tctx_split_shr_xprod|done]. } move=>/= ?[??].
    rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

(*
  Lemma tctx_extract_split_uniq_prod E L p p' κ ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (uniq_bor κ) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ &uniq{κ}(Π tyl)) :: T) (T' ++ T).
  Proof.
    intros. apply (tctx_incl_frame_r T [_] (_::_)). by rewrite tctx_split_uniq_prod.
  Qed.
*)

  (** * Merging with [tctx_extract_elt]. *)

(*
  Fixpoint extract_tyl E L p (ptr: type → type) tyl (off : nat) T T' : Prop :=
    match tyl with
    | [] => T = T'
    | ty :: tyl => ∃ T'',
        tctx_extract_hasty E L (p +ₗ #off) (ptr ty) T T'' ∧
        extract_tyl E L p ptr tyl (off + ty.(ty_size)) T'' T'
    end.

  Lemma tctx_extract_merge_ptr_prod E L p ptr tyl T T' :
    tctx_incl E L (hasty_ptr_offsets p ptr tyl 0) [p ◁ ptr $ product tyl] →
    extract_tyl E L p ptr tyl 0 T T' →
    tctx_extract_hasty E L p (ptr (Π tyl)) T T'.
  Proof.
    rewrite /extract_tyl /tctx_extract_hasty=>Hi Htyl.
    etrans; last by eapply (tctx_incl_frame_r T' _ [_]). revert T Htyl. clear.
    generalize 0%nat. induction tyl=>[T n /= -> //|T n /= [T'' [-> Htyl]]]. f_equiv. auto.
  Qed.

  Lemma tctx_extract_merge_own_prod E L p n tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (own_ptr n) tyl 0 T T' →
    tctx_extract_hasty E L p (own_ptr n (Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_own_prod. Qed.

  Lemma tctx_extract_merge_uniq_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (uniq_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&uniq{κ}(Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_uniq_prod. Qed.

  Lemma tctx_extract_merge_shr_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (shr_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&shr{κ}(Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_shr_prod. Qed.
*)

End product_split.

(*
(* We do not want unification to try to unify the definition of these
   types with anything in order to try splitting or merging. *)
Global Hint Opaque tctx_extract_hasty : lrust_typing lrust_typing_merge.

(* We make sure that splitting is tried before borrowing, so that not
   the entire product is borrowed when only a part is needed. *)
Global Hint Resolve tctx_extract_split_own_prod tctx_extract_split_uniq_prod tctx_extract_split_shr_prod
    | 5 : lrust_typing.

(* Merging is also tried after everything, except
   [tctx_extract_hasty_further]. Moreover, it is placed in a
   difference hint db. The reason is that it can make the proof search
   diverge if the type is an evar.

   Unfortunately, priorities are not taken into account accross hint
   databases with [typeclasses eauto], so this is useless, and some
   solve_typing get slow because of that. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5304
*)
Global Hint Resolve tctx_extract_merge_own_prod tctx_extract_merge_uniq_prod tctx_extract_merge_shr_prod
    | 40 : lrust_typing_merge.
Global Hint Unfold extract_tyl : lrust_typing.
*)
