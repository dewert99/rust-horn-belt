From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section array.
  Context `{!typeG Σ}.

  Lemma split_array_mt {𝔄 n} (ty: type 𝔄) l q (aπl: _ n) d tid :
    (l ↦∗{q}: λ vl, ∃wll: vec _ _, ⌜vl = concat wll⌝ ∗
      [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2)%I ⊣⊢
    [∗ list] i ↦ aπ ∈ aπl, (l +ₗ (i * ty.(ty_size))%nat) ↦∗{q}: ty.(ty_own) aπ d tid.
  Proof. iSplit.
    - iIntros "(%& ↦s &%&->& tys)". iInduction aπl as [] "IH" forall (l);
      inv_vec wll; [done|]=>/= ??. iRevert "↦s tys".
      rewrite heap_mapsto_vec_app. iIntros "[↦ ↦s][ty tys]".
      iDestruct (ty_size_eq with "ty") as %->. iSplitL "↦ ty".
      { iExists _. rewrite shift_loc_0. iFrame. }
      setoid_rewrite <-shift_loc_assoc_nat. iApply ("IH" with "↦s tys").
    - iIntros "↦owns". iInduction aπl as [] "IH" forall (l)=>/=.
      { iExists []. iSplitR; by [rewrite heap_mapsto_vec_nil|iExists [#]=>/=]. }
      iDestruct "↦owns" as "[(%& ↦ & ty) ↦owns]".
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "↦owns") as (?) "(↦s &%&->& tys)". iExists (_++_).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as %->.
      iFrame "↦ ↦s". iExists (_:::_). iSplit; [done|]. iFrame.
  Qed.

  Program Definition array {𝔄} n (ty: type 𝔄) : type (vecₛ 𝔄 n) := {|
    ty_size := n * ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := ∃wll: vec _ _, ⌜vl = concat wll⌝ ∗
      [∗ list] aπwl ∈ vzip (vfunsep vπ) wll, ty.(ty_own) aπwl.1 d tid aπwl.2;
    ty_shr vπ d κ tid l := [∗ list] i ↦ aπ ∈ vfunsep vπ,
      ty.(ty_shr) aπ d κ tid (l +ₗ (i * ty.(ty_size))%nat);
  |}%I.
  Next Obligation.
    iIntros "* (%&->& All)". setoid_rewrite ty_size_eq.
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl.
    iInduction aπl as [] "IH"; inv_vec wll; [done|]=>/= ??. rewrite/= app_length.
    iDestruct "All" as "[-> All]". by iDestruct ("IH" with "All") as %->.
  Qed.
  Next Obligation. move=>/= *. do 6 f_equiv. by apply ty_own_depth_mono. Qed.
  Next Obligation. move=>/= *. do 3 f_equiv. by apply ty_shr_depth_mono. Qed.
  Next Obligation.
    iIntros "* #In". rewrite !big_sepL_forall. iIntros "All %%%".
    iApply (ty_shr_lft_mono with "In"). by iApply "All".
  Qed.
  Next Obligation.
    iIntros (??????? l ? q ?) "#LFT #In Bor κ". rewrite split_array_mt.
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl. iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ+]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ+ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.
  Next Obligation.
    iIntros (????????? q ?) "#LFT #In (%&->& tys) κ".
    rewrite -{2}[vπ]vapply_funsep. move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl.
    iInduction aπl as [] "IH" forall (q); inv_vec wll=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      do 2 (iSplitR; [done|]). iIntros "_!>". iFrame "κ". by iExists [#]=>/=. }
    move=> ??. iDestruct "κ" as "[κ κ+]". iDestruct "tys" as "[ty tys]".
    iMod (ty_own_proph with "LFT In ty κ") as "Toty"; [done|].
    iMod ("IH" with "tys κ+") as "Totys". iCombine "Toty Totys" as "Totys".
    iApply (step_fupdN_wand with "Totys").
    iIntros "!>[>(%&%&%& ξl & Toty) >(%&%&%& ζl & Totys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iSplit. { iPureIntro. by apply proph_dep_vcons. }
    iFrame "ξζl". iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[ty $]".
    iMod ("Totys" with "ζl") as "[(%wll &%& tys) $]". iModIntro.
    iExists (_ ::: wll). iSplitR; [iPureIntro=>/=; by f_equal|]. iFrame.
  Qed.
  Next Obligation.
    iIntros (???????? l ? q ?) "#LFT #In #In' tys κ'".
    rewrite -{2}[vπ]vapply_funsep. move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl.
    iInduction aπl as [] "IH" forall (q l)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      do 2 (iSplitR; [done|]). iIntros "_!>". iFrame. }
    iDestruct "κ'" as "[κ' κ'+]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Toty"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "tys κ'+") as "Totys".
    iCombine "Toty Totys" as "Totys". iIntros "!>!>".
    iApply (step_fupdN_wand with "Totys").
    iIntros "[>(%&%&%& ξl & Toty) >(%&%&%& ζl & Totys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iSplit. { iPureIntro. by apply proph_dep_vcons. }
    iFrame "ξζl". iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[$$]". by iMod ("Totys" with "ζl") as "[$$]".
  Qed.

  Global Instance array_ne {𝔄} n : NonExpansive (@array 𝔄 n).
  Proof. solve_ne_type. Qed.

End array.

Notation "[ ty ; n ]" := (array n ty) (format "[ ty ;  n ]") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance array_type_ne {𝔄} n : TypeNonExpansive (@array _ _ 𝔄 n).
  Proof.
    split; [by apply type_lft_morph_id_like|by move=>/= ??->| | ]=>/= > Sz *;
    [by do 6 f_equiv|rewrite Sz; by do 3 f_equiv].
  Qed.

  Global Instance array_copy {𝔄} n (ty: _ 𝔄) : Copy ty → Copy [ty; n].
  Proof.
    split; [apply _|]=>/= vπ ???? F l q ? HF. iIntros "#LFT tys Na κ".
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl. iInduction aπl as [] "IH" forall (q l F HF)=>/=.
    { iModIntro. iExists 1%Qp, []. rewrite difference_empty_L heap_mapsto_vec_nil.
      iFrame "Na κ". iSplitR; [by iExists [#]=>/=|]. by iIntros. }
    rewrite shift_loc_0. iDestruct "tys" as "[ty tys]". iDestruct "κ" as "[κ κ+]".
    iMod (copy_shr_acc with "LFT ty Na κ") as (q' ?) "(Na & ↦ & #ty & Toκ)";
    [done| |]. { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    setoid_rewrite <-shift_loc_assoc_nat.
    iMod ("IH" with "[%] tys Na κ+") as (q'' ?) "(Na & ↦' & (%&>->& #tys) & Toκ+)".
    { apply subseteq_difference_r. { symmetry. apply shr_locsE_disj. }
      move: HF. rewrite -plus_assoc shr_locsE_shift. set_solver. }
    case (Qp_lower_bound q' q'')=> [q'''[?[?[->->]]]]. iExists q''', (_ ++ _).
    rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as ">->".
    iDestruct "↦" as "[$ ↦r]". iDestruct "↦'" as "[$ ↦r']".
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { rewrite shr_locsE_shift. set_solver. } iSplitR.
    { iIntros "!>!>". iExists (_:::_)=>/=. iSplit; by [|iSplit]. }
    iIntros "!> Na [↦ ↦']". iDestruct ("ToNa" with "Na") as "Na".
    iMod ("Toκ+" with "Na [$↦' $↦r']") as "[Na $]". iApply ("Toκ" with "Na [$↦ $↦r]").
  Qed.

  Global Instance array_send {𝔄} n (ty: _ 𝔄) : Send ty → Send [ty; n].
  Proof. move=> >/=. by do 6 f_equiv. Qed.
  Global Instance array_sync {𝔄} n (ty: _ 𝔄) : Sync ty → Sync [ty; n].
  Proof. move=> >/=. by do 3 f_equiv. Qed.

  Lemma array_subtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L [ty; n] [ty'; n] (vmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%Sz & ? & #InOwn & #InShr)".
    iSplit; [by rewrite/= Sz|]. iSplit; [done|].
    have Eq: ∀vπ, vfunsep (vmap f ∘ vπ) = vmap (f ∘.) (vfunsep vπ).
    { move=> ?? vπ. rewrite -{1}[vπ]vapply_funsep.
      move: {vπ}(vfunsep vπ)=> aπl. by elim aπl; [done|]=>/= ???<-. }
    iSplit; iIntros "!> %vπ %/="; rewrite Eq; move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl.
    - iIntros "* (%wll &->& tys)". iExists _. iSplit; [done|].
      iInduction aπl as [] "IH"; inv_vec wll; [done|]=>/= ??.
      iDestruct "tys" as "[ty tys]". iSplitL "ty"; by [iApply "InOwn"|iApply "IH"].
    - iIntros "%% %l". iInduction aπl as [] "IH" forall (l); [by iIntros|]=>/=.
      iIntros "[#ty #tys]". rewrite Sz. setoid_rewrite <-shift_loc_assoc_nat.
      iSplitL "ty"; by [iApply "InShr"|iApply "IH"].
  Qed.
  Lemma array_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' n E L :
    eqtype E L ty ty' f g → eqtype E L [ty; n] [ty'; n] (vmap f) (vmap g).
  Proof. move=> [??]. split; by apply array_subtype. Qed.

  Lemma array_one {𝔄} (ty: _ 𝔄) E L : eqtype E L [ty; 1] ty vhd (λ x, [#x]).
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "% _!>_".
    iSplit; [by rewrite/= Nat.add_0_r|]. iSplit; [iApply lft_equiv_refl|].
    have Eq: ∀vπ, vhd ∘ vπ = vhd (vfunsep vπ). { move=> ??? vπ.
    rewrite -{1}[vπ]vapply_funsep. move: (vfunsep vπ)=> aπl. by inv_vec aπl. }
    iSplit; iIntros "!> %vπ */="; rewrite Eq;
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl; inv_vec aπl=> ?; [iSplit|].
    - iIntros "(%wll &->&?)". inv_vec wll=>/= ?. by do 2 rewrite right_id.
    - iIntros "?". iExists [# _]=>/=. do 2 rewrite right_id. by iSplit.
    - rewrite right_id shift_loc_0. by iApply bi.equiv_iff.
  Qed.

  Lemma array_plus_prod {𝔄} m n (ty: _ 𝔄) E L :
    eqtype E L [ty; m + n] ([ty; m] * [ty; n]) (vsepat m) (curry vapp).
  Proof.
    apply eqtype_symm, eqtype_unfold; [apply _|]. iIntros (?) "_!>_".
    iSplit; [iPureIntro=>/=; lia|]. iSplit. { rewrite/= lft_intersect_list_app.
    iApply lft_intersect_equiv_idemp. }
    have Eq: ∀vπ: proph (vec 𝔄 _ * _), vfunsep (curry vapp ∘ vπ) =
      vfunsep (fst ∘ vπ) +++ vfunsep (snd ∘ vπ).
    { move=> ?? vπ. have {1}<-: pair ∘ vapply (vfunsep $ fst ∘ vπ) ⊛
      vapply (vfunsep $ snd ∘ vπ) = vπ by rewrite !semi_iso' -surjective_pairing_fun.
      move: (_ $ fst ∘ _)=> aπl. by elim aπl; [by rewrite semi_iso'|]=>/= ???<-. }
    iSplit; iIntros "!> %vπ %/="; rewrite Eq; move: (vfunsep (fst ∘ vπ))=> aπl;
    move: {vπ}(vfunsep (snd ∘ vπ))=> bπl; iIntros "*"; [iSplit|].
    - iIntros "(%&%&->&(%&->&?)&(%&->&?))". iExists (_+++_).
      rewrite vzip_with_app !vec_to_list_app concat_app. by iFrame.
    - iIntros "(%wll &->& tys)". move: (vapp_ex wll)=> [?[?->]].
      rewrite vzip_with_app !vec_to_list_app concat_app. iExists _, _. iSplit; [done|].
      iDestruct "tys" as "[tys tys']". iSplitL "tys"; iExists _; by iFrame.
    - iApply bi.equiv_iff.
      rewrite vec_to_list_app big_sepL_app vec_to_list_length. do 5 f_equiv.
      by rewrite shift_loc_assoc_nat -Nat.mul_add_distr_r.
  Qed.

  Lemma array_succ_prod {𝔄} n (ty: _ 𝔄) E L :
    eqtype E L [ty; S n] (ty * [ty; n]) (λ v, (vhd v, vtl v)) (curry (λ x, vcons x)).
  Proof.
    eapply eqtype_eq. { eapply eqtype_trans; [apply (array_plus_prod 1)|].
    apply prod_eqtype; [apply array_one|solve_typing]. } { done. } { fun_ext. by case. }
  Qed.

  Lemma array_leak {𝔄} (ty: _ 𝔄) n Φ E L :
    leak E L ty Φ → leak E L [ty; n] (λ al, lforall Φ al).
  Proof.
    move=> ?. elim n. { eapply leak_impl; [apply leak_just|]=> v. by inv_vec v. }
    move=> ? IH. eapply leak_impl. { eapply leak_subtype; [by eapply proj1,
    array_succ_prod|]. solve_typing. } move=> v. by inv_vec v.
  Qed.

  Lemma array_leak_just {𝔄} (ty: _ 𝔄) n E L :
    leak E L ty (const True) → leak E L [ty; n] (const True).
  Proof. move=> ?. apply leak_just. Qed.

End typing.

Global Hint Resolve array_leak | 5 : lrust_typing.
Global Hint Resolve array_leak_just array_subtype array_eqtype : lrust_typing.
