From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section choice.
  Context `{!typeG Σ}.

  Definition choice (b: bool) (P Q: iProp Σ) := if b then P else Q.

  Global Instance choice_proper :
    Proper ((=) ==> (⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choice_ne n :
    Proper ((=) ==> dist n ==> dist n ==> dist n) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choice_mono :
    Proper ((=) ==> (⊢) ==> (⊢) ==> (⊢)) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choise_persistent b P Q:
    Persistent P → Persistent Q → Persistent (choice b P Q).
  Proof. case b; apply _. Qed.
End choice.

Notation "if@ b 'then' P 'else' Q" := (choice b P Q) (at level 200,
  right associativity, format "if@  b  'then'  P  'else'  Q") : bi_scope.

Section smallvec.
  Context `{!typeG Σ}.

  Instance loc_inhabited : Inhabited loc := populate (inhabitant, inhabitant).

  Lemma split_mt_smallvec {𝔄} (ty: type 𝔄) k l' tid b d alπ Φ :
    (l' ↦∗: (λ vl, [S(d') := d] ∃(l: loc) (len ex: nat) wl (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #l; #len; #ex] ++ wl ∧ length wl = k ∧ alπ = lapply aπl⌝ ∗
      if@ b len then (* array mode *)
        ∃(wll: vec _ _) wl', ⌜wl = concat wll ++ wl'⌝ ∗
          [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d' tid aπwl.2
      else (* vector mode *) Φ d' l len ex aπl)) ⊣⊢
    [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗ l' ↦ #l ∗ (l' +ₗ 1) ↦ #len ∗ (l' +ₗ 2) ↦ #ex ∗
      if@ b len then (* array mode *)
        ([∗ list] i ↦ aπ ∈ aπl, (l' +ₗ 3 +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
          ∃wl', ⌜k = (len * ty.(ty_size) + length wl')%nat⌝ ∗ (l' +ₗ 3 +ₗ[ty] len) ↦∗ wl'
      else (* vector mode *)
        ∃wl, ⌜length wl = k⌝ ∗ (l' +ₗ 3) ↦∗ wl ∗ Φ d' l len ex aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (?????(->&?&?)) "big".
      iExists _, _, _, _. iSplit; [done|].
      rewrite !heap_mapsto_vec_cons !shift_loc_assoc. iDestruct "↦" as "($&$&$& ↦)".
      case b; [|iExists _; by iFrame]. iDestruct "big" as (??->) "tys/=".
      iDestruct (big_sepL_ty_own_length with "tys") as %<-.
      rewrite heap_mapsto_vec_app trans_big_sepL_mt_ty_own shift_loc_assoc.
      iDestruct "↦" as "[? ↦]". iSplitR "↦"; iExists _; iFrame.
      by rewrite -app_length.
    - iIntros "big". case d=>// ?.
      iDestruct "big" as (? len ???) "(↦₀ & ↦₁ & ↦₂ & big)". case Eqb: (b len)=>/=.
      + rewrite trans_big_sepL_mt_ty_own.
        iDestruct "big" as "[(%wll & ↦₃ & tys) (%wl' &->& ↦₄)]".
        iDestruct (big_sepL_ty_own_length with "tys") as %Eqsz. iExists ([_;_;_]++_++_).
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_app !shift_loc_assoc -Eqsz.
        iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦₄". iExists _, _, _, _, _.
        iSplit; [by rewrite -app_length|]. rewrite Eqb/=. iExists _, _. by iFrame.
      + iDestruct "big" as (?<-) "[↦₃ ?]". iExists ([_;_;_]++_).
        rewrite !heap_mapsto_vec_cons !shift_loc_assoc. iFrame "↦₀ ↦₁ ↦₂ ↦₃".
        iExists _, len, _, _, _. rewrite Eqb/=. by iFrame.
  Qed.

  (* For simplicity, it always has the location and capacity *)
  Program Definition smallvec_ty {𝔄} (n: nat) (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3 + n * ty.(ty_size);
    ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl := [S(d') := d]
      ∃(l: loc) (len ex: nat) wl (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #l; #len; #ex] ++ wl
          ∧ length wl = (n * ty.(ty_size))%nat ∧ alπ = lapply aπl⌝ ∗
        if@ bool_decide (len ≤ n) then (* array mode *)
          ∃(wll: vec _ _) wl', ⌜wl = concat wll ++ wl'⌝ ∗
            [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d' tid aπwl.2
        else (* vector mode *)
          ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
          (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
          freeable_sz' ((len + ex) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗
        &frac{κ} (λ q, l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #len ∗ (l' +ₗ 2) ↦{q} #ex) ∗
        if@ bool_decide (len ≤ n) then (* array mode *)
          [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l' +ₗ 3 +ₗ[ty] i)
        else (* vector mode *)
          ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros (????[]??) "svec //". iDestruct "svec" as (?????(->&Eq&_)) "?/=".
    by rewrite Eq.
  Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|].
    do 20 f_equiv; apply ty_own_depth_mono; lia.
  Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|].
    do 14 f_equiv; [|f_equiv]; apply ty_shr_depth_mono; lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&?& All)".
    iExists _, _, _, _. iSplit; [done|]. iSplit; [by iApply frac_bor_shorten|].
    case (bool_decide (_ ≤ _))=>/=; rewrite !big_sepL_forall; [|iNext];
    iIntros "**"; iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (? n ty ?? d ? l tid ??) "#LFT In Bor κ". rewrite split_mt_smallvec.
    case d. { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    move=> ?. iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (len) "Bor"; [done|].
    do 2 (iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    do 2 rewrite assoc. iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    rewrite -assoc. iMod (bor_fracture (λ q', _ ↦{q'} _ ∗ _ ↦{q'} _ ∗ _ ↦{q'} _)%I
      with "LFT Bor↦") as "Bor↦"; [done|].
    case Eqb: (bool_decide (len ≤ n))=>/=.
    - iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
      iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
      iApply (step_fupdN_wand with "Toshrs"). iIntros "!>!>!>!> >[?$] !>".
      iExists _, len, _, _. rewrite Eqb/=. iFrame.  done.
    - iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
      iMod (bor_sep_persistent with "LFT Bor κ") as "(_ & Bor & κ)"; [done|].
      iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
      iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
      iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|].
      iIntros "/=!>!>!>". iMod "Borκ" as "[Bor κ]".
      iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
      iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
      iExists _, len, _, _. rewrite Eqb/=. iFrame "Bor↦". by iSplit.
  Qed.
  Next Obligation.
    iIntros (?????[|?]) "*% LFT In svec κ/="; [done|].
    iDestruct "svec" as (? len ???(->&?&->)) "big".
    case Eqb: (bool_decide (len ≤ _))=>/=.
    - iDestruct "big" as (??->) "tys".
      iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd").
      iIntros "!>!>!>!> >(%&%&%& ξl & Totys) !>". iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[? $]". iExists _.
      iModIntro. iExists len, _, _, _. iSplit; [done|].
      rewrite Eqb/=. iExists _, _. by iFrame.
    - iDestruct "big" as "(↦tys & ex & †)". iIntros "!>!>!>".
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys κ") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
      iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
      iExists _, len, _, _, _. iSplit; [done|].
      rewrite Eqb/=. iFrame.
  Qed.
  Next Obligation.
    iIntros (?????[|?]) "*% LFT In In' svec κ'/="; [done|].
    iDestruct "svec" as (????->) "[? tys]".
    case Eqb: (bool_decide (len ≤ _))=>/=; iIntros "!>!>!>".
    - iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Upd"; [done|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%&%&%& ξl & Totys) !>". iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". by iMod ("Totys" with "ξl") as "[$$]".
    - iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Toκ'"; [done|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
      iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.

  Global Instance smallvec_ty_ne {𝔄} n : NonExpansive (@smallvec_ty 𝔄 n).
  Proof. solve_ne_type. Qed.

End smallvec.
