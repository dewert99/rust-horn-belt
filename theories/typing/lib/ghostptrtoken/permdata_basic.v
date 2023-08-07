From lrust.typing Require Export type.
From lrust.typing Require Import typing zst ptr always_true.
From lrust.typing.lib.ghostptrtoken Require Import permdata heap_util.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section permdata_basic.
  Context `{!typeG Σ}.

  Global Instance permdata_type_ne 𝔄 : TypeContractive (permdata_ty (𝔄:=𝔄)).
  Proof.
    split; [done|split| |]; simpl.
    - by apply type_lft_morphism_id_like.
    - intros. do 5 f_equiv. done.
    - intros ???(?&?&->&?). eexists [_], [_]. split. by constructor. 
      intros. eexists _, _. inversion_clear H0. done.  
    - intros ???->**. do 12 (f_contractive || f_equiv). by simpl in *.
    - intros **. do 8 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance permdata_send {𝔄} (ty: type 𝔄) : Send ty → Send (permdata_ty ty).
  Proof. move=> ?>/=. by do 12 (f_equiv || move=>?). Qed.

  Global Instance permdata_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (permdata_ty ty).
  Proof. move=> ?>/=. by do 8 (f_equiv || move=>?). Qed.

  Lemma permdata_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (permdata_ty ty) (Φ ∘ snd).
  Proof.
    iIntros (????????) "#LFT #PROPH #E L token".
    iDestruct "token" as (??[->->]) "box".
    eapply own_resolve in H. by iApply (H with "LFT PROPH E L box").
  Qed.

  Lemma permdata_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (permdata_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Program Global Instance flat_permdata {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : FlatOwn (permdata_ty ty) := {|
    T := (loc * (proph 𝔄));
    ty_flat' vπ d tid q '(l, vπ') vl := 
      ⌜vl = [] ∧ vπ = λ π, (l, vπ' π)⌝ ∗
        (ty_flat' (ty:=box ty) vπ' d tid q () [ #l]);
  |}%I.
  Next Obligation. 
    intros. iIntros "LFT (%&%&%p&ty) lft". rewrite exist_pair.
    do 2 (iExists' l; iExists' vπ').  setoid_rewrite (is_True_True p). setoid_rewrite bi.True_sep; [|typeclasses eauto..].
    iDestruct (ty_own_flat' with "LFT ty lft") as "X". rewrite exist_nil. done.
  Qed.
  Next Obligation.
    intros ??????[??]??. iIntros "((->&->)&flat)". iDestruct (ty_flat_proph' with "flat") as "(%&%&%&ξl&Toflat)".
    iExists _, _. iSplit. iPureIntro. eexists _, _. intuition. done.
    iFrame. iIntros "ξl". iDestruct ("Toflat" with "ξl") as "$". done.
  Qed.

  Lemma always_true_pair_permdata {𝔄} (ty: type 𝔄) `{!FlatOwn ty} :
    ty.(ty_size) ≠ 0 → (always_true_pair (permdata_ty ty) (λ x1 x2, x1.1 ≠ x2.1)).
  Proof.
    intros sz ?*. setoid_rewrite exist_pair. iIntros "(%&%&ty&_) (%&%&ty'&_)". simpl.
    iDestruct "ty" as "((->&->)&%&->&%&↦0&%&_&%&_)". iDestruct "ty'" as "((->&->)&%&->&%&↦1&%&_&%&_)".
    destruct vl. rewrite -H in sz; simpl in sz; done. destruct vl0. rewrite -H0 in sz; simpl in sz; done.
    do 2 rewrite heap_mapsto_vec_cons.
    iDestruct "↦0" as "(↦0 & _)". iDestruct "↦1" as "(↦1 & _)".
    destruct (decide (t = t0)) as [->|]. iDestruct (no_duplicate_heap_mapsto with "↦0 ↦1") as "[]".
    iApply proph_obs_true=>π. done.
  Qed.

  Lemma permdata_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=locₛ * _) E L (permdata_ty ty) (prod_map id f).
  Proof.
    move=> Rl. split; iIntros (????) "*% LFT E L token".
    - eapply own_real in Rl. destruct Rl as [Rlo _].
      iDestruct "token" as (??[->->]) "own".
      iMod (Rlo with "LFT E L own") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >((%&%Eq) &$&?) !>".
      iSplit; [|iExists _, _; by iSplit].
      iPureIntro. exists (l, v). fun_ext=>/= π. simpl.
      move: (equal_f Eq π)=>/= ->. done.
    - destruct Rl as [_ Rls].
      iDestruct "token" as (??) "(->&shr)". destruct d; [done|]. simpl.
      iIntros "!>!>!>". iMod (Rls with "LFT E L shr") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">((%&%Eq) &$& tys) !>". iSplit; [|iExists _, _; by iFrame].
      iPureIntro. exists (l0, v). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= ->. done.
  Qed.

  Lemma permdata_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (permdata_ty ty) (permdata_ty ty') (prod_map id f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub".
    eapply box_subtype in Sub. iDestruct (Sub with "L") as "#SubO". iIntros "!> #E".
    iDestruct ("Sub" with "E") as "((%EqSz&%Proph) &?&_&#Shr)".
    iDestruct ("SubO" with "E") as "(_&_&#Own&_)".
    have Eq: ∀ (l: loc) (vπ: (proph 𝔄)), (prod_map id f) ∘ (λ π, (l, vπ π)) = (λ π, (l, (f ∘ vπ) π)).
    { move=> ??. fun_ext=>/= ?. done. }
    iSplit. iPureIntro. split; [done|]. intros ??(?&?&->&?).
    rewrite Eq. apply Proph in H. eexists _, _. done.
    iSplit; [done|]. iSplit; iIntros "!>" (??) "* token".
    - iDestruct "token" as (??[->->]) "tys". iExists  _, _.
      iSplit; [done|]. by iApply "Own".
    - iDestruct "token" as (??->) "token". destruct d; [done|]. iExists _, _.
      rewrite Eq. iSplit; [done|]. iNext. by iApply "Shr".
  Qed.
  Lemma permdata_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (permdata_ty ty) (permdata_ty ty') (prod_map id f) (prod_map id g).
  Proof. move=> [??]. split; by apply permdata_subtype. Qed.

  Global Instance permdata_zst {𝔄} (ty: type 𝔄) : ZST (permdata_ty ty).
  Proof. done. Qed.

  Lemma permdata_from_box {𝔄} (ty: type 𝔄) p E L :
  tctx_incl E L +[p ◁ (box (box ty))] +[p ◁ (box ptr); null_val ◁ (box (permdata_ty ty))]
    (λ post '-[x], ∀ l, post -[l; (l, x)]).
  Proof. split. intros ????. do 2 f_equiv. split; intros; by [rewrite -H|rewrite H].
    iIntros (??(bπ&[])?) "_ _ _ _ $ (box&true) Obs".
    iDestruct "box" as ([[| |]|][|]?) "(#⧖&box)"; try done.
    iDestruct "box" as "((%&↦l&box)&†l)". simpl.
    set l' := match vl with | [] => null_loc | v :: _ => match v with | #l1 => match l1 with | LitLoc l2 => l2 | _ => null_loc end | _ => null_loc end end.
    iAssert (▷⌜vl = [ #l']⌝)%I as "#vleq". iNext.
    destruct n; try done. destruct vl as [|[[| |]|][|]]; done.
    iExists (-[const l'; λ π, (l', bπ π)]); iFrame.
    iModIntro. iSplit. rewrite tctx_elt_interp_zst tctx_hasty_val'; [|by rewrite H].
    iSplitL "↦l †l"; iExists _; iFrame "⧖". iFrame. iNext. iExists _. iFrame. iExists _. iFrame "vleq". done.
    iNext. iExists _, _. iSplit; [done|]. simpl. destruct n; try done. destruct vl as [|[[| |]|][|]]; done.
    iApply (proph_obs_impl with "Obs")=>π/=. intuition.
  Qed.

  Lemma permdata_to_box {𝔄} (ty: type 𝔄) p p2 E L :
  tctx_incl E L +[p ◁ (box ptr); p2 ◁ (box (permdata_ty ty))] +[p ◁ (box (box ty))] 
    (λ post '-[l1; (l2, x)], l1 = l2 ∧ post -[x]).
  Proof. split. solve_proper.
    iIntros (??(lπ&pπ&[])?) "_ PROPH _ _ $ (ptr&perm&true) #Obs".
    iExists (-[snd ∘ pπ]). iFrame.
    iDestruct "ptr" as ([[| |]|][|]?) "(_&ptr)"; try done.
    iDestruct "ptr" as "((%&↦l&ptr)&†l)". simpl.
    iMod (proph_obs_sat with "PROPH Obs") as "(%&%sat)"; [done|].
    iModIntro. iSplit. rewrite tctx_elt_interp_zst'' tctx_hasty_val'; [|done].
    iDestruct "perm" as (???) "(⧖&box)". iExists _. iFrame. iNext.
    iDestruct "ptr" as "(%&->&->)". iDestruct "box" as "(%&%&(_&->)&box)".
    iExists _. iFrame. destruct sat as [<- _]. done.
    iApply (proph_obs_impl with "Obs")=>π/=. destruct (pπ π). intuition.
  Qed.
End permdata_basic.

Global Hint Resolve permdata_resolve | 5 : lrust_typing.
Global Hint Resolve permdata_resolve_just permdata_subtype permdata_eqtype : lrust_typing.
