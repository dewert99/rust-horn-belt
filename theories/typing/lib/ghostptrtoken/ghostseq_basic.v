From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing logic_fn.
From lrust.typing.lib.ghostptrtoken Require Import ghostseq.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostseq_basic.
  Context `{!typeG Σ}.

  Lemma real_big_sepL'_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅)
    aπl (d: nat) κ tid l E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l)
      ={F}▷=∗ |={F}▷=>^d |={F}=>
        ⌜∃bm, (fmap f) ∘ lapply aπl = const bm⌝ ∗ llctx_interp L q ∗
        [∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l.
  Proof.
    iIntros ([_ Rl]?) "#LFT #E L tys". iInduction aπl as [|?] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. iFrame "L". iPureIntro. unfold compose. by exists []. }
    iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd". iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bm Eq']. exists (b :: bm).
    fun_ext=>/= π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Global Instance seq_type_ne 𝔄 : TypeNonExpansive (ghostseq_ty (𝔄:=𝔄)).
  Proof.
    split; [done|split| |]; simpl.
    - by apply type_lft_morphism_id_like.
    - intros. do 6 f_equiv. intros ?. by eapply Forall2_impl.
    - intros ???(?&?&->&->&?). eexists _, _. split. exact H. 
      intros. eexists _, _. done.  
    - intros **. by do 6 (f_contractive || f_equiv).
    - intros **. by do 6 (f_contractive || f_equiv).
  Qed.

  Global Instance seq_send {𝔄} (ty: type 𝔄) : Send ty → Send (ghostseq_ty ty).
  Proof.  move=> ?>/=. by do 6 (f_equiv || move=>?). Qed.

  Global Instance seq_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (ghostseq_ty ty).
  Proof. move=> ?>/=. by do 6 (f_equiv || move=>?). Qed.

  Definition always_true {𝔄} (P: 𝔄 → Prop) (ty: type 𝔄) := (∀ vπ d tid vl F, (ty_own ty vπ d tid vl) -∗ (|={F}▷=>^d ⟨ π , P (vπ π) ⟩) ∗ (ty_own ty vπ d tid vl) ).

  Lemma resolve_uniq_body' {𝔄} (P: 𝔄 → Prop) (ty: type 𝔄) vπ ξi d κ tid l E L q F :
    always_true P ty → lctx_lft_alive E L κ → ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗ llctx_interp L q -∗
    uniq_body ty vπ ξi d κ tid l ={F}=∗ |={F}▷=>^(S d) |={F}=>
      ⟨π, π (PrVar (𝔄 ↾ prval_to_inh vπ) ξi) = vπ π ∧ P (vπ π)⟩ ∗ llctx_interp L q.
  Proof.
    iIntros (H Alv ?) "#LFT PROPH In E L [Vo Bor] /=".
    iMod (Alv with "E L") as (?) "[[κ κ₊] ToL]"; [solve_ndisj|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&%& ⧖ & Pc &%& ↦ & ty) ToBor]";
      [solve_ndisj|]. iIntros "!>!>!>".
    iDestruct (H with "ty") as "(Obs&ty)".
    iMod (ty_own_proph with "LFT In ty κ₊") as "Upd"; [solve_ndisj|].
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-]. iCombine "Obs Upd" as "Upd".
    iApply (step_fupdN_wand with "Upd"). iIntros "!> (Obs&>(%&%&%& ξl & Toty))".
    iMod (uniq_resolve with "PROPH Vo Pc ξl") as "(Obs'& Pc & ξl)"; [solve_ndisj| |].
    by eapply ty_proph_weaken. iCombine "Obs' Obs" as "$".
    iMod ("Toty" with "ξl") as "[ty κ₊]".
    iMod ("ToBor" with "[⧖ Pc ↦ ty]") as "[_ κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
    iApply "ToL". iFrame.
  Qed.

  Lemma uniq_resolve' {𝔄} (P: 𝔄 → Prop) E L κ (ty: type 𝔄) :
    always_true P ty → lctx_lft_alive E L κ → resolve E L (&uniq{κ} ty) (λ '(a, a'), a' = a ∧ P a).
  Proof.
    move=>/= H??? vπ ?? vl ?. iIntros "LFT PROPH E L [In uniq]".
    case vl as [|[[]|][]]=>//. iDestruct "uniq" as (??[Le Eq]) "uniq".
    iMod (resolve_uniq_body' with "LFT PROPH In E L uniq") as "Upd"; [done..|].
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >(?&$) !>". iApply proph_obs_eq; [|done]=>/= π.
    move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
  Qed.

  Lemma uniq_seq_resolve {𝔄 T} (f: 𝔄 → T) E L κ (ty: type 𝔄) :
  (∀ vπ vπ' d d' tid tid' F, (ty_own ty vπ d tid []) -∗ (ty_own ty vπ' d' tid' []) -∗ (|={F}▷=>^d ⟨ π , f (vπ π) ≠ f (vπ' π)  ⟩) ∗ (ty_own ty vπ d tid []) ∗ (ty_own ty vπ' d' tid' []) )
    → lctx_lft_alive E L κ → resolve E L (&uniq{κ} (ghostseq_ty ty)) (λ '(a, a'), a' = a ∧ NoDup (f <$> a)).
  Proof.
    intros. apply (uniq_resolve'  (λ (a: listₛ 𝔄), _)); [|done].
    iIntros (?????) "token". iDestruct "token" as (?[->->]) "tys".
    iAssert ((|={F}▷=>^d _) ∗ _)%I with "[tys]" as "($&?)"; [|iExists aπl; (iSplit; [|done]; done)].
    iInduction aπl as [|aπ] "IH". iFrame "tys". iApply step_fupdN_full_intro. iApply proph_obs_true=>π/=. constructor.
    iAssert ((|={F}▷=>^d ⟨ π , _⟩) ∗ _ ∗ _)%I with "[tys]" as "(Obs&ty&tys)"; last first.
    iDestruct ("IH" with "tys") as "(Obs'&tys)". iCombine "Obs Obs'" as "Obs".
    iSplitL "Obs". iApply (step_fupdN_wand with "Obs"); iIntros "(Obs&Obs')"; iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>π/=?. rewrite NoDup_cons. done. iFrame. done.
    iClear "IH"; simpl. iInduction aπl as [|aπ'] "IH". iFrame "tys". iApply step_fupdN_full_intro. iApply proph_obs_true=>π/=. rewrite elem_of_nil. intros [].
    iDestruct "tys" as "(ty1&ty2&tys)".
    iDestruct (H with "ty1 ty2") as "(Obs&ty1&$)". 
    iDestruct ("IH" with "[ty1 tys]") as "(Obs'&($&$))". iFrame. iCombine "Obs Obs'" as "Obs".
    iApply (step_fupdN_wand with "Obs"); iIntros "(Obs&Obs')"; iCombine "Obs Obs'" as "Obs".
    iApply (proph_obs_impl with "Obs")=>π/=?. rewrite not_elem_of_cons. done.
  Qed.

  Lemma seq_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (ghostseq_ty ty) (lforall Φ).
  Proof.
    iIntros (????????) "#LFT #PROPH #E L token //=".
    iDestruct "token" as (?[->->]) "tys".
    rewrite trans_big_sepL'_mt_ty_own.
    iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd").
    rewrite vec_to_list_to_vec. unfold lapply. setoid_rewrite lforall_Forall.
    setoid_rewrite Forall_fmap. by iIntros "!> H".
  Qed.

  Lemma seq_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (ghostseq_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma seq_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (ghostseq_ty ty) (fmap f).
  Proof.
    move=> Rl. split; iIntros (????) "*% LFT E L token //=".
    - iDestruct "token" as (?[->->]) "tys".
      rewrite trans_big_sepL'_mt_ty_own.
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first.
      { iExists _. iSplit; [done|].
        rewrite trans_big_sepL'_mt_ty_own.  iFrame. }
      iPureIntro. move: Eq=> [bl Eq]. exists (vec_to_list bl). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.
      rewrite 2! vec_to_list_map vec_to_list_to_vec -list_fmap_compose. reflexivity.
    - iDestruct "token" as (?) "[%Bor tys]".
      iMod (real_big_sepL'_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%Eq &$& tys) !>". iSplit; [|iExists _; by iFrame].
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.  by rewrite Bor.
  Qed.

  Lemma seq_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (ghostseq_ty ty) (ghostseq_ty ty') (fmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "((%EqSz&%Proph) &?&#Own&#Shr)".
    have Eq: ∀(aπl: list (proph 𝔄)), fmap f ∘ lapply aπl = lapply (fmap (f ∘.) aπl).
    { move=> ?. fun_ext=>/= ?. rewrite /lapply -2!list_fmap_compose. reflexivity. }
    iSplit. iPureIntro. split; [done|]. intros ??(?&?&->&->&?).
    rewrite Eq. eexists _, _. do 2 (split; [done|]). rewrite Forall2_fmap_l.
    eapply Forall2_impl. done. simpl. intros. by apply Proph.
    iSplit; [done|]. iSplit; iIntros "!>" (??) "* token //=".
    - iDestruct "token" as (?[->->]) "tys". iExists  _.
      iSplit; [done|]. rewrite big_opL_fmap. simpl.
      iApply (big_sepL_impl with "[$]");
      iModIntro; iIntros (???). simpl. iApply "Own".
    - iDestruct "token" as (?->) "↦". iExists _. rewrite Eq.
      iSplit; [done|].
      rewrite big_opL_fmap. iApply (big_sepL_impl with "↦").
      iModIntro. iIntros (???). iApply "Shr".
  Qed.
  Lemma seq_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (ghostseq_ty ty) (ghostseq_ty ty') (fmap f) (fmap g).
  Proof. move=> [??]. split; by apply seq_subtype. Qed.

  Global Instance seq_zst {𝔄} (ty: type 𝔄) : ZST (ghostseq_ty ty).
  Proof. done. Qed.

  Lemma seq_append {𝔄} (ty: type 𝔄) p1 p2 E L :
  tctx_incl E L +[p1 ◁ (box (ghostseq_ty ty)); p2 ◁ (box (ghostseq_ty ty))] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[s1; s2], post -[s1 ++ s2]).
  Proof. split. solve_proper.
    iIntros (??(s1π&s2π&[])?) "_ _ _ _ $ (ty1&ty2&true) Obs"; 
    iExists (-[λ π, _]); iFrame.
    rewrite tctx_elt_interp_zst 2! tctx_elt_interp_zst''.
    iDestruct "ty1" as (???) "(⧖&%&>(_&->)&ty1)".
    iDestruct "ty2" as (???) "(⧖'&%&>(_&->)&ty2)".
    iCombine "⧖ ⧖'" as "⧖". simpl.
    iModIntro. iExists _. iFrame. iNext. iExists _.
    iSplit. iPureIntro. split; [done|]. fun_ext. intros. rewrite -fmap_app. done.
    rewrite big_sepL_app. iSplitL "ty1"; 
    (iApply (big_sepL_impl with "[-]"); [done|]); iIntros "!> **";
    (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Lemma seq_fappend {𝔄} (ty: type 𝔄) p1 p2 E L :
  tctx_incl E L +[p1 ◁ (box (ghostseq_ty ty)); p2 ◁ (box (ghostseq_ty ty))] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[s1; s2], post -[s2 ++ s1]).
  Proof.
    eapply tctx_incl_ext. eapply tctx_incl_trans. apply tctx_incl_swap. apply seq_append. done.
  Qed.

  Lemma seq_new {𝔄} (ty: type 𝔄) p E L :
  tctx_incl E L +[p ◁ (box ())] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[_], post -[[]]).
  Proof. split. solve_proper.
    iIntros (??(?&[])?) "_ _ _ _ $ (⧖&true) Obs"; 
    iExists (-[λ π, _]); iFrame.
    rewrite tctx_elt_interp_zst'' tctx_elt_interp_zst.
    iDestruct "⧖" as (???) "(⧖&_)".
    iModIntro. iExists _. iFrame. iNext. iExists []. iSplit; done.
  Qed.

  Lemma seq_split {𝔄} (ty: type 𝔄) p1 p2 E L :
  tctx_incl E L +[p1 ◁ (box (ghostseq_ty ty)); p2 ◁ (box (ghost int))] +[null_val ◁ (box (ghostseq_ty ty)); null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[s; i], exists (n: nat), (Z.of_nat n) = i ∧ post -[(take n s); (drop n s)]).
  Proof. split. solve_proper.
    iIntros (??(sπ&zπ&[])?) "_ PROPH _ _ $ (ty&tyz&?) #Obs".
    rewrite 2! tctx_elt_interp_zst''.
    iDestruct "ty" as (???) "(#⧖&%&>(_&->)&ty)".
    iDestruct "tyz" as (???) "(_&>(_&%&%&->))". simpl.
    iMod (proph_obs_sat with "PROPH Obs") as "(%&%&<-&%)"; [done|].
    set aπl1 := (take n aπl). set aπl2 := (drop n aπl).
    replace aπl with (aπl1 ++ aπl2); last first. apply take_drop.
    iDestruct "ty" as "(ty1&ty2)". iModIntro.
    iExists -[(lapply aπl1); (lapply aπl2)]. simpl. iFrame. rewrite 2! tctx_elt_interp_zst.
    iSplit. iSplitL "ty1"; iExists _; iFrame "⧖"; iExists _; iFrame; done.
    iApply (proph_obs_impl with "Obs")=>π/=. intros (?&->%inj&?).
    rewrite /lapply -fmap_take -fmap_drop take_drop in H2. done. intros ??. apply Nat2Z.inj.
  Qed.

  Lemma seq_singleton {𝔄} (ty: type 𝔄) `{!ZST ty} p E L :
  tctx_incl E L +[p ◁ (box ty)] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[x], post -[[x]]).
  Proof. split. solve_proper.
    iIntros (??(?&[])?) "_ _ _ _ $ (ty&true) Obs"; 
    iExists (-[λ π, _]); iFrame.
    rewrite tctx_elt_interp_zst'' tctx_elt_interp_zst.
    iDestruct "ty" as (???) "(⧖&ty)".
    iModIntro. iExists _. iFrame. iNext. iExists [_]. iSplit; [done|]. iFrame. done.
  Qed.

  Lemma seq_destruct_singleton {𝔄} (ty: type 𝔄) `{!ZST ty} p E L :
  tctx_incl E L +[p ◁ (box (ghostseq_ty ty))] +[null_val ◁ (box ty)]
    (λ post '-[s], exists (x: 𝔄), s = [x] ∧ post -[x]).
  Proof. split. solve_proper.
    iIntros (??(sπ&[])?) "_ PROPH _ _ $ (ty&true) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %(?&?&sat&_); [done|]. unfold phd in sat. simpl in sat.
    iExists (-[λ π, match (sπ π) with | [x] => x | _ => x0 end]); iFrame.
    rewrite tctx_elt_interp_zst'' tctx_elt_interp_zst.
    iDestruct "ty" as (???) "(⧖&ty)". iModIntro. iSplitL.
    iExists _. iFrame. iNext. iDestruct "ty" as ([|?[|]][_->]) "ty"; try done. iDestruct "ty" as "($&_)".
    iApply (proph_obs_impl with "Obs")=>π/=[?[->?]]. done.
  Qed.

  (* Lemma seq_one `{!Inhabited 𝔄} (ty: type 𝔄) `{!ZST ty} E L : eqtype E L (!{λ (l: listₛ 𝔄), length l = 1} (ghostseq_ty ty)) ty (λ (l: list 𝔄), l !!! 0) (λ x, [x]).
  Proof. 
    split; iIntros; iModIntro; iIntros "_".
    - iSplit. iPureIntro. split. rewrite zero_size. done.
      intros ??(([|?[|]]&?&->&->&?)&?&?); try done. 
      inversion_clear H. inversion_clear H2. simpl. rewrite right_id. done.
      iSplit. iApply lft_incl_refl.
      iSplit; iModIntro; iIntros (????); [|iIntros (?)]; iIntros "((_&%&%)&%&%&ty)"; [destruct H0 as [->->]| revert H0; intros ->];
      destruct aπl as [|?[|]]; try done; iDestruct "ty" as "(?&_)"; iFrame. 
    - iSplit. iPureIntro. split. rewrite zero_size. done.
      intros. simpl. split. exists [vπ], [ξl]. simpl. rewrite right_id. intuition. 
      exists inhabitant. done.
      iSplit. iApply lft_incl_refl.
      iSplit; iModIntro; iIntros; (iSplit; [by iApply proph_obs_s_true|]); iExists [vπ];
      [iDestruct (zst_size_eq with "[$]") as %->|]; simpl; (iSplit; [done|]); iSplit; done.
  Qed. *)

  Lemma seq_cons {𝔄} (ty: type 𝔄) `{!ZST ty} p1 p2 E L :
  tctx_incl E L +[p1 ◁ (box (ghostseq_ty ty)); p2 ◁ (box ty)] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[s; v], post -[v :: s]).
  Proof.
    eapply tctx_incl_ext. eapply tctx_incl_trans. eapply tctx_incl_tail. apply seq_singleton. done. 
    eapply seq_fappend. move=>?[?[?[]]]/=. done.
  Qed.

  Lemma seq_remove {𝔄} (ty: type 𝔄) `{!ZST ty} p1 p2 E L :
  tctx_incl E L +[p1 ◁ (box (ghostseq_ty ty)); p2 ◁ (box (ghost int))] +[null_val ◁ (box (ghostseq_ty ty)); null_val ◁ (box (ty))]
    (λ post '-[s; i], exists (n: nat) (v: 𝔄), (Z.of_nat n) = i ∧ s !! n = Some v ∧ post -[base.delete n s; v]).
  Proof.
    eapply tctx_incl_ext. eapply tctx_incl_trans. eapply tctx_incl_tail. eapply copy_ghost. done. apply ghost_copy.
    eapply tctx_incl_trans. eapply (tctx_incl_app +[_; _] _ +[_] _). apply seq_split.
    eapply (logic_fn_ghost_tctx_incl' [p2] _ +[]). eapply (plain_logic_fn +[_] _ (λ '-[x], (1: Zₛ))).
    eapply tctx_incl_trans. eapply tctx_incl_tail. eapply tctx_incl_trans. apply seq_split.
    eapply tctx_incl_trans. apply tctx_incl_swap. eapply tctx_incl_tail. apply seq_destruct_singleton. done.
    eapply (tctx_incl_frame_r +[_; _] +[_]). eapply seq_append.
    move=>?[s[?[]]]/=. rewrite /trans_app /trans_tail /trans_upper. simpl.
    f_equiv. f_equiv. setoid_rewrite delete_take_drop. setoid_rewrite drop_drop. setoid_rewrite Nat.add_comm. split.
    move=>[x[<-[lookup ?]]]. split. done. exists 1%nat. split. lia. exists x. simpl.
    split. rewrite -(take_drop_middle _ _ _ lookup) drop_app_alt. done. rewrite take_length. remember (lookup_lt_Some _ _ _ lookup). 
    rewrite min_l. done. apply (le_trans _ (S a) _). lia. done. done.
    intros [<-[? [->%Nat2Z.inj [x[td ?]]]]]. exists x. split. done. simpl in td.
    split. remember (lookup_drop s a 0) as eq. clear Heqeq.
    rewrite Nat.add_comm in eq. rewrite -eq. remember (drop a s) as d; destruct d. done. injection td=><-. done. done. 
  Qed.

      (* Lemma seq_perm {𝔄}  g ty E L :
   (∀ x, f x ≡ₚ x) → subtype E L (ghostseq_ty ty) (ghostseq_ty ty) f.
  Proof. move=> [??]. split; by apply seq_subtype. Qed. *)
  
  (* Rust's GhostSeq::new *)
  Definition ghostseq_new: val :=
    fn: [] :=
      Skip;;
      return: [ #null_loc].

  Lemma ghostseq_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostseq_new (fn(∅) → ghostseq_ty ty) (λ (post: (list 𝔄) → _) '-[], post []).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst. via_tr_impl.
    iApply ghost_dummy. iApply typed_body_tctx_incl. eapply seq_new.
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    move=>π//=.
  Qed.
End ghostseq_basic.

Global Hint Resolve seq_resolve | 5 : lrust_typing.
Global Hint Resolve seq_resolve_just seq_subtype seq_eqtype : lrust_typing.
