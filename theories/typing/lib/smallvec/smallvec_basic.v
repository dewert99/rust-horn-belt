From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.smallvec Require Import smallvec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_basic.
  Context `{!typeG Σ}.

  Global Instance smallvec_type_ne 𝔄 n : TypeNonExpansive (smallvec (𝔄:=𝔄) n).
  Proof.
    split.
    - by apply type_lft_morphism_id_like.
    - by move=> ??/=->.
    - move=>/= > ->*. by do 24 f_equiv.
    - move=>/= > ->*. by do 18 f_equiv; [|f_equiv].
  Qed.

  Global Instance smallvec_send {𝔄} n (ty: type 𝔄) : Send ty → Send (smallvec n ty).
  Proof. move=> ?>/=. by do 24 f_equiv. Qed.

  Global Instance smallvec_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (smallvec n ty).
  Proof. move=> ?>/=. by do 18 f_equiv; [|f_equiv]. Qed.

  Lemma smallvec_resolve {𝔄} n (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (smallvec n ty) (lforall Φ).
  Proof.
    iIntros (????[|]???) "LFT PROPH E L svec/="; [done|].
    iDestruct "svec" as (b ?????(->&?&->)) "big". case b=>/=.
    - iDestruct "big" as (???) "tys".
      by iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys").
    - iDestruct "big" as "[↦tys _]". iIntros "!>!>!>".
      rewrite trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
      iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). by iIntros "!> ?".
  Qed.

  Lemma smallvec_resolve_just {𝔄} n (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (smallvec n ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma smallvec_real {𝔄 𝔅} n (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (smallvec n ty) (map f).
  Proof.
    move=> Rl. split; iIntros (???[|]) "*% LFT E L svec//=".
    - iDestruct "svec" as (b ?????(->&?&->)) "big". case b=>/=.
      + iDestruct "big" as (???) "tys".
        iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
        iApply (step_fupdN_wand with "Upd"). iIntros "!>!>!>!> >(%Eq&$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists true, _, _, _, _, _. iSplit; [done|]. iExists _, _. by iFrame.
      + iDestruct "big" as "[↦tys ex†]". iIntros "!>!>!>".
        rewrite trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
        iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
        iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists false, _, _, _, _, _. iFrame "ex†". iSplit; [done|]. iNext.
        rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame.
    - iDestruct "svec" as (b ????->) "[Bor tys]". case b=>/=; iIntros "!>!>!>".
      + iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
        iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
        iIntros ">(%Eq &$&?) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists true, _, _, _, _. by iFrame.
      + iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
        iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
        iIntros ">(%Eq &$& tys) !>". iSplit.
        { iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
          move: (equal_f Eq π)=>/= <-. by rewrite -vec_to_list_apply vec_to_list_map. }
        iExists false, _, _, _, _. by iFrame.
  Qed.

  Lemma smallvec_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) n ty ty' E L :
    subtype E L ty ty' f → subtype E L (smallvec n ty) (smallvec n ty') (map f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz &?&#?&#?)".
    have Eq: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    iSplit. { iPureIntro. rewrite/=. lia. } iSplit; [done|].
    iSplit; iIntros "!>" (?[|]) "* svec //=".
    - iDestruct "svec" as (b ?????(->&?&->)) "big". iExists b, _, _, _, _, _. case b=>/=.
      + iDestruct "big" as (???) "?". rewrite Eq -EqSz. iSplit; [done|].
        iExists _, _. iSplit; [done|]. by iApply incl_big_sepL_ty_own.
      + iDestruct "big" as "[↦tys ex†]". rewrite !trans_big_sepL_mt_ty_own Eq -EqSz.
        iSplit; [done|]. iFrame "ex†". iNext. iDestruct "↦tys" as (?) "[↦ ?]".
        iExists _. iFrame "↦". by iApply incl_big_sepL_ty_own.
    - iDestruct "svec" as (b ????->) "[↦ big]". iExists b, _, _, _, _. rewrite Eq.
      iSplit; [done|]. iFrame "↦". case b=>/=; by iApply incl_big_sepL_ty_shr.
  Qed.
  Lemma smallvec_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g n ty ty' E L :
    eqtype E L ty ty' f g →
    eqtype E L (smallvec n ty) (smallvec n ty') (map f) (map g).
  Proof. move=> [??]. split; by apply smallvec_subtype. Qed.

  (* smallvec_new *)

  (* smallvec_delete *)

  (* smallvec_len *)

End smallvec_basic.

Global Hint Resolve smallvec_resolve | 5 : lrust_typing.
Global Hint Resolve smallvec_resolve_just smallvec_subtype smallvec_eqtype : lrust_typing.
