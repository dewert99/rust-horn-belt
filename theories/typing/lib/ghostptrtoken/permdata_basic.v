From lrust.typing Require Export type.
From lrust.typing Require Import typing zst.
From lrust.typing.lib.ghostptrtoken Require Import permdata.
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
End permdata_basic.

Global Hint Resolve permdata_resolve | 5 : lrust_typing.
Global Hint Resolve permdata_resolve_just permdata_subtype permdata_eqtype : lrust_typing.
