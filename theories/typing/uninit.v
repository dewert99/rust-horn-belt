Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic types.
From lrust.typing Require Import mod_ty array product.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit1: type unit :=
    {| pt_size := 1;  pt_own _ _ vl := ⌜∃v, vl = [v]⌝; |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (?) "->". Qed.
  Global Instance uninit1_send : Send uninit1. Proof. done. Qed.

  Definition uninit n : type unit := <{const ()}> (array n uninit1).

  Local Notation tts := (@prepeat id _ ()).
  Local Lemma pvec_unit_unique n x : x = tts n.
  Proof.
    move: x. elim n=> /=[|? IH] x; [by case x|]. case x=> [[]?]. f_equal. apply IH.
  Qed.
  Local Instance const_tt_tts_iso n : Iso (const ()) (const (tts n)).
  Proof.
    split; extensionality x; [|by case x]=>/=. symmetry. apply pvec_unit_unique.
  Qed.

  Lemma uninit_own' n vπd tid vl :
    (array n uninit1).(ty_own) vπd tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof. move: vl vπd. elim: n=> /=[|n IH] vl [vπ ?]; iSplit.
    - by iIntros ([_[_->]]).
    - rewrite length_zero_iff_nil. iIntros (->). iExists (const ()). iPureIntro.
      split; [|done]. extensionality π. simpl. by case (vπ π)=> [].
    - iDestruct 1 as (? _ ??->[_[_[?->]]]) "H /=". rewrite IH. by iDestruct "H" as %->.
    - case vl=> /=[|v vl']; iIntros (Eq); [done|]. iExists (const ((), tts n)).
      iSplit. { iPureIntro. extensionality π. simpl. apply (pvec_unit_unique (S n)). }
      iExists [v], vl'. rewrite IH. iPureIntro. split; [done|].
      split; [|by move: Eq=> [=]]. exists (). split; by [|exists v].
  Qed.
  Lemma uninit_own n vπd tid vl : (uninit n).(ty_own) vπd tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    simpl. setoid_rewrite uninit_own'. iPureIntro. split; [by move=> [_[_->]]|]=> ->.
    exists (const (tts n)). split; [|done]. extensionality π. by case (vπd.1 π).
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (const ((), ())) (const ()) (uninit (m + n)) (uninit m * uninit n).
  Proof.
    have [->->]: @const _ () ((), ()) =
        prod_map (const ()) (const ()) ∘ pvsep ∘ const (tts (m + n)) ∧
      @const _ (() * ()) () =
        const () ∘ (curry pvapp ∘ prod_map (const (tts m)) (const (tts n))).
    { split; extensionality x; by [case x|case x=>[[][]]]. }
    eapply eqtype_trans. { apply mod_ty_outin, _. } eapply eqtype_trans.
    { apply array_plus_prod. } apply prod_eqtype; apply mod_ty_inout, _.
  Qed.

End uninit.
