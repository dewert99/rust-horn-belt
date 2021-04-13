Require Import FunctionalExtensionality Equality.
From lrust.typing Require Export type.
From lrust.typing Require Import mod_ty array product.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit1: type () :=
    {| pt_size := 1;  pt_own _ _ vl := ⌜∃v, vl = [v]⌝; |}%I.
  Next Obligation. by iIntros "*[%->]". Qed.

  Definition uninit (n: nat) : type () := <{unique}> [uninit1; n].

End uninit.

Notation "↯" := uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit1_send: Send uninit1. Proof. done. Qed.
  Global Instance uninit1_sync: Sync uninit1. Proof. done. Qed.

  Lemma uninit_own n vπ d tid vl : (↯ n).(ty_own) vπ d tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    rewrite mod_ty_own. move: vl. elim: n=> [|n IH] vl.
    - by rewrite mod_ty_own length_zero_iff_nil.
    - rewrite mod_ty_own -/hrepeat -/xprod_ty. iSplit.
      + iDestruct 1 as (??->[?[_[?->]]]) "H /=". rewrite IH. by iDestruct "H" as %->.
      + case vl=>/= [|v vl']; iIntros ([=]). iExists [v], vl'. rewrite IH.
        iPureIntro. split; [done|]. split; [|done]. exists (). split; by [|exists v].
  Qed.

  Lemma uninit_0_unit: (↯ 0 ≡ ())%T.
  Proof.
    split=>// *; [rewrite !mod_ty_own|rewrite !mod_ty_shr];
    by rewrite compose_assoc semi_iso.
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L unique unique (↯ (m + n)) (↯ m * ↯ n).
  Proof.
    have [->->]:
      @unique (() → ()*()) _ = prod_map unique unique ∘ (@pvsep () m n) ∘ unique ∧
      @unique (()*() → ()) _ = unique ∘ (curry (@pvapp () m n) ∘ prod_map unique unique).
    { split; fun_ext; by [case|case=>[[][]]]. }
    eapply eqtype_trans. { apply mod_ty_outin, _. } eapply eqtype_trans.
    { apply array_plus_prod. } apply prod_eqtype; apply mod_ty_inout, _.
  Qed.

End typing.
