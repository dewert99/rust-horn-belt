From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

(* Minimal support for panic. Lambdarust does not support unwinding the
   stack. Instead, we just end the current thread by not calling any
   continuation.

   This properly models "panic=abort", but fails to take into account the
   trouble caused by unwinding. This is why we do not get into trouble with
   [take_mut]. *)

Section panic.
  Context `{!typeG Σ}.

  Definition panic : val :=
    fn: [] := #☠.

  Lemma panic_type : typed_val panic (fn(∅) → ∅) (λ _ _, False).
  Proof.
    eapply type_fn; [solve_typing|]=>/= *.
    iIntros (tid [] postπ) "LFT TIME UNIQ PROPH HE Hna HL Hk HT Hproph /=". simpl_subst.
    by iApply wp_value.
  Qed.

  Notation "'assert' e" :=
    (if: e then #0 else #☠)%E
    (at level 102, e at level 99 ) : expr_scope.

  Lemma type_assert_instr {ℭ} E L (C : cctx ℭ) p:
    typed_instr E L +[p ◁ bool_ty] (assert p) (const +[]) (λ post '-[b], if b then post -[] else False : Prop).
  Proof.
    iIntros (? postπ [vπ []]) "LFT TIME #PROPH UNIQ He Hna HL [HT _] #Hproph".
    wp_bind p. iApply (wp_hasty with "HT"). iIntros (???) "⧖ HT".
    iMod (proph_obs_sat with "PROPH Hproph") as (?) "?"; first solve_ndisj.
    iDestruct "HT" as ([|]->) "%Eq"; move: Eq=> [=->]; wp_case.
    - iExists -[]. iFrame "#∗".
    - done.
  Qed.

  Lemma type_assert {𝔄l 𝔅l ℭ} E L (C : cctx ℭ) (T : tctx 𝔄l) (T' : tctx 𝔅l) p e trx tr:
    Closed [] e → tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L C T' e tr -∗
    typed_body E L C T (assert p ;; e) (trx ∘ (λ post '(b -:: al), if b then tr post al else False : Prop)).
  Proof.
    iIntros (??) "?". iApply type_seq; [by eapply type_assert_instr |solve_typing| |done].
    f_equal. fun_ext => /= ?. fun_ext. by case.
  Qed.
End panic.
