From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(* [base] is a version of the empty type used internally in the model, using an
   arbitrary refinement type. It is used for two purposes:
     1- as a base case for the fixpoint (empty cannot be used since it is
        using the empty semantic type).
     2- as a default type in [sum.v] when performing lookups in lists of types
 *)

Section base.
  Context `{!typeG Σ}.

  Program Definition base {𝔄} : type 𝔄 :=
    {| pt_size := 0; pt_own _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.

  Global Instance base_send {𝔄} : Send (@base 𝔄).
  Proof. done. Qed.

  Lemma base_leak {𝔄} E L Φ : leak E L (@base 𝔄) Φ.
  Proof. by iIntros "* _ _ _ _" ([?[??]]). Qed.

  Lemma base_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) E L : subtype E L base base f.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|by iIntros].
  Qed.
  Lemma base_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g E L : eqtype E L base base f g.
  Proof. split; apply base_subtype. Qed.
End base.

Global Hint Resolve base_leak base_subtype base_eqtype : lrust_typing.
