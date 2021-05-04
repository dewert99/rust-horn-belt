From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section empty.
  Context `{!typeG Σ}.

  Program Definition empty {𝔄} (n: nat) : type 𝔄 :=
    {| pt_size := n; pt_own _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.

  Global Instance empty_empty : Empty (type ∅) := empty 0.

  Global Instance empty_send {𝔄} n : Send (@empty 𝔄 n). Proof. done. Qed.

  Lemma empty_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) n E L : subtype E L (empty n) (empty n) f.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|by iIntros].
  Qed.
  Lemma empty_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g n E L : eqtype E L (empty n) (empty n) f g.
  Proof. split; apply empty_subtype. Qed.

End empty.
