From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section empty.
  Context `{!typeG Σ}.

  Program Definition empty {𝔄} : type 𝔄 :=
    {| pt_size := 0; pt_own _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.

  Global Instance empty_empty : Empty (type ∅) := empty.

  Global Instance empty_send {𝔄} : Send (@empty 𝔄). Proof. done. Qed.

  Lemma empty_leak {𝔄} E L Φ : leak E L (@empty 𝔄) Φ.
  Proof. by iIntros "* _ _ _ _" ([?[??]]). Qed.

  Lemma empty_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) E L : subtype E L empty empty f.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|by iIntros].
  Qed.
  Lemma empty_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g E L : eqtype E L empty empty f g.
  Proof. split; apply empty_subtype. Qed.

End empty.

Global Hint Resolve empty_leak empty_subtype empty_eqtype : lrust_typing.
