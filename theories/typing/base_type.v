From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(* [base] is a version of the empty type used internally in the model, using an
  arbitrary refinement type. It is used for the base case of the fixpoint
  type. *)

Section base.
  Context `{!typeG Σ}.

  Program Definition base {𝔄} : type 𝔄 :=
    {| st_size := 0; st_lfts := [];  st_E := [];
       st_proph _ _ := false; st_own _ _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.

  Global Instance base_send {𝔄} : Send (@base 𝔄).
  Proof. done. Qed.

  Lemma base_resolve {𝔄} E L Φ : resolve E L (@base 𝔄) Φ.
  Proof. iIntros "* _ _ _ _" ([]). Qed.

  Lemma base_real {𝔄 𝔅} E L (f: 𝔄 → 𝔅) : real E L base f.
  Proof.
    split.
    - iIntros "*% _ _ _" ([]).
    - by iIntros "*% _ _ _ (%x&_&>%)".
  Qed.

  Lemma base_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) E L : subtype E L base base f.
  Proof.
    apply subtype_simple_type. simpl. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|by iIntros].
  Qed.
  Lemma base_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g E L : eqtype E L base base f g.
  Proof. split; apply base_subtype. Qed.
End base.

Global Hint Resolve base_resolve base_subtype base_eqtype : lrust_typing.
