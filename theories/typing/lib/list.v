From lrust.typing Require Export type.
From lrust.typing Require Import fixpoint mod_ty lib.option product own.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section list.
  Context `{!typeG Σ}.

  Definition list_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) :=
    fix_ty (λ ty', <{option_to_list: optionₛ (𝔄 * listₛ 𝔄) → listₛ 𝔄}>
      (option_ty (ty * box ty')))%T.

  Lemma list_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (list_ty ty) (list_ty ty') (map f).
  Proof.
    move=> ?. apply fix_subtype=> *. eapply subtype_eq; [solve_typing|].
    fun_ext. by case.
  Qed.

  Lemma list_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (list_ty ty) (list_ty ty') (map f) (map g).
  Proof. move=> [??]. by split; apply list_subtype. Qed.

End list.

Global Hint Resolve list_subtype list_eqtype : lrust_typing.
