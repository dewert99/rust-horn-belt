From lrust.typing Require Export type.
From lrust.typing Require Import typing lib.option.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section list.
  Context `{!typeG Σ}.

  Definition list_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) :=
    fix_ty (λ ty', <{option_to_list: optionₛ (𝔄 * listₛ 𝔄) → listₛ 𝔄}>
      (option_ty (ty * box ty')))%T.

  Lemma list_leak {𝔄} E L (ty: type 𝔄) Φ :
    leak E L ty Φ → leak E L (list_ty ty) (lforall Φ).
  Proof.
    move=> ?. apply fix_leak=> ??. eapply leak_impl; [solve_typing|]. by case.
  Qed.

  Lemma list_leak_just {𝔄} E L (ty: type 𝔄) :
    leak E L ty (const True) → leak E L (list_ty ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma list_real {𝔄 𝔅} ty (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (list_ty ty) (map f).
  Proof.
    move=> ?. apply fix_real=> ??. eapply real_eq.
    { apply mod_ty_real; [apply _|].
      apply (real_compose (𝔅:=optionₛ(_*listₛ _)) (ℭ:=listₛ _) option_to_list).
      solve_typing. }
    fun_ext. by case.
  Qed.

  Lemma list_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (list_ty ty) (list_ty ty') (map f).
  Proof.
    move=> ?. apply fix_subtype=> ???. eapply subtype_eq; [solve_typing|].
    fun_ext. by case.
  Qed.

  Lemma list_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (list_ty ty) (list_ty ty') (map f) (map g).
  Proof. move=> [??]. by split; apply list_subtype. Qed.
End list.

Global Hint Resolve list_leak | 5 : lrust_typing.
Global Hint Resolve list_leak_just list_real list_subtype list_eqtype
  : lrust_typing.
