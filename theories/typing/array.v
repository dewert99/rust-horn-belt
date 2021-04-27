From lrust.typing Require Export type.
From lrust.typing Require Import product mod_ty.
Set Default Proof Using "Type".

Section array.
  Context `{!typeG Σ}.

  Definition array {𝔄} n (ty: type 𝔄) : type (Π! (trepeat 𝔄 n)) := Π! (hrepeat ty n).

  Global Instance array_ne {𝔄} n : NonExpansive (@array 𝔄 n).
  Proof.
    elim n; [by constructor|]=> ? Eq' ??? Eq. apply (.$ Eq) in Eq'. solve_ne_type.
  Qed.

End array.

Notation "[ ty ; n ]" := (array n ty) (format "[ ty ;  n ]") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance array_type_ne {𝔄} n : TypeNonExpansive (@array _ _ 𝔄 n).
  Proof. elim n; apply _. Qed.
  Global Instance array_copy {𝔄} n (ty: _ 𝔄) : Copy ty → Copy [ty; n].
  Proof. elim n; apply _. Qed.
  Global Instance array_send {𝔄} n (ty: _ 𝔄) : Send ty → Send [ty; n].
  Proof. elim n; apply _. Qed.
  Global Instance array_sync {𝔄} n (ty: _ 𝔄) : Sync ty → Sync [ty; n].
  Proof. elim n; apply _. Qed.

  Lemma array_subtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) ty ty' :
    subtype E L f ty ty' → subtype E L (f -v<$>.) [ty; n] [ty'; n].
  Proof. move=> ?. elim: n; [done|]=>/= ??. by apply cons_prod_subtype. Qed.
  Lemma array_eqtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L (f -v<$>.) (g -v<$>.) [ty; n] [ty'; n].
  Proof. move=> [??]. split; by apply array_subtype. Qed.

  Lemma array_plus_prod {𝔄} E L m n (ty: _ 𝔄) :
    eqtype E L pvsep (curry pvapp) [ty; m + n] ([ty; m] * [ty; n]).
  Proof. elim: m=> [|? Eq].
    - eapply eqtype_eq. { eapply eqtype_trans;
      [apply eqtype_symm; apply prod_ty_left_id|]. apply prod_eqtype; [|done].
      apply mod_ty_inout, _. } { done. } { done. }
    - eapply eqtype_eq. { eapply eqtype_trans; [by apply mod_ty_outin, _|].
      eapply eqtype_trans. { eapply prod_eqtype; [reflexivity|apply Eq]. }
      eapply eqtype_trans; [by apply prod_ty_assoc|]. apply prod_eqtype;
      [apply mod_ty_inout, _|done]. } { fun_ext. by case. }
      { fun_ext. by case=> [[??]?]. }
  Qed.

End typing.
