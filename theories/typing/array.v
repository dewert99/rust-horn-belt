Require Import FunctionalExtensionality Equality.
From lrust.typing Require Export type.
From lrust.typing Require Import product mod_ty.
Set Default Proof Using "Type".

Section array.
  Context `{!typeG Σ}.

  Definition array {A} n (ty: type A) : type (pvec A n) := Π! (hrepeat ty n).

  Global Instance array_ne {A} n : NonExpansive (@array A n).
  Proof.
    elim n; [by constructor|]=> ? Eq' ??? Eq. apply (.$ Eq) in Eq'. solve_ne_type.
  Qed.

End array.

Notation "[ ty ; n ]" := (array n ty) (format "[ ty ;  n ]") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance array_type_ne {A} n : TypeNonExpansive (@array _ _ A n).
  Proof. elim n; apply _. Qed.
  Global Instance array_copy {A} n (ty: _ A) : Copy ty → Copy [ty; n].
  Proof. elim n; apply _. Qed.
  Global Instance array_send {A} n (ty: _ A) : Send ty → Send [ty; n].
  Proof. elim n; apply _. Qed.
  Global Instance array_sync {A} n (ty: _ A) : Sync ty → Sync [ty; n].
  Proof. elim n; apply _. Qed.

  Lemma array_subtype {A B} E L n (f: A → B) ty ty' :
    subtype E L f ty ty' → subtype E L (f -v<$>.) [ty; n] [ty'; n].
  Proof. move=> ?. elim: n; [done|]=>/= ??. by apply cons_prod_subtype. Qed.
  Lemma array_eqtype {A B} E L n (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L (f -v<$>.) (g -v<$>.) [ty; n] [ty'; n].
  Proof. move=> [??]. split; by apply array_subtype. Qed.

  Lemma array_plus_prod {A} E L m n (ty: _ A) :
    eqtype E L pvsep (curry pvapp) [ty; m + n] ([ty; m] * [ty; n]).
  Proof.
    elim: m=> [|m Eq].
    - have [->->]: @pvsep A 0 n = prod_map unique id ∘ prod_left_id' ∧
        curry (@pvapp A 0 n) = prod_left_id ∘ prod_map unique id.
      { split; fun_ext; by [case=> [[]?]|]. }
      eapply eqtype_trans; [apply eqtype_symm; apply prod_ty_left_id|].
      apply prod_eqtype; [|done]. apply mod_ty_inout, _.
    - have [->->]: @pvsep A (S m) n = prod_map prod_to_cons_prod id ∘
          prod_assoc ∘ prod_map id pvsep ∘ cons_prod_to_prod ∧
        curry (@pvapp A (S m) n) = prod_to_cons_prod ∘
          (prod_map id (curry pvapp) ∘ (prod_assoc' ∘ prod_map cons_prod_to_prod id)).
      { split; fun_ext; [|by case=> [[??]?]]. move=> [? xl]/=. by case (pvsep xl). }
      eapply eqtype_trans; [by apply mod_ty_outin, _|]. eapply eqtype_trans.
      { apply prod_eqtype; [reflexivity|apply Eq]. } eapply eqtype_trans;
      [by apply prod_ty_assoc|]. apply prod_eqtype; [apply mod_ty_inout, _|done].
  Qed.

End typing.
