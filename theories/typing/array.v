Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic types.
From lrust.typing Require Import product mod_ty.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section array.
  Context `{!typeG Σ}.

  Definition array {A} n (ty: type A) : type (pvec A n) := Π (hrepeat ty n).

  Global Instance array_copy {A} n (ty: _ A) : Copy ty → Copy (array n ty).
  Proof. elim n; apply _. Qed.
  Global Instance array_send {A} n (ty: _ A) : Send ty → Send (array n ty).
  Proof. elim n; apply _. Qed.
  Global Instance array_sync {A} n (ty: _ A) : Sync ty → Sync (array n ty).
  Proof. elim n; apply _. Qed.

  Lemma array_subtype {A B} E L n (f: A → B) ty ty' :
    subtype E L f ty ty' → subtype E L (f -v<$>.) (array n ty) (array n ty').
  Proof. move=> ?. elim: n; [done|]=>/= ??. by apply cons_prod_subtype. Qed.
  Lemma array_eqtype {A B} E L n (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L (f -v<$>.) (g -v<$>.) (array n ty) (array n ty').
  Proof. move=> [??]. split; by apply array_subtype. Qed.

  Lemma array_plus_prod {A} E L m n (ty: _ A) :
    eqtype E L pvsep (curry pvapp) (array (m + n) ty) (array m ty * array n ty).
  Proof.
    elim: m=> [|m Eq].
    - have [->->]: @pvsep A 0 n = prod_map (const -[]) id ∘ prod_left_id' ∧
        curry (@pvapp A 0 n) = prod_left_id ∘ prod_map (const ()) id.
      { split; extensionality x; by [case x=> [[]?]|]. }
      eapply eqtype_trans; [apply eqtype_symm; apply prod_ty_left_id|].
      apply prod_eqtype; [|done].
      apply mod_ty_inout, functional_extensionality. by move=> [].
    - have [->->]: @pvsep A (S m) n = prod_map prod_to_cons_prod id ∘
          prod_assoc ∘ prod_map id pvsep ∘ cons_prod_to_prod ∧
        curry (@pvapp A (S m) n) = prod_to_cons_prod ∘
          (prod_map id (curry pvapp) ∘ (prod_assoc' ∘ prod_map cons_prod_to_prod id)).
      { split; extensionality x; [|by case x=> [[??]?]]. case x=> [? xl]/=.
        by case (pvsep xl). }
      eapply eqtype_trans. { apply mod_ty_outin, _. } eapply eqtype_trans.
      { apply prod_eqtype; [done|apply Eq]. } eapply eqtype_trans.
      { apply prod_ty_assoc. } apply prod_eqtype; [apply mod_ty_inout, _|done].
  Qed.

End array.
