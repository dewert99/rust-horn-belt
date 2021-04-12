Require Import FunctionalExtensionality Equality.
From lrust.typing Require Export type.
From lrust.typing Require Import fixpoint mod_ty lib.option product own.
Set Default Proof Using "Type".

Section list.
  Context `{!typeG Σ}.

  Definition list_ty {A} (ty: type A) : type (list A) :=
    fix_ty (λ ty', <{option_to_list}> (option_ty (ty * box ty')))%T.

  Lemma list_subtype {A B} E L (f: A → B) ty ty' :
    subtype E L f ty ty' → subtype E L (map f) (list_ty ty) (list_ty ty').
  Proof.
    move=> ?. apply fix_subtype=> *. rewrite map_via_option_map.
    eapply subtype_trans; [apply mod_ty_out, _|]. eapply subtype_trans;
    [|apply mod_ty_in]. by apply option_subtype, prod_subtype, box_subtype.
  Qed.

  Lemma list_eqtype {A B} E L (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L (map f) (map g) (list_ty ty) (list_ty ty').
  Proof.
    move=> ?. apply fix_eqtype=> *. rewrite map_via_option_map
    [map g]map_via_option_map -compose_assoc. eapply eqtype_trans;
    [|apply mod_ty_inout, _]. eapply eqtype_trans; [apply mod_ty_outin, _|].
    by apply option_eqtype, prod_eqtype, box_eqtype.
  Qed.

End list.
