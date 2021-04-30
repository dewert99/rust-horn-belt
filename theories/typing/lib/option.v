From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import mod_ty uninit sum (* typing lib.panic *).
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section option.
  Context `{!typeG Σ}.

  Definition option_ty {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) :=
    <{sum_to_option: (() + 𝔄)%ST → optionₛ 𝔄}> (unit_ty + ty).

  Lemma option_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (option_ty ty) (option_ty ty') (option_map f).
  Proof.
    move=> ?. eapply subtype_eq; [solve_typing|]. fun_ext. by case.
  Qed.

  Lemma option_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g →
    eqtype E L (option_ty ty) (option_ty ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply option_subtype. Qed.

(*
  (* Variant indices. *)
  Definition none := 0%nat.
  Definition some := 1%nat.

  Definition option_as_mut : val :=
    fn: ["o"] :=
      let: "o'" := !"o" in
      let: "r" := new [ #2 ] in
    withcont: "k":
      case: !"o'" of
        [ "r" <-{Σ none} ();; "k" [];
          "r" <-{Σ some} "o'" +ₗ #1;; "k" [] ]
    cont: "k" [] :=
      delete [ #1; "o"];; return: ["r"].

  Lemma option_as_mut_type τ :
    typed_val
      option_as_mut (fn(∀ α, ∅; &uniq{α} (option τ)) → option (&uniq{α}τ)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret p).
      inv_vec p=>o. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (o'). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [o ◁ _; r ◁ _])) ; [solve_typing..| |].
    - iIntros (k). simpl_subst.
      iApply type_case_uniq; [solve_typing..|].
        constructor; last constructor; last constructor; left.
      + iApply (type_sum_unit (option $ &uniq{α}τ)%T); [solve_typing..|].
        iApply type_jump; solve_typing.
      + iApply (type_sum_assign (option $ &uniq{α}τ)%T); [try solve_typing..|].
        iApply type_jump; solve_typing.
    - iIntros "/= !>". iIntros (k args). inv_vec args. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition option_unwrap_or τ : val :=
    fn: ["o"; "def"] :=
      case: !"o" of
      [ delete [ #(S τ.(ty_size)); "o"];;
        return: ["def"];

        letalloc: "r" <-{τ.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];; delete [ #τ.(ty_size); "def"];;
        return: ["r"]].

  Lemma option_unwrap_or_type τ :
    typed_val (option_unwrap_or τ) (fn(∅; option τ, τ) → τ).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([] ϝ ret p). inv_vec p=>o def. simpl_subst.
    iApply type_case_own; [solve_typing|]. constructor; last constructor; last constructor.
    + right. iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    + left. iApply type_letalloc_n; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_delete (Π[uninit _;uninit _;uninit _])); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition option_unwrap τ : val :=
    fn: ["o"] :=
      case: !"o" of
      [ let: "panic" := panic in
        letcall: "emp" := "panic" [] in
        case: !"emp" of [];

        letalloc: "r" <-{τ.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];;
        return: ["r"]].

  Lemma option_unwrap_type τ :
    typed_val (option_unwrap τ) (fn(∅; option τ) → τ).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([] ϝ ret p). inv_vec p=>o. simpl_subst.
    iApply type_case_own; [solve_typing|]. constructor; last constructor; last constructor.
    + right. iApply type_let; [iApply panic_type|solve_typing|].
        iIntros (panic). simpl_subst.
      iApply (type_letcall ()); [solve_typing..|]. iIntros (r). simpl_subst.
      iApply type_case_own; solve_typing.
    + left. iApply type_letalloc_n; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_delete (Π[uninit _;uninit _;uninit _])); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.
*)

End option.

Global Hint Resolve option_subtype option_eqtype : lrust_typing.
