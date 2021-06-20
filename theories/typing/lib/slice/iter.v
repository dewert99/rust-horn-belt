From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util.
From lrust.typing.lib.slice Require Import uniq_slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section iter.
  Context `{!typeG Σ}.

  (** We model the unique iterator the same as the unique slice *)
  Definition iter_uniq {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ (𝔄 * 𝔄)) :=
    uniq_slice κ ty.

  Definition iter_next {𝔄} (ty: type 𝔄) : val :=
    fn: ["bit"] :=
      let: "it" := !"bit" in delete [ #1; "bit"];;
      let: "l" := !"it" in
      "it" <- "l" + #ty.(ty_size);; "it" +ₗ #1 <- !("it" +ₗ #1) - #1;;
      letalloc: "r" <-{ty.(ty_size)} !"l" in
      return: ["r"].

  (* The precondition requires that is the sliced list is non-empty *)
  Lemma iter_uniq_next_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → &uniq{α} ty)
      (λ post '-[(aal, aal')],
        ∃(aa: 𝔄 * 𝔄) aalₜ, aal = aa :: aalₜ ∧ (aal' = aalₜ → post aa)).
  Proof.
  Admitted.

  Definition iter_next_back {𝔄} (ty: type 𝔄) : val :=
    fn: ["bit"] :=
      let: "it" := !"bit" in delete [ #1; "bit"];;
      let: "len" := !("it" +ₗ #1) - #1 in "it" +ₗ #1 <- "len";;
      letalloc: "r" <-{ty.(ty_size)} !(!"it" +ₗ "len" * #ty.(ty_size)) in
      return: ["r"].

  (* The precondition requires that is the sliced list is non-empty *)
  Lemma iter_uniq_next_back_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next_back ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → &uniq{α} ty)
      (λ post '-[(aal, aal')],
        ∃aalᵢ (aa: 𝔄 * 𝔄), aal = aalᵢ ++ [aa] ∧ (aal' = aalᵢ → post aa)).
  Proof.
  Admitted.
End iter.
