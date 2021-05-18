From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit n : type () := {|
    ty_size := n;  ty_lfts := [];  ty_E := [];
    ty_own _ _ _ vl := ⌜length vl = n⌝;  ty_shr _ _ _ _ _ := True;
  |}%I.
  Next Obligation. by iIntros. Qed. Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed. Next Obligation. by iIntros. Qed.
  Next Obligation. iIntros. iApply step_fupdN_intro; [done|]. by iFrame. Qed.
  Next Obligation.
    iIntros. iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
    iSplit; [|simpl; by iFrame]. iPureIntro. apply proph_dep_unique.
  Qed.
  Next Obligation.
    iIntros. iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
    iSplit; [|simpl; by iFrame]. iPureIntro. apply proph_dep_unique.
  Qed.

End uninit.

Notation "↯" := uninit : lrust_type_scope.
Notation unit_ty := (uninit 0).
Notation "()" := unit_ty : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit_send n : Send (↯ n). Proof. done. Qed.
  Global Instance uninit_sync n : Sync (↯ n). Proof. done. Qed.

  Lemma uninit_leak n E L : leak E L (↯ n) (const True).
  Proof. apply leak_just. Qed.

  Global Instance unit_ty_copy: Copy ().
  Proof.
    split; [apply _|]=> *. iIntros "_ _ Na $ !> /=". iExists 1%Qp, [].
    rewrite heap_mapsto_vec_nil.
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
    do 2 (iSplit; [done|]). iIntros "Na". by iDestruct ("ToNa" with "Na") as "$".
  Qed.

End typing.

Global Hint Resolve uninit_leak : lrust_typing.
