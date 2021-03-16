From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From lrust.util Require Import types.

(* From lrust.util Require Import types. *)

Set Default Proof Using "Type".

Implicit Type b: bool.

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type bool :=
    {| pt_size := 1;  pt_own b _ vl := ⌜vl = [ #b]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance bool_send: Send bool_ty. Proof. done. Qed.

  Lemma type_bool_instr (b : Datatypes.bool) : typed_val #b bool_ty (λ post _, post -[b]).
  Proof.
    iIntros (E L tid post ?) "_ _ _ $ $ _ ?". iMod persistent_time_receipt_0 as "#H0".
    iApply wp_value. iExists +[const b]. iFrame. rewrite tctx_interp_singleton tctx_hasty_val' //. 
    iExists 0%nat. iFrame "H0". eauto.
  Qed.

  Lemma type_bool {As} (b : Datatypes.bool) E L C (T : tctx As) x e pre:
    Closed (x :b: []) e →
    (∀ (v : val), typed_body E L C ((v ◁ bool_ty) +:: T) (subst' x v e) pre) -∗
    typed_body E L C T (let: x := #b in e) (λ p, pre (b -:: p)).
  Proof. iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done|done]. Qed. 
  
  Lemma type_if {As} E L C (T : tctx As) e1 e2 p pre1 pre2:
    p ◁ bool_ty ∈ T →
    typed_body E L C T e1 pre1 -∗ typed_body E L C T e2 pre2 -∗
    typed_body E L C T (if: p then e1 else e2) (λ a, pre1 a /\ pre2 a).
  Proof.
    iIntros (Hp) "He1 He2". iIntros (tid V) "#LFT #TIME #HE Htl HL HC HT Hv".
    iDestruct (big_sepHLZip'_elem_of _ _ _ _ Hp with "HT") as (?) "#Hp".
    wp_bind p. iApply (wp_hasty with "Hp").
    iIntros (depth [[| |[|[]|]]|]) "_ _ H1"; try (iDestruct "H1" as ([|]) "[_ %]"; done); wp_case.
    - iApply ("He2" with "LFT TIME HE Htl HL HC HT"). 
      iApply (proph_obs_weaken with "Hv"). move => ? [? ?] //.
    - iApply ("He1" with "LFT TIME HE Htl HL HC HT").
      iApply (proph_obs_weaken with "Hv"); move => ? [? ?] //.
  Qed.

End bool.
