From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Utility for Vectors *)

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.

Lemma surjective_vcons {A n} (xl: vec A (S n)) : xl = vhd xl ::: vtl xl.
Proof. by inv_vec xl. Qed.

Lemma surjective_vcons_fun {A B n} (f: B → vec A (S n)) :
  f = (λ a, vcons a) ∘ (vhd ∘ f) ⊛ (vtl ∘ f).
Proof. fun_ext=>/= ?. by rewrite -surjective_vcons. Qed.

Program Global Instance vec_0_unique {A} : Unique (vec A 0) := {| unique := [#] |}.
Next Obligation. move=> ? v. by inv_vec v. Qed.

Global Instance vhd_vsingleton_iso {A} : Iso vhd (λ x: A, [#x]).
Proof. split; [|done]. fun_ext=> v. by inv_vec v. Qed.

Global Instance vhd_vtl_vcons_iso {A n} :
  Iso (λ v: _ A (S n), (vhd v, vtl v)) (curry (λ x, vcons x)).
Proof. split; fun_ext; [|by case]=> v. by inv_vec v. Qed.

(** [vzip] *)

Notation vzip := (vzip_with pair).

Lemma vzip_with_app {A B C m n} (f: A → B → C) (xl: _ m) (xl': _ n) yl yl' :
  vzip_with f (xl +++ xl') (yl +++ yl') = vzip_with f xl yl +++ vzip_with f xl' yl'.
Proof. induction xl; inv_vec yl; [done|]=>/= ??. by rewrite IHxl. Qed.

(** [vsepat] *)

Notation vsepat := Vector.splitat.

Lemma vsepat_app {A m n} (xl: _ A (m + n)) :
  xl = (vsepat m xl).1 +++ (vsepat m xl).2.
Proof.
  induction m; [done|]=>/=.
  by rewrite [vsepat _ _]surjective_pairing /= -IHm -surjective_vcons.
Qed.
Lemma vapp_ex {A m n} (xl: _ A (m + n)) : ∃yl zl, xl = yl +++ zl.
Proof. eexists _, _. apply vsepat_app. Qed.

Global Instance vapp_vsepat_iso {A} m n : Iso (curry vapp) (@vsepat A m n).
Proof. split; fun_ext.
  - move=> [xl ?]. by elim xl; [done|]=>/= ???->.
  - move=>/= ?. rewrite [vsepat _ _]surjective_pairing /=. induction m; [done|]=>/=.
    by rewrite [vsepat _ _]surjective_pairing /= IHm -surjective_vcons.
Qed.

(** [vapply] and [vfunsep] *)

Definition vapply {A B n} (fl: vec (B → A) n) (x: B) : vec A n := vmap (.$ x) fl.

Fixpoint vfunsep {A B n} : (B → vec A n) → vec (B → A) n :=
  match n with 0 => λ _, [#] | S _ => λ f, (vhd ∘ f) ::: vfunsep (vtl ∘ f) end.

Lemma vapply_lookup {A B n} (fl: _ (B → A) n) (i: fin n) :
  (.!!! i) ∘ vapply fl = fl !!! i.
Proof. by induction fl; inv_fin i. Qed.

Global Instance vapply_vfunsep_iso {A B n} : Iso vapply (@vfunsep A B n).
Proof.
  split; fun_ext; [by elim; [done|]=>/= ???->|]. move=> f. fun_ext=>/= x.
  induction n=>/=; [|rewrite IHn /=]; move: (f x)=> xl; by inv_vec xl.
Qed.

Lemma vapply_funsep {A B n} (f: B → _ A n) : vapply (vfunsep f) = f.
Proof. by rewrite semi_iso'. Qed.

Lemma vfunsep_lookup {A B n} (f: B → _ A n) (i: fin n) :
  vfunsep f !!! i = (.!!! i) ∘ f.
Proof. by rewrite -{2}[f]vapply_funsep vapply_lookup. Qed.

(** Iris *)

Lemma big_sepL_vlookup_acc {A n} {PROP: bi} (Φ: _ → _ → PROP) (xl: vec A n) (i: fin n) :
  ([∗ list] k ↦ x ∈ xl, Φ k x)%I ⊢
  Φ i (xl !!! i) ∗ (Φ i (xl !!! i) -∗ [∗ list] k ↦ x ∈ xl, Φ k x).
Proof. by apply big_sepL_lookup_acc, vlookup_lookup. Qed.

Lemma big_sepL_vlookup {A n} {PROP: bi} (Φ: nat → _ → PROP)
  (xl: vec A n) (i: fin n) `{!Absorbing (Φ i (xl !!! i))} :
  ([∗ list] k ↦ x ∈ xl, Φ k x)%I ⊢ Φ i (xl !!! i).
Proof. rewrite big_sepL_vlookup_acc. apply bi.sep_elim_l, _. Qed.
