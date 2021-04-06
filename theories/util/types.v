Require Import Equality FunctionalExtensionality.
From stdpp Require Import prelude.
From iris.algebra Require Import monoid ofe.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * List of Types *)
(** We avoid using [list Type] because that can cause universe inconsistency *)

Inductive Types := tnil: Types | tcons: Type → Types → Types.
Implicit Type (A B C D: Type) (As Bs: Types).

Notation "^[ ]" := tnil (at level 5, format "^[ ]").
Infix "^::" := tcons (at level 60, right associativity).
Notation "^[ A ; .. ; B ]" := (A ^:: .. (B ^:: ^[]) ..)
  (at level 5, format "^[ A ;  .. ;  B ]").

Fixpoint tapp As Bs :=
  match As with ^[] => Bs | A ^:: As' => A ^:: tapp As' Bs end.
Infix "^++" := tapp (at level 60, right associativity).

Fixpoint tnth B As (i: nat) := match As with
  ^[] => B | A ^:: As' => match i with 0 => A | S j => tnth B As' j end end.

Notation tnthe := (tnth ∅).

Fixpoint trepeat A n : Types := match n with 0 => ^[] | S m => A ^:: trepeat A m end.

(** * Heterogeneous List *)

Inductive hlist (F: Type → Type) : Types → Type :=
| hnil: hlist F ^[]
| hcons {A As} : F A → hlist F As → hlist F (A ^:: As).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Fixpoint happ {F As Bs} (xl: hlist F As) (yl: hlist F Bs)
  : hlist F (As ^++ Bs) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.
Infix "h++" := happ (at level 60, right associativity).

Fixpoint hmap {F G As} (f: ∀A, F A → G A) (xl: hlist F As) : hlist G As :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hmap f xl' end.
Infix "+<$>" := hmap (at level 61, left associativity).

Fixpoint hcmap {F B As} (f: ∀A, F A → B) (xl: hlist F As) : list B :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hcmap f xl' end.
Infix "+c<$>" := hcmap (at level 61, left associativity).

Fixpoint hnth {F B As} (y: F B) (xl: hlist F As) (i: nat) : F (tnth B As i) :=
  match xl with +[] => y | x +:: xl' =>
    match i with 0 => x | S j => hnth y xl' j end end.

Notation hnthe := (hnth ∅).

Fixpoint hrepeat {F A} (x: F A) n : hlist F (trepeat A n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with {F As} (f: ∀A, F A → nat) (xl: hlist F As) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Definition happly {F B As} (fl: hlist (λ A, B → F A) As) (x: B) : hlist F As :=
  (λ _ (f: _ → _), f x) +<$> fl.
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

Lemma hnth_apply {F C B As} (fl: _ As) (y: F B) (x: C) i :
  hnth y (fl +$ x) i = hnth (const y) fl i x.
Proof. move: i. elim fl; [done|]=> > IH [|i]; [done|]. by rewrite /= IH. Qed.

Inductive HForall {F} (Φ: ∀A, F A → Prop) : ∀{As}, hlist F As → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {A As} (x: _ A) (xl: _ As) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Lemma HForall_impl {F As} (Φ Ψ: ∀A, F A → Prop) (xl: _ As) :
  (∀A x, Φ A x → Ψ _ x) → HForall Φ xl → HForall Ψ xl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForall_nth {F B As} (Φ: ∀A, F A → Prop) (y: _ B) (xl: _ As) i :
  Φ _ y → HForall Φ xl → Φ _ (hnth y xl i).
Proof.
  move=> ? All. move: i. elim All=>/= [|> ???]; by [|case].
Qed.

Inductive HForall2 {F G} (Φ: ∀A, F A → G A → Prop)
  : ∀{As}, hlist F As → hlist G As → Prop :=
| HForall2_nil: HForall2 Φ +[] +[]
| HForall2_cons {A As} (x y: _ A) (xl yl: _ As) :
    Φ _ x y → HForall2 Φ xl yl → HForall2 Φ (x +:: xl) (y +:: yl).

Lemma HForall2_impl {F G As} (Φ Ψ: ∀A, F A → G A → Prop) (xl yl: _ As) :
  (∀A x y, Φ A x y → Ψ _ x y) → HForall2 Φ xl yl → HForall2 Ψ xl yl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForall2_forall `{Inhabited B} {F G As}
  (Φ: ∀A, B → F A → G A → Prop) (xl yl: _ As) :
  (∀z, HForall2 (λ A, Φ A z) xl yl) ↔ HForall2 (λ A x y, ∀z, Φ _ z x y) xl yl.
Proof.
  split; [|elim; by constructor]. move=> All. set One := All inhabitant.
  dependent induction One; [by constructor|]. constructor.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  have All': ∀z, HForall2 (λ A, Φ A z) xl yl.
  { move=> z. move/(.$ z) in All. by dependent destruction All. } auto.
Qed.

Lemma HForall2_nth {F G B As} (Φ: ∀A, F A → G A → Prop) (x y: _ B) (xl yl: _ As) i :
  Φ _ x y → HForall2 Φ xl yl → Φ _ (hnth x xl i) (hnth y yl i).
Proof.
  move=> ? All. move: i. elim All=>/= [|> ???]; by [|case].
Qed.

Global Instance HForall2_reflexive {F As} (R: ∀A, F A → F A → Prop) :
  (∀A, Reflexive (R A)) → Reflexive (@HForall2 _ _ R As).
Proof. move=> ?. elim; by constructor. Qed.

Global Instance HForall2_symmetric {F As} (R: ∀A, F A → F A → Prop) :
  (∀A, Symmetric (R A)) → Symmetric (@HForall2 _ _ R As).
Proof. move=> >. elim; by constructor. Qed.

Global Instance HForall2_transitive {F As} (R: ∀A, F A → F A → Prop) :
  (∀A, Transitive (R A)) → Transitive (@HForall2 _ _ R As).
Proof.
  move=> ??? zl All. move: zl. elim: All; [done|]=> > ?? IH ? All.
  dependent destruction All. constructor; by [etrans|apply IH].
Qed.

Global Instance HForall2_equivalence {F As} (R: ∀A, F A → F A → Prop) :
  (∀A, Equivalence (R A)) → Equivalence (@HForall2 _ _ R As).
Proof. split; apply _. Qed.

(** * List-like Product *)

Inductive nil_unit := nil_tt: nil_unit.
Program Global Instance nil_unit_unique: Unique nil_unit := {|unique := nil_tt|}.
Next Obligation. by case. Qed.

Record cons_prod A B := cons_pair { phead: A; ptail: B }.
Arguments cons_pair {_ _} _ _. Arguments phead {_ _} _. Arguments ptail {_ _} _.

Notation ":1" := nil_unit : type_scope.
Infix ":*" := cons_prod (at level 60, right associativity) : type_scope.
Notation "-[ ]" := nil_tt (at level 1, format "-[ ]").
Infix "-::" := cons_pair (at level 60, right associativity).
Notation "(-::)" := cons_pair (only parsing).
Notation "-[ a ; .. ; z ]" := (a -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ a ;  .. ;  z ]").

Definition prod_to_cons_prod {A B} '((x, y)) : _ A B := x -:: y.
Definition cons_prod_to_prod {A B} '(x -:: y) : _ A B := (x, y).
Global Instance prod_cons_prod_iso {A B} : Iso (@prod_to_cons_prod A B) cons_prod_to_prod.
Proof. split; fun_ext; by case. Qed.

Definition cons_prod_map {A B A' B'} (f: A → A') (g: B → B') '(x -:: y) := f x -:: g y.
Lemma cons_prod_map_via_prod_map {A B A' B'} (f: A → A') (g: B → B') :
  cons_prod_map f g = prod_to_cons_prod ∘ prod_map f g ∘ cons_prod_to_prod.
Proof. fun_ext; by case. Qed.

Fixpoint plist (F: Type → Type) As : Type :=
  match As with ^[] => :1 | A ^:: As' => F A :* plist F As' end.

Notation xprod := (plist id).

Fixpoint pmap {F G As} (f: ∀A, F A → G A) : plist F As → plist G As :=
  match As with ^[] => id | _ ^:: _ => λ '(x -:: xl'), f _ x -:: pmap f xl' end.
Infix "-<$>" := pmap (at level 61, left associativity).

Fixpoint papp {F As Bs} (xl: plist F As) (yl: plist F Bs) : plist F (As ^++ Bs) :=
  match As, xl with ^[], -[] => yl | _ ^:: _, x -:: xl' => x -:: papp xl' yl end.
Infix "-++" := papp (at level 60, right associativity).

Fixpoint psep {F As Bs} (xl: plist F (As ^++ Bs)) : plist F As * plist F Bs :=
  match As, xl with ^[], _ => (-[], xl) |
    _ ^:: _, x -:: xl' => let: (yl, zl) := psep xl' in (x -:: yl, zl) end.

Global Instance papp_psep_iso {F As Bs} : Iso (curry (@papp F As Bs)) psep.
Proof.
  elim As=>/= [|?? [Eq Eq']]; split; fun_ext;
  [by case=> [[]?]|done|case=> [[? xl]yl]|case=> [? xl]].
  - move: Eq. by move/equal_f/(.$ (xl, yl))=>/= ->.
  - move: Eq'. move/equal_f/(.$ xl)=>/=. by case (psep xl)=> [??]=>/= ->.
Qed.

Fixpoint prepeat {F A} (x: F A) n : plist F (trepeat A n) :=
  match n with 0 => -[] | S m => x -:: prepeat x m end.

Fixpoint hlist_to_plist {F As} (xl: hlist F As) : plist F As :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.
Fixpoint plist_to_hlist {F As} (xl: plist F As) : hlist F As :=
  match As, xl with ^[], _ => +[] | _ ^:: _, x -:: xl' => x +:: plist_to_hlist xl' end.
Global Instance hlist_plist_iso {F As} : Iso (@hlist_to_plist F As) plist_to_hlist.
Proof. split.
  - fun_ext. by elim; [done|]=>/= > ->.
  - fun_ext. elim As; [by case|]=>/= ?? IH [??] /=. by rewrite IH.
Qed.

Fixpoint plist2 (F: Type → Type → Type) As Bs : Type :=
  match As, Bs with ^[], ^[] => :1 |
    A ^:: As', B ^:: Bs' => F A B :* plist2 F As' Bs' | _, _ => ∅ end.

Fixpoint p2map {F G As Bs} (f: ∀A B, F A B → G A B) : plist2 F As Bs → plist2 G As Bs :=
  match As, Bs with ^[], ^[] => id
  | _ ^:: _, _ ^:: _ => λ '(x -:: xl'), f _ _ x -:: p2map f xl'
  | _, _ => absurd end.
Infix "-2<$>" := p2map (at level 61, left associativity).

Fixpoint p2nth {F As Bs C D} (y: F C D) :
  plist2 F As Bs → ∀i, F (tnth C As i) (tnth D Bs i) :=
  match As, Bs with ^[], ^[] => λ _ _, y
  | _ ^:: _, _ ^:: _ => λ '(x -:: xl') i, match i with 0 => x | S j => p2nth y xl' j end
  | _, _ => absurd end.

Fixpoint p2flip {F As Bs} : plist2 F As Bs → plist2 (flip F) Bs As :=
  match As, Bs with ^[], ^[] => id
  | _ ^:: _, _ ^:: _ => λ '(x -:: xl'), x -:: p2flip xl'
  | _, _ => absurd end.

Lemma p2flip_invol {F As Bs} (zl: _ F As Bs) : p2flip (p2flip zl) = zl.
Proof.
  dependent induction As; dependent induction Bs=>//. case zl=>/= *. by f_equal.
Qed.

Fixpoint p2zip {F G As Bs} :
  plist2 F As Bs → plist2 G As Bs → plist2 (λ A B, F A B * G A B)%type As Bs :=
  match As, Bs with ^[], ^[] => λ _ _, -[]
  | _ ^:: _, _ ^:: _ => λ '(x -:: xl') '(y -:: yl'), (x, y) -:: p2zip xl' yl'
  | _, _ => absurd end.

Lemma p2zip_fst {F G As Bs} (xl: _ F As Bs) (yl: _ G _ _) :
  (λ _ _, fst) -2<$> p2zip xl yl = xl.
Proof.
  dependent induction As; dependent induction Bs; case xl, yl=>//= *. by f_equal.
Qed.
Lemma p2zip_snd {F G As Bs} (xl: _ F As Bs) (yl: _ G _ _) :
  (λ _ _, snd) -2<$> p2zip xl yl = yl.
Proof.
  dependent induction As; dependent induction Bs; case xl, yl=>//= *. by f_equal.
Qed.

Fixpoint p2ids {As} : plist2 (→) As As :=
  match As with ^[] => -[] | _ ^:: _ => id -:: p2ids end.

Lemma p2ids_nth {B As} i : p2nth (@id B) (@p2ids As) i = id.
Proof. move: i. elim As; [done|]=> ???. by case. Qed.

Fixpoint xprod_map {As Bs} : plist2 (→) As Bs → xprod As → xprod Bs :=
  match As, Bs with ^[], ^[] => λ _, id
  | _ ^:: _, _ ^:: _ => λ '(f -:: fl') '(x -:: xl'), f x -:: xprod_map fl' xl'
  | _, _ => absurd end.

Lemma xprod_map_id {As} : xprod_map (@p2ids As) = id.
Proof. elim As; [done|]=>/= ??->. fun_ext. by case. Qed.

Definition pvec A n : Type := xprod (trepeat A n).

Fixpoint pvmap {A B n} (f: A → B) : pvec A n → pvec B n :=
  match n with 0 => id | S _ => λ '(x -:: xl'), f x -:: pvmap f xl' end.
Infix "-v<$>" := pvmap (at level 61, left associativity).
Notation "( f -v<$>.)" := (pvmap f) (only parsing).

Fixpoint pvapp {A m n} (xl: pvec A m) (yl: pvec A n) : pvec A (m + n) :=
  match m, xl with 0, _ => yl | S _, x -:: xl' => x -:: pvapp xl' yl end.
Infix "-v++" := papp (at level 60, right associativity).

Fixpoint pvsep {A m n} (xl: pvec A (m + n)) : pvec A m * pvec A n :=
  match m, xl with 0, _ => (-[], xl) |
    S _, x -:: xl' => let (yl, zl) := pvsep xl' in (x -:: yl, zl) end.

Global Instance pvapp_pvsep_iso {A m n} : Iso (curry (@pvapp A m n)) pvsep.
Proof.
  elim m=>/= [|?[Eq Eq']]; split; fun_ext;
  [by case=> [[]?]|done|case=> [[? xl]yl]|case=> [? xl]].
  - move: Eq. by move/equal_f/(.$ (xl, yl))=>/= ->.
  - move: Eq'. move/equal_f/(.$ xl)=>/=. by case (pvsep xl)=> [??]=>/= ->.
Qed.

Program Global Instance pvec_unique `{Unique A} n
  : Unique (pvec A n) := {| unique := prepeat unique n |}.
Next Obligation.
  move=> ?? n. elim n; [by case|]=> ? IH [x xl]. by rewrite (eq_unique x) (IH xl).
Qed.

Fixpoint vec_to_pvec {A n} (xl: vec A n) : pvec A n :=
  match xl with [#] => -[] | x ::: xl' => x -:: vec_to_pvec xl' end.
Fixpoint pvec_to_vec {A n} (xl: pvec A n) : vec A n :=
  match n, xl with 0, _ => [#] | S _, x -:: xl' => x ::: pvec_to_vec xl' end.
Global Instance vec_pvec_iso {A n} : Iso (@vec_to_pvec A n) pvec_to_vec.
Proof. split.
  - fun_ext. by elim; [done|]=>/= > ->.
  - fun_ext. elim n; [by case|]=>/= > IH [??] /=. by rewrite IH.
Qed.

Inductive HForallZip {F G H} (Φ: ∀A B, F A → G B → H A B → Prop)
  : ∀{As Bs}, hlist F As → hlist G Bs → plist2 H As Bs → Prop :=
| HForallZip_nil: HForallZip Φ +[] +[] -[]
| HForallZip_cons {A B As Bs} (x: _ A) (y: _ B) z (xl: _ As) (yl: _ Bs) zl :
    Φ _ _ x y z → HForallZip Φ xl yl zl →
    HForallZip Φ (x +:: xl) (y +:: yl) (z -:: zl).

Lemma HForallZip_impl {F G H H' As Bs} (Φ Ψ: ∀A B, _ → _ → _ → Prop)
  (f: ∀A B, H A B → H' _ _) (xl: _ F As) (yl: _ G Bs) zl :
  (∀A B x y z, Φ A B x y z → Ψ _ _ x y (f _ _ z)) →
  HForallZip Φ xl yl zl → HForallZip Ψ xl yl (f -2<$> zl).
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForallZip_flip {F G H As Bs}
  (Φ: ∀A B, _ → _ → _ → Prop) (xl: _ F As) (yl: _ G Bs) (zl: _ H _ _) :
  HForallZip Φ xl yl (p2flip zl) → HForallZip (λ _ _, flip (Φ _ _)) yl xl zl.
Proof. rewrite -{2}(p2flip_invol zl). elim=>/= *; by constructor. Qed.

Lemma HForallZip_zip {F G H H' As Bs} (Φ Ψ: ∀A B, _ → _ → _ → Prop)
  (xl: _ F As) (yl: _ G Bs) (zl: _ H _ _) (zl': _ H' _ _) :
  HForallZip (λ _ _ x y '(z, z'), Φ _ _ x y z ∧ Ψ _ _ x y z') xl yl (p2zip zl zl') →
  HForallZip Φ xl yl zl ∧ HForallZip Ψ xl yl zl'.
Proof.
  rewrite -{2}(p2zip_fst zl zl'). rewrite -{3}(p2zip_snd zl zl').
  elim=> [|??????[??] > [??]_[??]]; split; by constructor.
Qed.

Lemma HForallZip_nth {F G H C D As Bs} (Φ: ∀A B, F A → G B → H A B → Prop)
  (x: _ C) (y: _ D) z (xl: _ As) (yl: _ Bs) zl i :
  Φ _ _ x y z → HForallZip Φ xl yl zl → Φ _ _ (hnth x xl i) (hnth y yl i) (p2nth z zl i).
Proof.
  move=> ? All. move: i. elim All=>/= [|> ???]; by [|case].
Qed.

(** * Sum *)

Inductive xsum As : Type := xinj (i: nat) : tnthe As i → xsum As.
Arguments xinj {_} _ _.

Global Instance xinj_inj {As} i : Inj (=) (=) (@xinj As i).
Proof. move=> ?? Eq. by dependent destruction Eq. Qed.

Definition xsum_map {As Bs} (fl: plist2 (→) As Bs) (xl: xsum As) : xsum Bs :=
  let: xinj i x := xl in xinj i (p2nth id fl i x).

Lemma xsum_map_id {As} : xsum_map (@p2ids As) = id.
Proof. fun_ext. case=>/= *. by rewrite p2ids_nth. Qed.

(** * Setoid *)

Global Instance hlist_equiv `{∀A, Equiv (F A)} {As} : Equiv (hlist F As) :=
  HForall2 (λ _, (≡)).

Section lemmas.
Context `{∀A, Equiv (F A)}.

Global Instance hcons_proper {A As} : Proper ((≡) ==> (≡) ==> (≡)) (@hcons F A As).
Proof. by constructor. Qed.

Global Instance hnth_proper {B As} :
  Proper ((≡) ==> (≡) ==> forall_relation (λ _, (≡))) (@hnth F B As).
Proof. move=> ???????. by apply (HForall2_nth _). Qed.

End lemmas.

(** * Ofe *)

Global Instance hlist_dist {F: _ → ofe} {As} : Dist (hlist F As) :=
  λ n, HForall2 (λ _, dist n).

Definition hlist_ofe_mixin {F: _ → ofe} {As} : OfeMixin (hlist F As).
Proof. split=> >.
  - rewrite /equiv /hlist_equiv HForall2_forall.
    split=> H; dependent induction H; constructor; try done; by apply equiv_dist.
  - apply _.
  - rewrite /dist /hlist_dist. apply HForall2_impl=> >. apply dist_S.
Qed.

Canonical Structure hlistO (F: _ → ofe) As := Ofe (hlist F As) hlist_ofe_mixin.

Section lemmas.
Context {F: Type → ofe}.

Global Instance hcons_ne {A As} : NonExpansive2 (@hcons F A As).
Proof. by constructor. Qed.

Global Instance hnth_ne {B As} n :
  Proper (dist n ==> dist n ==> forall_relation (λ _, dist n)) (@hnth F B As).
Proof. move=> ???????. by apply (HForall2_nth (λ A, ofe_dist (F A) n)). Qed.

End lemmas.

(** * Iris *)

Section def.
Context {PROP: bi}.

Fixpoint big_sepHL {F As} (Φ: ∀A, F A → PROP) (xl: hlist F As) : PROP :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end%I.

Fixpoint big_sepHLZip {F G H As Bs} (Φ: ∀A B, F A → G B → H A B → PROP)
  (xl: hlist F As) (yl: hlist G Bs) (zl: plist2 H As Bs) : PROP:=
  match xl, yl, zl with +[], +[], _ => True
  | x +:: xl', y +:: yl', z -:: zl' => Φ _ _ x y z ∗ big_sepHLZip Φ xl' yl' zl'
  | _, _, _ => False end%I.

End def.

Notation "[∗ hlist] x ∈ xl , P" := (big_sepHL (λ _ x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.

Notation "[∗ hlist] x ; y ;- z ∈ xl ; yl ;- zl , P" :=
  (big_sepHLZip (λ _ _ x y z, P%I) xl yl zl)
  (at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,
    format "[∗  hlist]  x ;  y ;-  z  ∈  xl ;  yl ;-  zl ,  P") : bi_scope.

Section lemmas.
Context `{BiAffine PROP}.

Lemma big_sepHL_singleton {F B} (Φ: ∀A, F A → PROP) (y: F B) :
  ([∗ hlist] x ∈ +[y]@{F}, Φ _ x) ⊣⊢ Φ _ y.
Proof. by rewrite /= right_id. Qed.

Lemma big_sepHL_app {F As Bs} (Φ: ∀A, F A → PROP) (l: hlist F As) (l': hlist F Bs) :
  ([∗ hlist] x ∈ l h++ l', Φ _ x) ⊣⊢
  ([∗ hlist] x ∈ l, Φ _ x) ∗ ([∗ hlist] x ∈ l', Φ _ x).
Proof. elim l; [by rewrite left_id|]=>/= > ->. by rewrite assoc. Qed.

End lemmas.
