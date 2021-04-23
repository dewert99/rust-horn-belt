Require Import Equality FunctionalExtensionality.
From stdpp Require Import prelude.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * List for X higher universe *)
(** We use tlist 𝒯 for 𝒯 that contains Type *)

Inductive tlist 𝒯 := tnil: tlist 𝒯 | tcons: 𝒯 → tlist 𝒯 → tlist 𝒯.

Notation "^[ ]" := (tnil _) (at level 5, format "^[ ]").
Infix "^::" := (tcons _) (at level 60, right associativity).
Notation "^[ X ; .. ; Y ]" := (X ^:: .. (Y ^:: ^[]) ..)
  (at level 5, format "^[ X ;  .. ;  Y ]").

Fixpoint tapp {𝒯} (Xl Yl: tlist 𝒯) : tlist 𝒯 :=
  match Xl with ^[] => Yl | X ^:: Xl' => X ^:: tapp Xl' Yl end.
Infix "^++" := tapp (at level 60, right associativity).

Fixpoint tmap {𝒯 Y} (F: 𝒯 → Y) (Xl: tlist 𝒯) : tlist Y :=
  match Xl with ^[] => ^[] | X ^:: Xl' => F X ^:: tmap F Xl' end.
Infix "^<$>" := tmap (at level 61, left associativity).

Fixpoint tnth {𝒯} (Y: 𝒯) (Xl: tlist 𝒯) (i: nat) : 𝒯 := match Xl with
  ^[] => Y | X ^:: Xl' => match i with 0 => X | S j => tnth Y Xl' j end end.
Notation tnthe := (tnth ∅).

Fixpoint trepeat {𝒯} (X: 𝒯) (n: nat) : tlist 𝒯 :=
  match n with 0 => ^[] | S m => X ^:: trepeat X m end.

Inductive elem_of_tlist {𝒯} : ElemOf 𝒯 (tlist 𝒯) :=
| elem_of_tlist_here X Xl : X ∈ X ^:: Xl
| elem_of_tlist_further X Y Xl : X ∈ Xl → X ∈ Y ^:: Xl.
Existing Instance elem_of_tlist.

Lemma elem_of_tnil {𝒯} (X: 𝒯) : X ∈ ^[] ↔ False.
Proof. split; [|done]. move=> H. inversion H. Qed.
Lemma elem_of_tcons {𝒯} (Y: 𝒯) X Xl : Y ∈ X ^:: Xl ↔ Y = X ∨ Y ∈ Xl.
Proof. split=> H.
  - inversion H; by [left|right].
  - case H; [move=> ->|]; by constructor.
Qed.
Lemma not_elem_of_tcons {𝒯} (Y: 𝒯) X Xl : Y ∉ X ^:: Xl ↔ Y ≠ X ∧ Y ∉ Xl.
Proof. rewrite elem_of_tcons. tauto. Qed.

Lemma elem_of_tapp {𝒯} (X: 𝒯) Xl Xl' : X ∈ Xl ^++ Xl' ↔ X ∈ Xl ∨ X ∈ Xl'.
Proof.
  elim Xl; [rewrite elem_of_tnil; tauto|]=>/= ?? IH. rewrite !elem_of_tcons IH. tauto.
Qed.

Lemma elem_of_tmap {𝒯} (F: 𝒯 → 𝒯) Y Xl :
  Y ∈ F ^<$> Xl ↔ ∃ X, Y = F X ∧ X ∈ Xl.
Proof. elim Xl=> /=[|X ? IH].
  - setoid_rewrite elem_of_tnil. split; [done|]. move=> [?[?[]]].
  - rewrite elem_of_tcons IH. split.
    + move=> [->|[X'[->?]]]; [exists X|exists X']; split; by constructor.
    + move=> [X'[? /elem_of_tcons[<-|?]]]; [by left|]. right. by exists X'.
Qed.
Lemma elem_of_tmap_1 {𝒯} (F: 𝒯 → 𝒯) X Xl : X ∈ Xl → F X ∈ F ^<$> Xl.
Proof. move=> ?. apply elem_of_tmap. by exists X. Qed.

Definition tlist_elem_equiv {𝒯} (Xl Xl': tlist 𝒯) := ∀X, X ∈ Xl ↔ X ∈ Xl'.
Infix "≡ₜₑ" := tlist_elem_equiv (at level 70, no associativity).
Notation "(≡ₜₑ)" := tlist_elem_equiv (only parsing).

Notation Types := (tlist Type).

(** * Heterogeneous List *)

Inductive hlist {𝒯} (F: 𝒯 → Type) : tlist 𝒯 → Type :=
| hnil: hlist F ^[]
| hcons {X Xs} : F X → hlist F Xs → hlist F (X ^:: Xs).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Fixpoint happ `{F: 𝒯 → _} {Xl Yl} (xl: hlist F Xl) (yl: hlist F Yl)
  : hlist F (Xl ^++ Yl) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.
Infix "h++" := happ (at level 60, right associativity).

Fixpoint hmap `{F: 𝒯 → _} {G Xl} (f: ∀X, F X → G X) (xl: hlist F Xl) : hlist G Xl :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hmap f xl' end.
Infix "+<$>" := hmap (at level 61, left associativity).

Fixpoint hcmap `{F: 𝒯 → _} {Y Xl} (f: ∀X, F X → Y) (xl: hlist F Xl) : list Y :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hcmap f xl' end.
Infix "+c<$>" := hcmap (at level 61, left associativity).

Fixpoint hnth `{F: 𝒯 → _} {Y Xl} (y: F Y) (xl: hlist F Xl) (i: nat)
  : F (tnth Y Xl i) := match xl with +[] => y | x +:: xl' =>
    match i with 0 => x | S j => hnth y xl' j end end.
Notation hnthe := (hnth ∅).

Fixpoint hrepeat `{F: 𝒯 → _} {X} (x: F X) n : hlist F (trepeat X n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with `{F: 𝒯 → _} {Xl} (f: ∀X, F X → nat) (xl: hlist F Xl) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Fixpoint happly `{F: 𝒯 → _} {Y Xl} (fl: hlist (λ X, Y → F X) Xl) (x: Y)
  : hlist F Xl :=
  match fl with +[] => +[] | f +:: fl' => f x +:: happly fl' x end.
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

Lemma hnth_apply `{F: 𝒯 → _} {Z Y Xl} (fl: _ Xl) (y: F Y) (x: Z) i :
  hnth y (fl +$ x) i = hnth (const y) fl i x.
Proof. move: i. elim fl; [done|]=> > IH [|i]; [done|]. by rewrite /= IH. Qed.

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
Notation "-[ X ; .. ; z ]" := (X -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ X ;  .. ;  z ]").

Definition prod_to_cons_prod {A B} '((x, y)) : _ A B := x -:: y.
Definition cons_prod_to_prod {A B} '(x -:: y) : _ A B := (x, y).
Global Instance prod_cons_prod_iso {A B} :
  Iso (@prod_to_cons_prod A B) cons_prod_to_prod.
Proof. split; fun_ext; by case. Qed.

Definition cons_prod_map {A B A' B'} (f: A → A') (g: B → B') '(x -:: y)
  := f x -:: g y.

Fixpoint plist {𝒯} (F: 𝒯 → Type) Xl : Type :=
  match Xl with ^[] => :1 | X ^:: Xl' => F X :* plist F Xl' end.

Notation xprod := (plist id).
Notation "Π!" := xprod : type_scope.

Fixpoint papp `{F: 𝒯 → _} {Xl Yl} (xl: plist F Xl) (yl: plist F Yl) :
  plist F (Xl ^++ Yl) :=
  match Xl, xl with ^[], _ => yl | _ ^:: _, x -:: xl' => x -:: papp xl' yl end.
Infix "-++" := papp (at level 60, right associativity).

Fixpoint psepl `{F: 𝒯 → _} {Xl Yl} (xl: plist F (Xl ^++ Yl)) : plist F Xl :=
  match Xl, xl with ^[], _ => -[] | _ ^:: _, x -:: xl' => x -:: psepl xl' end.
Fixpoint psepr `{F: 𝒯 → _} {Xl Yl} (xl: plist F (Xl ^++ Yl)) : plist F Yl :=
  match Xl, xl with ^[], _ => xl | _ ^:: _, _ -:: xl' => psepr xl' end.
Notation psep := (λ xl, (psepl xl, psepr xl)).

Lemma papp_sepl `{F: 𝒯 → _} {Xl Yl} (xl: _ F Xl) (yl: _ Yl) : psepl (xl -++ yl) = xl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.
Lemma papp_sepr `{F: 𝒯 → _} {Xl Yl} (xl: _ F Xl) (yl: _ Yl) : psepr (xl -++ yl) = yl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.

Lemma psep_app `{F: 𝒯 → _} {Xl Yl} (xl: _ F (Xl ^++ Yl)) : psepl xl -++ psepr xl = xl.
Proof. move: xl. elim Xl; [done|]=>/= > IH [??]. by rewrite IH. Qed.
Lemma papp_ex `{F: 𝒯 → _} {Xl Yl} (xl: _ F _) : ∃(yl: _ Xl) (zl: _ Yl), xl = yl -++ zl.
Proof. exists (psepl xl), (psepr xl). by rewrite psep_app. Qed.

Global Instance papp_psep_iso `{F: 𝒯 → _} {Xl Yl} : Iso (curry (@papp _ F Xl Yl)) psep.
Proof. split; fun_ext.
  - case=>/= [??]. by rewrite papp_sepl papp_sepr.
  - move=>/= ?. by rewrite psep_app.
Qed.

Fixpoint pmap `{F: 𝒯 → _} {G Xl} (f: ∀X, F X → G X) : plist F Xl → plist G Xl :=
  match Xl with ^[] => id | _ ^:: _ => λ '(x -:: xl'), f _ x -:: pmap f xl' end.
Infix "-<$>" := pmap (at level 61, left associativity).

Lemma pmap_app `{F: 𝒯 → _} {G Xl Yl} (f: ∀X, F X → G X) (xl: _ F Xl) (yl: _ Yl) :
  f -<$> (xl -++ yl) = (f -<$> xl) -++ (f -<$> yl).
Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint prepeat `{F: 𝒯 → _} {X} (x: F X) n : plist F (trepeat X n) :=
  match n with 0 => -[] | S m => x -:: prepeat x m end.

Fixpoint hlist_to_plist `{F: 𝒯 → _} {Xl} (xl: hlist F Xl) : plist F Xl :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.
Fixpoint plist_to_hlist `{F: 𝒯 → _} {Xl} (xl: plist F Xl) : hlist F Xl :=
  match Xl, xl with ^[], _ => +[] | _ ^:: _, x -:: xl' => x +:: plist_to_hlist xl' end.
Global Instance hlist_plist_iso `{F: 𝒯 → _} {Xl} :
  Iso (@hlist_to_plist _ F Xl) plist_to_hlist.
Proof. split.
  - fun_ext. by elim; [done|]=>/= > ->.
  - fun_ext. elim Xl; [by case|]=>/= ?? IH [??] /=. by rewrite IH.
Qed.

Fixpoint plist2 {𝒯} (F: 𝒯 → 𝒯 → Type) Xl Yl : Type :=
  match Xl, Yl with ^[], ^[] => :1 |
    X ^:: Xl', Y ^:: Yl' => F X Y :* plist2 F Xl' Yl' | _, _ => ∅ end.

Fixpoint p2map `{F: 𝒯 → _} {G Xl Yl} (f: ∀X Y, F X Y → G X Y)
  : plist2 F Xl Yl → plist2 G Xl Yl := match Xl, Yl with ^[], ^[] => id |
    _ ^:: _, _ ^:: _ => λ '(x -:: xl'), f _ _ x -:: p2map f xl' | _, _ => absurd end.
Infix "-2<$>" := p2map (at level 61, left associativity).

Fixpoint p2nth `{F: 𝒯 → _} {Xl Yl Z W} (y: F Z W) :
  plist2 F Xl Yl → ∀i, F (tnth Z Xl i) (tnth W Yl i) :=
  match Xl, Yl with ^[], ^[] => λ _ _, y
  | _ ^:: _, _ ^:: _ => λ '(x -:: xl') i, match i with 0 => x | S j => p2nth y xl' j end
  | _, _ => absurd end.

Fixpoint p2ids {Xl} : plist2 (→) Xl Xl :=
  match Xl with ^[] => -[] | _ ^:: _ => id -:: p2ids end.

Lemma p2ids_nth {Y Xl} i : p2nth (@id Y) (@p2ids Xl) i = id.
Proof. move: i. elim Xl; [done|]=> ???. by case. Qed.

Notation plist_fun Y F := (plist (λ X, Y → F X)).

Fixpoint papply `{F: 𝒯 → _} {Y Xl} (fl: plist_fun Y F Xl) (x: Y) : plist F Xl :=
  match Xl, fl with ^[], _ => -[] | _ ^:: _, f -:: fl' => f x -:: papply fl' x end.
Infix "-$" := papply (at level 61, left associativity).
Notation "( fl -$.)" := (papply fl) (only parsing).

Lemma papply_app `{F: 𝒯 → _} {Z Xl Yl} (fl: plist_fun Z F Xl) (gl: _ Yl) (x: Z) :
  (fl -++ gl) -$ x = (fl -$ x) -++ (gl -$ x).
Proof. move: fl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint xprod_map {Al Bl} : plist2 (→) Al Bl → Π! Al → Π! Bl :=
  match Al, Bl with ^[], ^[] => λ _, id
  | _ ^:: _, _ ^:: _ => λ '(f -:: fl') '(x -:: xl'), f x -:: xprod_map fl' xl'
  | _, _ => absurd end.

Lemma xprod_map_id {Al} : xprod_map (@p2ids Al) = id.
Proof. elim Al; [done|]=>/= ??->. fun_ext. by case. Qed.

Definition pvec A n : Type := Π! (trepeat A n).

Fixpoint pvmap {A B n} (f: A → B) : pvec A n → pvec B n :=
  match n with 0 => id | S _ => λ '(x -:: xl'), f x -:: pvmap f xl' end.
Infix "-v<$>" := pvmap (at level 61, left associativity).
Notation "( f -v<$>.)" := (pvmap f) (only parsing).

Fixpoint pvapp {A m n} (xl: pvec A m) (yl: pvec A n) : pvec A (m + n) :=
  match m, xl with 0, _ => yl | S _, x -:: xl' => x -:: pvapp xl' yl end.
Infix "-v++" := pvapp (at level 60, right associativity).

Fixpoint pvsepl {A m n} (xl: pvec A (m + n)) : pvec A m :=
  match m, xl with 0, _ => -[] | S _, x -:: xl' => x -:: pvsepl xl' end.
Fixpoint pvsepr {A m n} (xl: pvec A (m + n)) : pvec A n :=
  match m, xl with 0, _ => xl | S _, x -:: xl' => pvsepr xl' end.
Notation pvsep := (λ xl, (pvsepl xl, pvsepr xl)).

Lemma pvapp_sepl {A m n} (xl: _ A m) (yl: _ n) : pvsepl (xl -v++ yl) = xl.
Proof. move: xl yl. elim m; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.
Lemma pvapp_sepr {A m n} (xl: _ A m) (yl: _ n) : pvsepr (xl -v++ yl) = yl.
Proof. move: xl yl. elim m; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.

Lemma pvsep_app {A m n} (xl: _ A (m + n)) : pvsepl xl -v++ pvsepr xl = xl.
Proof. move: xl. elim m; [done|]=>/= > IH [??]. by rewrite IH. Qed.
Lemma pvapp_ex {A m n} (xl: _ A _) : ∃(yl: _ m) (zl: _ n), xl = yl -v++ zl.
Proof. exists (pvsepl xl), (pvsepr xl). by rewrite pvsep_app. Qed.

Global Instance pvapp_pvsep_iso {A m n} : Iso (curry (@pvapp A m n)) pvsep.
Proof. split; fun_ext.
  - case=>/= [??]. by rewrite pvapp_sepl pvapp_sepr.
  - move=>/= ?. by rewrite pvsep_app.
Qed.

Program Global Instance pvec_unique `{!Unique A} n
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

(** * Sum *)

Inductive xsum Al : Type := xinj (i: nat) : tnthe Al i → xsum Al.
Arguments xinj {_} _ _.
Notation "Σ!" := xsum : type_scope.

Global Instance xinj_inj {Al} i : Inj (=) (=) (@xinj Al i).
Proof. move=> ?? Eq. by dependent destruction Eq. Qed.

Definition xsum_map {Al Bl} (fl: plist2 (→) Al Bl) (xl: Σ! Al) : Σ! Bl :=
  let: xinj i x := xl in xinj i (p2nth id fl i x).

Lemma xsum_map_id {Al} : xsum_map (@p2ids Al) = id.
Proof. fun_ext. case=>/= *. by rewrite p2ids_nth. Qed.

Global Instance xsum_nil_void : Void (Σ! ^[]). Proof. move=> ?. by case. Qed.

Definition sum_to_xsum {A B} (s: A + B) : Σ! ^[A; B] := match s with
  inl x => @xinj ^[A; B] 0 x | inr y => @xinj ^[A; B] 1 y end.
Definition xsum_to_sum {A B} (s: Σ! ^[A; B]) : A + B := match s with
  xinj 0 x => inl x | xinj 1 y => inr y | xinj (S (S _)) z => absurd z end.
Global Instance sum_xsum_iso {A B} : Iso (@sum_to_xsum A B) xsum_to_sum.
Proof. split; fun_ext; case; by [| |case=> [|[|]]]. Qed.

(** * Forall *)

Inductive HForall `{F: 𝒯 → _} (Φ: ∀X, F X → Prop) : ∀{Xl}, hlist F Xl → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {X Xl} (x: _ X) (xl: _ Xl) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Inductive HForall2_1 `{F: 𝒯 → _} {G H} (Φ: ∀X Y, F X → G Y → H X Y → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → Prop :=
| HForall2_1_nil: HForall2_1 Φ +[] +[] -[]
| HForall2_1_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z (xl: _ Xl) (yl: _ Yl) zl :
    Φ _ _ x y z → HForall2_1 Φ xl yl zl → HForall2_1 Φ (x +:: xl) (y +:: yl) (z -:: zl).

Inductive HForall2_2flip `{F: 𝒯 → _} {G H K} (Φ: ∀X Y, F X → G Y → H X Y → K Y X → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → plist2 K Yl Xl → Prop :=
| HForall2_2flip_nil: HForall2_2flip Φ +[] +[] -[] -[]
| HForall2_2flip_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z w (xl: _ Xl) (yl: _ Yl) zl wl :
    Φ _ _ x y z w → HForall2_2flip Φ xl yl zl wl →
    HForall2_2flip Φ (x +:: xl) (y +:: yl) (z -:: zl) (w -:: wl).

Inductive HForallTwo `{F: 𝒯 → _} {G} (Φ: ∀X, F X → G X → Prop)
  : ∀{Xl}, hlist F Xl → hlist G Xl → Prop :=
| HForallTwo_nil: HForallTwo Φ +[] +[]
| HForallTwo_cons {X Xl} (x y: _ X) (xl yl: _ Xl) :
    Φ _ x y → HForallTwo Φ xl yl → HForallTwo Φ (x +:: xl) (y +:: yl).

Lemma HForall_impl `{F: 𝒯 → _} {Xl} (Φ Ψ: ∀X, F X → Prop) (xl: _ Xl) :
(∀X x, Φ X x → Ψ _ x) → HForall Φ xl → HForall Ψ xl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForallTwo_impl `{F: 𝒯 → _} {G Xl} (Φ Ψ: ∀X, F X → G X → Prop) (xl yl: _ Xl) :
  (∀X x y, Φ X x y → Ψ _ x y) → HForallTwo Φ xl yl → HForallTwo Ψ xl yl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForall_nth `{F: 𝒯 → _} {Y Xl} (Φ: ∀X, F X → Prop) (y: _ Y) (xl: _ Xl) i :
Φ _ y → HForall Φ xl → Φ _ (hnth y xl i).
Proof.
move=> ? All. move: i. elim All=>/= [|> ???]; by [|case].
Qed.

Lemma HForallTwo_nth `{F: 𝒯 → _} {G Y Xl} (Φ: ∀X, F X → G X → Prop)
  (x y: _ Y) (xl yl: _ Xl) i :
  Φ _ x y → HForallTwo Φ xl yl → Φ _ (hnth x xl i) (hnth y yl i).
Proof.
move=> ? All. move: i. elim All=>/= [|> ???]; by [|case].
Qed.

Lemma HForallTwo_forall `{!Inhabited Y} `{F: 𝒯 → _} {G Xl}
  (Φ: ∀X, Y → F X → G X → Prop) (xl yl: _ Xl) :
  (∀z, HForallTwo (λ X, Φ X z) xl yl) ↔ HForallTwo (λ X x y, ∀z, Φ _ z x y) xl yl.
Proof.
  split; [|elim; by constructor]. move=> All. set One := All inhabitant.
  dependent induction One; [by constructor|]. constructor.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  have All': ∀z, HForallTwo (λ X, Φ X z) xl yl.
  { move=> z. move/(.$ z) in All. by dependent destruction All. } auto.
Qed.

Global Instance HForallTwo_reflexive `{F: 𝒯 → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Reflexive (R X)) → Reflexive (HForallTwo R (Xl:=Xl)).
Proof. move=> ?. elim; by constructor. Qed.
Global Instance HForallTwo_symmetric `{F: 𝒯 → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Symmetric (R X)) → Symmetric (HForallTwo R (Xl:=Xl)).
Proof. move=> >. elim; by constructor. Qed.
Global Instance HForallTwo_transitive `{F: 𝒯 → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Transitive (R X)) → Transitive (HForallTwo R (Xl:=Xl)).
Proof.
  move=> ??? zl All. move: zl. elim: All; [done|]=> > ?? IH ? All.
  dependent destruction All. constructor; by [etrans|apply IH].
Qed.
Global Instance HForallTwo_equivalence `{F: 𝒯 → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Equivalence (R X)) → Equivalence (HForallTwo R (Xl:=Xl)).
Proof. split; apply _. Qed.

(** * Setoid *)

Global Instance hlist_equiv `{F: 𝒯 → _, ∀X, Equiv (F X)} {Xl}
  : Equiv (hlist F Xl) := HForallTwo (λ _, (≡)).

Section lemmas.
Context `{F: 𝒯 → _, ∀X, Equiv (F X)}.

Global Instance hcons_proper {X Xl} : Proper ((≡@{_ X}) ==> (≡@{_ Xl}) ==> (≡)) (hcons F).
Proof. by constructor. Qed.

Global Instance hnth_proper {Y Xl} :
  Proper ((≡@{_ Y}) ==> (≡@{_ Xl}) ==> forall_relation (λ _, (≡))) hnth.
Proof. move=> ???????. by apply (HForallTwo_nth _). Qed.

End lemmas.

(** * Ofe *)

Global Instance hlist_dist `{F: 𝒯 → ofe} {Xl} : Dist (hlist F Xl) :=
  λ n, HForallTwo (λ _, (≡{n}≡)).

Definition hlist_ofe_mixin `{F: 𝒯 → ofe} {Xl} : OfeMixin (hlist F Xl).
Proof. split=> >.
  - rewrite /equiv /hlist_equiv HForallTwo_forall.
    split=> H; induction H; constructor=>//; by apply equiv_dist.
  - apply _.
  - rewrite /dist /hlist_dist. apply HForallTwo_impl=> >. apply dist_S.
Qed.

Canonical Structure hlistO {𝒯} (F: 𝒯 → ofe) Xl := Ofe (hlist F Xl) hlist_ofe_mixin.

Section lemmas.
Context `{F: 𝒯 → ofe}.

Global Instance hcons_ne {X Xl} : NonExpansive2 (@hcons _ F X Xl).
Proof. by constructor. Qed.

Global Instance hnth_ne {Y Xl} n :
  Proper ((≡{n}≡) ==> (≡{n}≡) ==> forall_relation (λ _, (≡{n}≡))) (@hnth _ F Y Xl).
Proof. move=> ???????. by apply (HForallTwo_nth (λ X, ofe_dist (F X) n)). Qed.

End lemmas.

(** * big_sep *)

Section def.
Context {PROP: bi}.

Fixpoint big_sepTL {X} (Φ: X → PROP) (xl: tlist X) : PROP :=
  match xl with ^[] => True | x ^:: xl' => Φ x ∗ big_sepTL Φ xl' end%I.

Fixpoint big_sepHL `{F: 𝒯 → _} {Xl} (Φ: ∀X, F X → PROP) (xl: hlist F Xl) : PROP :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end%I.

Fixpoint big_sepHL_1 `{F: 𝒯 → _} {G Xl} (Φ: ∀X, F X → G X → PROP)
  (xl: hlist F Xl) (yl: plist G Xl) : PROP := match xl, yl with +[], _ => True |
    x +:: xl', y -:: yl' => Φ _ x y ∗ big_sepHL_1 Φ xl' yl' end%I.

Fixpoint big_sepHL2_1 `{F: 𝒯 → _} {G H Xl Yl} (Φ: ∀X Y, F X → G Y → H X Y → PROP)
  (xl: hlist F Xl) (yl: hlist G Yl) (zl: plist2 H Xl Yl) : PROP :=
  match xl, yl, zl with +[], +[], _ => True
  | x +:: xl', y +:: yl', z -:: zl' => Φ _ _ x y z ∗ big_sepHL2_1 Φ xl' yl' zl'
  | _, _, _ => False end%I.

End def.

Notation "[∗ tlist] x ∈ xl , P" := (big_sepTL (λ x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  tlist]  x  ∈  xl ,  P") : bi_scope.

Notation "[∗ hlist] x ∈ xl , P" := (big_sepHL (λ _ x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.

Notation "[∗ hlist] x ;- y ∈ xl ;- yl , P" := (big_sepHL_1 (λ _ x y, P%I) xl yl)
  (at level 200, xl, yl at level 10, x, y at level 1, right associativity,
    format "[∗  hlist]  x ;-  y  ∈  xl ;-  yl ,  P") : bi_scope.

Notation "[∗ hlist] x ; y ;- z ∈ xl ; yl ;- zl , P" :=
  (big_sepHL2_1 (λ _ _ x y z, P%I) xl yl zl)
  (at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,
    format "[∗  hlist]  x ;  y ;-  z  ∈  xl ;  yl ;-  zl ,  P") : bi_scope.

Section lemmas.
Context `{!BiAffine PROP}.

Global Instance big_sepTL_persistent {X} (Φ: X → PROP) xl :
  (∀x, Persistent (Φ x)) → Persistent (big_sepTL Φ xl).
Proof. move=> ?. elim xl; apply _. Qed.

Lemma big_sepTL_app {X} xl xl' (Φ: X → PROP) :
  big_sepTL Φ (xl ^++ xl') ⊣⊢ big_sepTL Φ xl ∗ big_sepTL Φ xl'.
Proof. elim xl; [by rewrite left_id|]=>/= > ->. by rewrite assoc. Qed.

Lemma big_sepHL_app `{F: 𝒯 → _} {Xl Yl} (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  big_sepHL Φ (xl h++ xl') ⊣⊢ big_sepHL Φ xl ∗ big_sepHL Φ xl'.
Proof. elim xl; [by rewrite left_id|]=>/= > ->. by rewrite assoc. Qed.

Lemma big_sepHL_1_app `{F: 𝒯 → _} {G Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  big_sepHL_1 Φ (xl h++ xl') (yl -++ yl') ⊣⊢ big_sepHL_1 Φ xl yl ∗ big_sepHL_1 Φ xl' yl'.
Proof.
  dependent induction xl; case yl=>/= >; by [rewrite left_id|rewrite IHxl assoc].
Qed.

Global Instance into_from_sep_big_sepTL_app {X} xl xl' (Φ: X → PROP) :
  IntoFromSep (big_sepTL Φ (xl ^++ xl')) (big_sepTL Φ xl) (big_sepTL Φ xl').
Proof. by apply get_into_from_sep, big_sepTL_app. Qed.

Global Instance into_from_sep_big_sepHL_app `{F: 𝒯 → _} {Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  IntoFromSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL Φ xl').
Proof. by apply get_into_from_sep, big_sepHL_app. Qed.

Global Instance into_from_sep_big_sepHL_1_app `{F: 𝒯 → _} {G Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  IntoFromSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 Φ xl' yl').
Proof. by apply get_into_from_sep, big_sepHL_1_app. Qed.

Lemma big_sepTL_elem_of {X} x xl (Φ: X → PROP) :
  x ∈ xl → big_sepTL Φ xl ⊢ Φ x.
Proof.
  elim xl; [by rewrite elem_of_tnil|]=>/= ?? IH. rewrite elem_of_tcons.
  case=> [->|?]; iIntros "[??]"; [iFrame|by iApply IH].
Qed.

Lemma big_sepTL_forall {X} xl (Φ: X → PROP) :
  (∀ x, Persistent (Φ x)) → big_sepTL Φ xl ⊣⊢ ∀x, ⌜x ∈ xl⌝ → Φ x.
Proof.
  move=> ?. elim xl=>/= [|??->].
  - iSplit; [|by iIntros]. setoid_rewrite elem_of_tnil. by iIntros.
  - setoid_rewrite elem_of_tcons. iSplit.
    + iIntros "[? To]" (?[->|?]); [done|]. by iApply "To".
    + iIntros "To". iSplit; [|iIntros (??)]; iApply "To"; by [iLeft|iRight].
Qed.

End lemmas.
