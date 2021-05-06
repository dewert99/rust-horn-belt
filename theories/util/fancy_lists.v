From stdpp Require Import prelude.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Heterogeneous List *)

Inductive hlist {A} (F: A → Type) : list A → Type :=
| hnil: hlist F []
| hcons {X Xl} : F X → hlist F Xl → hlist F (X :: Xl).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Fixpoint happ `{F: A → _} {Xl Yl} (xl: hlist F Xl) (yl: hlist F Yl)
  : hlist F (Xl ++ Yl) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.
Infix "h++" := happ (at level 60, right associativity).

Fixpoint hmap `{F: A → _} {G Xl} (f: ∀X, F X → G X) (xl: hlist F Xl) : hlist G Xl :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hmap f xl' end.
Infix "+<$>" := hmap (at level 61, left associativity).

Fixpoint hcmap `{F: A → _} {Y Xl} (f: ∀X, F X → Y) (xl: hlist F Xl) : list Y :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hcmap f xl' end.
Infix "+c<$>" := hcmap (at level 61, left associativity).

Fixpoint hnth `{F: A → _} {Xl D} (d: F D) (xl: hlist F Xl)
  : ∀i, F (lnth D Xl i) :=
  match xl with +[] => λ _, d | x +:: xl' =>
    λ i, match i with 0 => x | S j => hnth d xl' j end end.
Notation hnthe := (hnth ∅).

Fixpoint hrepeat `{F: A → _} {X} (x: F X) n : hlist F (repeat X n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with `{F: A → _} {Xl} (f: ∀X, F X → nat) (xl: hlist F Xl) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Fixpoint happly `{F: A → _} {Y Xl} (fl: hlist (λ X, Y → F X) Xl) (x: Y)
  : hlist F Xl :=
  match fl with +[] => +[] | f +:: fl' => f x +:: happly fl' x end.
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

Lemma hnth_apply `{F: A → _} {Xl Y D} (g: Y → F D)
  (fl: _ (λ X, Y → F X) Xl) (x: Y) i :
  hnth (g x) (fl +$ x) i = hnth g fl i x.
Proof. move: i. elim fl; [done|]=> > ?. by case. Qed.

(** * Passive Heterogeneous List *)

Inductive nil_unit: Set := nil_tt: nil_unit.
Program Global Instance nil_unit_unique: Unique nil_unit := {|unique := nil_tt|}.
Next Obligation. by case. Qed.

Record cons_prod (A B: Type) : Type := cons_pair { phd: A; ptl: B }.
Arguments cons_pair {_ _} _ _. Arguments phd {_ _} _. Arguments ptl {_ _} _.

Notation ":1" := nil_unit : type_scope.
Infix ":*" := cons_prod (at level 60, right associativity) : type_scope.
Notation "-[ ]" := nil_tt (at level 1, format "-[ ]").
Infix "-::" := cons_pair (at level 60, right associativity).
Notation "(-::)" := cons_pair (only parsing).
Notation "-[ X ; .. ; z ]" := (X -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ X ;  .. ;  z ]").

Definition to_cons_prod {A B} : A * B → A :* B := λ '(a, al), a -:: al.
Definition of_cons_prod {A B} : A :* B → A * B := λ '(a -:: al), (a, al).
Global Instance cons_prod_iso {A B} : Iso (@to_cons_prod A B) of_cons_prod.
Proof. split; fun_ext; by case. Qed.

Notation plist_raw F := (fix plist_raw Xl : Type :=
  match Xl with [] => :1 | X :: Xl' => F X :* plist_raw Xl' end).

Definition plist {A} (F: A → Type) Xl : Type := plist_raw F Xl.

Fixpoint papp `{F: A → _} {Xl Yl} (xl: plist F Xl) (yl: plist F Yl) :
  plist F (Xl ++ Yl) :=
  match Xl, xl with [], _ => yl | _ :: _, x -:: xl' => x -:: papp xl' yl end.
Infix "-++" := papp (at level 60, right associativity).

Fixpoint psepl `{F: A → _} {Xl Yl} (xl: plist F (Xl ++ Yl)) : plist F Xl :=
  match Xl, xl with [], _ => -[] | _ :: _, x -:: xl' => x -:: psepl xl' end.
Fixpoint psepr `{F: A → _} {Xl Yl} (xl: plist F (Xl ++ Yl)) : plist F Yl :=
  match Xl, xl with [], _ => xl | _ :: _, _ -:: xl' => psepr xl' end.
Notation psep := (λ xl, (psepl xl, psepr xl)).

Lemma papp_sepl `{F: A → _} {Xl Yl} (xl: _ F Xl) (yl: _ Yl) : psepl (xl -++ yl) = xl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.
Lemma papp_sepr `{F: A → _} {Xl Yl} (xl: _ F Xl) (yl: _ Yl) : psepr (xl -++ yl) = yl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.

Lemma psep_app `{F: A → _} {Xl Yl} (xl: _ F (Xl ++ Yl)) : psepl xl -++ psepr xl = xl.
Proof. move: xl. elim Xl; [done|]=>/= > IH [??]. by rewrite IH. Qed.
Lemma papp_ex `{F: A → _} {Xl Yl} (xl: _ F _) : ∃(yl: _ Xl) (zl: _ Yl), xl = yl -++ zl.
Proof. exists (psepl xl), (psepr xl). by rewrite psep_app. Qed.

Global Instance papp_psep_iso `{F: A → _} {Xl Yl} : Iso (curry (@papp _ F Xl Yl)) psep.
Proof. split; fun_ext.
  - case=>/= [??]. by rewrite papp_sepl papp_sepr.
  - move=>/= ?. by rewrite psep_app.
Qed.

Fixpoint pmap `{F: A → _} {G Xl} (f: ∀X, F X → G X) : plist F Xl → plist G Xl :=
  match Xl with [] => id | _ :: _ => λ '(x -:: xl'), f _ x -:: pmap f xl' end.
Infix "-<$>" := pmap (at level 61, left associativity).

Lemma pmap_app `{F: A → _} {G Xl Yl} (f: ∀X, F X → G X) (xl: _ F Xl) (yl: _ Yl) :
  f -<$> (xl -++ yl) = (f -<$> xl) -++ (f -<$> yl).
Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint hlist_to_plist `{F: A → _} {Xl} (xl: hlist F Xl) : plist F Xl :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.
Fixpoint plist_to_hlist `{F: A → _} {Xl} (xl: plist F Xl) : hlist F Xl :=
  match Xl, xl with [], _ => +[] | _ :: _, x -:: xl' => x +:: plist_to_hlist xl' end.
Global Instance hlist_plist_iso `{F: A → _} {Xl} :
  Iso (@hlist_to_plist _ F Xl) plist_to_hlist.
Proof. split.
  - fun_ext. by elim; [done|]=>/= > ->.
  - fun_ext. elim Xl; [by case|]=>/= ?? IH [??] /=. by rewrite IH.
Qed.

Fixpoint plist2 {A} (F: A → A → Type) Xl Yl : Type :=
  match Xl, Yl with [], [] => :1 |
    X :: Xl', Y :: Yl' => F X Y :* plist2 F Xl' Yl' | _, _ => ∅ end.

Fixpoint p2map `{F: A → _} {G Xl Yl} (f: ∀X Y, F X Y → G X Y)
  : plist2 F Xl Yl → plist2 G Xl Yl := match Xl, Yl with [], [] => id |
    _ :: _, _ :: _ => λ '(x -:: xl'), f _ _ x -:: p2map f xl' | _, _ => absurd end.
Infix "-2<$>" := p2map (at level 61, left associativity).

Fixpoint p2nth `{F: A → _} {Xl Yl D D'} (d: F D D')
  : plist2 F Xl Yl → ∀i, F (lnth D Xl i) (lnth D' Yl i) :=
  match Xl, Yl with [], [] => λ _ _, d
  | _ :: _, _ :: _ =>
      λ '(x -:: xl') i, match i with 0 => x | S j => p2nth d xl' j end
  | _, _ => absurd end.

Fixpoint papply `{F: A → _} {B Xl} (fl: plist (λ X, B → F X) Xl) (x: B)
  : plist F Xl := match Xl, fl with
    [], _ => -[] | _ :: _, f -:: fl' => f x -:: papply fl' x end.
Infix "-$" := papply (at level 61, left associativity).
Notation "( fl -$.)" := (papply fl) (only parsing).

Lemma papply_app `{F: A → _} {B Xl Yl}
  (fl: plist (λ X, B → F X) Xl) (gl: _ Yl) (x: B) :
  (fl -++ gl) -$ x = (fl -$ x) -++ (gl -$ x).
Proof. move: fl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint plist_map `{F: A → _} {Xl Yl} :
  plist2 (λ X Y, F X → F Y) Xl Yl → plist F Xl → plist F Yl :=
  match Xl, Yl with [], [] => λ _, id
  | _ :: _, _ :: _ => λ '(f -:: fl') '(x -:: xl'), f x -:: plist_map fl' xl'
  | _, _ => absurd end.

Fixpoint plist_map_with `{F: A → _} {G} {Xl Yl} (h: ∀X Y, G X Y → F X → F Y) :
  plist2 G Xl Yl → plist F Xl → plist F Yl :=
  match Xl, Yl with [], [] => λ _, id
  | _ :: _, _ :: _ => λ '(f -:: fl') '(x -:: xl'), h _ _ f x -:: plist_map_with h fl' xl'
  | _, _ => absurd end.

Fixpoint hzip_with `{F: A → _} {G H Xl} (f: ∀X, F X → G X → H X)
  (xl: hlist F Xl) (yl: plist G Xl) : hlist H Xl :=
  match xl, yl with +[], _ => +[] |
    x +:: xl', y -:: yl' => f _ x y +:: hzip_with f xl' yl' end.
Notation hzip := (hzip_with (λ _, pair)).

Fixpoint pzip_with `{F: A → _} {G H Xl} (f: ∀X, F X → G X → H X)
  (xl: plist F Xl) (yl: plist G Xl) : plist H Xl :=
  match Xl, xl, yl with [], _, _ => -[] |
    _ :: _, x -:: xl', y -:: yl' => f _ x y -:: pzip_with f xl' yl' end.
Notation pzip := (pzip_with (λ _, pair)).

Fixpoint ptrans `{F: A → B} {G Xl} (xl: plist (G ∘ F) Xl) : plist G (map F Xl) :=
  match Xl, xl with [], _ => -[] | _ :: _, x -:: xl' => x -:: ptrans xl' end.

Fixpoint plist2_eq_nat_len `{F: A → _} {Xl Yl} :
  plist2 F Xl Yl → eq_nat (length Xl) (length Yl) :=
  match Xl, Yl with [], [] => λ _, I |
    _ :: _, _ :: _ => λ '(_ -:: xl'), plist2_eq_nat_len xl' | _, _ => absurd end.

Lemma plist2_eq_len `{F: A → _} {Xl Yl} : plist2 F Xl Yl → length Xl = length Yl.
Proof. by move=> /plist2_eq_nat_len/eq_nat_is_eq ?. Qed.

(** * Uniform plist *)

Definition plistc {B} (A: Type) (Xl: list B) : Type := plist (const A) Xl.

Fixpoint plistc_to_vec {B A} {Xl: _ B} (xl: plistc A Xl) : vec A (length Xl) :=
  match Xl, xl with [], _ => [#] | _ :: _, x -:: xl' => x ::: plistc_to_vec xl' end.
Coercion plistc_to_vec: plistc >-> vec.

Fixpoint plistc_renew {A} `{Xl: _ B} `{Yl: _ C}
  : eq_nat (length Xl) (length Yl) → plistc A Xl → plistc A Yl :=
  match Xl, Yl with [], [] => λ _ _, -[] |
    _ :: Xl', _ :: Yl' => λ e '(x -:: xl'), x -:: plistc_renew (Xl:=Xl') e xl' |
    _, _ => absurd end.

Lemma plistc_renew_eq {A} `{Xl: _ B} `{Yl: _ C} (xl: _ A _) (e: _ (_ Xl) (_ Yl)) :
  (plistc_renew e xl: list _) = xl.
Proof.
  move: Xl Yl e xl. fix FIX 1. case=> [|??]; case=>//= ???[??]/=. f_equal. apply FIX.
Qed.

(** * Vector *)

Fixpoint pvec A n : Type := match n with 0 => :1 | S m => A :* pvec A m end.

Fixpoint pvec_to_list {A n} (xl: pvec A n) : list A := match n, xl with
  0, _ => [] | S _, x -:: xl' => x :: pvec_to_list xl' end.
Coercion pvec_to_list: pvec >-> list.

Fixpoint pvmap {A B n} (f: A → B) : pvec A n → pvec B n :=
  match n with 0 => id | S _ => λ '(x -:: xl'), f x -:: pvmap f xl' end.
Infix "-v<$>" := pvmap (at level 61, left associativity).
Notation "( f -v<$>.)" := (pvmap f) (only parsing).

Fixpoint pvrepeat {A} (x: A) n : pvec A n :=
  match n with 0 => -[] | S m => x -:: pvrepeat x m end.

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
  : Unique (pvec A n) := {| unique := pvrepeat unique n |}.
Next Obligation.
  move=> ?? n. elim n; [by case|]=> ? IH [x xl]. by rewrite (eq_unique x) (IH xl).
Qed.

Fixpoint vec_to_pvec {A n} (xl: vec A n) : pvec A n :=
  match xl with [#] => -[] | x ::: xl' => x -:: vec_to_pvec xl' end.
Fixpoint pvec_to_vec {A n} (xl: pvec A n) : vec A n :=
  match n, xl with 0, _ => [#] | S _, x -:: xl' => x ::: pvec_to_vec xl' end.
Global Instance vec_pvec_iso {A n} : Iso (@vec_to_pvec A n) pvec_to_vec.
Proof.
  split; fun_ext. { by elim; [done|]=>/= > ->. }
  elim n; [by case|]=>/= > IH [??]. by rewrite/= IH.
Qed.

(** * Sum *)

Notation psum_raw F := (fix psum_raw Xl := match Xl with
  [] => ∅ | X :: Xl' => F X + psum_raw Xl' end%type).
Definition psum {A} (F: A → Type) (Xl: list A) : Type := psum_raw F Xl.

Fixpoint pinj `{F: A → _} {Xl} `{!Void (F D)} i :
  F (lnth D Xl i) → psum F Xl :=
  match Xl with [] => absurd | X :: Xl' =>
    match i with 0 => inl | S j => λ x, inr (pinj j x) end end.

Fixpoint psum_map `{F: A → _} {Xl Yl} :
  plist2 (λ X Y, F X → F Y) Xl Yl → psum F Xl → psum F Yl :=
  match Xl, Yl with [], [] => λ _, absurd
  | _ :: _, _ :: _ => λ '(f -:: fl'), sum_map f (psum_map fl')
  | _, _ => absurd end.

Lemma psum_map_pinj `{F: A → _} {Xl Yl} `{!Void (F D)}
  (fl: _ Xl Yl) i (x: F (lnth D _ _)) :
  psum_map fl (pinj i x) = pinj i (p2nth id fl i x).
Proof.
  move: Xl Yl fl i x. fix FIX 1. move=> [|??][|??]//=; [move=> *; by apply absurd|].
  case=> ??. case; [done|]=>/= *. by rewrite FIX.
Qed.

Definition to_psum_2 `{F: A → _} {X Y} (s: F X + F Y) : psum F [X; Y] :=
  match s with inl x => inl x | inr y => inr (inl y) end.
Definition of_psum_2 `{F: A → _} {X Y} (s: psum F [X; Y]) : F X + F Y :=
  match s with inl x => inl x | inr (inl y) => inr y | inr (inr e) => absurd e end.
Global Instance psum_2_iso `{F: A → _} {X Y} : Iso (@to_psum_2 _ F X Y) of_psum_2.
Proof. split; fun_ext; by [case|case=> [?|[?|[]]]]. Qed.

(** * Forall *)

Inductive HForall `{F: A → _} (Φ: ∀X, F X → Prop) : ∀{Xl}, hlist F Xl → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {X Xl} (x: _ X) (xl: _ Xl) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Inductive HForall2_1 `{F: A → _} {G H} (Φ: ∀X Y, F X → G Y → H X Y → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → Prop :=
| HForall2_1_nil: HForall2_1 Φ +[] +[] -[]
| HForall2_1_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z (xl: _ Xl) (yl: _ Yl) zl :
    Φ _ _ x y z → HForall2_1 Φ xl yl zl → HForall2_1 Φ (x +:: xl) (y +:: yl) (z -:: zl).

Inductive HForall2_2flip `{F: A → _} {G H K} (Φ: ∀X Y, F X → G Y → H X Y → K Y X → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → plist2 K Yl Xl → Prop :=
| HForall2_2flip_nil: HForall2_2flip Φ +[] +[] -[] -[]
| HForall2_2flip_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z w (xl: _ Xl) (yl: _ Yl) zl wl :
    Φ _ _ x y z w → HForall2_2flip Φ xl yl zl wl →
    HForall2_2flip Φ (x +:: xl) (y +:: yl) (z -:: zl) (w -:: wl).

Inductive HForallTwo `{F: A → _} {G} (Φ: ∀X, F X → G X → Prop)
  : ∀{Xl}, hlist F Xl → hlist G Xl → Prop :=
| HForallTwo_nil: HForallTwo Φ +[] +[]
| HForallTwo_cons {X Xl} (x y: _ X) (xl yl: _ Xl) :
    Φ _ x y → HForallTwo Φ xl yl → HForallTwo Φ (x +:: xl) (y +:: yl).

Lemma HForall_impl `{F: A → _} {Xl} (Φ Ψ: ∀X, F X → Prop) (xl: _ Xl) :
(∀X x, Φ X x → Ψ _ x) → HForall Φ xl → HForall Ψ xl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForallTwo_impl `{F: A → _} {G Xl} (Φ Ψ: ∀X, F X → G X → Prop) (xl yl: _ Xl) :
  (∀X x y, Φ X x y → Ψ _ x y) → HForallTwo Φ xl yl → HForallTwo Ψ xl yl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForall_nth `{F: A → _} {Xl D} (Φ: ∀X, F X → Prop) (d: _ D) (xl: _ Xl) i :
  Φ _ d → HForall Φ xl → Φ _ (hnth d xl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallTwo_nth `{F: A → _} {G Xl D}
  (Φ: ∀X, F X → G X → Prop) (d d': _ D) (xl yl: _ Xl) i :
  Φ _ d d' → HForallTwo Φ xl yl → Φ _ (hnth d xl i) (hnth d' yl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallTwo_forall `{!Inhabited Y} `{F: A → _} {G Xl}
  (Φ: ∀X, Y → F X → G X → Prop) (xl yl: _ Xl) :
  (∀z, HForallTwo (λ X, Φ X z) xl yl) ↔ HForallTwo (λ X x y, ∀z, Φ _ z x y) xl yl.
Proof.
  split; [|elim; by constructor]. move=> All. set One := All inhabitant.
  dependent induction One; [by constructor|]. constructor.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  have All': ∀z, HForallTwo (λ X, Φ X z) xl yl.
  { move=> z. move/(.$ z) in All. by dependent destruction All. } auto.
Qed.

Global Instance HForallTwo_reflexive `{F: A → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Reflexive (R X)) → Reflexive (HForallTwo R (Xl:=Xl)).
Proof. move=> ?. elim; by constructor. Qed.
Global Instance HForallTwo_symmetric `{F: A → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Symmetric (R X)) → Symmetric (HForallTwo R (Xl:=Xl)).
Proof. move=> >. elim; by constructor. Qed.
Global Instance HForallTwo_transitive `{F: A → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Transitive (R X)) → Transitive (HForallTwo R (Xl:=Xl)).
Proof.
  move=> ??? zl All. move: zl. elim: All; [done|]=> > ?? IH ? All.
  dependent destruction All. constructor; by [etrans|apply IH].
Qed.
Global Instance HForallTwo_equivalence `{F: A → _} {Xl} (R: ∀X, F X → F X → Prop) :
  (∀X, Equivalence (R X)) → Equivalence (HForallTwo R (Xl:=Xl)).
Proof. split; apply _. Qed.

(** * Ofe *)

Global Instance hlist_equiv `{F: A → ofe} {Xl}
: Equiv (hlist F Xl) := HForallTwo (λ _, (≡)).
Global Instance hlist_dist `{F: A → ofe} {Xl} : Dist (hlist F Xl) :=
  λ n, HForallTwo (λ _, (≡{n}≡)).

Definition hlist_ofe_mixin `{F: A → ofe} {Xl} : OfeMixin (hlist F Xl).
Proof. split=> >.
  - rewrite /equiv /hlist_equiv HForallTwo_forall.
    split=> H; induction H; constructor=>//; by apply equiv_dist.
  - apply _.
  - rewrite /dist /hlist_dist. apply HForallTwo_impl=> >. apply dist_S.
Qed.

Canonical Structure hlistO {A} (F: A → ofe) Xl := Ofe (hlist F Xl) hlist_ofe_mixin.

Section lemmas.
Context `{F: A → ofe}.

Global Instance hcons_ne {X Xl} : NonExpansive2 (@hcons _ F X Xl).
Proof. by constructor. Qed.
Global Instance hcons_proper {X Xl} :
  Proper ((≡@{_ X}) ==> (≡@{_ Xl}) ==> (≡)) (hcons F).
Proof. by constructor. Qed.

Global Instance hnth_ne {Xl D} n :
  Proper ((=@{_ D}) ==> (≡{n}@{hlist F Xl}≡) ==> forall_relation (λ _, (≡{n}≡))) hnth.
Proof. move=> ??->????. by apply (HForallTwo_nth (λ X, ofe_dist (F X) n)). Qed.
Global Instance hnth_proper {Xl D} :
  Proper ((=@{_ D}) ==> (≡@{hlist F Xl}) ==> forall_relation (λ _, (≡))) hnth.
Proof. move=> ??->?? /equiv_dist ??. apply equiv_dist=> ?. by apply hnth_ne. Qed.

End lemmas.

(** * big_sep *)

Section def.
Context {PROP: bi}.

Fixpoint big_sepHL `{F: A → _} {Xl} (Φ: ∀X, F X → PROP) (xl: hlist F Xl) : PROP :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end%I.

Fixpoint big_sepHL_1 `{F: A → _} {G Xl} (Φ: ∀X, F X → G X → PROP)
  (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  match xl, yl with +[], _ => True |
    x +:: xl', y -:: yl' => Φ _ x y ∗ big_sepHL_1 Φ xl' yl' end%I.

Fixpoint big_sepHL2_1 `{F: A → _} {G H Xl Yl} (Φ: ∀X Y, F X → G Y → H X Y → PROP)
  (xl: hlist F Xl) (yl: hlist G Yl) (zl: plist2 H Xl Yl) : PROP :=
  match xl, yl, zl with +[], +[], _ => True
  | x +:: xl', y +:: yl', z -:: zl' => Φ _ _ x y z ∗ big_sepHL2_1 Φ xl' yl' zl'
  | _, _, _ => False end%I.

End def.

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

Lemma big_sepHL_app `{F: A → _} {Xl Yl} (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  big_sepHL Φ (xl h++ xl') ⊣⊢ big_sepHL Φ xl ∗ big_sepHL Φ xl'.
Proof. elim xl; [by rewrite/= left_id|]=>/= > ->. by rewrite assoc. Qed.

Lemma big_sepHL_1_app `{F: A → _} {G Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  big_sepHL_1 Φ (xl h++ xl') (yl -++ yl') ⊣⊢ big_sepHL_1 Φ xl yl ∗ big_sepHL_1 Φ xl' yl'.
Proof.
  dependent induction xl; case yl=>/= >; by [rewrite left_id|rewrite IHxl assoc].
Qed.

Global Instance into_sep_big_sepHL_app `{F: A → _} {Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  IntoSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL Φ xl').
Proof. by rewrite /IntoSep big_sepHL_app. Qed.
Global Instance from_sep_big_sepHL_app `{F: A → _} {Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  FromSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL Φ xl').
Proof. by rewrite /FromSep big_sepHL_app. Qed.

Global Instance into_sep_big_sepHL_1_app `{F: A → _} {G Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  IntoSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 Φ xl' yl').
Proof. by rewrite /IntoSep big_sepHL_1_app. Qed.
Global Instance from_sep_big_sepHL_1_app `{F: A → _} {G Xl Yl}
  (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  FromSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 Φ xl' yl').
Proof. by rewrite /FromSep big_sepHL_1_app. Qed.

Global Instance frame_big_sepHL_app `{F: A → _} {Xl Yl}
  p R Q (xl: _ F Xl) (xl': _ Yl) (Φ: ∀C, _ → PROP) :
  Frame p R (big_sepHL Φ xl ∗ big_sepHL Φ xl') Q →
  Frame p R (big_sepHL Φ (xl h++ xl')) Q.
Proof. by rewrite /Frame big_sepHL_app. Qed.

Global Instance frame_big_sepHL_1_app `{F: A → _} {G Xl Yl}
  p R Q (xl: _ F Xl) (xl': _ Yl) (yl: _ G _) yl' (Φ: ∀C, _ → _ → PROP) :
  Frame p R (big_sepHL_1 Φ xl yl ∗ big_sepHL_1 Φ xl' yl') Q →
  Frame p R (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl')) Q.
Proof. by rewrite /Frame big_sepHL_1_app. Qed.

End lemmas.
