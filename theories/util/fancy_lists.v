Require Import Equality.
From stdpp Require Import prelude.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Natural number with a bound; a passive variant of fin *)

Inductive poption (A: Set) : Set := PO | PS (ppred: A).
Arguments PO {_}. Arguments PS {_} _.
Fixpoint pfin (n: nat) : Set :=
  match n with 0 => ∅ | S m => poption (pfin m) end.

Declare Scope pfin_scope.
Bind Scope pfin_scope with pfin. Delimit Scope pfin_scope with PF.
Notation "0" := (PO) : pfin_scope. Notation "1" := (PS 0%PF) : pfin_scope.
Notation "2" := (PS 1%PF) : pfin_scope. Notation "3" := (PS 2%PF) : pfin_scope.

Fixpoint pfin_to_nat {n} : pfin n → nat := match n with 0 => absurd |
  S _ => λ i, match i with PO => 0 | PS j => pfin_to_nat j end end.
Coercion pfin_to_nat: pfin >-> nat.

Fixpoint p2fin (m: nat) (n: nat) : Set :=
  match m, n with S m', S n' => poption (p2fin m' n') | _, _ => ∅ end.

Fixpoint p2fin_to_nat {m n} : p2fin m n → nat := match m, n with
  S _, S _ => λ i, match i with PO => 0 | PS j => p2fin_to_nat j end |
  _, _ => absurd end.
Coercion p2fin_to_nat: p2fin >-> nat.

Fixpoint p2fin_l {m n} : p2fin m n → pfin m := match m, n with
  S _, S _ => λ i, match i with PO => PO | PS j => PS (p2fin_l j) end |
  _, _ => absurd end.
Fixpoint p2fin_r {m n} : p2fin m n → pfin n := match m, n with
  S _, S _ => λ i, match i with PO => PO | PS j => PS (p2fin_r j) end |
  _, _ => absurd end.

Lemma p2fin_lr_eq {m n} (i: p2fin m n) : (p2fin_l i : nat) = (p2fin_r i : nat).
Proof.
  move: m n i. elim; [done|]=> ? IH. do 2 (case; [done|]=> ?). by apply IH.
Qed.

Lemma ex_p2fin_l m n (i: pfin m) : m = n → ∃j: p2fin m n, i = p2fin_l j.
Proof.
  move=> <-. move: m i. elim; [done|]=> ? IH. case; [by exists PO|]=> i.
  move: (IH i)=> [j Eq]. exists (PS j). by rewrite Eq.
Qed.

(** * List for a higher universe *)
(** We use tlist 𝒯 for 𝒯 that contains Type *)

Inductive tlist 𝒯 := tnil: tlist 𝒯 | tcons: 𝒯 → tlist 𝒯 → tlist 𝒯.

Notation "^[ ]" := (tnil _) (at level 5, format "^[ ]").
Infix "^::" := (tcons _) (at level 60, right associativity).
Notation "^[ X ; .. ; Y ]" := (X ^:: .. (Y ^:: ^[]) ..)
  (at level 5, format "^[ X ;  .. ;  Y ]").

Fixpoint tapp {𝒯} (Xl Yl: tlist 𝒯) : tlist 𝒯 :=
  match Xl with ^[] => Yl | X ^:: Xl' => X ^:: tapp Xl' Yl end.
Infix "^++" := tapp (at level 60, right associativity).

Fixpoint tmap {𝒯 𝒰} (F: 𝒯 → 𝒰) (Xl: tlist 𝒯) : tlist 𝒰 :=
  match Xl with ^[] => ^[] | X ^:: Xl' => F X ^:: tmap F Xl' end.
Infix "^<$>" := tmap (at level 61, left associativity).

Fixpoint tlength {𝒯} (Xl: tlist 𝒯) : nat :=
  match Xl with ^[] => 0 | _ ^:: Xl' => S (tlength Xl') end.

Notation pidx Xl := (pfin (tlength Xl)).
Notation p2idx Xl Yl := (p2fin (tlength Xl) (tlength Yl)).

Fixpoint tget {𝒯} (Xl: tlist 𝒯) : pidx Xl → 𝒯 :=
  match Xl with ^[] => absurd |
    X ^:: Xl' => λ i, match i with PO => X | PS j => tget Xl' j end end.

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

Fixpoint hget `{F: 𝒯 → _} {Xl} (xl: hlist F Xl) : ∀i: pidx Xl, F (tget Xl i) :=
  match xl with +[] => λ i, absurd i | x +:: xl' =>
    λ i, match i with PO => x | PS j => hget xl' j end end.

Fixpoint hrepeat `{F: 𝒯 → _} {X} (x: F X) n : hlist F (trepeat X n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with `{F: 𝒯 → _} {Xl} (f: ∀X, F X → nat) (xl: hlist F Xl) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Fixpoint happly `{F: 𝒯 → _} {Y Xl} (fl: hlist (λ X, Y → F X) Xl) (x: Y)
  : hlist F Xl :=
  match fl with +[] => +[] | f +:: fl' => f x +:: happly fl' x end.
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

Lemma hget_apply `{F: 𝒯 → _} {Xl Y} (fl: _ (λ X, Y → F X) Xl) (x: Y) i :
  hget (fl +$ x) i = hget fl i x.
Proof. move: i. elim fl; [done|]=> > ?. by case. Qed.

(** * Passive Heterogeneous List *)

Inductive nil_unit: Set := nil_tt: nil_unit.
Program Global Instance nil_unit_unique: Unique nil_unit := {|unique := nil_tt|}.
Next Obligation. by case. Qed.

Record cons_prod (A B: Type) : Type := cons_pair { phead: A; ptail: B }.
Arguments cons_pair {_ _} _ _. Arguments phead {_ _} _. Arguments ptail {_ _} _.

Notation ":1" := nil_unit : type_scope.
Infix ":*" := cons_prod (at level 60, right associativity) : type_scope.
Notation "-[ ]" := nil_tt (at level 1, format "-[ ]").
Infix "-::" := cons_pair (at level 60, right associativity).
Notation "(-::)" := cons_pair (only parsing).
Notation "-[ X ; .. ; z ]" := (X -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ X ;  .. ;  z ]").

Definition to_cons_prod {A B} : A * B → A :* B := λ '((a, al)), a -:: al.
Definition of_cons_prod {A B} : A :* B → A * B := λ '(a -:: al), (a, al).
Global Instance cons_prod_iso {A B} : Iso (@to_cons_prod A B) of_cons_prod.
Proof. split; fun_ext; by case. Qed.

Notation plist_raw F := (fix plist_raw Xl : Type :=
  match Xl with ^[] => :1 | X ^:: Xl' => F X :* plist_raw Xl' end).

Definition plist {𝒯} (F: 𝒯 → Type) Xl : Type := plist_raw F Xl.

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

Fixpoint p2get `{F: 𝒯 → _} {Xl Yl}
  : plist2 F Xl Yl → ∀i, F (tget Xl (p2fin_l i)) (tget Yl (p2fin_r i)) :=
  match Xl, Yl with _ ^:: _, _ ^:: _ =>
    λ '(x -:: xl') i, match i with PO => x | PS j => p2get xl' j end
  | _, _ => λ _ i, absurd i end.

Fixpoint papply `{F: 𝒯 → _} {A Xl} (fl: plist (λ X, A → F X) Xl) (x: A)
  : plist F Xl := match Xl, fl with
    ^[], _ => -[] | _ ^:: _, f -:: fl' => f x -:: papply fl' x end.
Infix "-$" := papply (at level 61, left associativity).
Notation "( fl -$.)" := (papply fl) (only parsing).

Lemma papply_app `{F: 𝒯 → _} {A Xl Yl}
  (fl: plist (λ X, A → F X) Xl) (gl: _ Yl) (x: A) :
  (fl -++ gl) -$ x = (fl -$ x) -++ (gl -$ x).
Proof. move: fl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint plist_map `{F: 𝒯 → _} {Xl Yl} :
  plist2 (λ A B, F A → F B) Xl Yl → plist F Xl → plist F Yl :=
  match Xl, Yl with ^[], ^[] => λ _, id
  | _ ^:: _, _ ^:: _ => λ '(f -:: fl') '(x -:: xl'), f x -:: plist_map fl' xl'
  | _, _ => absurd end.

(** * Vector *)

Fixpoint pvec A n : Type := match n with 0 => :1 | S m => A :* pvec A m end.

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
  ^[] => ∅ | X ^:: Xl' => F X + psum_raw Xl' end%type).
Definition psum `(F: 𝒯 → Type) (Xl: tlist 𝒯) : Type := psum_raw F Xl.

Fixpoint pinj `{F: 𝒯 → _} {Xl} : ∀(i: pidx Xl) (x: F (tget Xl i)), psum F Xl :=
  match Xl with ^[] => λ i, absurd i | X ^:: Xl' => λ i,
    match i with PO => inl | PS j => λ x, inr (pinj j x) end end.

Fixpoint psum_map `{F: 𝒯 → _} {Xl Yl} :
  plist2 (λ A B, F A → F B) Xl Yl → psum F Xl → psum F Yl :=
  match Xl, Yl with ^[], ^[] => λ _, absurd
  | _ ^:: _, _ ^:: _ => λ '(f -:: fl'), sum_map f (psum_map fl')
  | _, _ => absurd end.

Lemma psum_map_pinj `{F: 𝒯 → _} {Xl Yl} (fl: plist2 (λ A B, F A → F B) Xl Yl)
  (i: p2idx Xl Yl) (x: F (tget Xl (p2fin_l i))) :
  psum_map fl (pinj (p2fin_l i) x) = pinj (p2fin_r i) (p2get fl i x).
Proof.
  move: Xl Yl fl i x. fix FIX 1. move=> [|??] [|??] /= fl; case=> [|?];
  case fl; [done|]=>/= *. by rewrite FIX.
Qed.

Definition of_psum_2 `{F: 𝒯 → _} {X Y} (s: psum F ^[X; Y]) : F X + F Y :=
  match s with inl x => inl x | inr (inl y) => inr y | inr (inr e) => absurd e end.
Definition to_psum_2 `{F: 𝒯 → _} {X Y} (s: F X + F Y) : psum F ^[X; Y] :=
  match s with inl x => inl x | inr y => inr (inl y) end.
Global Instance psum_2_iso `{F: 𝒯 → _} {X Y} : Iso (@of_psum_2 _ F X Y) to_psum_2.
Proof. split; fun_ext; by [case=> [?|[?|[]]]|case]. Qed.

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

Lemma HForall_get `{F: 𝒯 → _} {Xl} (Φ: ∀X, F X → Prop) (xl: _ Xl) i :
  HForall Φ xl → Φ _ (hget xl i).
Proof. move=> All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallTwo_get `{F: 𝒯 → _} {G Xl} (Φ: ∀X, F X → G X → Prop) (xl yl: _ Xl) i :
  HForallTwo Φ xl yl → Φ _ (hget xl i) (hget yl i).
Proof. move=> All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForall2_1_eq_len `{F: 𝒯 → _} {G H Xl Yl}
  (Φ: ∀X Y, F X → G Y → H X Y → Prop) (xl: _ Xl) (yl: _ Yl) zl :
  HForall2_1 Φ xl yl zl → tlength Xl = tlength Yl.
Proof. by elim; [done|]=>/= > ??->. Qed.

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

Global Instance hcons_proper {X Xl} :
  Proper ((≡@{_ X}) ==> (≡@{_ Xl}) ==> (≡)) (hcons F).
Proof. by constructor. Qed.

Global Instance hget_proper {Xl} :
  Proper ((≡@{_ F Xl}) ==> forall_relation (λ _, (≡))) hget.
Proof. move=> ????. by apply (HForallTwo_get _). Qed.

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

Canonical Structure hlistO `(F: 𝒯 → ofe) Xl := Ofe (hlist F Xl) hlist_ofe_mixin.

Section lemmas.
Context `{F: 𝒯 → ofe}.

Global Instance hcons_ne {X Xl} : NonExpansive2 (@hcons _ F X Xl).
Proof. by constructor. Qed.

Global Instance hget_ne {Xl} n :
  Proper ((≡{n}≡@{hlist F Xl}) ==> forall_relation (λ _, (≡{n}≡))) hget.
Proof. move=> ????. by apply (HForallTwo_get (λ X, ofe_dist (F X) n)). Qed.

End lemmas.

(** * big_sep *)

Section def.
Context {PROP: bi}.

Fixpoint big_sepTL {X} (Φ: X → PROP) (xl: tlist X) : PROP :=
  match xl with ^[] => True | x ^:: xl' => Φ x ∗ big_sepTL Φ xl' end%I.

Fixpoint big_sepHL `{F: 𝒯 → _} {Xl} (Φ: ∀X, F X → PROP) (xl: hlist F Xl) : PROP :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end%I.

Fixpoint big_sepHL_1 `{F: 𝒯 → _} {G Xl} (Φ: ∀X, F X → G X → PROP)
  (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  match xl, yl with +[], _ => True |
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
