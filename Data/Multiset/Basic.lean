/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.ZeroCons

/-!
# Basic results on multisets

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.toList` -/

section ToList

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (s : Multiset α)
  body: s.out

@[simp, norm_cast]

中文:
定义 toList
  签名: (s : Multiset α)
  定义体: s.out

@[simp, norm_cast]

Depends on / 依赖: s.out
-/
noncomputable def toList (s : Multiset α) :=
  s.out

@[simp, norm_cast]
/--
theorem `coe_toList` / 定理 `coe_toList`

English:
theorem coe_toList
  given: (s : Multiset α)
  statement: (s.toList : Multiset α) = s
  proof: s.out_eq'

@[simp]

中文:
定理 coe_toList
  条件: (s : Multiset α)
  结论: (s.toList : Multiset α) = s
  证明: s.out_eq'

@[simp]

Depends on / 依赖: out_eq, s.out_eq
-/
theorem coe_toList (s : Multiset α) : (s.toList : Multiset α) = s :=
  s.out_eq'

@[simp]
/--
theorem `toList_eq_nil` / 定理 `toList_eq_nil`

English:
theorem toList_eq_nil
  given: {s : Multiset α}
  statement: s.toList = [] ↔ s = 0
  proof: by
  rw [← coe_eq_zero]; rw [coe_toList]

中文:
定理 toList_eq_nil
  条件: {s : Multiset α}
  结论: s.toList = [] ↔ s = 0
  证明: by
  rw [← coe_eq_zero]; rw [coe_toList]

Depends on / 依赖: coe_eq_zero, coe_toList
-/
theorem toList_eq_nil {s : Multiset α} : s.toList = [] ↔ s = 0 := by
  rw [← coe_eq_zero]; rw [coe_toList]

/--
theorem `empty_toList` / 定理 `empty_toList`

English:
theorem empty_toList
  given: {s : Multiset α}
  statement: s.toList.isEmpty ↔ s = 0
  proof: by simp

@[simp]

中文:
定理 empty_toList
  条件: {s : Multiset α}
  结论: s.toList.isEmpty ↔ s = 0
  证明: by simp

@[simp]
-/
theorem empty_toList {s : Multiset α} : s.toList.isEmpty ↔ s = 0 := by simp

@[simp]
/--
theorem `toList_zero` / 定理 `toList_zero`

English:
theorem toList_zero
  statement: (Multiset.toList 0 : List α) = []
  proof: toList_eq_nil.mpr rfl

@[simp]

中文:
定理 toList_zero
  结论: (Multiset.toList 0 : List α) = []
  证明: toList_eq_nil.mpr rfl

@[simp]

Depends on / 依赖: toList_eq_nil, toList_eq_nil.mpr
-/
theorem toList_zero : (Multiset.toList 0 : List α) = [] :=
  toList_eq_nil.mpr rfl

@[simp]
/--
theorem `mem_toList` / 定理 `mem_toList`

English:
theorem mem_toList
  given: {a : α} {s : Multiset α}
  statement: a in s.toList ↔ a in s
  proof: by
  rw [← mem_coe]; rw [coe_toList]

@[simp]

中文:
定理 mem_toList
  条件: {a : α} {s : Multiset α}
  结论: a in s.toList ↔ a in s
  证明: by
  rw [← mem_coe]; rw [coe_toList]

@[simp]

Depends on / 依赖: coe_toList, mem_coe
-/
theorem mem_toList {a : α} {s : Multiset α} : a in s.toList ↔ a in s := by
  rw [← mem_coe]; rw [coe_toList]

@[simp]
/--
theorem `toList_eq_singleton_iff` / 定理 `toList_eq_singleton_iff`

English:
theorem toList_eq_singleton_iff
  given: {a : α} {m : Multiset α}
  statement: m.toList = [a] ↔ m = {a}
  proof: by
  rw [← perm_singleton]; rw [← coe_eq_coe]; rw [coe_toList]; rw [coe_singleton]

@[simp]

中文:
定理 toList_eq_singleton_iff
  条件: {a : α} {m : Multiset α}
  结论: m.toList = [a] ↔ m = {a}
  证明: by
  rw [← perm_singleton]; rw [← coe_eq_coe]; rw [coe_toList]; rw [coe_singleton]

@[simp]

Depends on / 依赖: coe_eq_coe, coe_singleton, coe_toList, perm_singleton
-/
theorem toList_eq_singleton_iff {a : α} {m : Multiset α} : m.toList = [a] ↔ m = {a} := by
  rw [← perm_singleton]; rw [← coe_eq_coe]; rw [coe_toList]; rw [coe_singleton]

@[simp]
/--
theorem `toList_singleton` / 定理 `toList_singleton`

English:
theorem toList_singleton
  given: (a : α)
  statement: ({a} : Multiset α).toList = [a]
  proof: Multiset.toList_eq_singleton_iff.2 rfl

@[simp]

中文:
定理 toList_singleton
  条件: (a : α)
  结论: ({a} : Multiset α).toList = [a]
  证明: Multiset.toList_eq_singleton_iff.2 rfl

@[simp]

Depends on / 依赖: Multiset, Multiset.toList_eq_singleton_iff, toList_eq_singleton_iff
-/
theorem toList_singleton (a : α) : ({a} : Multiset α).toList = [a] :=
  Multiset.toList_eq_singleton_iff.2 rfl

@[simp]
/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  given: (s : Multiset α)
  statement: s.toList.length = card s
  proof: by
  rw [← coe_card]; rw [coe_toList]

中文:
定理 length_toList
  条件: (s : Multiset α)
  结论: s.toList.length = card s
  证明: by
  rw [← coe_card]; rw [coe_toList]

Depends on / 依赖: coe_card, coe_toList
-/
theorem length_toList (s : Multiset α) : s.toList.length = card s := by
  rw [← coe_card]; rw [coe_toList]

end ToList

/-! ### Induction principles -/

/-- The strong induction principle for multisets. -/
@[elab_as_elim]
/--
Definition of `strongInductionOn` / `strongInductionOn` 的定义

English:
definition strongInductionOn
  signature: {p : Multiset α -> Sort*} (s : Multiset α) (ih : forall s, (forall t < s, p t) -> p s)
  body: (ih s) fun t _h =>
      strongInductionOn t ih
termination_by card s
decreasing_by exact card_lt_card _h

中文:
定义 strongInductionOn
  签名: {p : Multiset α -> Sort*} (s : Multiset α) (ih : 对任意 s, (对任意 t < s, p t) -> p s)
  定义体: (ih s) fun t _h =>
      strongInductionOn t ih
termination_by card s
decreasing_by exact card_lt_card _h

Depends on / 依赖: card_lt_card, decreasing_by, strongInductionOn, termination_by
-/
def strongInductionOn {p : Multiset α -> Sort*} (s : Multiset α) (ih : forall s, (forall t < s, p t) -> p s) :
    p s :=
    (ih s) fun t _h =>
      strongInductionOn t ih
termination_by card s
decreasing_by exact card_lt_card _h

/--
theorem `strongInductionOn_eq` / 定理 `strongInductionOn_eq`

English:
theorem strongInductionOn_eq
  given: {p : Multiset α -> Sort*} (s : Multiset α) (H)
  proof: by
  rw [strongInductionOn]

@[elab_as_elim]

中文:
定理 strongInductionOn_eq
  条件: {p : Multiset α -> Sort*} (s : Multiset α) (H)
  证明: by
  rw [strongInductionOn]

@[elab_as_elim]

Depends on / 依赖: strongInductionOn
-/
theorem strongInductionOn_eq {p : Multiset α -> Sort*} (s : Multiset α) (H) :
    @strongInductionOn _ p s H = H s fun t _h => @strongInductionOn _ p t H := by
  rw [strongInductionOn]

@[elab_as_elim]
/--
theorem `case_strongInductionOn` / 定理 `case_strongInductionOn`

English:
theorem case_strongInductionOn
  statement: {p : Multiset α -> Prop} (s : Multiset α) (h₀ : p 0)
  proof: Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun _a _s _ ih =>
(h₁ _ _) fun _t h => ih _ lt_of_le_of_lt h lt_cons_self _ _

中文:
定理 case_strongInductionOn
  结论: {p : Multiset α -> 命题} (s : Multiset α) (h₀ : p 0)
  证明: Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun _a _s _ ih =>
(h₁ _ _) fun _t h => ih _ lt_of_le_of_lt h lt_cons_self _ _

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.strongInductionOn, induction_on, lt_cons_self, lt_of_le_of_lt, strongInductionOn
-/
theorem case_strongInductionOn {p : Multiset α -> Prop} (s : Multiset α) (h₀ : p 0)
    (h₁ : forall a s, (forall t <= s, p t) -> p (a ::ₘ s)) : p s :=
  Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun _a _s _ ih =>
(h₁ _ _) fun _t h => ih _ lt_of_le_of_lt h lt_cons_self _ _

/--
Definition of `strongDownwardInduction` / `strongDownwardInduction` 的定义

English:
definition strongDownwardInduction
  signature: {p : Multiset α -> Sort*} {n : Nat}
  body: H s fun {t} ht _h =>
    strongDownwardInduction H t ht
termination_by n - card s
decreasing_by have := (card_lt_card _h); lia

中文:
定义 strongDownwardInduction
  签名: {p : Multiset α -> Sort*} {n : 自然数}
  定义体: H s fun {t} ht _h =>
    strongDownwardInduction H t ht
termination_by n - card s
decreasing_by have := (card_lt_card _h); lia

Depends on / 依赖: card_lt_card, decreasing_by, strongDownwardInduction, termination_by
-/
def strongDownwardInduction {p : Multiset α -> Sort*} {n : Nat}
    (H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n -> p t₁)
    (s : Multiset α) :
    card s <= n -> p s :=
  H s fun {t} ht _h =>
    strongDownwardInduction H t ht
termination_by n - card s
decreasing_by have := (card_lt_card _h); lia

/--
theorem `strongDownwardInduction_eq` / 定理 `strongDownwardInduction_eq`

English:
theorem strongDownwardInduction_eq
  statement: {p : Multiset α -> Sort*} {n : Nat}
  proof: by
  rw [strongDownwardInduction]

中文:
定理 strongDownwardInduction_eq
  结论: {p : Multiset α -> Sort*} {n : 自然数}
  证明: by
  rw [strongDownwardInduction]

Depends on / 依赖: strongDownwardInduction
-/
theorem strongDownwardInduction_eq {p : Multiset α -> Sort*} {n : Nat}
    (H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n -> p t₁)
    (s : Multiset α) :
    strongDownwardInduction H s = H s fun ht _hst => strongDownwardInduction H _ ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
/--
Definition of `strongDownwardInductionOn` / `strongDownwardInductionOn` 的定义

English:
definition strongDownwardInductionOn
  signature: {p : Multiset α -> Sort*} {n : Nat}
  body: fun s H => strongDownwardInduction H s

中文:
定义 strongDownwardInductionOn
  签名: {p : Multiset α -> Sort*} {n : 自然数}
  定义体: fun s H => strongDownwardInduction H s

Depends on / 依赖: strongDownwardInduction
-/
def strongDownwardInductionOn {p : Multiset α -> Sort*} {n : Nat} :
    forall s : Multiset α,
      (forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n -> p t₁) ->
        card s <= n -> p s :=
  fun s H => strongDownwardInduction H s

/--
theorem `strongDownwardInductionOn_eq` / 定理 `strongDownwardInductionOn_eq`

English:
theorem strongDownwardInductionOn_eq
  statement: {p : Multiset α -> Sort*} (s : Multiset α) {n : Nat}
  proof: by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

中文:
定理 strongDownwardInductionOn_eq
  结论: {p : Multiset α -> Sort*} (s : Multiset α) {n : 自然数}
  证明: by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

Depends on / 依赖: strongDownwardInduction, strongDownwardInductionOn
-/
theorem strongDownwardInductionOn_eq {p : Multiset α -> Sort*} (s : Multiset α) {n : Nat}
    (H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n -> p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _h => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

section Choose

variable (p : α -> Prop) [DecidablePred p] (l : Multiset α)

/--
Definition of `chooseX` / `chooseX` 的定义

English:
definition chooseX
  signature: : forall _hp : exists! a, a in l ∧ p a, { a // a in l ∧ p a }
  body: Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intro a b _
      funext hp
      suffices all_equal : forall x y : { t // t in b ∧ p t }, x = y by
        apply all_equal
      rintro ⟨x, px⟩ ⟨y, py⟩
      rcases hp with ⟨z, ⟨_z_mem_l, _pz⟩, z_

中文:
定义 chooseX
  签名: : 对任意 _hp : 存在! a, a in l ∧ p a, { a // a in l ∧ p a }
  定义体: Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intro a b _
      funext hp
      suffices all_equal : forall x y : { t // t in b ∧ p t }, x = y by
        apply all_equal
      rintro ⟨x, px⟩ ⟨y, py⟩
      rcases hp with ⟨z, ⟨_z_mem_l, _pz⟩, z_

Depends on / 依赖: ExistsUnique, ExistsUnique.exists, List.chooseX, Quotient, Quotient.recOn, _z_mem_l, all_equal, chooseX, ex_unique, z_unique
-/
def chooseX : forall _hp : exists! a, a in l ∧ p a, { a // a in l ∧ p a } :=
  Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intro a b _
      funext hp
      suffices all_equal : forall x y : { t // t in b ∧ p t }, x = y by
        apply all_equal
      rintro ⟨x, px⟩ ⟨y, py⟩
      rcases hp with ⟨z, ⟨_z_mem_l, _pz⟩, z_unique⟩
      congr
      calc
        x = z := z_unique x px
        _ = y := (z_unique y py).symm)

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: (hp : exists! a, a in l ∧ p a)
  body: chooseX p l hp

中文:
定义 choose
  签名: (hp : 存在! a, a in l ∧ p a)
  定义体: chooseX p l hp

Depends on / 依赖: chooseX
-/
def choose (hp : exists! a, a in l ∧ p a) : α :=
  chooseX p l hp

/--
theorem `choose_spec` / 定理 `choose_spec`

English:
theorem choose_spec
  given: (hp : exists! a, a in l ∧ p a)
  statement: choose p l hp in l ∧ p (choose p l hp)
  proof: (chooseX p l hp).property

中文:
定理 choose_spec
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: choose p l hp in l ∧ p (choose p l hp)
  证明: (chooseX p l hp).property

Depends on / 依赖: chooseX, property
-/
theorem choose_spec (hp : exists! a, a in l ∧ p a) : choose p l hp in l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

/--
theorem `choose_mem` / 定理 `choose_mem`

English:
theorem choose_mem
  given: (hp : exists! a, a in l ∧ p a)
  statement: choose p l hp in l
  proof: (choose_spec _ _ _).1

中文:
定理 choose_mem
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: choose p l hp in l
  证明: (choose_spec _ _ _).1

Depends on / 依赖: choose_spec
-/
theorem choose_mem (hp : exists! a, a in l ∧ p a) : choose p l hp in l :=
  (choose_spec _ _ _).1

/--
theorem `choose_property` / 定理 `choose_property`

English:
theorem choose_property
  given: (hp : exists! a, a in l ∧ p a)
  statement: p (choose p l hp)
  proof: (choose_spec _ _ _).2

中文:
定理 choose_property
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: p (choose p l hp)
  证明: (choose_spec _ _ _).2

Depends on / 依赖: choose_spec
-/
theorem choose_property (hp : exists! a, a in l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

/--
theorem `choose_eq_iff` / 定理 `choose_eq_iff`

English:
theorem choose_eq_iff
  given: (hp : exists! a, a in l ∧ p a) {a : α}
  statement: choose p l hp = a ↔ a in l ∧ p a
  proof: ⟨fun h => h ▸ choose_spec p l hp, hp.unique (choose_spec p l hp)⟩

中文:
定理 choose_eq_iff
  条件: (hp : 存在! a, a in l ∧ p a) {a : α}
  结论: choose p l hp = a ↔ a in l ∧ p a
  证明: ⟨fun h => h ▸ choose_spec p l hp, hp.unique (choose_spec p l hp)⟩

Depends on / 依赖: choose_spec, hp.unique, unique
-/
theorem choose_eq_iff (hp : exists! a, a in l ∧ p a) {a : α} : choose p l hp = a ↔ a in l ∧ p a :=
  ⟨fun h => h ▸ choose_spec p l hp, hp.unique (choose_spec p l hp)⟩

end Choose

variable (α) in
/--
Definition of `subsingletonEquiv` / `subsingletonEquiv` 的定义

English:
definition subsingletonEquiv
  signature: [Subsingleton α]
  body: ofList
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) =>
      (List.ext_get h.length_eq) fun _ _ _ => Subsingleton.elim _ _
  right_inv m := Quot.inductionOn m fun _ => rfl

@[simp]

中文:
定义 subsingletonEquiv
  签名: [Subsingleton α]
  定义体: ofList
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) =>
      (List.ext_get h.length_eq) fun _ _ _ => Subsingleton.elim _ _
  right_inv m := Quot.inductionOn m fun _ => rfl

@[simp]

Depends on / 依赖: ofList
-/
def subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α where
  toFun := ofList
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) =>
      (List.ext_get h.length_eq) fun _ _ _ => Subsingleton.elim _ _
  right_inv m := Quot.inductionOn m fun _ => rfl

@[simp]
/--
theorem `coe_subsingletonEquiv` / 定理 `coe_subsingletonEquiv`

English:
theorem coe_subsingletonEquiv
  given: [Subsingleton α]
  proof: rfl

中文:
定理 coe_subsingletonEquiv
  条件: [Subsingleton α]
  证明: rfl
-/
theorem coe_subsingletonEquiv [Subsingleton α] :
    (subsingletonEquiv α : List α -> Multiset α) = ofList :=
  rfl

end Multiset
