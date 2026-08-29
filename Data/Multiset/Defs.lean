/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Quot
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Multisets

Multisets are finite sets with duplicates allowed. They are implemented here as the quotient of
lists by permutation. This gives them computational content.

This file contains the definition of `Multiset` and the basic predicates. Most operations
have been split off into their own files. The goal is that we can define `Finset` with only
importing `Multiset.Defs`.

## Main definitions

* `Multiset`: the type of finite sets with duplicates allowed.

* `Coe (List α) (Multiset α)`: turn a list into a multiset by forgetting the order.
* `Multiset.pmap`: map a partial function defined on a superset of the multiset's elements.
* `Multiset.attach`: add a proof of membership to the elements of the multiset.
* `Multiset.card`: number of elements of a multiset (counted with repetition).

* `Membership α (Multiset α)` instance: `x ∈ s` if `x` has multiplicity at least one in `s`.
* `Subset (Multiset α)` instance: `s ⊆ t` if every `x ∈ s` also enjoys `x ∈ t`.
* `PartialOrder (Multiset α)` instance: `s ≤ t` if all `x` have multiplicity in
  `s` less than their multiplicity in `t`.
* `Multiset.Pairwise`: `Pairwise r s` holds iff there exists a list of elements
  of `s` such that `r` holds pairwise.
* `Multiset.Nodup`: `Nodup s` holds if the multiplicity of any element is at most 1.

## Notation (defined later)

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.
* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.
* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

/--
Definition of `Multiset.` / `Multiset.` 的定义

English:
definition Multiset.{u}
  signature: (α : Type u)
  body: Quotient (List.isSetoid α)

中文:
定义 Multiset.{u}
  签名: (α : 类型u)
  定义体: Quotient (List.isSetoid α)

Depends on / 依赖: List.isSetoid, Quotient, isSetoid
-/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

/-- The quotient map from `List α` to `Multiset α`. -/
@[coe]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: : List α -> Multiset α
  body: Quot.mk _

中文:
定义 ofList
  签名: : 列表 α -> Multiset α
  定义体: Quot.mk _

Depends on / 依赖: Quot.mk
-/
def ofList : List α -> Multiset α :=
  Quot.mk _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (List α) (Multiset α)
  body: ⟨ofList⟩

@[simp]

中文:
实例 :
  签名: Coe (列表 α) (Multiset α)
  定义体: ⟨ofList⟩

@[simp]

Depends on / 依赖: ofList
-/
instance : Coe (List α) (Multiset α) :=
  ⟨ofList⟩

@[simp]
/--
theorem `quot_mk_to_coe` / 定理 `quot_mk_to_coe`

English:
theorem quot_mk_to_coe
  given: (l : List α)
  statement: @Eq (Multiset α) ⟦l⟧ l
  proof: rfl

@[simp]

中文:
定理 quot_mk_to_coe
  条件: (l : 列表 α)
  结论: @相等 (Multiset α) ⟦l⟧ l
  证明: rfl

@[simp]
-/
theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l :=
  rfl

@[simp]
/--
theorem `quot_mk_to_coe'` / 定理 `quot_mk_to_coe'`

English:
theorem quot_mk_to_coe'
  given: (l : List α)
  statement: @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l
  proof: rfl

@[simp]

中文:
定理 quot_mk_to_coe'
  条件: (l : 列表 α)
  结论: @相等 (Multiset α) (商.mk (· ≈ ·) l) l
  证明: rfl

@[simp]
-/
theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l :=
  rfl

@[simp]
/--
theorem `quot_mk_to_coe''` / 定理 `quot_mk_to_coe''`

English:
theorem quot_mk_to_coe''
  given: (l : List α)
  statement: @Eq (Multiset α) (Quot.mk Setoid.r l) l
  proof: rfl

@[simp]

中文:
定理 quot_mk_to_coe''
  条件: (l : 列表 α)
  结论: @相等 (Multiset α) (商.mk 集合等价关系.r l) l
  证明: rfl

@[simp]
-/
theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l :=
  rfl

@[simp]
/--
theorem `lift_coe` / 定理 `lift_coe`

English:
theorem lift_coe
  statement: {α β : Type*} (x : List α) (f : List α -> β)
  proof: Quotient.lift_mk _ _ _

@[simp]

中文:
定理 lift_coe
  结论: {α β : 类型} (x : 列表 α) (f : 列表 α -> β)
  证明: Quotient.lift_mk _ _ _

@[simp]

Depends on / 依赖: Quotient, Quotient.lift_mk, lift_mk
-/
theorem lift_coe {α β : Type*} (x : List α) (f : List α -> β)
    (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _

@[simp]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {l₁ l₂ : List α}
  statement: (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂
  proof: Quotient.eq

中文:
定理 coe_eq_coe
  条件: {l₁ l₂ : 列表 α}
  结论: (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Quotient.eq

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: move to better place
-- (upstream to Batteries?)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (l₁ l₂
  body: inferInstanceAs (Decidable (l₁ ~ l₂))

中文:
实例 [DecidableEq
  签名: α] (l₁ l₂
  定义体: inferInstanceAs (Decidable (l₁ ~ l₂))

Depends on / 依赖: Decidable
-/
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ ≈ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (l₁ l₂
  body: inferInstanceAs (Decidable (l₁ ~ l₂))

中文:
实例 [DecidableEq
  签名: α] (l₁ l₂
  定义体: inferInstanceAs (Decidable (l₁ ~ l₂))

Depends on / 依赖: Decidable
-/
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (isSetoid α l₁ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [DecidableEq α]

中文:
实例 decidableEq
  签名: [DecidableEq α]
-/
instance decidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => Quotient.recOnSubsingleton₂ s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq_iff_equiv

section Mem

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : Multiset α) (a : α)
  body: Quot.liftOn s (fun l => a in l) fun l₁ l₂ (e : l₁ ~ l₂) => propext e.mem_iff

中文:
定义 Mem
  签名: (s : Multiset α) (a : α)
  定义体: Quot.liftOn s (fun l => a in l) fun l₁ l₂ (e : l₁ ~ l₂) => propext e.mem_iff

Depends on / 依赖: Quot.liftOn, e.mem_iff, liftOn, mem_iff, propext
-/
def Mem (s : Multiset α) (a : α) : Prop :=
Quot.liftOn s (fun l => a in l) fun l₁ l₂ (e : l₁ ~ l₂) => propext e.mem_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Multiset α)
  body: ⟨Mem⟩

@[simp]

中文:
实例 :
  签名: Membership α (Multiset α)
  定义体: ⟨Mem⟩

@[simp]
-/
instance : Membership α (Multiset α) :=
  ⟨Mem⟩

@[simp]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {a : α} {l : List α}
  statement: a in (l : Multiset α) ↔ a in l
  proof: Iff.rfl

中文:
定理 mem_coe
  条件: {a : α} {l : 列表 α}
  结论: a in (l : Multiset α) ↔ a in l
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔ a in l :=
  Iff.rfl

/--
Instance `decidableMem` / 实例 `decidableMem`

English:
instance decidableMem
  signature: [DecidableEq α] (a : α) (s : Multiset α)
  body: Quot.recOnSubsingleton s fun l => inferInstanceAs (Decidable (a in l))

中文:
实例 decidableMem
  签名: [DecidableEq α] (a : α) (s : Multiset α)
  定义体: Quot.recOnSubsingleton s fun l => inferInstanceAs (Decidable (a in l))

Depends on / 依赖: Decidable, Quot.recOnSubsingleton, recOnSubsingleton
-/
instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a in s) :=
  Quot.recOnSubsingleton s fun l => inferInstanceAs (Decidable (a in l))

end Mem

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

/--
Definition of `Subset` / `Subset` 的定义

English:
definition Subset
  signature: (s t : Multiset α)
  body: forall ⦃a : α⦄, a in s -> a in t

中文:
定义 子集
  签名: (s t : Multiset α)
  定义体: forall ⦃a : α⦄, a in s -> a in t
-/
protected def Subset (s t : Multiset α) : Prop :=
  forall ⦃a : α⦄, a in s -> a in t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSubset (Multiset α)
  body: ⟨Multiset.Subset⟩

中文:
实例 :
  签名: HasSubset (Multiset α)
  定义体: ⟨Multiset.Subset⟩

Depends on / 依赖: Multiset, Multiset.Subset, Subset
-/
instance : HasSubset (Multiset α) :=
  ⟨Multiset.Subset⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSSubset (Multiset α)
  body: ⟨fun s t => s subseteq t ∧ ¬t subseteq s⟩

中文:
实例 :
  签名: HasSSubset (Multiset α)
  定义体: ⟨fun s t => s subseteq t ∧ ¬t subseteq s⟩

Depends on / 依赖: subseteq
-/
instance : HasSSubset (Multiset α) :=
  ⟨fun s t => s subseteq t ∧ ¬t subseteq s⟩

/--
Instance `instIsNonstrictStrictOrder` / 实例 `instIsNonstrictStrictOrder`

English:
instance instIsNonstrictStrictOrder
  signature: : IsNonstrictStrictOrder (Multiset α) (· subseteq ·) (· ⊂ ·) where
  body: Iff.rfl

@[simp]

中文:
实例 instIsNonstrictStrictOrder
  签名: : 是NonstrictStrict序 (Multiset α) (· subseteq ·) (· ⊂ ·) where
  定义体: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
instance instIsNonstrictStrictOrder : IsNonstrictStrictOrder (Multiset α) (· subseteq ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

@[simp]
/--
theorem `coe_subset` / 定理 `coe_subset`

English:
theorem coe_subset
  given: {l₁ l₂ : List α}
  statement: (l₁ : Multiset α) subseteq l₂ ↔ l₁ subseteq l₂
  proof: Iff.rfl

@[simp]

中文:
定理 coe_subset
  条件: {l₁ l₂ : 列表 α}
  结论: (l₁ : Multiset α) subseteq l₂ ↔ l₁ subseteq l₂
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) subseteq l₂ ↔ l₁ subseteq l₂ :=
  Iff.rfl

@[simp]
/--
theorem `Subset.refl` / 定理 `Subset.refl`

English:
theorem Subset.refl
  given: (s : Multiset α)
  statement: s subseteq s
  proof: fun _ h => h

中文:
定理 子集.refl
  条件: (s : Multiset α)
  结论: s subseteq s
  证明: fun _ h => h
-/
theorem Subset.refl (s : Multiset α) : s subseteq s := fun _ h => h

/--
theorem `Subset.trans` / 定理 `Subset.trans`

English:
theorem Subset.trans
  given: {s t u : Multiset α}
  statement: s subseteq t -> t subseteq u -> s subseteq u
  proof: fun h₁ h₂ _ m => h₂ (h₁ m)

中文:
定理 子集.trans
  条件: {s t u : Multiset α}
  结论: s subseteq t -> t subseteq u -> s subseteq u
  证明: fun h₁ h₂ _ m => h₂ (h₁ m)
-/
theorem Subset.trans {s t u : Multiset α} : s subseteq t -> t subseteq u -> s subseteq u := fun h₁ h₂ _ m => h₂ (h₁ m)

/--
theorem `subset_iff` / 定理 `subset_iff`

English:
theorem subset_iff
  given: {s t : Multiset α}
  statement: s subseteq t ↔ forall ⦃x⦄, x in s -> x in t
  proof: Iff.rfl

@[gcongr]

中文:
定理 subset_iff
  条件: {s t : Multiset α}
  结论: s subseteq t ↔ 对任意 ⦃x⦄, x in s -> x in t
  证明: Iff.rfl

@[gcongr]

Depends on / 依赖: Iff.rfl
-/
theorem subset_iff {s t : Multiset α} : s subseteq t ↔ forall ⦃x⦄, x in s -> x in t :=
  Iff.rfl

@[gcongr]
/--
theorem `mem_of_subset` / 定理 `mem_of_subset`

English:
theorem mem_of_subset
  given: {s t : Multiset α} {a : α} (h : s subseteq t)
  statement: a in s -> a in t
  proof: @h _

中文:
定理 mem_of_subset
  条件: {s t : Multiset α} {a : α} (h : s subseteq t)
  结论: a in s -> a in t
  证明: @h _
-/
theorem mem_of_subset {s t : Multiset α} {a : α} (h : s subseteq t) : a in s -> a in t :=
  @h _

end Subset

/-! ### Partial order on `Multiset`s -/


/--
Definition of `Le` / `Le` 的定义

English:
definition Le
  signature: (s t : Multiset α)
  body: (Quotient.liftOn₂ s t (· <+~ ·)) fun _ _ _ _ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)

中文:
定义 Le
  签名: (s t : Multiset α)
  定义体: (Quotient.liftOn₂ s t (· <+~ ·)) fun _ _ _ _ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)
-/
protected def Le (s t : Multiset α) : Prop :=
  (Quotient.liftOn₂ s t (· <+~ ·)) fun _ _ _ _ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Multiset α)
  body: Multiset.Le
  le_refl := by rintro ⟨l⟩; exact Subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @Subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact Quot.sound (Subperm.antisymm h₁ h₂)

中文:
实例 :
  签名: 偏序 (Multiset α)
  定义体: Multiset.Le
  le_refl := by rintro ⟨l⟩; exact Subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @Subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact Quot.sound (Subperm.antisymm h₁ h₂)

Depends on / 依赖: Multiset, Multiset.Le
-/
instance : PartialOrder (Multiset α) where
  le := Multiset.Le
  le_refl := by rintro ⟨l⟩; exact Subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @Subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact Quot.sound (Subperm.antisymm h₁ h₂)

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [DecidableEq α]
  body: fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

中文:
实例 decidableLE
  签名: [DecidableEq α]
  定义体: fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

Depends on / 依赖: List.decidableSubperm, Quotient, Quotient.recOnSubsingleton, decidableSubperm
-/
instance decidableLE [DecidableEq α] : DecidableLE (Multiset α) :=
  fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

section

variable {s t : Multiset α} {a : α}

/--
theorem `subset_of_le` / 定理 `subset_of_le`

English:
theorem subset_of_le
  statement: s <= t -> s subseteq t
  proof: Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le

中文:
定理 subset_of_le
  结论: s <= t -> s subseteq t
  证明: Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le

Depends on / 依赖: Quotient, Quotient.inductionOn, Subperm, Subperm.subset, subset
-/
theorem subset_of_le : s <= t -> s subseteq t :=
  Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le

/--
theorem `mem_of_le` / 定理 `mem_of_le`

English:
theorem mem_of_le
  given: (h : s <= t)
  statement: a in s -> a in t
  proof: mem_of_subset (subset_of_le h)

中文:
定理 mem_of_le
  条件: (h : s <= t)
  结论: a in s -> a in t
  证明: mem_of_subset (subset_of_le h)

Depends on / 依赖: mem_of_subset, subset_of_le
-/
theorem mem_of_le (h : s <= t) : a in s -> a in t :=
  mem_of_subset (subset_of_le h)

/--
theorem `notMem_mono` / 定理 `notMem_mono`

English:
theorem notMem_mono
  given: (h : s subseteq t)
  statement: a ∉ t -> a ∉ s
  proof: mt @h _

@[simp]

中文:
定理 notMem_mono
  条件: (h : s subseteq t)
  结论: a ∉ t -> a ∉ s
  证明: mt @h _

@[simp]
-/
theorem notMem_mono (h : s subseteq t) : a ∉ t -> a ∉ s :=
mt @h _

@[simp]
/--
theorem `coe_le` / 定理 `coe_le`

English:
theorem coe_le
  given: {l₁ l₂ : List α}
  statement: (l₁ : Multiset α) <= l₂ ↔ l₁ <+~ l₂
  proof: Iff.rfl

@[elab_as_elim]

中文:
定理 coe_le
  条件: {l₁ l₂ : 列表 α}
  结论: (l₁ : Multiset α) <= l₂ ↔ l₁ <+~ l₂
  证明: Iff.rfl

@[elab_as_elim]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) <= l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl

@[elab_as_elim]
/--
theorem `leInductionOn` / 定理 `leInductionOn`

English:
theorem leInductionOn
  statement: {C : Multiset α -> Multiset α -> Prop} {s t : Multiset α} (h : s <= t)
  proof: Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

中文:
定理 leInductionOn
  结论: {C : Multiset α -> Multiset α -> 命题} {s t : Multiset α} (h : s <= t)
  证明: Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

Depends on / 依赖: Quot.sound, Quotient, Quotient.inductionOn
-/
theorem leInductionOn {C : Multiset α -> Multiset α -> Prop} {s t : Multiset α} (h : s <= t)
    (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C l₁ l₂) : C s t :=
  Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

end

/-! ### Cardinality -/


/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: : Multiset α -> Nat
  body: Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]

中文:
定义 card
  签名: : Multiset α -> 自然数
  定义体: Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, Perm.length_eq, Quot.lift, Sym.replicate, Sym.replicate_right_injective, length, length_eq, of_injective, replicate, replicate_right_injective
-/
def card : Multiset α -> Nat := Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]
/--
theorem `coe_card` / 定理 `coe_card`

English:
theorem coe_card
  given: (l : List α)
  statement: card (l : Multiset α) = length l
  proof: rfl

中文:
定理 coe_card
  条件: (l : 列表 α)
  结论: card (l : Multiset α) = length l
  证明: rfl
-/
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl

/--
theorem `card_le_card` / 定理 `card_le_card`

English:
theorem card_le_card
  given: {s t : Multiset α} (h : s <= t)
  statement: card s <= card t
  proof: leInductionOn h Sublist.length_le

中文:
定理 card_le_card
  条件: {s t : Multiset α} (h : s <= t)
  结论: card s <= card t
  证明: leInductionOn h Sublist.length_le

Depends on / 依赖: Sublist, Sublist.length_le, leInductionOn, length_le
-/
theorem card_le_card {s t : Multiset α} (h : s <= t) : card s <= card t :=
  leInductionOn h Sublist.length_le

/--
theorem `eq_of_le_of_card_le` / 定理 `eq_of_le_of_card_le`

English:
theorem eq_of_le_of_card_le
  given: {s t : Multiset α} (h : s <= t)
  statement: card t <= card s -> s = t
  proof: leInductionOn h fun s h₂ => congr_arg _ s.eq_of_length_le h₂

中文:
定理 eq_of_le_of_card_le
  条件: {s t : Multiset α} (h : s <= t)
  结论: card t <= card s -> s = t
  证明: leInductionOn h fun s h₂ => congr_arg _ s.eq_of_length_le h₂

Depends on / 依赖: congr_arg, eq_of_length_le, leInductionOn, s.eq_of_length_le
-/
theorem eq_of_le_of_card_le {s t : Multiset α} (h : s <= t) : card t <= card s -> s = t :=
leInductionOn h fun s h₂ => congr_arg _ s.eq_of_length_le h₂

/--
theorem `card_lt_card` / 定理 `card_lt_card`

English:
theorem card_lt_card
  given: {s t : Multiset α} (h : s < t)
  statement: card s < card t
  proof: lt_of_not_ge fun h₂ => _root_.ne_of_lt h eq_of_le_of_card_le (le_of_lt h) h₂

@[gcongr, mono]

中文:
定理 card_lt_card
  条件: {s t : Multiset α} (h : s < t)
  结论: card s < card t
  证明: lt_of_not_ge fun h₂ => _root_.ne_of_lt h eq_of_le_of_card_le (le_of_lt h) h₂

@[gcongr, mono]

Depends on / 依赖: _root_, _root_.ne_of_lt, eq_of_le_of_card_le, le_of_lt, lt_of_not_ge, ne_of_lt
-/
theorem card_lt_card {s t : Multiset α} (h : s < t) : card s < card t :=
lt_of_not_ge fun h₂ => _root_.ne_of_lt h eq_of_le_of_card_le (le_of_lt h) h₂

@[gcongr, mono]
/--
theorem `card_mono` / 定理 `card_mono`

English:
theorem card_mono
  statement: Monotone (@card α)
  proof: fun _a _b => card_le_card

@[gcongr]

中文:
定理 card_mono
  结论: 递增 (@card α)
  证明: fun _a _b => card_le_card

@[gcongr]

Depends on / 依赖: card_le_card
-/
theorem card_mono : Monotone (@card α) := fun _a _b => card_le_card

@[gcongr]
/--
lemma `card_strictMono` / 引理 `card_strictMono`

English:
lemma card_strictMono
  statement: StrictMono (@card α)
  proof: fun _ _ => card_lt_card

中文:
引理 card_strictMono
  结论: 严格递增 (@card α)
  证明: fun _ _ => card_lt_card

Depends on / 依赖: card_lt_card
-/
lemma card_strictMono : StrictMono (@card α) := fun _ _ => card_lt_card

/--
Instance `instWellFoundedLT` / 实例 `instWellFoundedLT`

English:
instance instWellFoundedLT
  signature: : WellFoundedLT (Multiset α)
  body: ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

@[simp]

中文:
实例 instWellFoundedLT
  签名: : WellFoundedLT (Multiset α)
  定义体: ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.card, Multiset.card_lt_card, Subrelation, Subrelation.wf, card_lt_card, measure
-/
instance instWellFoundedLT : WellFoundedLT (Multiset α) :=
  ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

@[simp]
/--
theorem `coe_reverse` / 定理 `coe_reverse`

English:
theorem coe_reverse
  given: (l : List α)
  statement: (reverse l : Multiset α) = l
  proof: Quot.sound reverse_perm _

中文:
定理 coe_reverse
  条件: (l : 列表 α)
  结论: (reverse l : Multiset α) = l
  证明: Quot.sound reverse_perm _

Depends on / 依赖: Quot.sound, reverse_perm
-/
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
Quot.sound reverse_perm _

/-! ### Map for partial functions -/

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
nonrec def pmap {p : α -> Prop} (f : forall a, p a -> β) (s : Multiset α) : (forall a in s, p a) -> Multiset β :=
  Quot.recOn s (fun l H => ↑(pmap f l H)) fun l₁ l₂ (pp : l₁ ~ l₂) =>
    funext fun H₂ : forall a in l₂, p a =>
      have H₁ : forall a in l₁, p a := fun a h => H₂ a (pp.subset h)
      have : forall {s₂ e H}, @Eq.ndrec (Multiset α) l₁ (fun s => (forall a in s, p a) -> Multiset β)
          (fun _ => ↑(pmap f l₁ H₁)) s₂ e H = ↑(pmap f l₁ H₁) := by
        intro s₂ e _; subst e; rfl
this.trans Quot.sound pp.pmap f

@[simp]
/--
theorem `coe_pmap` / 定理 `coe_pmap`

English:
theorem coe_pmap
  given: {p : α -> Prop} (f : forall a, p a -> β) (l : List α) (H : forall a in l, p a)
  proof: rfl

中文:
定理 coe_pmap
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) (l : 列表 α) (H : 对任意 a in l, p a)
  证明: rfl
-/
theorem coe_pmap {p : α -> Prop} (f : forall a, p a -> β) (l : List α) (H : forall a in l, p a) :
    pmap f l H = l.pmap f H :=
  rfl

/--
theorem `pmap_congr` / 定理 `pmap_congr`

English:
theorem pmap_congr
  given: {p q : α -> Prop} {f : forall a, p a -> β} {g : forall a, q a -> β} (s : Multiset α)
  proof: @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

@[simp]

中文:
定理 pmap_congr
  条件: {p q : α -> 命题} {f : 对任意 a, p a -> β} {g : 对任意 a, q a -> β} (s : Multiset α)
  证明: @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

@[simp]

Depends on / 依赖: List.pmap_congr_left, Quot.inductionOn, congr_arg, inductionOn, pmap_congr_left
-/
theorem pmap_congr {p q : α -> Prop} {f : forall a, p a -> β} {g : forall a, q a -> β} (s : Multiset α) :
    forall {H₁ H₂}, (forall a in s, forall (h₁ h₂), f a h₁ = g a h₂) -> pmap f s H₁ = pmap g s H₂ :=
  @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

@[simp]
/--
theorem `mem_pmap` / 定理 `mem_pmap`

English:
theorem mem_pmap
  given: {p : α -> Prop} {f : forall a, p a -> β} {s H b}
  proof: Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]

中文:
定理 mem_pmap
  条件: {p : α -> 命题} {f : 对任意 a, p a -> β} {s H b}
  证明: Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]

Depends on / 依赖: List.mem_pmap, Quot.inductionOn, inductionOn, mem_pmap, rule_sets
-/
theorem mem_pmap {p : α -> Prop} {f : forall a, p a -> β} {s H b} :
    b in pmap f s H ↔ exists (a : _) (h : a in s), f a (H a h) = b :=
  Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]
/--
theorem `card_pmap` / 定理 `card_pmap`

English:
theorem card_pmap
  given: {p : α -> Prop} (f : forall a, p a -> β) (s H)
  statement: card (pmap f s H) = card s
  proof: Quot.inductionOn s (fun _l _H => length_pmap) H

中文:
定理 card_pmap
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) (s H)
  结论: card (pmap f s H) = card s
  证明: Quot.inductionOn s (fun _l _H => length_pmap) H

Depends on / 依赖: Quot.inductionOn, inductionOn, length_pmap
-/
theorem card_pmap {p : α -> Prop} (f : forall a, p a -> β) (s H) : card (pmap f s H) = card s :=
  Quot.inductionOn s (fun _l _H => length_pmap) H

/--
Definition of `attach` / `attach` 的定义

English:
definition attach
  signature: (s : Multiset α)
  body: pmap Subtype.mk s fun _a => id

@[simp]

中文:
定义 attach
  签名: (s : Multiset α)
  定义体: pmap Subtype.mk s fun _a => id

@[simp]

Depends on / 依赖: Subtype, Subtype.mk
-/
def attach (s : Multiset α) : Multiset { x // x in s } :=
  pmap Subtype.mk s fun _a => id

@[simp]
/--
theorem `coe_attach` / 定理 `coe_attach`

English:
theorem coe_attach
  given: (l : List α)
  statement: @Eq (Multiset { x // x in l }) (@attach α l) l.attach
  proof: rfl

@[simp]

中文:
定理 coe_attach
  条件: (l : 列表 α)
  结论: @相等 (Multiset { x // x in l }) (@attach α l) l.attach
  证明: rfl

@[simp]
-/
theorem coe_attach (l : List α) : @Eq (Multiset { x // x in l }) (@attach α l) l.attach :=
  rfl

@[simp]
/--
theorem `mem_attach` / 定理 `mem_attach`

English:
theorem mem_attach
  given: (s : Multiset α)
  statement: forall x, x in s.attach
  proof: Quot.inductionOn s fun _l => List.mem_attach _

@[simp]

中文:
定理 mem_attach
  条件: (s : Multiset α)
  结论: 对任意 x, x in s.attach
  证明: Quot.inductionOn s fun _l => List.mem_attach _

@[simp]

Depends on / 依赖: List.mem_attach, Quot.inductionOn, inductionOn, mem_attach
-/
theorem mem_attach (s : Multiset α) : forall x, x in s.attach :=
  Quot.inductionOn s fun _l => List.mem_attach _

@[simp]
/--
theorem `card_attach` / 定理 `card_attach`

English:
theorem card_attach
  given: {m : Multiset α}
  statement: card (attach m) = card m
  proof: card_pmap _ _ _

中文:
定理 card_attach
  条件: {m : Multiset α}
  结论: card (attach m) = card m
  证明: card_pmap _ _ _

Depends on / 依赖: card_pmap
-/
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _

section Decidable

variable {m : Multiset α}

/--
Definition of `decidableForallMultiset` / `decidableForallMultiset` 的定义

English:
definition decidableForallMultiset
  signature: {p : α -> Prop} [forall a, Decidable (p a)]
  body: Quotient.recOnSubsingleton m fun l => decidable_of_iff (forall a in l, p a) by simp

中文:
定义 decidableForallMultiset
  签名: {p : α -> 命题} [对任意 a, 可判定 (p a)]
  定义体: Quotient.recOnSubsingleton m fun l => decidable_of_iff (forall a in l, p a) by simp
-/
protected def decidableForallMultiset {p : α -> Prop} [forall a, Decidable (p a)] :
    Decidable (forall a in m, p a) :=
Quotient.recOnSubsingleton m fun l => decidable_of_iff (forall a in l, p a) by simp

/--
Instance `decidableDforallMultiset` / 实例 `decidableDforallMultiset`

English:
instance decidableDforallMultiset
  signature: {p : forall a in m, Prop} [_hp : forall (a) (h : a in m), Decidable (p a h)]
  body: @decidable_of_iff _ _
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨_a, _ha⟩ _ => h _ _)
    (@Multiset.decidableForallMultiset _ m.attach (fun a => p a.1 a.2) _)

中文:
实例 decidableD对任意Multiset
  签名: {p : 对任意 a in m, 命题} [_hp : 对任意 (a) (h : a in m), 可判定 (p a h)]
  定义体: @decidable_of_iff _ _
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨_a, _ha⟩ _ => h _ _)
    (@Multiset.decidableForallMultiset _ m.attach (fun a => p a.1 a.2) _)

Depends on / 依赖: Iff.intro, Multiset, Multiset.decidableForallMultiset, attach, decidableForallMultiset, decidable_of_iff, m.attach, mem_attach
-/
instance decidableDforallMultiset {p : forall a in m, Prop} [_hp : forall (a) (h : a in m), Decidable (p a h)] :
    Decidable (forall (a) (h : a in m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨_a, _ha⟩ _ => h _ _)
    (@Multiset.decidableForallMultiset _ m.attach (fun a => p a.1 a.2) _)

/--
Instance `decidableEqPiMultiset` / 实例 `decidableEqPiMultiset`

English:
instance decidableEqPiMultiset
  signature: {β : α -> Type*} [forall a, DecidableEq (β a)]
  body: fun f g =>
  decidable_of_iff (forall (a) (h : a in m), f a h = g a h) (by simp [funext_iff])

中文:
实例 decidableEqPiMultiset
  签名: {β : α -> 类型} [对任意 a, DecidableEq (β a)]
  定义体: fun f g =>
  decidable_of_iff (forall (a) (h : a in m), f a h = g a h) (by simp [funext_iff])
-/
instance decidableEqPiMultiset {β : α -> Type*} [forall a, DecidableEq (β a)] :
    DecidableEq (forall a in m, β a) := fun f g =>
  decidable_of_iff (forall (a) (h : a in m), f a h = g a h) (by simp [funext_iff])

/--
Definition of `decidableExistsMultiset` / `decidableExistsMultiset` 的定义

English:
definition decidableExistsMultiset
  signature: {p : α -> Prop} [DecidablePred p]
  body: Quotient.recOnSubsingleton m fun l => decidable_of_iff (exists a in l, p a) by simp

中文:
定义 decidableExistsMultiset
  签名: {p : α -> 命题} [DecidablePred p]
  定义体: Quotient.recOnSubsingleton m fun l => decidable_of_iff (exists a in l, p a) by simp
-/
protected def decidableExistsMultiset {p : α -> Prop} [DecidablePred p] : Decidable (exists x in m, p x) :=
Quotient.recOnSubsingleton m fun l => decidable_of_iff (exists a in l, p a) by simp

/--
Instance `decidableDexistsMultiset` / 实例 `decidableDexistsMultiset`

English:
instance decidableDexistsMultiset
  signature: {p : forall a in m, Prop} [_hp : forall (a) (h : a in m), Decidable (p a h)]
  body: @decidable_of_iff _ _
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
    (@Multiset.decidableExistsMultiset { a // a in m } m.attach (fun a => p a.1 a.2) _)

中文:
实例 decidableD存在Multiset
  签名: {p : 对任意 a in m, 命题} [_hp : 对任意 (a) (h : a in m), 可判定 (p a h)]
  定义体: @decidable_of_iff _ _
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
    (@Multiset.decidableExistsMultiset { a // a in m } m.attach (fun a => p a.1 a.2) _)

Depends on / 依赖: Iff.intro, Multiset, Multiset.decidableExistsMultiset, attach, decidableExistsMultiset, decidable_of_iff, m.attach, mem_attach
-/
instance decidableDexistsMultiset {p : forall a in m, Prop} [_hp : forall (a) (h : a in m), Decidable (p a h)] :
    Decidable (exists (a : _) (h : a in m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
    (@Multiset.decidableExistsMultiset { a // a in m } m.attach (fun a => p a.1 a.2) _)

end Decidable

/--
Definition of `Pairwise` / `Pairwise` 的定义

English:
definition Pairwise
  signature: (r : α -> α -> Prop) (m : Multiset α)
  body: exists l : List α, m = l ∧ l.Pairwise r

中文:
定义 两两
  签名: (r : α -> α -> 命题) (m : Multiset α)
  定义体: exists l : List α, m = l ∧ l.Pairwise r

Depends on / 依赖: Pairwise, l.Pairwise
-/
def Pairwise (r : α -> α -> Prop) (m : Multiset α) : Prop :=
  exists l : List α, m = l ∧ l.Pairwise r

/--
theorem `pairwise_coe_iff` / 定理 `pairwise_coe_iff`

English:
theorem pairwise_coe_iff
  given: {r : α -> α -> Prop} {l : List α}
  proof: exists_congr by simp

中文:
定理 pairwise_coe_iff
  条件: {r : α -> α -> 命题} {l : 列表 α}
  证明: exists_congr by simp

Depends on / 依赖: exists_congr
-/
theorem pairwise_coe_iff {r : α -> α -> Prop} {l : List α} :
    Multiset.Pairwise r l ↔ exists l' : List α, l ~ l' ∧ l'.Pairwise r :=
exists_congr by simp

/--
theorem `pairwise_coe_iff_pairwise` / 定理 `pairwise_coe_iff_pairwise`

English:
theorem pairwise_coe_iff_pairwise
  given: {r : α -> α -> Prop} [Std.Symm r] {l : List α}
  proof: .mpr h, fun h => ⟨l, rfl, h⟩⟩ .pairwise_iff symm ⟨fun ⟨_l', Eq, h⟩ => Quotient.exact Eq

中文:
定理 pairwise_coe_iff_pairwise
  条件: {r : α -> α -> 命题} [Std.Symm r] {l : 列表 α}
  证明: .mpr h, fun h => ⟨l, rfl, h⟩⟩ .pairwise_iff symm ⟨fun ⟨_l', Eq, h⟩ => Quotient.exact Eq

Depends on / 依赖: Quotient, Quotient.exact, pairwise_iff
-/
theorem pairwise_coe_iff_pairwise {r : α -> α -> Prop} [Std.Symm r] {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
.mpr h, fun h => ⟨l, rfl, h⟩⟩ .pairwise_iff symm ⟨fun ⟨_l', Eq, h⟩ => Quotient.exact Eq

section Nodup

/--
Definition of `Nodup` / `Nodup` 的定义

English:
definition Nodup
  signature: (s : Multiset α)
  body: Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]

中文:
定义 Nodup
  签名: (s : Multiset α)
  定义体: Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]

Depends on / 依赖: List.Nodup, Quot.liftOn, liftOn, nodup_iff, p.nodup_iff, propext
-/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]
/--
theorem `coe_nodup` / 定理 `coe_nodup`

English:
theorem coe_nodup
  given: {l : List α}
  statement: @Nodup α l ↔ l.Nodup
  proof: Iff.rfl

中文:
定理 coe_nodup
  条件: {l : 列表 α}
  结论: @Nodup α l ↔ l.Nodup
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup :=
  Iff.rfl

/--
theorem `Nodup.ext` / 定理 `Nodup.ext`

English:
theorem Nodup.ext
  given: {s t : Multiset α}
  statement: Nodup s -> Nodup t -> (s = t ↔ forall a, a in s ↔ a in t)
  proof: Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans perm_ext_iff_of_nodup d₁ d₂

中文:
定理 Nodup.ext
  条件: {s t : Multiset α}
  结论: Nodup s -> Nodup t -> (s = t ↔ 对任意 a, a in s ↔ a in t)
  证明: Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans perm_ext_iff_of_nodup d₁ d₂

Depends on / 依赖: Quotient, Quotient.eq.trans, Quotient.inductionOn, perm_ext_iff_of_nodup
-/
theorem Nodup.ext {s t : Multiset α} : Nodup s -> Nodup t -> (s = t ↔ forall a, a in s ↔ a in t) :=
Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans perm_ext_iff_of_nodup d₁ d₂

/--
theorem `le_iff_subset` / 定理 `le_iff_subset`

English:
theorem le_iff_subset
  given: {s t : Multiset α}
  statement: Nodup s -> (s <= t ↔ s subseteq t)
  proof: Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩

中文:
定理 le_iff_subset
  条件: {s t : Multiset α}
  结论: Nodup s -> (s <= t ↔ s subseteq t)
  证明: Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩

Depends on / 依赖: Quotient, Quotient.inductionOn, d.subperm, subperm, subset_of_le
-/
theorem le_iff_subset {s t : Multiset α} : Nodup s -> (s <= t ↔ s subseteq t) :=
  Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩

/--
theorem `nodup_of_le` / 定理 `nodup_of_le`

English:
theorem nodup_of_le
  given: {s t : Multiset α} (h : s <= t)
  statement: Nodup t -> Nodup s
  proof: Multiset.leInductionOn h fun {_ _} => Nodup.sublist

中文:
定理 nodup_of_le
  条件: {s t : Multiset α} (h : s <= t)
  结论: Nodup t -> Nodup s
  证明: Multiset.leInductionOn h fun {_ _} => Nodup.sublist

Depends on / 依赖: Multiset, Multiset.leInductionOn, Nodup.sublist, leInductionOn, sublist
-/
theorem nodup_of_le {s t : Multiset α} (h : s <= t) : Nodup t -> Nodup s :=
  Multiset.leInductionOn h fun {_ _} => Nodup.sublist

/--
Instance `nodupDecidable` / 实例 `nodupDecidable`

English:
instance nodupDecidable
  signature: [DecidableEq α] (s : Multiset α)
  body: Quotient.recOnSubsingleton s fun l => l.nodupDecidable

中文:
实例 nodupDecidable
  签名: [DecidableEq α] (s : Multiset α)
  定义体: Quotient.recOnSubsingleton s fun l => l.nodupDecidable

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, l.nodupDecidable, nodupDecidable, recOnSubsingleton
-/
instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s) :=
  Quotient.recOnSubsingleton s fun l => l.nodupDecidable

end Nodup

section SizeOf

/-- Defines a size for a multiset by referring to the size of the underlying list.

This has to be defined before the definition of `Finset`, otherwise its automatically generated
`SizeOf` instance will be wrong.
-/
protected
/--
Definition of `sizeOf` / `sizeOf` 的定义

English:
definition sizeOf
  signature: [SizeOf α] (s : Multiset α)
  body: (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf

中文:
定义 sizeOf
  签名: [SizeOf α] (s : Multiset α)
  定义体: (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf

Depends on / 依赖: Perm.sizeOf_eq_sizeOf, Quot.liftOn, SizeOf, SizeOf.sizeOf, liftOn, sizeOf, sizeOf_eq_sizeOf
-/
def sizeOf [SizeOf α] (s : Multiset α) : Nat :=
  (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SizeOf
  signature: α] : SizeOf (Multiset α)
  body: ⟨Multiset.sizeOf⟩

中文:
实例 [SizeOf
  签名: α] : SizeOf (Multiset α)
  定义体: ⟨Multiset.sizeOf⟩

Depends on / 依赖: Multiset, Multiset.sizeOf, sizeOf
-/
instance [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeOf⟩

end SizeOf

end Multiset
