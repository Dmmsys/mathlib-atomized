/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.Coset.Defs

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`,
  or `s <• a` with `open scoped Pointwise RightActions`)

If instead `G` is an additive group, we can write (with `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a +ᵥ s` with `open AddOpposite`,
  or `s <+ᵥ a` with `open scoped Pointwise RightActions`)

## Main definitions

* `Subgroup.leftCosetEquivSubgroup`: the natural bijection between a left coset and the subgroup,
  for an `AddGroup` this is `AddSubgroup.leftCosetEquivAddSubgroup`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

@[expose] public section

assert_not_exists Cardinal Multiset

open Function MulOpposite Set
open scoped Pointwise

variable {α : Type*}

section CosetMul

variable [Mul α]

@[to_additive mem_leftAddCoset]
/--
theorem `mem_leftCoset` / 定理 `mem_leftCoset`

English:
theorem mem_leftCoset
  given: {s : Set α} {x : α} (a : α) (hxS : x in s)
  statement: a * x in a • s
  proof: mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_rightAddCoset]

中文:
定理 mem_leftCoset
  条件: {s : Set α} {x : α} (a : α) (hxS : x in s)
  结论: a * x in a • s
  证明: mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_rightAddCoset]

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) : a * x in a • s :=
  mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_rightAddCoset]
/--
theorem `mem_rightCoset` / 定理 `mem_rightCoset`

English:
theorem mem_rightCoset
  given: {s : Set α} {x : α} (a : α) (hxS : x in s)
  statement: x * a in op a • s
  proof: mem_image_of_mem (fun b : α => b * a) hxS

中文:
定理 mem_rightCoset
  条件: {s : Set α} {x : α} (a : α) (hxS : x in s)
  结论: x * a in op a • s
  证明: mem_image_of_mem (fun b : α => b * a) hxS

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x in s) : x * a in op a • s :=
  mem_image_of_mem (fun b : α => b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence /-- Equality of two left cosets `a + s` and `b + s`. -/]
/--
Definition of `LeftCosetEquivalence` / `LeftCosetEquivalence` 的定义

English:
definition LeftCosetEquivalence
  signature: (s : Set α) (a b : α)
  body: a • s = b • s

@[to_additive leftAddCosetEquivalence_rel]

中文:
定义 LeftCosetEquivalence
  签名: (s : Set α) (a b : α)
  定义体: a • s = b • s

@[to_additive leftAddCosetEquivalence_rel]
-/
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a • s = b • s

@[to_additive leftAddCosetEquivalence_rel]
/--
theorem `leftCosetEquivalence_rel` / 定理 `leftCosetEquivalence_rel`

English:
theorem leftCosetEquivalence_rel
  given: (s : Set α)
  statement: Equivalence (LeftCosetEquivalence s)
  proof: @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans

中文:
定理 leftCosetEquivalence_rel
  条件: (s : Set α)
  结论: Equivalence (LeftCosetEquivalence s)
  证明: @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans

Depends on / 依赖: Eq.symm, Eq.trans, Equivalence, Equivalence.mk, LeftCosetEquivalence
-/
theorem leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) :=
  @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence /-- Equality of two right cosets `s + a` and `s + b`. -/]
/--
Definition of `RightCosetEquivalence` / `RightCosetEquivalence` 的定义

English:
definition RightCosetEquivalence
  signature: (s : Set α) (a b : α)
  body: op a • s = op b • s

@[to_additive rightAddCosetEquivalence_rel]

中文:
定义 RightCosetEquivalence
  签名: (s : Set α) (a b : α)
  定义体: op a • s = op b • s

@[to_additive rightAddCosetEquivalence_rel]
-/
def RightCosetEquivalence (s : Set α) (a b : α) :=
  op a • s = op b • s

@[to_additive rightAddCosetEquivalence_rel]
/--
theorem `rightCosetEquivalence_rel` / 定理 `rightCosetEquivalence_rel`

English:
theorem rightCosetEquivalence_rel
  given: (s : Set α)
  statement: Equivalence (RightCosetEquivalence s)
  proof: @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans

中文:
定理 rightCosetEquivalence_rel
  条件: (s : Set α)
  结论: Equivalence (RightCosetEquivalence s)
  证明: @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans

Depends on / 依赖: Eq.symm, Eq.trans, Equivalence, Equivalence.mk, RightCosetEquivalence
-/
theorem rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) :=
  @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans

end CosetMul

section CosetSemigroup

variable [Semigroup α]

@[to_additive leftAddCoset_assoc]
/--
theorem `leftCoset_assoc` / 定理 `leftCoset_assoc`

English:
theorem leftCoset_assoc
  given: (s : Set α) (a b : α)
  statement: a • (b • s) = (a * b) • s
  proof: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive rightAddCoset_assoc]

中文:
定理 leftCoset_assoc
  条件: (s : Set α) (a b : α)
  结论: a • (b • s) = (a * b) • s
  证明: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive rightAddCoset_assoc]

Depends on / 依赖: Function, Function.comp, image_comp, image_smul, mul_assoc
-/
theorem leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive rightAddCoset_assoc]
/--
theorem `rightCoset_assoc` / 定理 `rightCoset_assoc`

English:
theorem rightCoset_assoc
  given: (s : Set α) (a b : α)
  statement: op b • op a • s = op (a * b) • s
  proof: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive leftAddCoset_rightAddCoset]

中文:
定理 rightCoset_assoc
  条件: (s : Set α) (a b : α)
  结论: op b • op a • s = op (a * b) • s
  证明: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive leftAddCoset_rightAddCoset]

Depends on / 依赖: Function, Function.comp, image_comp, image_smul, mul_assoc
-/
theorem rightCoset_assoc (s : Set α) (a b : α) : op b • op a • s = op (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive leftAddCoset_rightAddCoset]
/--
theorem `leftCoset_rightCoset` / 定理 `leftCoset_rightCoset`

English:
theorem leftCoset_rightCoset
  given: (s : Set α) (a b : α)
  statement: op b • a • s = a • (op b • s)
  proof: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

中文:
定理 leftCoset_rightCoset
  条件: (s : Set α) (a b : α)
  结论: op b • a • s = a • (op b • s)
  证明: by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

Depends on / 依赖: Function, Function.comp, image_comp, image_smul, mul_assoc
-/
theorem leftCoset_rightCoset (s : Set α) (a b : α) : op b • a • s = a • (op b • s) := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

end CosetSemigroup

section CosetMonoid

variable [Monoid α] (s : Set α)

@[to_additive zero_leftAddCoset]
/--
theorem `one_leftCoset` / 定理 `one_leftCoset`

English:
theorem one_leftCoset
  statement: (1 : α) • s = s
  proof: Set.ext by simp

@[to_additive rightAddCoset_zero]

中文:
定理 one_leftCoset
  结论: (1 : α) • s = s
  证明: Set.ext by simp

@[to_additive rightAddCoset_zero]

Depends on / 依赖: Set.ext
-/
theorem one_leftCoset : (1 : α) • s = s :=
Set.ext by simp

@[to_additive rightAddCoset_zero]
/--
theorem `rightCoset_one` / 定理 `rightCoset_one`

English:
theorem rightCoset_one
  statement: op (1 : α) • s = s
  proof: Set.ext by simp

中文:
定理 rightCoset_one
  结论: op (1 : α) • s = s
  证明: Set.ext by simp

Depends on / 依赖: Set.ext
-/
theorem rightCoset_one : op (1 : α) • s = s :=
Set.ext by simp

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoid α] (s : Submonoid α)

@[to_additive mem_own_leftAddCoset]
/--
theorem `mem_own_leftCoset` / 定理 `mem_own_leftCoset`

English:
theorem mem_own_leftCoset
  given: (a : α)
  statement: a in a • (s : Set α)
  proof: suffices a * 1 in a • (s : Set α) by simpa
  mem_leftCoset a (one_mem s : 1 in s)

@[to_additive mem_own_rightAddCoset]

中文:
定理 mem_own_leftCoset
  条件: (a : α)
  结论: a in a • (s : Set α)
  证明: suffices a * 1 in a • (s : Set α) by simpa
  mem_leftCoset a (one_mem s : 1 in s)

@[to_additive mem_own_rightAddCoset]

Depends on / 依赖: mem_leftCoset, one_mem
-/
theorem mem_own_leftCoset (a : α) : a in a • (s : Set α) :=
  suffices a * 1 in a • (s : Set α) by simpa
  mem_leftCoset a (one_mem s : 1 in s)

@[to_additive mem_own_rightAddCoset]
/--
theorem `mem_own_rightCoset` / 定理 `mem_own_rightCoset`

English:
theorem mem_own_rightCoset
  given: (a : α)
  statement: a in op a • (s : Set α)
  proof: suffices 1 * a in op a • (s : Set α) by simpa
  mem_rightCoset a (one_mem s : 1 in s)

@[to_additive mem_leftAddCoset_leftAddCoset]

中文:
定理 mem_own_rightCoset
  条件: (a : α)
  结论: a in op a • (s : Set α)
  证明: suffices 1 * a in op a • (s : Set α) by simpa
  mem_rightCoset a (one_mem s : 1 in s)

@[to_additive mem_leftAddCoset_leftAddCoset]

Depends on / 依赖: mem_rightCoset, one_mem
-/
theorem mem_own_rightCoset (a : α) : a in op a • (s : Set α) :=
  suffices 1 * a in op a • (s : Set α) by simpa
  mem_rightCoset a (one_mem s : 1 in s)

@[to_additive mem_leftAddCoset_leftAddCoset]
/--
theorem `mem_leftCoset_leftCoset` / 定理 `mem_leftCoset_leftCoset`

English:
theorem mem_leftCoset_leftCoset
  given: {a : α} (ha : a • (s : Set α) = s)
  statement: a in s
  proof: by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_leftCoset s a

@[to_additive mem_rightAddCoset_rightAddCoset]

中文:
定理 mem_leftCoset_leftCoset
  条件: {a : α} (ha : a • (s : Set α) = s)
  结论: a in s
  证明: by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_leftCoset s a

@[to_additive mem_rightAddCoset_rightAddCoset]

Depends on / 依赖: SetLike, SetLike.mem_coe, mem_coe, mem_own_leftCoset
-/
theorem mem_leftCoset_leftCoset {a : α} (ha : a • (s : Set α) = s) : a in s := by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_leftCoset s a

@[to_additive mem_rightAddCoset_rightAddCoset]
/--
theorem `mem_rightCoset_rightCoset` / 定理 `mem_rightCoset_rightCoset`

English:
theorem mem_rightCoset_rightCoset
  given: {a : α} (ha : op a • (s : Set α) = s)
  statement: a in s
  proof: by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_rightCoset s a

中文:
定理 mem_rightCoset_rightCoset
  条件: {a : α} (ha : op a • (s : Set α) = s)
  结论: a in s
  证明: by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_rightCoset s a

Depends on / 依赖: SetLike, SetLike.mem_coe, mem_coe, mem_own_rightCoset
-/
theorem mem_rightCoset_rightCoset {a : α} (ha : op a • (s : Set α) = s) : a in s := by
  rw [← SetLike.mem_coe]; rw [← ha]; exact mem_own_rightCoset s a

end CosetSubmonoid

section CosetGroup

variable [Group α] {s : Set α} {x : α}

@[to_additive mem_leftAddCoset_iff]
/--
theorem `mem_leftCoset_iff` / 定理 `mem_leftCoset_iff`

English:
theorem mem_leftCoset_iff
  given: (a : α)
  statement: x in a • s ↔ a⁻¹ * x in s
  proof: Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩

@[to_additive mem_rightAddCoset_iff]

中文:
定理 mem_leftCoset_iff
  条件: (a : α)
  结论: x in a • s ↔ a⁻¹ * x in s
  证明: Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩

@[to_additive mem_rightAddCoset_iff]

Depends on / 依赖: Iff.intro, h.symm
-/
theorem mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s :=
  Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩

@[to_additive mem_rightAddCoset_iff]
/--
theorem `mem_rightCoset_iff` / 定理 `mem_rightCoset_iff`

English:
theorem mem_rightCoset_iff
  given: (a : α)
  statement: x in op a • s ↔ x * a⁻¹ in s
  proof: Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩

中文:
定理 mem_rightCoset_iff
  条件: (a : α)
  结论: x in op a • s ↔ x * a⁻¹ in s
  证明: Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩

Depends on / 依赖: Iff.intro, h.symm
-/
theorem mem_rightCoset_iff (a : α) : x in op a • s ↔ x * a⁻¹ in s :=
  Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Group α] (s : Subgroup α)

@[to_additive leftAddCoset_mem_leftAddCoset]
/--
theorem `leftCoset_mem_leftCoset` / 定理 `leftCoset_mem_leftCoset`

English:
theorem leftCoset_mem_leftCoset
  given: {a : α} (ha : a in s)
  statement: a • (s : Set α) = s
  proof: Set.ext by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive rightAddCoset_mem_rightAddCoset]

中文:
定理 leftCoset_mem_leftCoset
  条件: {a : α} (ha : a in s)
  结论: a • (s : Set α) = s
  证明: Set.ext by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive rightAddCoset_mem_rightAddCoset]

Depends on / 依赖: Set.ext, inv_mem, mem_leftCoset_iff, mul_mem_cancel_left, s.inv_mem
-/
theorem leftCoset_mem_leftCoset {a : α} (ha : a in s) : a • (s : Set α) = s :=
Set.ext by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive rightAddCoset_mem_rightAddCoset]
/--
theorem `rightCoset_mem_rightCoset` / 定理 `rightCoset_mem_rightCoset`

English:
theorem rightCoset_mem_rightCoset
  given: {a : α} (ha : a in s)
  statement: op a • (s : Set α) = s
  proof: Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive]

中文:
定理 rightCoset_mem_rightCoset
  条件: {a : α} (ha : a in s)
  结论: op a • (s : Set α) = s
  证明: Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive]

Depends on / 依赖: Set.ext, inv_mem, mem_rightCoset_iff, mul_mem_cancel_right, s.inv_mem
-/
theorem rightCoset_mem_rightCoset {a : α} (ha : a in s) : op a • (s : Set α) = s :=
  Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive]
/--
theorem `orbit_subgroup_eq_rightCoset` / 定理 `orbit_subgroup_eq_rightCoset`

English:
theorem orbit_subgroup_eq_rightCoset
  given: (a : α)
  statement: MulAction.orbit s a = op a • s
  proof: Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩

@[to_additive]

中文:
定理 orbit_subgroup_eq_rightCoset
  条件: (a : α)
  结论: MulAction.orbit s a = op a • s
  证明: Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩

@[to_additive]

Depends on / 依赖: Set.ext
-/
theorem orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = op a • s :=
  Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩

@[to_additive]
/--
theorem `orbit_subgroup_eq_self_of_mem` / 定理 `orbit_subgroup_eq_self_of_mem`

English:
theorem orbit_subgroup_eq_self_of_mem
  given: {a : α} (ha : a in s)
  statement: MulAction.orbit s a = s
  proof: (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)

@[to_additive]

中文:
定理 orbit_subgroup_eq_self_of_mem
  条件: {a : α} (ha : a in s)
  结论: MulAction.orbit s a = s
  证明: (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)

@[to_additive]

Depends on / 依赖: orbit_subgroup_eq_rightCoset, rightCoset_mem_rightCoset
-/
theorem orbit_subgroup_eq_self_of_mem {a : α} (ha : a in s) : MulAction.orbit s a = s :=
  (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)

@[to_additive]
/--
theorem `orbit_subgroup_one_eq_self` / 定理 `orbit_subgroup_one_eq_self`

English:
theorem orbit_subgroup_one_eq_self
  statement: MulAction.orbit s (1 : α) = s
  proof: orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_addCosets_of_normal]

中文:
定理 orbit_subgroup_one_eq_self
  结论: MulAction.orbit s (1 : α) = s
  证明: orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_addCosets_of_normal]

Depends on / 依赖: one_mem, orbit_subgroup_eq_self_of_mem, s.one_mem
-/
theorem orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s :=
  orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_addCosets_of_normal]
/--
theorem `eq_cosets_of_normal` / 定理 `eq_cosets_of_normal`

English:
theorem eq_cosets_of_normal
  given: (N : s.Normal) (g : α)
  statement: g • (s : Set α) = op g • s
  proof: Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff, N.mem_comm_iff]

@[to_additive normal_of_eq_addCosets]

中文:
定理 eq_cosets_of_normal
  条件: (N : s.Normal) (g : α)
  结论: g • (s : Set α) = op g • s
  证明: Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff, N.mem_comm_iff]

@[to_additive normal_of_eq_addCosets]

Depends on / 依赖: N.mem_comm_iff, Set.ext, mem_comm_iff, mem_leftCoset_iff, mem_rightCoset_iff
-/
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g • (s : Set α) = op g • s :=
  Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff, N.mem_comm_iff]

@[to_additive normal_of_eq_addCosets]
/--
theorem `normal_of_eq_cosets` / 定理 `normal_of_eq_cosets`

English:
theorem normal_of_eq_cosets
  given: (h : forall g : α, g • (s : Set α) = op g • s)
  statement: s.Normal
  proof: ⟨fun a ha g =>
    show g * a * g⁻¹ in (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩

@[to_additive normal_iff_eq_addCosets]

中文:
定理 normal_of_eq_cosets
  条件: (h : 对任意 g : α, g • (s : Set α) = op g • s)
  结论: s.Normal
  证明: ⟨fun a ha g =>
    show g * a * g⁻¹ in (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩

@[to_additive normal_iff_eq_addCosets]

Depends on / 依赖: mem_leftCoset, mem_rightCoset_iff
-/
theorem normal_of_eq_cosets (h : forall g : α, g • (s : Set α) = op g • s) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ in (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩

@[to_additive normal_iff_eq_addCosets]
/--
theorem `normal_iff_eq_cosets` / 定理 `normal_iff_eq_cosets`

English:
theorem normal_iff_eq_cosets
  statement: s.Normal ↔ forall g : α, g • (s : Set α) = op g • s
  proof: ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive leftAddCoset_eq_iff]

中文:
定理 normal_iff_eq_cosets
  结论: s.Normal ↔ 对任意 g : α, g • (s : Set α) = op g • s
  证明: ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive leftAddCoset_eq_iff]

Depends on / 依赖: eq_cosets_of_normal, normal_of_eq_cosets
-/
theorem normal_iff_eq_cosets : s.Normal ↔ forall g : α, g • (s : Set α) = op g • s :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive leftAddCoset_eq_iff]
/--
theorem `leftCoset_eq_iff` / 定理 `leftCoset_eq_iff`

English:
theorem leftCoset_eq_iff
  given: {x y : α}
  statement: x • (s : Set α) = y • s ↔ x⁻¹ * y in s
  proof: by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [inv_mul_cancel]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h

@[to_additive rightAddCoset_eq_iff]

中文:
定理 leftCoset_eq_iff
  条件: {x y : α}
  结论: x • (s : Set α) = y • s ↔ x⁻¹ * y in s
  证明: by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [inv_mul_cancel]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h

@[to_additive rightAddCoset_eq_iff]

Depends on / 依赖: Set.ext_iff, SetLike, SetLike.mem_coe, ext_iff, inv_mul_cancel, mem_coe, mem_leftCoset_iff, mul_assoc, mul_inv_cancel_right, mul_mem_cancel_left, one_mem, s.mul_mem_cancel_left, s.one_mem, simp_rw
-/
theorem leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔ x⁻¹ * y in s := by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [inv_mul_cancel]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h

@[to_additive rightAddCoset_eq_iff]
/--
theorem `rightCoset_eq_iff` / 定理 `rightCoset_eq_iff`

English:
theorem rightCoset_eq_iff
  given: {x y : α}
  statement: op x • (s : Set α) = op y • s ↔ y * x⁻¹ in s
  proof: by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_inv_cancel]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h

中文:
定理 rightCoset_eq_iff
  条件: {x y : α}
  结论: op x • (s : Set α) = op y • s ↔ y * x⁻¹ in s
  证明: by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_inv_cancel]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h

Depends on / 依赖: Set.ext_iff, SetLike, SetLike.mem_coe, ext_iff, inv_mul_cancel_left, mem_coe, mem_rightCoset_iff, mul_assoc, mul_inv_cancel, mul_mem_cancel_right, one_mem, s.mul_mem_cancel_right, s.one_mem, simp_rw
-/
theorem rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op y • s ↔ y * x⁻¹ in s := by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_inv_cancel]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h

end CosetSubgroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/--
theorem `leftRel_r_eq_leftCosetEquivalence` / 定理 `leftRel_r_eq_leftCosetEquivalence`

English:
theorem leftRel_r_eq_leftCosetEquivalence
  proof: by
  ext
  rw [leftRel_eq]
  exact (leftCoset_eq_iff s).symm

@[to_additive leftRel_prod]

中文:
定理 leftRel_r_eq_leftCosetEquivalence
  证明: by
  ext
  rw [leftRel_eq]
  exact (leftCoset_eq_iff s).symm

@[to_additive leftRel_prod]

Depends on / 依赖: leftCoset_eq_iff, leftRel_eq
-/
theorem leftRel_r_eq_leftCosetEquivalence :
    ⇑(QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  rw [leftRel_eq]
  exact (leftCoset_eq_iff s).symm

@[to_additive leftRel_prod]
/--
lemma `leftRel_prod` / 引理 `leftRel_prod`

English:
lemma leftRel_prod
  given: {β : Type*} [Group β] (s' : Subgroup β)
  proof: by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]

中文:
引理 leftRel_prod
  条件: {β : 类型} [Group β] (s' : Subgroup β)
  证明: by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]

Depends on / 依赖: Setoid, Setoid.ext, Setoid.prod_apply, leftRel_apply, prod_apply, simp_rw
-/
lemma leftRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    leftRel (s.prod s') = (leftRel s).prod (leftRel s') := by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]
/--
lemma `leftRel_pi` / 引理 `leftRel_pi`

English:
lemma leftRel_pi
  given: {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : forall i, Subgroup (β i))
  proof: by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]

中文:
引理 leftRel_pi
  条件: {ι : 类型} {β : ι -> 类型} [对任意 i, Group (β i)] (s' : 对任意 i, Subgroup (β i))
  证明: by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]

Depends on / 依赖: Decidable, Setoid, Setoid.ext, Setoid.piSetoid_apply, Subgroup, Subgroup.mem_pi, leftRel_apply, mem_pi, piSetoid_apply
-/
lemma leftRel_pi {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : forall i, Subgroup (β i)) :
    leftRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i => leftRel (s' i) := by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]

/--
theorem `rightRel_r_eq_rightCosetEquivalence` / 定理 `rightRel_r_eq_rightCosetEquivalence`

English:
theorem rightRel_r_eq_rightCosetEquivalence
  proof: by
  ext
  rw [rightRel_eq]
  exact (rightCoset_eq_iff s).symm

@[to_additive rightRel_prod]

中文:
定理 rightRel_r_eq_rightCosetEquivalence
  证明: by
  ext
  rw [rightRel_eq]
  exact (rightCoset_eq_iff s).symm

@[to_additive rightRel_prod]

Depends on / 依赖: rightCoset_eq_iff, rightRel_eq
-/
theorem rightRel_r_eq_rightCosetEquivalence :
    ⇑(QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  rw [rightRel_eq]
  exact (rightCoset_eq_iff s).symm

@[to_additive rightRel_prod]
/--
lemma `rightRel_prod` / 引理 `rightRel_prod`

English:
lemma rightRel_prod
  given: {β : Type*} [Group β] (s' : Subgroup β)
  proof: by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]

中文:
引理 rightRel_prod
  条件: {β : 类型} [Group β] (s' : Subgroup β)
  证明: by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]

Depends on / 依赖: Setoid, Setoid.ext, Setoid.prod_apply, prod_apply, rightRel_apply, simp_rw
-/
lemma rightRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    rightRel (s.prod s') = (rightRel s).prod (rightRel s') := by
  refine Setoid.ext fun x y => ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]
/--
lemma `rightRel_pi` / 引理 `rightRel_pi`

English:
lemma rightRel_pi
  given: {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : forall i, Subgroup (β i))
  proof: by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

中文:
引理 rightRel_pi
  条件: {ι : 类型} {β : ι -> 类型} [对任意 i, Group (β i)] (s' : 对任意 i, Subgroup (β i))
  证明: by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

Depends on / 依赖: Setoid, Setoid.ext, Setoid.piSetoid_apply, Subgroup, Subgroup.mem_pi, mem_pi, piSetoid_apply, rightRel_apply
-/
lemma rightRel_pi {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : forall i, Subgroup (β i)) :
    rightRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i => rightRel (s' i) := by
  refine Setoid.ext fun x y => ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

variable (s)

/-- Given a subgroup `s`, the function that sends a subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s` is strictly monotone, even though
it is not injective in general. -/
@[to_additive QuotientAddGroup.strictMono_comap_prod_image /-- Given an additive subgroup `s`,
the function that sends an additive subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s`
is strictly monotone, even though it is not injective in general. -/]
/--
theorem `strictMono_comap_prod_image` / 定理 `strictMono_comap_prod_image`

English:
theorem strictMono_comap_prod_image
  proof: by
  refine fun t₁ t₂ h => ⟨⟨Subgroup.comap_mono h.1, Set.image_mono h.1⟩,
    mt (fun ⟨le1, le2⟩ a ha => ?_) h.2⟩
  obtain ⟨a', h', eq⟩ := le2 ⟨_, ha, rfl⟩
  convert t₁.mul_mem h' (@le1 ⟨_, QuotientGroup.eq.1 eq⟩ <| t₂.mul_mem (t₂.inv_mem <| h.1 h') ha)
  simp

中文:
定理 strictMono_comap_prod_image
  证明: by
  refine fun t₁ t₂ h => ⟨⟨Subgroup.comap_mono h.1, Set.image_mono h.1⟩,
    mt (fun ⟨le1, le2⟩ a ha => ?_) h.2⟩
  obtain ⟨a', h', eq⟩ := le2 ⟨_, ha, rfl⟩
  convert t₁.mul_mem h' (@le1 ⟨_, QuotientGroup.eq.1 eq⟩ <| t₂.mul_mem (t₂.inv_mem <| h.1 h') ha)
  simp

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, Set.image_mono, Subgroup, Subgroup.comap_mono, comap_mono, convert, image_mono, inv_mem, mul_mem
-/
theorem strictMono_comap_prod_image :
    StrictMono fun t : Subgroup α => (t.comap s.subtype, mk (s := s) '' t) := by
  refine fun t₁ t₂ h => ⟨⟨Subgroup.comap_mono h.1, Set.image_mono h.1⟩,
    mt (fun ⟨le1, le2⟩ a ha => ?_) h.2⟩
  obtain ⟨a', h', eq⟩ := le2 ⟨_, ha, rfl⟩
  convert t₁.mul_mem h' (@le1 ⟨_, QuotientGroup.eq.1 eq⟩ <| t₂.mul_mem (t₂.inv_mem <| h.1 h') ha)
  simp

variable {s} {a b : α}

@[to_additive]
/--
theorem `eq_class_eq_leftCoset` / 定理 `eq_class_eq_leftCoset`

English:
theorem eq_class_eq_leftCoset
  given: (s : Subgroup α) (g : α)
  proof: Set.ext fun z => by
    rw [mem_leftCoset_iff]; rw [Set.mem_ofPred_eq]; rw [eq_comm]; rw [QuotientGroup.eq]; rw [SetLike.mem_coe]

中文:
定理 eq_class_eq_leftCoset
  条件: (s : Subgroup α) (g : α)
  证明: Set.ext fun z => by
    rw [mem_leftCoset_iff]; rw [Set.mem_ofPred_eq]; rw [eq_comm]; rw [QuotientGroup.eq]; rw [SetLike.mem_coe]

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, Set.ext, Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, eq_comm, mem_coe, mem_leftCoset_iff, mem_ofPred_eq
-/
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    { x : α | (x : α ⧸ s) = g } = g • s :=
  Set.ext fun z => by
    rw [mem_leftCoset_iff]; rw [Set.mem_ofPred_eq]; rw [eq_comm]; rw [QuotientGroup.eq]; rw [SetLike.mem_coe]

open MulAction in
@[to_additive]
/--
lemma `orbit_mk_eq_smul` / 引理 `orbit_mk_eq_smul`

English:
lemma orbit_mk_eq_smul
  given: (x : α)
  statement: MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) = x • s
  proof: by
  ext
  rw [orbitRel.Quotient.mem_orbit]
  simpa [mem_smul_set_iff_inv_smul_mem, ← leftRel_apply, Quotient.eq''] using Setoid.comm' _

@[to_additive]

中文:
引理 orbit_mk_eq_smul
  条件: (x : α)
  结论: MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) = x • s
  证明: by
  ext
  rw [orbitRel.Quotient.mem_orbit]
  simpa [mem_smul_set_iff_inv_smul_mem, ← leftRel_apply, Quotient.eq''] using Setoid.comm' _

@[to_additive]

Depends on / 依赖: Quotient, Quotient.eq, Setoid, Setoid.comm, leftRel_apply, mem_orbit, mem_smul_set_iff_inv_smul_mem, orbitRel, orbitRel.Quotient.mem_orbit
-/
lemma orbit_mk_eq_smul (x : α) : MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) = x • s := by
  ext
  rw [orbitRel.Quotient.mem_orbit]
  simpa [mem_smul_set_iff_inv_smul_mem, ← leftRel_apply, Quotient.eq''] using Setoid.comm' _

@[to_additive]
/--
lemma `orbit_eq_out_smul` / 引理 `orbit_eq_out_smul`

English:
lemma orbit_eq_out_smul
  given: (x : α ⧸ s)
  statement: MulAction.orbitRel.Quotient.orbit x = x.out • s
  proof: by
  induction x using QuotientGroup.induction_on
  simp only [orbit_mk_eq_smul, ← eq_class_eq_leftCoset, Quotient.out_eq']

中文:
引理 orbit_eq_out_smul
  条件: (x : α ⧸ s)
  结论: MulAction.orbitRel.Quotient.orbit x = x.out • s
  证明: by
  induction x using QuotientGroup.induction_on
  simp only [orbit_mk_eq_smul, ← eq_class_eq_leftCoset, Quotient.out_eq']

Depends on / 依赖: Quotient, Quotient.out_eq, QuotientGroup, QuotientGroup.induction_on, eq_class_eq_leftCoset, induction_on, orbit_mk_eq_smul, out_eq
-/
lemma orbit_eq_out_smul (x : α ⧸ s) : MulAction.orbitRel.Quotient.orbit x = x.out • s := by
  induction x using QuotientGroup.induction_on
  simp only [orbit_mk_eq_smul, ← eq_class_eq_leftCoset, Quotient.out_eq']

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `g + s` and `s`. -/]
/--
Definition of `leftCosetEquivSubgroup` / `leftCosetEquivSubgroup` 的定义

English:
definition leftCosetEquivSubgroup
  signature: (g : α)
  body: ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

中文:
定义 leftCosetEquivSubgroup
  签名: (g : α)
  定义体: ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_leftCoset_iff
-/
def leftCosetEquivSubgroup (g : α) : (g • s : Set α) ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `s + g` and `s`. -/]
/--
Definition of `rightCosetEquivSubgroup` / `rightCosetEquivSubgroup` 的定义

English:
definition rightCosetEquivSubgroup
  signature: (g : α)
  body: ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

中文:
定义 rightCosetEquivSubgroup
  签名: (g : α)
  定义体: ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_rightCoset_iff
-/
def rightCosetEquivSubgroup (g : α) : (op g • s : Set α) ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
fun ⟨x, _⟩ => Subtype.ext by simp, fun ⟨g, _⟩ => Subtype.ext by simp⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive addGroupEquivQuotientProdAddSubgroup
  /-- A (non-canonical) bijection between an `AddGroup` `α` and the product `(α/s) × s` -/]
/--
Definition of `groupEquivQuotientProdSubgroup` / `groupEquivQuotientProdSubgroup` 的定义

English:
definition groupEquivQuotientProdSubgroup
  signature: : α ≃ (α ⧸ s) × s
  body: calc
    α ≃ Σ L : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ Σ L : α ⧸ s, (Quotient.out L • s : Set α) :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        change
          (_root_.Subtype fun x : α => Quotient.mk'

中文:
定义 groupEquivQuotientProdSubgroup
  签名: : α ≃ (α ⧸ s) × s
  定义体: calc
    α ≃ Σ L : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ Σ L : α ⧸ s, (Quotient.out L • s : Set α) :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        change
          (_root_.Subtype fun x : α => Quotient.mk'

Depends on / 依赖: Equiv.sigmaCongrRight, Equiv.sigmaEquivProd, Equiv.sigmaFiberEquiv, Quotient, Quotient.mk, Quotient.out, QuotientGroup, QuotientGroup.mk, Subtype, _root_, _root_.Subtype, eq_class_eq_leftCoset, leftCosetEquivSubgroup, sigmaCongrRight, sigmaEquivProd, sigmaFiberEquiv
-/
noncomputable def groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ Σ L : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ Σ L : α ⧸ s, (Quotient.out L • s : Set α) :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        change
          (_root_.Subtype fun x : α => Quotient.mk'' x = L) ≃
            _root_.Subtype fun x : α => Quotient.mk'' x = Quotient.mk'' _
        simp
        rfl
    _ ≃ Σ _L : α ⧸ s, s := Equiv.sigmaCongrRight fun _ => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equiv.sigmaEquivProd _ _

variable {t : Subgroup α}

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `Subgroup.quotientEquivProdOfLE`. -/
@[to_additive (attr := simps) quotientEquivProdOfLE'
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
  of the quotient map `G → G/K`. The classical version is `AddSubgroup.quotientEquivProdOfLE`. -/]
/--
Definition of `quotientEquivProdOfLE'` / `quotientEquivProdOfLE'` 的定义

English:
definition quotientEquivProdOfLE'
  signature: (h_le : s <= t) (f : α ⧸ t -> α)
  body: ⟨a.map' id fun _ _ h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) in s
        have key : f b = 

中文:
定义 quotientEquivProdOfLE'
  签名: (h_le : s <= t) (f : α ⧸ t -> α)
  定义体: ⟨a.map' id fun _ _ h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) in s
        have key : f b = 

Depends on / 依赖: Quotient, Quotient.exact, Quotient.mk, Quotient.sound, a.map, congr_arg, h_le, invFun, inv_inv, leftRel_apply, leftRel_apply.mp, leftRel_apply.mpr, mul_assoc, mul_inv_cancel_left, mul_inv_rev
-/
def quotientEquivProdOfLE' (h_le : s <= t) (f : α ⧸ t -> α)
    (hf : Function.RightInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t where
  toFun a :=
    ⟨a.map' id fun _ _ h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) in s
        have key : f b = f c :=
          congr_arg f (Quotient.sound' (leftRel_apply.mpr (h_le (leftRel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← leftRel_apply]⟩
  invFun a := by
    refine a.2.map' (fun (b : { x // x in t}) => f a.1 * b) fun b c h => by
      rw [leftRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  left_inv := by
    refine Quotient.ind' fun a => ?_
    simp_rw [Quotient.map'_mk'', id, mul_inv_cancel_left]
  right_inv := by
    refine Prod.rec ?_
    refine Quotient.ind' fun a => ?_
    refine Quotient.ind' fun b => ?_
    have key : Quotient.mk'' (f (Quotient.mk'' a) * b) = Quotient.mk'' a :=
      (QuotientGroup.mk_mul_of_mem (f a) b.2).trans (hf a)
    simp_rw [Quotient.map'_mk'', id, key, inv_mul_cancel_left]

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotientEquivProdOfLE'`. -/
@[to_additive (attr := simps!) quotientEquivProdOfLE
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively. The
constructive version is `quotientEquivProdOfLE'`. -/]
/--
Definition of `quotientEquivProdOfLE` / `quotientEquivProdOfLE` 的定义

English:
definition quotientEquivProdOfLE
  signature: (h_le : s <= t)
  body: quotientEquivProdOfLE' h_le Quotient.out Quotient.out_eq'

中文:
定义 quotientEquivProdOfLE
  签名: (h_le : s <= t)
  定义体: quotientEquivProdOfLE' h_le Quotient.out Quotient.out_eq'

Depends on / 依赖: Quotient, Quotient.out, Quotient.out_eq, h_le, out_eq, quotientEquivProdOfLE
-/
noncomputable def quotientEquivProdOfLE (h_le : s <= t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLE' h_le Quotient.out Quotient.out_eq'

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t`. -/
@[to_additive
/-- If `s ≤ t`, there is an embedding `s ⧸ H.addSubgroupOf s ↪ t ⧸ H.addSubgroupOf t`. -/]
/--
Definition of `quotientSubgroupOfEmbeddingOfLE` / `quotientSubgroupOfEmbeddingOfLE` 的定义

English:
definition quotientSubgroupOfEmbeddingOfLE
  signature: (H : Subgroup α) (h : s <= t)
  body: Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      exact id
  inj' :=
Quotient.ind₂' by
      intro a b h
      simpa only [Quotient.map'_mk'', QuotientGroup.eq] using! h

@[to_additive (attr := simp)]

中文:
定义 quotientSubgroupOfEmbeddingOfLE
  签名: (H : Subgroup α) (h : s <= t)
  定义体: Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      exact id
  inj' :=
Quotient.ind₂' by
      intro a b h
      simpa only [Quotient.map'_mk'', QuotientGroup.eq] using! h

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.ind, Quotient.map, QuotientGroup, QuotientGroup.eq, inclusion, leftRel_eq, simp_rw
-/
def quotientSubgroupOfEmbeddingOfLE (H : Subgroup α) (h : s <= t) :
    s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t where
  toFun :=
    Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      exact id
  inj' :=
Quotient.ind₂' by
      intro a b h
      simpa only [Quotient.map'_mk'', QuotientGroup.eq] using! h

@[to_additive (attr := simp)]
/--
theorem `quotientSubgroupOfEmbeddingOfLE_apply_mk` / 定理 `quotientSubgroupOfEmbeddingOfLE_apply_mk`

English:
theorem quotientSubgroupOfEmbeddingOfLE_apply_mk
  given: (H : Subgroup α) (h : s <= t) (g : s)
  proof: rfl

中文:
定理 quotientSubgroupOfEmbeddingOfLE_apply_mk
  条件: (H : Subgroup α) (h : s <= t) (g : s)
  证明: rfl
-/
theorem quotientSubgroupOfEmbeddingOfLE_apply_mk (H : Subgroup α) (h : s <= t) (g : s) :
    quotientSubgroupOfEmbeddingOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk (inclusion h g) :=
  rfl

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H`. -/
@[to_additive
/-- If `s ≤ t`, then there is a map `H ⧸ s.addSubgroupOf H → H ⧸ t.addSubgroupOf H`. -/]
/--
Definition of `quotientSubgroupOfMapOfLE` / `quotientSubgroupOfMapOfLE` 的定义

English:
definition quotientSubgroupOfMapOfLE
  signature: (H : Subgroup α) (h : s <= t)
  body: Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]

中文:
定义 quotientSubgroupOfMapOfLE
  签名: (H : Subgroup α) (h : s <= t)
  定义体: Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.map, leftRel_eq, simp_rw
-/
def quotientSubgroupOfMapOfLE (H : Subgroup α) (h : s <= t) :
    H ⧸ s.subgroupOf H -> H ⧸ t.subgroupOf H :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
/--
theorem `quotientSubgroupOfMapOfLE_apply_mk` / 定理 `quotientSubgroupOfMapOfLE_apply_mk`

English:
theorem quotientSubgroupOfMapOfLE_apply_mk
  given: (H : Subgroup α) (h : s <= t) (g : H)
  proof: rfl

中文:
定理 quotientSubgroupOfMapOfLE_apply_mk
  条件: (H : Subgroup α) (h : s <= t) (g : H)
  证明: rfl
-/
theorem quotientSubgroupOfMapOfLE_apply_mk (H : Subgroup α) (h : s <= t) (g : H) :
    quotientSubgroupOfMapOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive /-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/]
/--
Definition of `quotientMapOfLE` / `quotientMapOfLE` 的定义

English:
definition quotientMapOfLE
  signature: (h : s <= t)
  body: Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]

中文:
定义 quotientMapOfLE
  签名: (h : s <= t)
  定义体: Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.map, leftRel_eq, simp_rw
-/
def quotientMapOfLE (h : s <= t) : α ⧸ s -> α ⧸ t :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
/--
theorem `quotientMapOfLE_apply_mk` / 定理 `quotientMapOfLE_apply_mk`

English:
theorem quotientMapOfLE_apply_mk
  given: (h : s <= t) (g : α)
  proof: rfl

中文:
定理 quotientMapOfLE_apply_mk
  条件: (h : s <= t) (g : α)
  证明: rfl
-/
theorem quotientMapOfLE_apply_mk (h : s <= t) (g : α) :
    quotientMapOfLE h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroupOf H ↪ Π i, H ⧸ (f i).subgroupOf H`. -/
@[to_additive (attr := simps) /-- The natural embedding
`H ⧸ (⨅ i, f i).addSubgroupOf H) ↪ Π i, H ⧸ (f i).addSubgroupOf H`. -/]
/--
Definition of `quotientiInfSubgroupOfEmbedding` / `quotientiInfSubgroupOfEmbedding` 的定义

English:
definition quotientiInfSubgroupOfEmbedding
  signature: {ι : Type*} (f : ι -> Subgroup α) (H : Subgroup α)
  body: quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf,
        mem_iInf, imp_self, forall_const]

@[to_additive (attr := simp)]

中文:
定义 quotientiInfSubgroupOfEmbedding
  签名: {ι : 类型} (f : ι -> Subgroup α) (H : Subgroup α)
  定义体: quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf,
        mem_iInf, imp_self, forall_const]

@[to_additive (attr := simp)]

Depends on / 依赖: iInf_le, quotientSubgroupOfMapOfLE
-/
def quotientiInfSubgroupOfEmbedding {ι : Type*} (f : ι -> Subgroup α) (H : Subgroup α) :
    H ⧸ (⨅ i, f i).subgroupOf H ↪ forall i, H ⧸ (f i).subgroupOf H where
  toFun q i := quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf,
        mem_iInf, imp_self, forall_const]

@[to_additive (attr := simp)]
/--
theorem `quotientiInfSubgroupOfEmbedding_apply_mk` / 定理 `quotientiInfSubgroupOfEmbedding_apply_mk`

English:
theorem quotientiInfSubgroupOfEmbedding_apply_mk
  statement: {ι : Type*} (f : ι -> Subgroup α) (H : Subgroup α)
  proof: rfl

中文:
定理 quotientiInfSubgroupOfEmbedding_apply_mk
  结论: {ι : 类型} (f : ι -> Subgroup α) (H : Subgroup α)
  证明: rfl
-/
theorem quotientiInfSubgroupOfEmbedding_apply_mk {ι : Type*} (f : ι -> Subgroup α) (H : Subgroup α)
    (g : H) (i : ι) :
    quotientiInfSubgroupOfEmbedding f H (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive (attr := simps) /-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/]
/--
Definition of `quotientiInfEmbedding` / `quotientiInfEmbedding` 的定义

English:
definition quotientiInfEmbedding
  signature: {ι : Type*} (f : ι -> Subgroup α)
  body: quotientMapOfLE (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, QuotientGroup.eq, mem_iInf, imp_self,
        forall_const]

@[to_additive (attr := simp)]

中文:
定义 quotientiInfEmbedding
  签名: {ι : 类型} (f : ι -> Subgroup α)
  定义体: quotientMapOfLE (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, QuotientGroup.eq, mem_iInf, imp_self,
        forall_const]

@[to_additive (attr := simp)]

Depends on / 依赖: iInf_le, quotientMapOfLE
-/
def quotientiInfEmbedding {ι : Type*} (f : ι -> Subgroup α) : (α ⧸ ⨅ i, f i) ↪ forall i, α ⧸ f i where
  toFun q i := quotientMapOfLE (iInf_le f i) q
  inj' :=
Quotient.ind₂' by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, QuotientGroup.eq, mem_iInf, imp_self,
        forall_const]

@[to_additive (attr := simp)]
/--
theorem `quotientiInfEmbedding_apply_mk` / 定理 `quotientiInfEmbedding_apply_mk`

English:
theorem quotientiInfEmbedding_apply_mk
  given: {ι : Type*} (f : ι -> Subgroup α) (g : α) (i : ι)
  proof: rfl

中文:
定理 quotientiInfEmbedding_apply_mk
  条件: {ι : 类型} (f : ι -> Subgroup α) (g : α) (i : ι)
  证明: rfl
-/
theorem quotientiInfEmbedding_apply_mk {ι : Type*} (f : ι -> Subgroup α) (g : α) (i : ι) :
    quotientiInfEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

end Subgroup

namespace MonoidHom

variable [Group α] {H : Type*} [Group H]

/-- An equivalence between any non-empty fiber of a `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any non-empty fiber of an `AddMonoidHom` and its kernel. -/]
/--
Definition of `fiberEquivKer` / `fiberEquivKer` 的定义

English:
definition fiberEquivKer
  signature: (f : α ->* H) (a : α)
  body: .trans
    (Equiv.setCongr <| Set.ext fun _ => by
      rw [mem_preimage]; rw [mem_singleton_iff]; rw [mem_smul_set_iff_inv_smul_mem]; rw [SetLike.mem_coe]; rw [mem_ker]; rw [smul_eq_mul]; rw [map_mul]; rw [map_inv]; rw [inv_mul_eq_one]; rw [eq_comm])
    (Subgroup.leftCosetEquivSubgroup a)

@[to_ad

中文:
定义 fiberEquivKer
  签名: (f : α ->* H) (a : α)
  定义体: .trans
    (Equiv.setCongr <| Set.ext fun _ => by
      rw [mem_preimage]; rw [mem_singleton_iff]; rw [mem_smul_set_iff_inv_smul_mem]; rw [SetLike.mem_coe]; rw [mem_ker]; rw [smul_eq_mul]; rw [map_mul]; rw [map_inv]; rw [inv_mul_eq_one]; rw [eq_comm])
    (Subgroup.leftCosetEquivSubgroup a)

@[to_ad

Depends on / 依赖: Equiv.setCongr, Set.ext, SetLike, SetLike.mem_coe, Subgroup, Subgroup.leftCosetEquivSubgroup, eq_comm, inv_mul_eq_one, leftCosetEquivSubgroup, map_inv, map_mul, mem_coe, mem_ker, mem_preimage, mem_singleton_iff, mem_smul_set_iff_inv_smul_mem, setCongr, smul_eq_mul
-/
def fiberEquivKer (f : α ->* H) (a : α) : f ⁻¹' {f a} ≃ f.ker :=
  .trans
    (Equiv.setCongr <| Set.ext fun _ => by
      rw [mem_preimage]; rw [mem_singleton_iff]; rw [mem_smul_set_iff_inv_smul_mem]; rw [SetLike.mem_coe]; rw [mem_ker]; rw [smul_eq_mul]; rw [map_mul]; rw [map_inv]; rw [inv_mul_eq_one]; rw [eq_comm])
    (Subgroup.leftCosetEquivSubgroup a)

@[to_additive (attr := simp)]
/--
lemma `fiberEquivKer_apply` / 引理 `fiberEquivKer_apply`

English:
lemma fiberEquivKer_apply
  given: (f : α ->* H) (a : α) (g : f ⁻¹' {f a})
  statement: f.fiberEquivKer a g = a⁻¹ * g
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 fiberEquivKer_apply
  条件: (f : α ->* H) (a : α) (g : f ⁻¹' {f a})
  结论: f.fiberEquivKer a g = a⁻¹ * g
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma fiberEquivKer_apply (f : α ->* H) (a : α) (g : f ⁻¹' {f a}) : f.fiberEquivKer a g = a⁻¹ * g :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `fiberEquivKer_symm_apply` / 引理 `fiberEquivKer_symm_apply`

English:
lemma fiberEquivKer_symm_apply
  given: (f : α ->* H) (a : α) (g : f.ker)
  proof: rfl

中文:
引理 fiberEquivKer_symm_apply
  条件: (f : α ->* H) (a : α) (g : f.ker)
  证明: rfl
-/
lemma fiberEquivKer_symm_apply (f : α ->* H) (a : α) (g : f.ker) :
    (f.fiberEquivKer a).symm g = a * g :=
  rfl

/-- An equivalence between any fiber of a surjective `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any fiber of a surjective `AddMonoidHom` and its kernel. -/]
/--
Definition of `fiberEquivKerOfSurjective` / `fiberEquivKerOfSurjective` 的定义

English:
definition fiberEquivKerOfSurjective
  signature: {f : α ->* H} (hf : Function.Surjective f) (h : H)
  body: (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

中文:
定义 fiberEquivKerOfSurjective
  签名: {f : α ->* H} (hf : Function.Surjective f) (h : H)
  定义体: (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

Depends on / 依赖: choose_spec, f.fiberEquivKer, fiberEquivKer
-/
noncomputable def fiberEquivKerOfSurjective {f : α ->* H} (hf : Function.Surjective f) (h : H) :
    f ⁻¹' {h} ≃ f.ker :=
  (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

/-- An equivalence between any two non-empty fibers of a `MonoidHom`. -/
@[to_additive /-- An equivalence between any two non-empty fibers of an `AddMonoidHom`. -/]
/--
Definition of `fiberEquiv` / `fiberEquiv` 的定义

English:
definition fiberEquiv
  signature: (f : α ->* H) (a b : α)
  body: (f.fiberEquivKer a).trans (f.fiberEquivKer b).symm

@[to_additive (attr := simp)]

中文:
定义 fiberEquiv
  签名: (f : α ->* H) (a b : α)
  定义体: (f.fiberEquivKer a).trans (f.fiberEquivKer b).symm

@[to_additive (attr := simp)]

Depends on / 依赖: f.fiberEquivKer, fiberEquivKer
-/
def fiberEquiv (f : α ->* H) (a b : α) : f ⁻¹' {f a} ≃ f ⁻¹' {f b} :=
  (f.fiberEquivKer a).trans (f.fiberEquivKer b).symm

@[to_additive (attr := simp)]
/--
lemma `fiberEquiv_apply` / 引理 `fiberEquiv_apply`

English:
lemma fiberEquiv_apply
  given: (f : α ->* H) (a b : α) (g : f ⁻¹' {f a})
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 fiberEquiv_apply
  条件: (f : α ->* H) (a b : α) (g : f ⁻¹' {f a})
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma fiberEquiv_apply (f : α ->* H) (a b : α) (g : f ⁻¹' {f a}) :
    f.fiberEquiv a b g = b * (a⁻¹ * g) :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `fiberEquiv_symm_apply` / 引理 `fiberEquiv_symm_apply`

English:
lemma fiberEquiv_symm_apply
  given: (f : α ->* H) (a b : α) (g : f ⁻¹' {f b})
  proof: rfl

中文:
引理 fiberEquiv_symm_apply
  条件: (f : α ->* H) (a b : α) (g : f ⁻¹' {f b})
  证明: rfl
-/
lemma fiberEquiv_symm_apply (f : α ->* H) (a b : α) (g : f ⁻¹' {f b}) :
    (f.fiberEquiv a b).symm g = a * (b⁻¹ * g) :=
  rfl

/-- An equivalence between any two fibers of a surjective `MonoidHom`. -/
@[to_additive /-- An equivalence between any two fibers of a surjective `AddMonoidHom`. -/]
/--
Definition of `fiberEquivOfSurjective` / `fiberEquivOfSurjective` 的定义

English:
definition fiberEquivOfSurjective
  signature: {f : α ->* H} (hf : Function.Surjective f) (h h' : H)
  body: (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

中文:
定义 fiberEquivOfSurjective
  签名: {f : α ->* H} (hf : Function.Surjective f) (h h' : H)
  定义体: (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

Depends on / 依赖: fiberEquivKerOfSurjective
-/
noncomputable def fiberEquivOfSurjective {f : α ->* H} (hf : Function.Surjective f) (h h' : H) :
    f ⁻¹' {h} ≃ f ⁻¹' {h'} :=
  (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

end MonoidHom

namespace QuotientGroup

variable [Group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive preimageMkEquivAddSubgroupProdSet
/-- If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product
`s × t`. -/]
/--
Definition of `preimageMkEquivSubgroupProdSet` / `preimageMkEquivSubgroupProdSet` 的定义

English:
definition preimageMkEquivSubgroupProdSet
  signature: (s : Subgroup α) (t : Set (α ⧸ s))
  body: ⟨⟨((Quotient.out (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out a.2.1 * a.1.1,
      show QuotientGroup.mk _ in t by
        rw [mk_mul_of_mem _ a.1.2]; rw [out_e

中文:
定义 preimageMkEquivSubgroupProdSet
  签名: (s : Subgroup α) (t : Set (α ⧸ s))
  定义体: ⟨⟨((Quotient.out (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out a.2.1 * a.1.1,
      show QuotientGroup.mk _ in t by
        rw [mk_mul_of_mem _ a.1.2]; rw [out_e

Depends on / 依赖: Quotient, Quotient.exact, Quotient.out, Quotient.out_eq, QuotientGroup, QuotientGroup.mk, Subtype, Subtype.ext, invFun, leftRel, leftRel_apply, leftRel_apply.mp, left_inv, mk_mul_of_mem, out_eq, right_inv
-/
noncomputable def preimageMkEquivSubgroupProdSet (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t where
  toFun a :=
    ⟨⟨((Quotient.out (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out a.2.1 * a.1.1,
      show QuotientGroup.mk _ in t by
        rw [mk_mul_of_mem _ a.1.2]; rw [out_eq']
        exact a.2.2⟩
left_inv := fun ⟨a, _⟩ => Subtype.ext show _ * _ = a by simp
  right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ => by ext <;> simp [ha]

open MulAction in
/-- A group is made up of a disjoint union of cosets of a subgroup. -/
@[to_additive /-- An additive group is made up of a disjoint union of cosets of an additive
subgroup. -/]
/--
lemma `univ_eq_iUnion_smul` / 引理 `univ_eq_iUnion_smul`

English:
lemma univ_eq_iUnion_smul
  given: (H : Subgroup α)
  proof: by
  simp_rw [univ_eq_iUnion_orbit H.op, orbit_eq_out_smul]
  rfl

中文:
引理 univ_eq_iUnion_smul
  条件: (H : Subgroup α)
  证明: by
  simp_rw [univ_eq_iUnion_orbit H.op, orbit_eq_out_smul]
  rfl

Depends on / 依赖: H.op, orbit_eq_out_smul, simp_rw, univ_eq_iUnion_orbit, x.out
-/
lemma univ_eq_iUnion_smul (H : Subgroup α) :
    (Set.univ (α := α)) = ⋃ x : α ⧸ H, x.out • (H : Set _) := by
  simp_rw [univ_eq_iUnion_orbit H.op, orbit_eq_out_smul]
  rfl

variable (α) in
/-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientGroup.quotientBot` for a multiplicative
version. -/
@[to_additive /-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientAddGroup.quotientBot` for an
additive version. -/]
/--
Definition of `quotientEquivSelf` / `quotientEquivSelf` 的定义

English:
definition quotientEquivSelf
  signature: : α ⧸ (⊥ : Subgroup α) ≃ α where
  body: Quotient.lift id fun x y (h : leftRel ⊥ x y) =>
eq_of_inv_mul_eq_one by rwa [leftRel_apply, Subgroup.mem_bot] at h
  invFun := QuotientGroup.mk
  left_inv x := by induction x using Quotient.inductionOn; simp
  right_inv x := by simp

中文:
定义 quotientEquivSelf
  签名: : α ⧸ (⊥ : Subgroup α) ≃ α where
  定义体: Quotient.lift id fun x y (h : leftRel ⊥ x y) =>
eq_of_inv_mul_eq_one by rwa [leftRel_apply, Subgroup.mem_bot] at h
  invFun := QuotientGroup.mk
  left_inv x := by induction x using Quotient.inductionOn; simp
  right_inv x := by simp

Depends on / 依赖: Quotient, Quotient.lift, leftRel
-/
def quotientEquivSelf : α ⧸ (⊥ : Subgroup α) ≃ α where
toFun := Quotient.lift id fun x y (h : leftRel ⊥ x y) =>
eq_of_inv_mul_eq_one by rwa [leftRel_apply, Subgroup.mem_bot] at h
  invFun := QuotientGroup.mk
  left_inv x := by induction x using Quotient.inductionOn; simp
  right_inv x := by simp

end QuotientGroup
