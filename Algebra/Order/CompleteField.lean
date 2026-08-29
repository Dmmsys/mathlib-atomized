/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Hom
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an isomorphism
preserving these properties to the reals.
This is `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`.
Moreover this isomorphism is unique.

We show all conditionally complete linear ordered fields are
archimedean. We also construct the natural map from a linearly ordered field to such a field.

## Main definitions

* `ConditionallyCompleteLinearOrderedField.inducedMap`: A (unique) map from any archimedean linear
  ordered field to a conditionally complete linear ordered field. Various bundlings are available.

## Main results

* `ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom` : Uniqueness of `OrderRingHom`s
  from an archimedean linear ordered field to a conditionally complete linear ordered field.
* `ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso` : Uniqueness of `OrderRingIso`s
  between two conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

@[expose] public section

variable {F α β γ : Type*}

noncomputable section

open Function Rat Set

open scoped Pointwise

/-- A field which is both linearly ordered and conditionally complete with respect to the order.
This axiomatizes the reals. -/
@[deprecated "Use `[Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2026-02-23")]
/--
Definition of `ConditionallyCompleteLinearOrderedField` / `ConditionallyCompleteLinearOrderedField` 的定义

English:
structure ConditionallyCompleteLinearOrderedField
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 余nditionallyCompleteLinearOrderedField
  参数: (α : 类型)
  (无附加公理)

Depends on / 依赖: ConditionallyCompleteLinearOrderedField, ConditionallyCompleteLinearOrderedField.to_archimedean, to_archimedean
-/
structure ConditionallyCompleteLinearOrderedField (α : Type*) extends
    Field α, ConditionallyCompleteLinearOrder α, IsStrictOrderedRing α where

-- see Note [lower instance priority]
/-- Any conditionally complete linearly ordered field is archimedean. -/
scoped instance (priority := 100) ConditionallyCompleteLinearOrderedField.to_archimedean
    [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α] : Archimedean α :=
archimedean_iff_nat_lt.2 by
    by_contra! ⟨x, h⟩
    have := csSup_le (range_nonempty Nat.cast)
      (forall_mem_range.2 fun m =>
le_sub_iff_add_le.2 le_csSup ⟨x, forall_mem_range.2 h⟩ ⟨m+1, Nat.cast_succ m⟩)
    linarith

namespace LinearOrderedField

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `LinearOrderedField.cutMap β : α → Set β` which sends `a : α` to the
"rationals in `β`" that are less than `a`.
-/


section CutMap

variable [Field α] [LinearOrder α]

section DivisionRing

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : Rat}

/--
Definition of `cutMap` / `cutMap` 的定义

English:
definition cutMap
  signature: (a : α)
  body: (Rat.cast : Rat -> β) '' {t | ↑t < a}

中文:
定义 cutMap
  签名: (a : α)
  定义体: (Rat.cast : Rat -> β) '' {t | ↑t < a}

Depends on / 依赖: Rat.cast
-/
def cutMap (a : α) : Set β :=
  (Rat.cast : Rat -> β) '' {t | ↑t < a}

/--
theorem `cutMap_mono` / 定理 `cutMap_mono`

English:
theorem cutMap_mono
  given: (h : a₁ <= a₂)
  statement: cutMap β a₁ subseteq cutMap β a₂
  proof: image_mono fun _ => h.trans_lt'

中文:
定理 cutMap_mono
  条件: (h : a₁ <= a₂)
  结论: cutMap β a₁ subseteq cutMap β a₂
  证明: image_mono fun _ => h.trans_lt'

Depends on / 依赖: h.trans_lt, image_mono, trans_lt
-/
theorem cutMap_mono (h : a₁ <= a₂) : cutMap β a₁ subseteq cutMap β a₂ := image_mono fun _ => h.trans_lt'

variable {β}

@[simp]
/--
theorem `mem_cutMap_iff` / 定理 `mem_cutMap_iff`

English:
theorem mem_cutMap_iff
  statement: b in cutMap β a ↔ exists q : Rat, (q : α) < a ∧ (q : β) = b
  proof: Iff.rfl

中文:
定理 mem_cutMap_iff
  结论: b in cutMap β a ↔ 存在 q : 有理数, (q : α) < a ∧ (q : β) = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cutMap_iff : b in cutMap β a ↔ exists q : Rat, (q : α) < a ∧ (q : β) = b := Iff.rfl

/--
theorem `coe_mem_cutMap_iff` / 定理 `coe_mem_cutMap_iff`

English:
theorem coe_mem_cutMap_iff
  given: [CharZero β]
  statement: (q : β) in cutMap β a ↔ (q : α) < a
  proof: Rat.cast_injective.mem_set_image

中文:
定理 coe_mem_cutMap_iff
  条件: [特征零 β]
  结论: (q : β) in cutMap β a ↔ (q : α) < a
  证明: Rat.cast_injective.mem_set_image

Depends on / 依赖: Rat.cast_injective.mem_set_image, cast_injective, mem_set_image
-/
theorem coe_mem_cutMap_iff [CharZero β] : (q : β) in cutMap β a ↔ (q : α) < a :=
  Rat.cast_injective.mem_set_image

/--
theorem `cutMap_self` / 定理 `cutMap_self`

English:
theorem cutMap_self
  given: (a : α)
  statement: cutMap α a = Iio a inter range (Rat.cast : Rat -> α)
  proof: by
  grind [mem_cutMap_iff]

中文:
定理 cutMap_self
  条件: (a : α)
  结论: cutMap α a = 左无界右开区间 a inter range (有理数.cast : 有理数 -> α)
  证明: by
  grind [mem_cutMap_iff]

Depends on / 依赖: mem_cutMap_iff
-/
theorem cutMap_self (a : α) : cutMap α a = Iio a inter range (Rat.cast : Rat -> α) := by
  grind [mem_cutMap_iff]

end DivisionRing

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : Rat}

/--
theorem `cutMap_coe` / 定理 `cutMap_coe`

English:
theorem cutMap_coe
  given: (q : Rat)
  statement: cutMap β (q : α) = Rat.cast '' {r : Rat | (r : β) < q}
  proof: by
  simp_rw [cutMap, Rat.cast_lt]

中文:
定理 cutMap_coe
  条件: (q : 有理数)
  结论: cutMap β (q : α) = 有理数.cast '' {r : 有理数 | (r : β) < q}
  证明: by
  simp_rw [cutMap, Rat.cast_lt]

Depends on / 依赖: Rat.cast_lt, cast_lt, cutMap, simp_rw
-/
theorem cutMap_coe (q : Rat) : cutMap β (q : α) = Rat.cast '' {r : Rat | (r : β) < q} := by
  simp_rw [cutMap, Rat.cast_lt]

variable [Archimedean α]

omit [LinearOrder β] [IsStrictOrderedRing β] in
/--
theorem `cutMap_nonempty` / 定理 `cutMap_nonempty`

English:
theorem cutMap_nonempty
  given: (a : α)
  statement: (cutMap β a).Nonempty
  proof: Nonempty.image _ exists_rat_lt a

中文:
定理 cutMap_nonempty
  条件: (a : α)
  结论: (cutMap β a).非空
  证明: Nonempty.image _ exists_rat_lt a

Depends on / 依赖: Nonempty, Nonempty.image, exists_rat_lt
-/
theorem cutMap_nonempty (a : α) : (cutMap β a).Nonempty :=
Nonempty.image _ exists_rat_lt a

/--
theorem `cutMap_bddAbove` / 定理 `cutMap_bddAbove`

English:
theorem cutMap_bddAbove
  given: (a : α)
  statement: BddAbove (cutMap β a)
  proof: by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩

中文:
定理 cutMap_bddAbove
  条件: (a : α)
  结论: BddAbove (cutMap β a)
  证明: by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩

Depends on / 依赖: exists_rat_gt, forall_mem_image, hq.trans, mod_cast
-/
theorem cutMap_bddAbove (a : α) : BddAbove (cutMap β a) := by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩

/--
theorem `cutMap_add` / 定理 `cutMap_add`

English:
theorem cutMap_add
  given: (a b : α)
  statement: cutMap β (a + b) = cutMap β a + cutMap β b
  proof: by
  refine (image_subset_iff.2 fun q hq => ?_).antisymm ?_
  · rw [mem_ofPred_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine ⟨q₁, by rwa [coe_mem_cutMap_iff], q - q₁, ?_, add_sub_cancel _ _⟩
    norm_cast
    rw [coe_mem_cutMap_iff]
    exact mod_cast sub_lt_comm.mp hq₁q
  · rintro _ ⟨_, ⟨qa, ha, rfl⟩, _, ⟨qb, hb, rfl⟩, rfl⟩
    -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
    refine ⟨qa + qb, ?_, by beta_reduce; norm_cast⟩
    rw [mem_ofPred_eq]; rw [cast_add]
    exact add_lt_add ha hb

中文:
定理 cutMap_add
  条件: (a b : α)
  结论: cutMap β (a + b) = cutMap β a + cutMap β b
  证明: by
  refine (image_subset_iff.2 fun q hq => ?_).antisymm ?_
  · rw [mem_ofPred_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine ⟨q₁, by rwa [coe_mem_cutMap_iff], q - q₁, ?_, add_sub_cancel _ _⟩
    norm_cast
    rw [coe_mem_cutMap_iff]
    exact mod_cast sub_lt_comm.mp hq₁q
  · rintro _ ⟨_, ⟨qa, ha, rfl⟩, _, ⟨qb, hb, rfl⟩, rfl⟩
    -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
    refine ⟨qa + qb, ?_, by beta_reduce; norm_cast⟩
    rw [mem_ofPred_eq]; rw [cast_add]
    exact add_lt_add ha hb

Depends on / 依赖: add_sub_cancel, antisymm, coe_mem_cutMap_iff, exists_rat_btwn, image_subset_iff, mem_ofPred_eq, mod_cast, sub_lt_comm, sub_lt_comm.mp, sub_lt_iff_lt_add
-/
theorem cutMap_add (a b : α) : cutMap β (a + b) = cutMap β a + cutMap β b := by
  refine (image_subset_iff.2 fun q hq => ?_).antisymm ?_
  · rw [mem_ofPred_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine ⟨q₁, by rwa [coe_mem_cutMap_iff], q - q₁, ?_, add_sub_cancel _ _⟩
    norm_cast
    rw [coe_mem_cutMap_iff]
    exact mod_cast sub_lt_comm.mp hq₁q
  · rintro _ ⟨_, ⟨qa, ha, rfl⟩, _, ⟨qb, hb, rfl⟩, rfl⟩
    -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
    refine ⟨qa + qb, ?_, by beta_reduce; norm_cast⟩
    rw [mem_ofPred_eq]; rw [cast_add]
    exact add_lt_add ha hb

end CutMap

end LinearOrderedField

namespace ConditionallyCompleteLinearOrderedField

open LinearOrderedField

/-!
### Induced map

`LinearOrderedField.cutMap` spits out a `Set β`. To get something in `β`, we now take the supremum.
-/


section InducedMap

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

/--
Definition of `inducedMap` / `inducedMap` 的定义

English:
definition inducedMap
  signature: (x : α)
  body: sSup cutMap β x

中文:
定义 inducedMap
  签名: (x : α)
  定义体: sSup cutMap β x

Depends on / 依赖: cutMap
-/
def inducedMap (x : α) : β :=
sSup cutMap β x

variable [Archimedean α]

/--
theorem `inducedMap_mono` / 定理 `inducedMap_mono`

English:
theorem inducedMap_mono
  statement: Monotone (inducedMap α β)
  proof: fun _ _ h =>
  csSup_le_csSup (cutMap_bddAbove β _) (cutMap_nonempty β _) (cutMap_mono β h)

中文:
定理 inducedMap_mono
  结论: 递增 (inducedMap α β)
  证明: fun _ _ h =>
  csSup_le_csSup (cutMap_bddAbove β _) (cutMap_nonempty β _) (cutMap_mono β h)
-/
theorem inducedMap_mono : Monotone (inducedMap α β) := fun _ _ h =>
  csSup_le_csSup (cutMap_bddAbove β _) (cutMap_nonempty β _) (cutMap_mono β h)

/--
theorem `inducedMap_rat` / 定理 `inducedMap_rat`

English:
theorem inducedMap_rat
  given: (q : Rat)
  statement: inducedMap α β (q : α) = q
  proof: by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (cutMap_nonempty β (q : α)) (fun x h => ?_) fun w h => ?_
  · rw [cutMap_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_lt h
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [cutMap_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩

@[simp]

中文:
定理 inducedMap_rat
  条件: (q : 有理数)
  结论: inducedMap α β (q : α) = q
  证明: by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (cutMap_nonempty β (q : α)) (fun x h => ?_) fun w h => ?_
  · rw [cutMap_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_lt h
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [cutMap_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩

@[simp]

Depends on / 依赖: csSup_eq_of_forall_le_of_forall_lt_exists_gt, cutMap_coe, cutMap_nonempty, exists_rat_btwn, le_of_lt
-/
theorem inducedMap_rat (q : Rat) : inducedMap α β (q : α) = q := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (cutMap_nonempty β (q : α)) (fun x h => ?_) fun w h => ?_
  · rw [cutMap_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_lt h
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [cutMap_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩

@[simp]
/--
theorem `inducedMap_zero` / 定理 `inducedMap_zero`

English:
theorem inducedMap_zero
  statement: inducedMap α β 0 = 0
  proof: mod_cast inducedMap_rat α β 0

@[simp]

中文:
定理 inducedMap_zero
  结论: inducedMap α β 0 = 0
  证明: mod_cast inducedMap_rat α β 0

@[simp]

Depends on / 依赖: inducedMap_rat, mod_cast
-/
theorem inducedMap_zero : inducedMap α β 0 = 0 := mod_cast inducedMap_rat α β 0

@[simp]
/--
theorem `inducedMap_one` / 定理 `inducedMap_one`

English:
theorem inducedMap_one
  statement: inducedMap α β 1 = 1
  proof: mod_cast inducedMap_rat α β 1

中文:
定理 inducedMap_one
  结论: inducedMap α β 1 = 1
  证明: mod_cast inducedMap_rat α β 1

Depends on / 依赖: inducedMap_rat, mod_cast
-/
theorem inducedMap_one : inducedMap α β 1 = 1 := mod_cast inducedMap_rat α β 1

variable {α β} {a : α} {b : β} {q : Rat}

/--
theorem `inducedMap_nonneg` / 定理 `inducedMap_nonneg`

English:
theorem inducedMap_nonneg
  given: (ha : 0 <= a)
  statement: 0 <= inducedMap α β a
  proof: (inducedMap_zero α _).ge.trans inducedMap_mono _ _ ha

中文:
定理 inducedMap_nonneg
  条件: (ha : 0 <= a)
  结论: 0 <= inducedMap α β a
  证明: (inducedMap_zero α _).ge.trans inducedMap_mono _ _ ha

Depends on / 依赖: ge.trans, inducedMap_mono, inducedMap_zero
-/
theorem inducedMap_nonneg (ha : 0 <= a) : 0 <= inducedMap α β a :=
(inducedMap_zero α _).ge.trans inducedMap_mono _ _ ha

/--
theorem `coe_lt_inducedMap_iff` / 定理 `coe_lt_inducedMap_iff`

English:
theorem coe_lt_inducedMap_iff
  statement: (q : β) < inducedMap α β a ↔ (q : α) < a
  proof: by
  refine ⟨fun h => ?_, fun hq => ?_⟩
  · rw [← inducedMap_rat α] at h
    exact (inducedMap_mono α β).reflect_lt h
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_csSup_of_lt (cutMap_bddAbove β a) (coe_mem_cutMap_iff.mpr hqa)
    exact mod_cast hq

中文:
定理 coe_lt_inducedMap_iff
  结论: (q : β) < inducedMap α β a ↔ (q : α) < a
  证明: by
  refine ⟨fun h => ?_, fun hq => ?_⟩
  · rw [← inducedMap_rat α] at h
    exact (inducedMap_mono α β).reflect_lt h
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_csSup_of_lt (cutMap_bddAbove β a) (coe_mem_cutMap_iff.mpr hqa)
    exact mod_cast hq

Depends on / 依赖: coe_mem_cutMap_iff, coe_mem_cutMap_iff.mpr, cutMap_bddAbove, exists_rat_btwn, inducedMap_mono, inducedMap_rat, lt_csSup_of_lt, mod_cast, reflect_lt
-/
theorem coe_lt_inducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a := by
  refine ⟨fun h => ?_, fun hq => ?_⟩
  · rw [← inducedMap_rat α] at h
    exact (inducedMap_mono α β).reflect_lt h
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_csSup_of_lt (cutMap_bddAbove β a) (coe_mem_cutMap_iff.mpr hqa)
    exact mod_cast hq

/--
theorem `lt_inducedMap_iff` / 定理 `lt_inducedMap_iff`

English:
theorem lt_inducedMap_iff
  statement: b < inducedMap α β a ↔ exists q : Rat, b < q ∧ (q : α) < a
  proof: ⟨fun h => (exists_rat_btwn h).imp fun _ => And.imp_right coe_lt_inducedMap_iff.1,
fun ⟨q, hbq, hqa⟩ => hbq.trans by rwa [coe_lt_inducedMap_iff]⟩

@[simp]

中文:
定理 lt_inducedMap_iff
  结论: b < inducedMap α β a ↔ 存在 q : 有理数, b < q ∧ (q : α) < a
  证明: ⟨fun h => (exists_rat_btwn h).imp fun _ => And.imp_right coe_lt_inducedMap_iff.1,
fun ⟨q, hbq, hqa⟩ => hbq.trans by rwa [coe_lt_inducedMap_iff]⟩

@[simp]

Depends on / 依赖: And.imp_right, coe_lt_inducedMap_iff, exists_rat_btwn, hbq.trans, imp_right
-/
theorem lt_inducedMap_iff : b < inducedMap α β a ↔ exists q : Rat, b < q ∧ (q : α) < a :=
  ⟨fun h => (exists_rat_btwn h).imp fun _ => And.imp_right coe_lt_inducedMap_iff.1,
fun ⟨q, hbq, hqa⟩ => hbq.trans by rwa [coe_lt_inducedMap_iff]⟩

@[simp]
/--
theorem `inducedMap_self` / 定理 `inducedMap_self`

English:
theorem inducedMap_self
  given: (b : β)
  statement: inducedMap β β b = b
  proof: eq_of_forall_rat_lt_iff_lt fun _ => coe_lt_inducedMap_iff

中文:
定理 inducedMap_self
  条件: (b : β)
  结论: inducedMap β β b = b
  证明: eq_of_forall_rat_lt_iff_lt fun _ => coe_lt_inducedMap_iff

Depends on / 依赖: coe_lt_inducedMap_iff, eq_of_forall_rat_lt_iff_lt
-/
theorem inducedMap_self (b : β) : inducedMap β β b = b :=
  eq_of_forall_rat_lt_iff_lt fun _ => coe_lt_inducedMap_iff

variable (α β)

@[simp]
/--
theorem `inducedMap_inducedMap` / 定理 `inducedMap_inducedMap`

English:
theorem inducedMap_inducedMap
  given: (a : α)
  statement: inducedMap β γ (inducedMap α β a) = inducedMap α γ a
  proof: eq_of_forall_rat_lt_iff_lt fun q => by
    rw [coe_lt_inducedMap_iff]; rw [coe_lt_inducedMap_iff]; rw [Iff.comm]; rw [coe_lt_inducedMap_iff]

中文:
定理 inducedMap_inducedMap
  条件: (a : α)
  结论: inducedMap β γ (inducedMap α β a) = inducedMap α γ a
  证明: eq_of_forall_rat_lt_iff_lt fun q => by
    rw [coe_lt_inducedMap_iff]; rw [coe_lt_inducedMap_iff]; rw [Iff.comm]; rw [coe_lt_inducedMap_iff]

Depends on / 依赖: Iff.comm, coe_lt_inducedMap_iff, eq_of_forall_rat_lt_iff_lt
-/
theorem inducedMap_inducedMap (a : α) : inducedMap β γ (inducedMap α β a) = inducedMap α γ a :=
  eq_of_forall_rat_lt_iff_lt fun q => by
    rw [coe_lt_inducedMap_iff]; rw [coe_lt_inducedMap_iff]; rw [Iff.comm]; rw [coe_lt_inducedMap_iff]

/--
theorem `inducedMap_inv_self` / 定理 `inducedMap_inv_self`

English:
theorem inducedMap_inv_self
  given: (b : β)
  statement: inducedMap γ β (inducedMap β γ b) = b
  proof: by
  rw [inducedMap_inducedMap]; rw [inducedMap_self]

中文:
定理 inducedMap_inv_self
  条件: (b : β)
  结论: inducedMap γ β (inducedMap β γ b) = b
  证明: by
  rw [inducedMap_inducedMap]; rw [inducedMap_self]

Depends on / 依赖: inducedMap_inducedMap, inducedMap_self
-/
theorem inducedMap_inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b := by
  rw [inducedMap_inducedMap]; rw [inducedMap_self]

/--
theorem `inducedMap_add` / 定理 `inducedMap_add`

English:
theorem inducedMap_add
  given: (x y : α)
  proof: by
  rw [inducedMap]; rw [cutMap_add]
  exact csSup_add (cutMap_nonempty β x) (cutMap_bddAbove β x) (cutMap_nonempty β y)
    (cutMap_bddAbove β y)

中文:
定理 inducedMap_add
  条件: (x y : α)
  证明: by
  rw [inducedMap]; rw [cutMap_add]
  exact csSup_add (cutMap_nonempty β x) (cutMap_bddAbove β x) (cutMap_nonempty β y)
    (cutMap_bddAbove β y)

Depends on / 依赖: csSup_add, cutMap_add, cutMap_bddAbove, cutMap_nonempty, inducedMap
-/
theorem inducedMap_add (x y : α) :
    inducedMap α β (x + y) = inducedMap α β x + inducedMap α β y := by
  rw [inducedMap]; rw [cutMap_add]
  exact csSup_add (cutMap_nonempty β x) (cutMap_bddAbove β x) (cutMap_nonempty β y)
    (cutMap_bddAbove β y)

variable {α β}

/--
theorem `le_inducedMap_mul_self_of_mem_cutMap` / 定理 `le_inducedMap_mul_self_of_mem_cutMap`

English:
theorem le_inducedMap_mul_self_of_mem_cutMap
  given: (ha : 0 < a) (b : β) (hb : b in cutMap β (a * a))
  proof: by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  · exact mod_cast hqq'.le
  · rw [pow_two] at hqa ⊢
    exact mul_self_le_mul_self (mod_cast hq'.le)
      (le_csSup (cutMap_bddAbove β a) <|
coe_mem_cutMap_iff.2 lt_of_mul_self_lt_mul_self₀ ha.le hqa)

中文:
定理 le_inducedMap_mul_self_of_mem_cutMap
  条件: (ha : 0 < a) (b : β) (hb : b in cutMap β (a * a))
  证明: by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  · exact mod_cast hqq'.le
  · rw [pow_two] at hqa ⊢
    exact mul_self_le_mul_self (mod_cast hq'.le)
      (le_csSup (cutMap_bddAbove β a) <|
coe_mem_cutMap_iff.2 lt_of_mul_self_lt_mul_self₀ ha.le hqa)

Depends on / 依赖: coe_mem_cutMap_iff, cutMap_bddAbove, exists_rat_pow_btwn, ha.le, ha.ne, le_csSup, mod_cast, mul_self_le_mul_self, mul_self_pos, pow_two, two_ne_zero
-/
theorem le_inducedMap_mul_self_of_mem_cutMap (ha : 0 < a) (b : β) (hb : b in cutMap β (a * a)) :
    b <= inducedMap α β a * inducedMap α β a := by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  · exact mod_cast hqq'.le
  · rw [pow_two] at hqa ⊢
    exact mul_self_le_mul_self (mod_cast hq'.le)
      (le_csSup (cutMap_bddAbove β a) <|
coe_mem_cutMap_iff.2 lt_of_mul_self_lt_mul_self₀ ha.le hqa)

/--
theorem `exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self` / 定理 `exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self`

English:
theorem exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self
  statement: (ha : 0 < a) (b : β)
  proof: by
  obtain hb | hb := lt_or_ge b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero]; rw [coe_mem_cutMap_iff]; rw [Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : Rat), coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

中文:
定理 存在_mem_cutMap_mul_self_of_lt_inducedMap_mul_self
  结论: (ha : 0 < a) (b : β)
  证明: by
  obtain hb | hb := lt_or_ge b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero]; rw [coe_mem_cutMap_iff]; rw [Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : Rat), coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

Depends on / 依赖: Rat.cast_zero, cast_pow, cast_zero, coe_mem_cutMap_iff, exists_rat_pow_btwn, ha.le, ha.ne, hb.trans_lt, hq.le, inducedMap_nonneg, lt_inducedMap_iff, lt_or_ge, mod_cast, mul_self_lt_mul_self, mul_self_pos, pow_two, trans_lt, two_ne_zero
-/
theorem exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self (ha : 0 < a) (b : β)
    (hba : b < inducedMap α β a * inducedMap α β a) : exists c in cutMap β (a * a), b < c := by
  obtain hb | hb := lt_or_ge b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero]; rw [coe_mem_cutMap_iff]; rw [Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : Rat), coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

variable (α β)

/--
Definition of `inducedAddHom` / `inducedAddHom` 的定义

English:
definition inducedAddHom
  signature: : α ->+ β
  body: ⟨⟨inducedMap α β, inducedMap_zero α β⟩, inducedMap_add α β⟩

中文:
定义 inducedAddHom
  签名: : α ->+ β
  定义体: ⟨⟨inducedMap α β, inducedMap_zero α β⟩, inducedMap_add α β⟩

Depends on / 依赖: inducedMap, inducedMap_add, inducedMap_zero
-/
def inducedAddHom : α ->+ β :=
  ⟨⟨inducedMap α β, inducedMap_zero α β⟩, inducedMap_add α β⟩

/-- `inducedMap` as an `OrderRingHom`. -/
@[simps!]
/--
Definition of `inducedOrderRingHom` / `inducedOrderRingHom` 的定义

English:
definition inducedOrderRingHom
  signature: : α ->+*o β
  body: { AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero (inducedAddHom α β) (by
      suffices forall x, 0 < x -> inducedAddHom α β (x * x) = inducedAddHom α β x * inducedAddHom α β x by
        intro x
        obtain h | rfl | h := lt_trichotomy x 0
        · convert! this (-x) (neg_pos.2 h) using 1
          · rw [neg_mul, mul_neg, neg_neg]
          · simp_rw [map_neg, neg_mul, mul_neg, neg_neg]
        · simp only [mul_zero, map_zero]
        · exact this x h
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine fun x hx => csSup_eq_of_forall_le_of_forall_lt_exists_gt (cutMap_nonempty β _) ?_ ?_
      · exact le_inducedMap_mul_self_of_mem_cutMap hx
      · exact exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self hx)
          two_ne_zero (inducedMap_one _ _) with
    monotone' := inducedMap_mono _ _ }

中文:
定义 inducedOrderRingHom
  签名: : α ->+*o β
  定义体: { AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero (inducedAddHom α β) (by
      suffices forall x, 0 < x -> inducedAddHom α β (x * x) = inducedAddHom α β x * inducedAddHom α β x by
        intro x
        obtain h | rfl | h := lt_trichotomy x 0
        · convert! this (-x) (neg_pos.2 h) using 1
          · rw [neg_mul, mul_neg, neg_neg]
          · simp_rw [map_neg, neg_mul, mul_neg, neg_neg]
        · simp only [mul_zero, map_zero]
        · exact this x h
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine fun x hx => csSup_eq_of_forall_le_of_forall_lt_exists_gt (cutMap_nonempty β _) ?_ ?_
      · exact le_inducedMap_mul_self_of_mem_cutMap hx
      · exact exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self hx)
          two_ne_zero (inducedMap_one _ _) with
    monotone' := inducedMap_mono _ _ }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero, convert, inducedAddHom, lt_trichotomy, map_neg, map_zero, mkRingHomOfMulSelfOfTwoNeZero, mul_neg, mul_zero, neg_mul, neg_neg, neg_pos, simp_rw
-/
def inducedOrderRingHom : α ->+*o β :=
  { AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero (inducedAddHom α β) (by
      suffices forall x, 0 < x -> inducedAddHom α β (x * x) = inducedAddHom α β x * inducedAddHom α β x by
        intro x
        obtain h | rfl | h := lt_trichotomy x 0
        · convert! this (-x) (neg_pos.2 h) using 1
          · rw [neg_mul, mul_neg, neg_neg]
          · simp_rw [map_neg, neg_mul, mul_neg, neg_neg]
        · simp only [mul_zero, map_zero]
        · exact this x h
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine fun x hx => csSup_eq_of_forall_le_of_forall_lt_exists_gt (cutMap_nonempty β _) ?_ ?_
      · exact le_inducedMap_mul_self_of_mem_cutMap hx
      · exact exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self hx)
          two_ne_zero (inducedMap_one _ _) with
    monotone' := inducedMap_mono _ _ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inducedOrderRingIso` / `inducedOrderRingIso` 的定义

English:
definition inducedOrderRingIso
  signature: : β ≃+*o γ
  body: { inducedOrderRingHom β γ with
    invFun := inducedMap γ β
    left_inv := inducedMap_inv_self _ _
    right_inv := inducedMap_inv_self _ _
    map_le_map_iff' := by
      dsimp
      refine ⟨fun h => ?_, fun h => inducedMap_mono _ _ h⟩
      convert! inducedMap_mono γ β h <;>
      · rw [inducedOrderRingHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, inducedAddHom]
        dsimp
        rw [inducedMap_inv_self β γ _] }

@[simp]

中文:
定义 inducedOrderRingIso
  签名: : β ≃+*o γ
  定义体: { inducedOrderRingHom β γ with
    invFun := inducedMap γ β
    left_inv := inducedMap_inv_self _ _
    right_inv := inducedMap_inv_self _ _
    map_le_map_iff' := by
      dsimp
      refine ⟨fun h => ?_, fun h => inducedMap_mono _ _ h⟩
      convert! inducedMap_mono γ β h <;>
      · rw [inducedOrderRingHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, inducedAddHom]
        dsimp
        rw [inducedMap_inv_self β γ _] }

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, coe_fn_mkRingHomOfMulSelfOfTwoNeZero, convert, inducedAddHom, inducedMap, inducedMap_inv_self, inducedMap_mono, inducedOrderRingHom, invFun, left_inv, map_le_map_iff, right_inv
-/
def inducedOrderRingIso : β ≃+*o γ :=
  { inducedOrderRingHom β γ with
    invFun := inducedMap γ β
    left_inv := inducedMap_inv_self _ _
    right_inv := inducedMap_inv_self _ _
    map_le_map_iff' := by
      dsimp
      refine ⟨fun h => ?_, fun h => inducedMap_mono _ _ h⟩
      convert! inducedMap_mono γ β h <;>
      · rw [inducedOrderRingHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, inducedAddHom]
        dsimp
        rw [inducedMap_inv_self β γ _] }

@[simp]
/--
theorem `coe_inducedOrderRingIso` / 定理 `coe_inducedOrderRingIso`

English:
theorem coe_inducedOrderRingIso
  statement: ⇑(inducedOrderRingIso β γ) = inducedMap β γ
  proof: rfl

@[simp]

中文:
定理 coe_inducedOrderRingIso
  结论: ⇑(inducedOrderRingIso β γ) = inducedMap β γ
  证明: rfl

@[simp]
-/
theorem coe_inducedOrderRingIso : ⇑(inducedOrderRingIso β γ) = inducedMap β γ := rfl

@[simp]
/--
theorem `inducedOrderRingIso_symm` / 定理 `inducedOrderRingIso_symm`

English:
theorem inducedOrderRingIso_symm
  statement: (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β
  proof: rfl

@[simp]

中文:
定理 inducedOrderRingIso_symm
  结论: (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β
  证明: rfl

@[simp]
-/
theorem inducedOrderRingIso_symm : (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β := rfl

@[simp]
/--
theorem `inducedOrderRingIso_self` / 定理 `inducedOrderRingIso_self`

English:
theorem inducedOrderRingIso_self
  statement: inducedOrderRingIso β β = OrderRingIso.refl β
  proof: OrderRingIso.ext inducedMap_self

中文:
定理 inducedOrderRingIso_self
  结论: inducedOrderRingIso β β = OrderRingIso.refl β
  证明: OrderRingIso.ext inducedMap_self

Depends on / 依赖: OrderRingIso, OrderRingIso.ext, inducedMap_self
-/
theorem inducedOrderRingIso_self : inducedOrderRingIso β β = OrderRingIso.refl β :=
  OrderRingIso.ext inducedMap_self

open OrderRingIso

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
scoped instance uniqueOrderRingHom : Unique (α ->+*o β) :=
uniqueOfSubsingleton inducedOrderRingHom α β

/-- There is a unique ordered ring isomorphism between two conditionally complete linear ordered
fields. -/
scoped instance uniqueOrderRingIso : Unique (β ≃+*o γ) :=
uniqueOfSubsingleton inducedOrderRingIso β γ

end InducedMap

end ConditionallyCompleteLinearOrderedField

namespace LinearOrderedField

@[deprecated (since := "2026-02-24")]
alias inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap
@[deprecated (since := "2026-02-24")]
alias inducedMap_mono := ConditionallyCompleteLinearOrderedField.inducedMap_mono
@[deprecated (since := "2026-02-24")]
alias inducedMap_rat := ConditionallyCompleteLinearOrderedField.inducedMap_rat
@[deprecated (since := "2026-02-24")]
alias inducedMap_zero := ConditionallyCompleteLinearOrderedField.inducedMap_zero
@[deprecated (since := "2026-02-24")]
alias inducedMap_one := ConditionallyCompleteLinearOrderedField.inducedMap_one
@[deprecated (since := "2026-02-24")]
alias inducedMap_nonneg := ConditionallyCompleteLinearOrderedField.inducedMap_nonneg
@[deprecated (since := "2026-02-24")]
alias coe_lt_inducedMap_iff := ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff
@[deprecated (since := "2026-02-24")]
alias lt_inducedMap_iff := ConditionallyCompleteLinearOrderedField.lt_inducedMap_iff
@[deprecated (since := "2026-02-24")]
alias inducedMap_self := ConditionallyCompleteLinearOrderedField.inducedMap_self
@[deprecated (since := "2026-02-24")]
alias inducedMap_inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap_inducedMap
@[deprecated (since := "2026-02-24")]
alias inducedMap_inv_self := ConditionallyCompleteLinearOrderedField.inducedMap_inv_self
@[deprecated (since := "2026-02-24")]
alias inducedMap_add := ConditionallyCompleteLinearOrderedField.inducedMap_add
@[deprecated (since := "2026-02-24")]
alias le_inducedMap_mul_self_of_mem_cutMap :=
  ConditionallyCompleteLinearOrderedField.le_inducedMap_mul_self_of_mem_cutMap
@[deprecated (since := "2026-02-24")]
alias exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self :=
  ConditionallyCompleteLinearOrderedField.exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self
@[deprecated (since := "2026-02-24")]
alias inducedAddHom := ConditionallyCompleteLinearOrderedField.inducedAddHom
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingHom := ConditionallyCompleteLinearOrderedField.inducedOrderRingHom
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso
@[deprecated (since := "2026-02-24")]
alias coe_inducedOrderRingIso := ConditionallyCompleteLinearOrderedField.coe_inducedOrderRingIso
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso_symm := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_symm
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso_self := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_self

end LinearOrderedField
