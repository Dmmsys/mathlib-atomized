/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Bounds on scalar multiplication of set

This file proves order properties of pointwise operations of sets.
-/

public section

open scoped Pointwise

variable {α β : Type*}

section PosSMulMono
variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

/--
lemma `smul_lowerBounds_subset_lowerBounds_smul_of_nonneg` / 引理 `smul_lowerBounds_subset_lowerBounds_smul_of_nonneg`

English:
lemma smul_lowerBounds_subset_lowerBounds_smul_of_nonneg
  given: (ha : 0 <= a)
  proof: (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

中文:
引理 smul_lowerBounds_subset_lowerBounds_smul_of_nonneg
  条件: (ha : 0 <= a)
  证明: (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

Depends on / 依赖: image_lowerBounds_subset_lowerBounds_image, monotone_smul_left_of_nonneg
-/
lemma smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 <= a) :
    a • lowerBounds s subseteq lowerBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

/--
lemma `smul_upperBounds_subset_upperBounds_smul_of_nonneg` / 引理 `smul_upperBounds_subset_upperBounds_smul_of_nonneg`

English:
lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg
  given: (ha : 0 <= a)
  proof: (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image

中文:
引理 smul_upperBounds_subset_upperBounds_smul_of_nonneg
  条件: (ha : 0 <= a)
  证明: (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image

Depends on / 依赖: image_upperBounds_subset_upperBounds_image, monotone_smul_left_of_nonneg
-/
lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 <= a) :
    a • upperBounds s subseteq upperBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image

/--
lemma `BddBelow.smul_of_nonneg` / 引理 `BddBelow.smul_of_nonneg`

English:
lemma BddBelow.smul_of_nonneg
  given: (hs : BddBelow s) (ha : 0 <= a)
  statement: BddBelow (a • s)
  proof: (monotone_smul_left_of_nonneg ha).map_bddBelow hs

中文:
引理 BddBelow.smul_of_nonneg
  条件: (hs : BddBelow s) (ha : 0 <= a)
  结论: BddBelow (a • s)
  证明: (monotone_smul_left_of_nonneg ha).map_bddBelow hs

Depends on / 依赖: map_bddBelow, monotone_smul_left_of_nonneg
-/
lemma BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 <= a) : BddBelow (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddBelow hs

/--
lemma `BddAbove.smul_of_nonneg` / 引理 `BddAbove.smul_of_nonneg`

English:
lemma BddAbove.smul_of_nonneg
  given: (hs : BddAbove s) (ha : 0 <= a)
  statement: BddAbove (a • s)
  proof: (monotone_smul_left_of_nonneg ha).map_bddAbove hs

中文:
引理 BddAbove.smul_of_nonneg
  条件: (hs : BddAbove s) (ha : 0 <= a)
  结论: BddAbove (a • s)
  证明: (monotone_smul_left_of_nonneg ha).map_bddAbove hs

Depends on / 依赖: map_bddAbove, monotone_smul_left_of_nonneg
-/
lemma BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 <= a) : BddAbove (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddAbove hs

end PosSMulMono


section
variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulActionWithZero α β]
  [PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α}

/--
lemma `lowerBounds_smul_of_pos` / 引理 `lowerBounds_smul_of_pos`

English:
lemma lowerBounds_smul_of_pos
  given: (ha : 0 < a)
  statement: lowerBounds (a • s) = a • lowerBounds s
  proof: (OrderIso.smulRight ha).lowerBounds_image

中文:
引理 lowerBounds_smul_of_pos
  条件: (ha : 0 < a)
  结论: lowerBounds (a • s) = a • lowerBounds s
  证明: (OrderIso.smulRight ha).lowerBounds_image
-/
@[simp] lemma lowerBounds_smul_of_pos (ha : 0 < a) : lowerBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRight ha).lowerBounds_image

/--
lemma `upperBounds_smul_of_pos` / 引理 `upperBounds_smul_of_pos`

English:
lemma upperBounds_smul_of_pos
  given: (ha : 0 < a)
  statement: upperBounds (a • s) = a • upperBounds s
  proof: (OrderIso.smulRight ha).upperBounds_image

中文:
引理 upperBounds_smul_of_pos
  条件: (ha : 0 < a)
  结论: upperBounds (a • s) = a • upperBounds s
  证明: (OrderIso.smulRight ha).upperBounds_image
-/
@[simp] lemma upperBounds_smul_of_pos (ha : 0 < a) : upperBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRight ha).upperBounds_image

/--
lemma `bddBelow_smul_iff_of_pos` / 引理 `bddBelow_smul_iff_of_pos`

English:
lemma bddBelow_smul_iff_of_pos
  given: (ha : 0 < a)
  statement: BddBelow (a • s) ↔ BddBelow s
  proof: (OrderIso.smulRight ha).bddBelow_image

中文:
引理 bddBelow_smul_iff_of_pos
  条件: (ha : 0 < a)
  结论: BddBelow (a • s) ↔ BddBelow s
  证明: (OrderIso.smulRight ha).bddBelow_image
-/
@[simp] lemma bddBelow_smul_iff_of_pos (ha : 0 < a) : BddBelow (a • s) ↔ BddBelow s :=
  (OrderIso.smulRight ha).bddBelow_image

/--
lemma `bddAbove_smul_iff_of_pos` / 引理 `bddAbove_smul_iff_of_pos`

English:
lemma bddAbove_smul_iff_of_pos
  given: (ha : 0 < a)
  statement: BddAbove (a • s) ↔ BddAbove s
  proof: (OrderIso.smulRight ha).bddAbove_image

中文:
引理 bddAbove_smul_iff_of_pos
  条件: (ha : 0 < a)
  结论: BddAbove (a • s) ↔ BddAbove s
  证明: (OrderIso.smulRight ha).bddAbove_image
-/
@[simp] lemma bddAbove_smul_iff_of_pos (ha : 0 < a) : BddAbove (a • s) ↔ BddAbove s :=
  (OrderIso.smulRight ha).bddAbove_image

end

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

/--
lemma `smul_lowerBounds_subset_upperBounds_smul` / 引理 `smul_lowerBounds_subset_upperBounds_smul`

English:
lemma smul_lowerBounds_subset_upperBounds_smul
  given: (ha : a <= 0)
  proof: (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image

中文:
引理 smul_lowerBounds_subset_upperBounds_smul
  条件: (ha : a <= 0)
  证明: (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image

Depends on / 依赖: antitone_smul_left, image_lowerBounds_subset_upperBounds_image
-/
lemma smul_lowerBounds_subset_upperBounds_smul (ha : a <= 0) :
    a • lowerBounds s subseteq upperBounds (a • s) :=
  (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image

/--
lemma `smul_upperBounds_subset_lowerBounds_smul` / 引理 `smul_upperBounds_subset_lowerBounds_smul`

English:
lemma smul_upperBounds_subset_lowerBounds_smul
  given: (ha : a <= 0)
  proof: (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image

中文:
引理 smul_upperBounds_subset_lowerBounds_smul
  条件: (ha : a <= 0)
  证明: (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image

Depends on / 依赖: antitone_smul_left, image_upperBounds_subset_lowerBounds_image
-/
lemma smul_upperBounds_subset_lowerBounds_smul (ha : a <= 0) :
    a • upperBounds s subseteq lowerBounds (a • s) :=
  (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image

/--
lemma `BddBelow.smul_of_nonpos` / 引理 `BddBelow.smul_of_nonpos`

English:
lemma BddBelow.smul_of_nonpos
  given: (ha : a <= 0) (hs : BddBelow s)
  statement: BddAbove (a • s)
  proof: (antitone_smul_left ha).map_bddBelow hs

中文:
引理 BddBelow.smul_of_nonpos
  条件: (ha : a <= 0) (hs : BddBelow s)
  结论: BddAbove (a • s)
  证明: (antitone_smul_left ha).map_bddBelow hs

Depends on / 依赖: antitone_smul_left, map_bddBelow
-/
lemma BddBelow.smul_of_nonpos (ha : a <= 0) (hs : BddBelow s) : BddAbove (a • s) :=
  (antitone_smul_left ha).map_bddBelow hs

/--
lemma `BddAbove.smul_of_nonpos` / 引理 `BddAbove.smul_of_nonpos`

English:
lemma BddAbove.smul_of_nonpos
  given: (ha : a <= 0) (hs : BddAbove s)
  statement: BddBelow (a • s)
  proof: (antitone_smul_left ha).map_bddAbove hs

中文:
引理 BddAbove.smul_of_nonpos
  条件: (ha : a <= 0) (hs : BddAbove s)
  结论: BddBelow (a • s)
  证明: (antitone_smul_left ha).map_bddAbove hs

Depends on / 依赖: antitone_smul_left, map_bddAbove
-/
lemma BddAbove.smul_of_nonpos (ha : a <= 0) (hs : BddAbove s) : BddBelow (a • s) :=
  (antitone_smul_left ha).map_bddAbove hs

end OrderedRing

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β}
  {a : α}

/--
lemma `lowerBounds_smul_of_neg` / 引理 `lowerBounds_smul_of_neg`

English:
lemma lowerBounds_smul_of_neg
  given: (ha : a < 0)
  statement: lowerBounds (a • s) = a • upperBounds s
  proof: (OrderIso.smulRightDual β ha).upperBounds_image

中文:
引理 lowerBounds_smul_of_neg
  条件: (ha : a < 0)
  结论: lowerBounds (a • s) = a • upperBounds s
  证明: (OrderIso.smulRightDual β ha).upperBounds_image
-/
@[simp] lemma lowerBounds_smul_of_neg (ha : a < 0) : lowerBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRightDual β ha).upperBounds_image

/--
lemma `upperBounds_smul_of_neg` / 引理 `upperBounds_smul_of_neg`

English:
lemma upperBounds_smul_of_neg
  given: (ha : a < 0)
  statement: upperBounds (a • s) = a • lowerBounds s
  proof: (OrderIso.smulRightDual β ha).lowerBounds_image

中文:
引理 upperBounds_smul_of_neg
  条件: (ha : a < 0)
  结论: upperBounds (a • s) = a • lowerBounds s
  证明: (OrderIso.smulRightDual β ha).lowerBounds_image
-/
@[simp] lemma upperBounds_smul_of_neg (ha : a < 0) : upperBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRightDual β ha).lowerBounds_image

/--
lemma `bddBelow_smul_iff_of_neg` / 引理 `bddBelow_smul_iff_of_neg`

English:
lemma bddBelow_smul_iff_of_neg
  given: (ha : a < 0)
  statement: BddBelow (a • s) ↔ BddAbove s
  proof: (OrderIso.smulRightDual β ha).bddAbove_image

中文:
引理 bddBelow_smul_iff_of_neg
  条件: (ha : a < 0)
  结论: BddBelow (a • s) ↔ BddAbove s
  证明: (OrderIso.smulRightDual β ha).bddAbove_image
-/
@[simp] lemma bddBelow_smul_iff_of_neg (ha : a < 0) : BddBelow (a • s) ↔ BddAbove s :=
  (OrderIso.smulRightDual β ha).bddAbove_image

/--
lemma `bddAbove_smul_iff_of_neg` / 引理 `bddAbove_smul_iff_of_neg`

English:
lemma bddAbove_smul_iff_of_neg
  given: (ha : a < 0)
  statement: BddAbove (a • s) ↔ BddBelow s
  proof: (OrderIso.smulRightDual β ha).bddBelow_image

中文:
引理 bddAbove_smul_iff_of_neg
  条件: (ha : a < 0)
  结论: BddAbove (a • s) ↔ BddBelow s
  证明: (OrderIso.smulRightDual β ha).bddBelow_image
-/
@[simp] lemma bddAbove_smul_iff_of_neg (ha : a < 0) : BddAbove (a • s) ↔ BddBelow s :=
  (OrderIso.smulRightDual β ha).bddBelow_image

end LinearOrderedField
