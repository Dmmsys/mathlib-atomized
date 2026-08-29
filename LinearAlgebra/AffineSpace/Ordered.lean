/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `lineMap` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/

public section


open AffineMap

variable {k E PE : Type*}

/-!
### Monotonicity of `lineMap`

In this section we prove that `lineMap a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/


section OrderedRing

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
variable {a a' b b' : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_mono_left` / 定理 `lineMap_mono_left`

English:
theorem lineMap_mono_left
  given: (ha : a <= a') (hr : r <= 1)
  statement: lineMap a b r <= lineMap a' b r
  proof: by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

中文:
定理 lineMap_mono_left
  条件: (ha : a <= a') (hr : r <= 1)
  结论: lineMap a b r <= lineMap a' b r
  证明: by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

Depends on / 依赖: lineMap_apply_module, sub_nonneg
-/
theorem lineMap_mono_left (ha : a <= a') (hr : r <= 1) : lineMap a b r <= lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_strict_mono_left` / 定理 `lineMap_strict_mono_left`

English:
theorem lineMap_strict_mono_left
  given: (ha : a < a') (hr : r < 1)
  statement: lineMap a b r < lineMap a' b r
  proof: by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

中文:
定理 lineMap_strict_mono_left
  条件: (ha : a < a') (hr : r < 1)
  结论: lineMap a b r < lineMap a' b r
  证明: by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

Depends on / 依赖: lineMap_apply_module, sub_pos
-/
theorem lineMap_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

set_option backward.isDefEq.respectTransparency false in
omit [IsOrderedRing k] in
/--
theorem `lineMap_mono_right` / 定理 `lineMap_mono_right`

English:
theorem lineMap_mono_right
  given: (hb : b <= b') (hr : 0 <= r)
  statement: lineMap a b r <= lineMap a b' r
  proof: by
  simp only [lineMap_apply_module]
  gcongr

中文:
定理 lineMap_mono_right
  条件: (hb : b <= b') (hr : 0 <= r)
  结论: lineMap a b r <= lineMap a b' r
  证明: by
  simp only [lineMap_apply_module]
  gcongr

Depends on / 依赖: lineMap_apply_module
-/
theorem lineMap_mono_right (hb : b <= b') (hr : 0 <= r) : lineMap a b r <= lineMap a b' r := by
  simp only [lineMap_apply_module]
  gcongr

set_option backward.isDefEq.respectTransparency false in
omit [IsOrderedRing k] in
/--
theorem `lineMap_strict_mono_right` / 定理 `lineMap_strict_mono_right`

English:
theorem lineMap_strict_mono_right
  given: (hb : b < b') (hr : 0 < r)
  statement: lineMap a b r < lineMap a b' r
  proof: by
  simp only [lineMap_apply_module]; gcongr

中文:
定理 lineMap_strict_mono_right
  条件: (hb : b < b') (hr : 0 < r)
  结论: lineMap a b r < lineMap a b' r
  证明: by
  simp only [lineMap_apply_module]; gcongr

Depends on / 依赖: lineMap_apply_module
-/
theorem lineMap_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r := by
  simp only [lineMap_apply_module]; gcongr

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_mono_endpoints` / 定理 `lineMap_mono_endpoints`

English:
theorem lineMap_mono_endpoints
  given: (ha : a <= a') (hb : b <= b') (h₀ : 0 <= r) (h₁ : r <= 1)
  proof: (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

中文:
定理 lineMap_mono_endpoints
  条件: (ha : a <= a') (hb : b <= b') (h₀ : 0 <= r) (h₁ : r <= 1)
  证明: (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

Depends on / 依赖: lineMap_mono_left, lineMap_mono_right
-/
theorem lineMap_mono_endpoints (ha : a <= a') (hb : b <= b') (h₀ : 0 <= r) (h₁ : r <= 1) :
    lineMap a b r <= lineMap a' b' r :=
  (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_strict_mono_endpoints` / 定理 `lineMap_strict_mono_endpoints`

English:
theorem lineMap_strict_mono_endpoints
  given: (ha : a < a') (hb : b < b') (h₀ : 0 <= r) (h₁ : r <= 1)
  proof: by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

中文:
定理 lineMap_strict_mono_endpoints
  条件: (ha : a < a') (hb : b < b') (h₀ : 0 <= r) (h₁ : r <= 1)
  证明: by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

Depends on / 依赖: eq_or_lt, ha.le, lineMap_mono_left, lineMap_strict_mono_right, trans_lt
-/
theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 <= r) (h₁ : r <= 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

variable [PosSMulReflectLT k E]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_lineMap_iff_of_lt` / 定理 `lineMap_lt_lineMap_iff_of_lt`

English:
theorem lineMap_lt_lineMap_iff_of_lt
  given: (h : r < r')
  statement: lineMap a b r < lineMap a b r' ↔ a < b
  proof: by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt]; rw [add_sub_assoc]; rw [← sub_lt_iff_lt_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

中文:
定理 lineMap_lt_lineMap_iff_of_lt
  条件: (h : r < r')
  结论: lineMap a b r < lineMap a b r' ↔ a < b
  证明: by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt]; rw [add_sub_assoc]; rw [← sub_lt_iff_lt_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

Depends on / 依赖: add_sub_assoc, lineMap_apply_module, lt_sub_iff_add_lt, smul_lt_smul_iff_of_pos_left, sub_lt_iff_lt_add, sub_pos, sub_smul, sub_sub_sub_cancel_left
-/
theorem lineMap_lt_lineMap_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b := by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt]; rw [add_sub_assoc]; rw [← sub_lt_iff_lt_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_lt_lineMap_iff_lt` / 定理 `left_lt_lineMap_iff_lt`

English:
theorem left_lt_lineMap_iff_lt
  given: (h : 0 < r)
  statement: a < lineMap a b r ↔ a < b
  proof: Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

中文:
定理 left_lt_lineMap_iff_lt
  条件: (h : 0 < r)
  结论: a < lineMap a b r ↔ a < b
  证明: Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

Depends on / 依赖: Iff.trans, lineMap_apply_zero, lineMap_lt_lineMap_iff_of_lt
-/
theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_left_iff_lt` / 定理 `lineMap_lt_left_iff_lt`

English:
theorem lineMap_lt_left_iff_lt
  given: (h : 0 < r)
  statement: lineMap a b r < a ↔ b < a
  proof: left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

中文:
定理 lineMap_lt_left_iff_lt
  条件: (h : 0 < r)
  结论: lineMap a b r < a ↔ b < a
  证明: left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

Depends on / 依赖: left_lt_lineMap_iff_lt
-/
theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a :=
  left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_right_iff_lt` / 定理 `lineMap_lt_right_iff_lt`

English:
theorem lineMap_lt_right_iff_lt
  given: (h : r < 1)
  statement: lineMap a b r < b ↔ a < b
  proof: Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

中文:
定理 lineMap_lt_right_iff_lt
  条件: (h : r < 1)
  结论: lineMap a b r < b ↔ a < b
  证明: Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

Depends on / 依赖: Iff.trans, lineMap_apply_one, lineMap_lt_lineMap_iff_of_lt
-/
theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_lt_lineMap_iff_lt` / 定理 `right_lt_lineMap_iff_lt`

English:
theorem right_lt_lineMap_iff_lt
  given: (h : r < 1)
  statement: b < lineMap a b r ↔ b < a
  proof: lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

中文:
定理 right_lt_lineMap_iff_lt
  条件: (h : r < 1)
  结论: b < lineMap a b r ↔ b < a
  证明: lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

Depends on / 依赖: lineMap_lt_right_iff_lt
-/
theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a :=
  lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

end OrderedRing

section LinearOrderedRing

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_lineMap_iff_of_lt'` / 定理 `lineMap_le_lineMap_iff_of_lt'`

English:
theorem lineMap_le_lineMap_iff_of_lt'
  given: (h : a < b)
  statement: lineMap a b r <= lineMap a b r' ↔ r <= r'
  proof: by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right]; rw [smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

中文:
定理 lineMap_le_lineMap_iff_of_lt'
  条件: (h : a < b)
  结论: lineMap a b r <= lineMap a b r' ↔ r <= r'
  证明: by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right]; rw [smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

Depends on / 依赖: add_le_add_iff_right, lineMap_apply_module, smul_le_smul_iff_of_pos_right, sub_pos, sub_pos.mpr
-/
theorem lineMap_le_lineMap_iff_of_lt' (h : a < b) : lineMap a b r <= lineMap a b r' ↔ r <= r' := by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right]; rw [smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_le_lineMap_iff_nonneg` / 定理 `left_le_lineMap_iff_nonneg`

English:
theorem left_le_lineMap_iff_nonneg
  given: (h : a < b)
  statement: a <= lineMap a b r ↔ 0 <= r
  proof: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

中文:
定理 left_le_lineMap_iff_nonneg
  条件: (h : a < b)
  结论: a <= lineMap a b r ↔ 0 <= r
  证明: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

Depends on / 依赖: lineMap_apply_zero, lineMap_le_lineMap_iff_of_lt
-/
theorem left_le_lineMap_iff_nonneg (h : a < b) : a <= lineMap a b r ↔ 0 <= r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_left_iff_nonpos` / 定理 `lineMap_le_left_iff_nonpos`

English:
theorem lineMap_le_left_iff_nonpos
  given: (h : a < b)
  statement: lineMap a b r <= a ↔ r <= 0
  proof: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

中文:
定理 lineMap_le_left_iff_nonpos
  条件: (h : a < b)
  结论: lineMap a b r <= a ↔ r <= 0
  证明: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

Depends on / 依赖: lineMap_apply_zero, lineMap_le_lineMap_iff_of_lt
-/
theorem lineMap_le_left_iff_nonpos (h : a < b) : lineMap a b r <= a ↔ r <= 0 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_le_lineMap_iff_one_le` / 定理 `right_le_lineMap_iff_one_le`

English:
theorem right_le_lineMap_iff_one_le
  given: (h : a < b)
  statement: b <= lineMap a b r ↔ 1 <= r
  proof: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

中文:
定理 right_le_lineMap_iff_one_le
  条件: (h : a < b)
  结论: b <= lineMap a b r ↔ 1 <= r
  证明: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

Depends on / 依赖: lineMap_apply_one, lineMap_le_lineMap_iff_of_lt
-/
theorem right_le_lineMap_iff_one_le (h : a < b) : b <= lineMap a b r ↔ 1 <= r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_right_iff_le_one` / 定理 `lineMap_le_right_iff_le_one`

English:
theorem lineMap_le_right_iff_le_one
  given: (h : a < b)
  statement: lineMap a b r <= b ↔ r <= 1
  proof: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

中文:
定理 lineMap_le_right_iff_le_one
  条件: (h : a < b)
  结论: lineMap a b r <= b ↔ r <= 1
  证明: by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

Depends on / 依赖: lineMap_apply_one, lineMap_le_lineMap_iff_of_lt
-/
theorem lineMap_le_right_iff_le_one (h : a < b) : lineMap a b r <= b ↔ r <= 1 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_lineMap_iff_of_lt'` / 定理 `lineMap_lt_lineMap_iff_of_lt'`

English:
theorem lineMap_lt_lineMap_iff_of_lt'
  given: (h : a < b)
  statement: lineMap a b r < lineMap a b r' ↔ r < r'
  proof: by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right]; rw [smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

中文:
定理 lineMap_lt_lineMap_iff_of_lt'
  条件: (h : a < b)
  结论: lineMap a b r < lineMap a b r' ↔ r < r'
  证明: by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right]; rw [smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

Depends on / 依赖: add_lt_add_iff_right, lineMap_apply_module, smul_lt_smul_iff_of_pos_right, sub_pos, sub_pos.mpr
-/
theorem lineMap_lt_lineMap_iff_of_lt' (h : a < b) : lineMap a b r < lineMap a b r' ↔ r < r' := by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right]; rw [smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_lt_lineMap_iff_pos` / 定理 `left_lt_lineMap_iff_pos`

English:
theorem left_lt_lineMap_iff_pos
  given: (h : a < b)
  statement: a < lineMap a b r ↔ 0 < r
  proof: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

中文:
定理 left_lt_lineMap_iff_pos
  条件: (h : a < b)
  结论: a < lineMap a b r ↔ 0 < r
  证明: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

Depends on / 依赖: lineMap_apply_zero, lineMap_lt_lineMap_iff_of_lt
-/
theorem left_lt_lineMap_iff_pos (h : a < b) : a < lineMap a b r ↔ 0 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_left_iff_neg` / 定理 `lineMap_lt_left_iff_neg`

English:
theorem lineMap_lt_left_iff_neg
  given: (h : a < b)
  statement: lineMap a b r < a ↔ r < 0
  proof: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

中文:
定理 lineMap_lt_left_iff_neg
  条件: (h : a < b)
  结论: lineMap a b r < a ↔ r < 0
  证明: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

Depends on / 依赖: lineMap_apply_zero, lineMap_lt_lineMap_iff_of_lt
-/
theorem lineMap_lt_left_iff_neg (h : a < b) : lineMap a b r < a ↔ r < 0 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_lt_lineMap_iff_one_lt` / 定理 `right_lt_lineMap_iff_one_lt`

English:
theorem right_lt_lineMap_iff_one_lt
  given: (h : a < b)
  statement: b < lineMap a b r ↔ 1 < r
  proof: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

中文:
定理 right_lt_lineMap_iff_one_lt
  条件: (h : a < b)
  结论: b < lineMap a b r ↔ 1 < r
  证明: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

Depends on / 依赖: lineMap_apply_one, lineMap_lt_lineMap_iff_of_lt
-/
theorem right_lt_lineMap_iff_one_lt (h : a < b) : b < lineMap a b r ↔ 1 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_right_iff_lt_one` / 定理 `lineMap_lt_right_iff_lt_one`

English:
theorem lineMap_lt_right_iff_lt_one
  given: (h : a < b)
  statement: lineMap a b r < b ↔ r < 1
  proof: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

中文:
定理 lineMap_lt_right_iff_lt_one
  条件: (h : a < b)
  结论: lineMap a b r < b ↔ r < 1
  证明: by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

Depends on / 依赖: lineMap_apply_one, lineMap_lt_lineMap_iff_of_lt
-/
theorem lineMap_lt_right_iff_lt_one (h : a < b) : lineMap a b r < b ↔ r < 1 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h]; rw [lineMap_apply_one]

/--
theorem `midpoint_le_midpoint` / 定理 `midpoint_le_midpoint`

English:
theorem midpoint_le_midpoint
  given: [Invertible (2 : k)] (ha : a <= a') (hb : b <= b')
  proof: lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) invOf_le_one one_le_two

中文:
定理 midpoint_le_midpoint
  条件: [可逆 (2 : k)] (ha : a <= a') (hb : b <= b')
  证明: lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) invOf_le_one one_le_two

Depends on / 依赖: invOf_le_one, invOf_nonneg, lineMap_mono_endpoints, one_le_two, zero_le_two
-/
theorem midpoint_le_midpoint [Invertible (2 : k)] (ha : a <= a') (hb : b <= b') :
    midpoint k a b <= midpoint k a' b' :=
lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) invOf_le_one one_le_two

end LinearOrderedRing

section LinearOrderedField

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

section

variable {a b : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_lineMap_iff_of_lt` / 定理 `lineMap_le_lineMap_iff_of_lt`

English:
theorem lineMap_le_lineMap_iff_of_lt
  given: (h : r < r')
  statement: lineMap a b r <= lineMap a b r' ↔ a <= b
  proof: by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le]; rw [add_sub_assoc]; rw [← sub_le_iff_le_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

中文:
定理 lineMap_le_lineMap_iff_of_lt
  条件: (h : r < r')
  结论: lineMap a b r <= lineMap a b r' ↔ a <= b
  证明: by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le]; rw [add_sub_assoc]; rw [← sub_le_iff_le_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

Depends on / 依赖: add_sub_assoc, le_sub_iff_add_le, lineMap_apply_module, smul_le_smul_iff_of_pos_left, sub_le_iff_le_add, sub_pos, sub_smul, sub_sub_sub_cancel_left
-/
theorem lineMap_le_lineMap_iff_of_lt (h : r < r') : lineMap a b r <= lineMap a b r' ↔ a <= b := by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le]; rw [add_sub_assoc]; rw [← sub_le_iff_le_add']; rw [← sub_smul]; rw [← sub_smul]; rw [sub_sub_sub_cancel_left]; rw [smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_le_lineMap_iff_le` / 定理 `left_le_lineMap_iff_le`

English:
theorem left_le_lineMap_iff_le
  given: (h : 0 < r)
  statement: a <= lineMap a b r ↔ a <= b
  proof: Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]

中文:
定理 left_le_lineMap_iff_le
  条件: (h : 0 < r)
  结论: a <= lineMap a b r ↔ a <= b
  证明: Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]

Depends on / 依赖: Iff.trans, lineMap_apply_zero, lineMap_le_lineMap_iff_of_lt
-/
theorem left_le_lineMap_iff_le (h : 0 < r) : a <= lineMap a b r ↔ a <= b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]
/--
theorem `left_le_midpoint` / 定理 `left_le_midpoint`

English:
theorem left_le_midpoint
  statement: a <= midpoint k a b ↔ a <= b
  proof: left_le_lineMap_iff_le inv_pos.2 zero_lt_two

中文:
定理 left_le_midpoint
  结论: a <= midpoint k a b ↔ a <= b
  证明: left_le_lineMap_iff_le inv_pos.2 zero_lt_two

Depends on / 依赖: inv_pos, left_le_lineMap_iff_le, zero_lt_two
-/
theorem left_le_midpoint : a <= midpoint k a b ↔ a <= b :=
left_le_lineMap_iff_le inv_pos.2 zero_lt_two

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_left_iff_le` / 定理 `lineMap_le_left_iff_le`

English:
theorem lineMap_le_left_iff_le
  given: (h : 0 < r)
  statement: lineMap a b r <= a ↔ b <= a
  proof: left_le_lineMap_iff_le (E := Eᵒᵈ) h

@[simp]

中文:
定理 lineMap_le_left_iff_le
  条件: (h : 0 < r)
  结论: lineMap a b r <= a ↔ b <= a
  证明: left_le_lineMap_iff_le (E := Eᵒᵈ) h

@[simp]

Depends on / 依赖: left_le_lineMap_iff_le
-/
theorem lineMap_le_left_iff_le (h : 0 < r) : lineMap a b r <= a ↔ b <= a :=
  left_le_lineMap_iff_le (E := Eᵒᵈ) h

@[simp]
/--
theorem `midpoint_le_left` / 定理 `midpoint_le_left`

English:
theorem midpoint_le_left
  statement: midpoint k a b <= a ↔ b <= a
  proof: lineMap_le_left_iff_le inv_pos.2 zero_lt_two

中文:
定理 midpoint_le_left
  结论: midpoint k a b <= a ↔ b <= a
  证明: lineMap_le_left_iff_le inv_pos.2 zero_lt_two

Depends on / 依赖: inv_pos, lineMap_le_left_iff_le, zero_lt_two
-/
theorem midpoint_le_left : midpoint k a b <= a ↔ b <= a :=
lineMap_le_left_iff_le inv_pos.2 zero_lt_two

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_right_iff_le` / 定理 `lineMap_le_right_iff_le`

English:
theorem lineMap_le_right_iff_le
  given: (h : r < 1)
  statement: lineMap a b r <= b ↔ a <= b
  proof: Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]

中文:
定理 lineMap_le_right_iff_le
  条件: (h : r < 1)
  结论: lineMap a b r <= b ↔ a <= b
  证明: Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]

Depends on / 依赖: Iff.trans, lineMap_apply_one, lineMap_le_lineMap_iff_of_lt
-/
theorem lineMap_le_right_iff_le (h : r < 1) : lineMap a b r <= b ↔ a <= b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]
/--
theorem `midpoint_le_right` / 定理 `midpoint_le_right`

English:
theorem midpoint_le_right
  statement: midpoint k a b <= b ↔ a <= b
  proof: lineMap_le_right_iff_le two_inv_lt_one

中文:
定理 midpoint_le_right
  结论: midpoint k a b <= b ↔ a <= b
  证明: lineMap_le_right_iff_le two_inv_lt_one

Depends on / 依赖: lineMap_le_right_iff_le, two_inv_lt_one
-/
theorem midpoint_le_right : midpoint k a b <= b ↔ a <= b := lineMap_le_right_iff_le two_inv_lt_one

set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_le_lineMap_iff_le` / 定理 `right_le_lineMap_iff_le`

English:
theorem right_le_lineMap_iff_le
  given: (h : r < 1)
  statement: b <= lineMap a b r ↔ b <= a
  proof: lineMap_le_right_iff_le (E := Eᵒᵈ) h

@[simp]

中文:
定理 right_le_lineMap_iff_le
  条件: (h : r < 1)
  结论: b <= lineMap a b r ↔ b <= a
  证明: lineMap_le_right_iff_le (E := Eᵒᵈ) h

@[simp]

Depends on / 依赖: lineMap_le_right_iff_le
-/
theorem right_le_lineMap_iff_le (h : r < 1) : b <= lineMap a b r ↔ b <= a :=
  lineMap_le_right_iff_le (E := Eᵒᵈ) h

@[simp]
/--
theorem `right_le_midpoint` / 定理 `right_le_midpoint`

English:
theorem right_le_midpoint
  statement: b <= midpoint k a b ↔ b <= a
  proof: right_le_lineMap_iff_le two_inv_lt_one

中文:
定理 right_le_midpoint
  结论: b <= midpoint k a b ↔ b <= a
  证明: right_le_lineMap_iff_le two_inv_lt_one

Depends on / 依赖: right_le_lineMap_iff_le, two_inv_lt_one
-/
theorem right_le_midpoint : b <= midpoint k a b ↔ b <= a := right_le_lineMap_iff_le two_inv_lt_one

end

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = lineMap a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `lineMap (f a) (f b) r`;
* compare `slope f a c` to `slope f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = lineMap a b r`. Then we prove lemmas like

```
lemma map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `lineMap (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

These inequalities can be used to restate `convexOn` in terms of monotonicity of the slope.
-/


variable {f : k -> E} {a b r : k}

local notation "c" => lineMap a b r

section
omit [IsStrictOrderedRing k]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_le_lineMap_iff_slope_le_slope_left` / 定理 `map_le_lineMap_iff_slope_le_slope_left`

English:
theorem map_le_lineMap_iff_slope_le_slope_left
  given: (h : 0 < r * (b - a))
  proof: by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [slope]; rw [slope]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [vadd_eq_add]; rw [smul_eq_mul]; rw [add_sub_cancel_right]; rw [smul_sub]; rw [smul_sub]; rw [smul_sub]; rw [sub_le_iff_le_add]; rw [mul_inv_rev]; rw [mul_smul]; rw [mul_smul]; rw [← smul_sub]; rw [← smul_sub]; rw [← smul_add]; rw [smul_smul]; rw [← mul_inv_rev]; rw [inv_smul_le_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne')]; rw [smul_add]; rw [smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]

中文:
定理 map_le_lineMap_iff_slope_le_slope_left
  条件: (h : 0 < r * (b - a))
  证明: by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [slope]; rw [slope]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [vadd_eq_add]; rw [smul_eq_mul]; rw [add_sub_cancel_right]; rw [smul_sub]; rw [smul_sub]; rw [smul_sub]; rw [sub_le_iff_le_add]; rw [mul_inv_rev]; rw [mul_smul]; rw [mul_smul]; rw [← smul_sub]; rw [← smul_sub]; rw [← smul_add]; rw [smul_smul]; rw [← mul_inv_rev]; rw [inv_smul_le_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne')]; rw [smul_add]; rw [smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]
-/
theorem map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c <= lineMap (f a) (f b) r ↔ slope f a c <= slope f a b := by
  rw [lineMap_apply]; rw [lineMap_apply]; rw [slope]; rw [slope]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [vadd_eq_add]; rw [smul_eq_mul]; rw [add_sub_cancel_right]; rw [smul_sub]; rw [smul_sub]; rw [smul_sub]; rw [sub_le_iff_le_add]; rw [mul_inv_rev]; rw [mul_smul]; rw [mul_smul]; rw [← smul_sub]; rw [← smul_sub]; rw [← smul_add]; rw [smul_smul]; rw [← mul_inv_rev]; rw [inv_smul_le_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne')]; rw [smul_add]; rw [smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_map_iff_slope_le_slope_left` / 定理 `lineMap_le_map_iff_slope_le_slope_left`

English:
theorem lineMap_le_map_iff_slope_le_slope_left
  given: (h : 0 < r * (b - a))
  proof: map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

中文:
定理 lineMap_le_map_iff_slope_le_slope_left
  条件: (h : 0 < r * (b - a))
  证明: map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

Depends on / 依赖: map_le_lineMap_iff_slope_le_slope_left
-/
theorem lineMap_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r <= f c ↔ slope f a b <= slope f a c :=
  map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_lt_lineMap_iff_slope_lt_slope_left` / 定理 `map_lt_lineMap_iff_slope_lt_slope_left`

English:
theorem map_lt_lineMap_iff_slope_lt_slope_left
  given: (h : 0 < r * (b - a))
  proof: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)

中文:
定理 map_lt_lineMap_iff_slope_lt_slope_left
  条件: (h : 0 < r * (b - a))
  证明: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)

Depends on / 依赖: lineMap_le_map_iff_slope_le_slope_left, lt_iff_lt_of_le_iff_le, map_le_lineMap_iff_slope_le_slope_left
-/
theorem map_lt_lineMap_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f a b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_map_iff_slope_lt_slope_left` / 定理 `lineMap_lt_map_iff_slope_lt_slope_left`

English:
theorem lineMap_lt_map_iff_slope_lt_slope_left
  given: (h : 0 < r * (b - a))
  proof: map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

中文:
定理 lineMap_lt_map_iff_slope_lt_slope_left
  条件: (h : 0 < r * (b - a))
  证明: map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

Depends on / 依赖: map_lt_lineMap_iff_slope_lt_slope_left
-/
theorem lineMap_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f a b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_le_lineMap_iff_slope_le_slope_right` / 定理 `map_le_lineMap_iff_slope_le_slope_right`

English:
theorem map_le_lineMap_iff_slope_le_slope_right
  given: (h : 0 < (1 - r) * (b - a))
  proof: by
  rw [← lineMap_apply_one_sub]; rw [← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap]; rw [sub_self]; rw [zero_sub]; rw [neg_mul_eq_mul_neg]; rw [neg_sub]; rw [le_inv_smul_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀]; rw [le_sub_comm]; rw [← neg_sub (f b)]; rw [smul_neg]; rw [neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'

中文:
定理 map_le_lineMap_iff_slope_le_slope_right
  条件: (h : 0 < (1 - r) * (b - a))
  证明: by
  rw [← lineMap_apply_one_sub]; rw [← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap]; rw [sub_self]; rw [zero_sub]; rw [neg_mul_eq_mul_neg]; rw [neg_sub]; rw [le_inv_smul_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀]; rw [le_sub_comm]; rw [← neg_sub (f b)]; rw [smul_neg]; rw [neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'

Depends on / 依赖: generalize, h.ne, le_inv_smul_iff_of_pos, le_sub_comm, lineMap_apply, lineMap_apply_one_sub, neg_add_eq_sub, neg_mul_eq_mul_neg, neg_sub, revert, right_ne_zero_of_mul, simp_rw, smul_eq_mul, smul_neg, smul_smul, sub_add_eq_sub_sub_swap, sub_self, vadd_eq_add, vsub_eq_sub, zero_sub
-/
theorem map_le_lineMap_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c <= lineMap (f a) (f b) r ↔ slope f a b <= slope f c b := by
  rw [← lineMap_apply_one_sub]; rw [← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap]; rw [sub_self]; rw [zero_sub]; rw [neg_mul_eq_mul_neg]; rw [neg_sub]; rw [le_inv_smul_iff_of_pos h]; rw [smul_smul]; rw [mul_inv_cancel_right₀]; rw [le_sub_comm]; rw [← neg_sub (f b)]; rw [smul_neg]; rw [neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_map_iff_slope_le_slope_right` / 定理 `lineMap_le_map_iff_slope_le_slope_right`

English:
theorem lineMap_le_map_iff_slope_le_slope_right
  given: (h : 0 < (1 - r) * (b - a))
  proof: map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

中文:
定理 lineMap_le_map_iff_slope_le_slope_right
  条件: (h : 0 < (1 - r) * (b - a))
  证明: map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

Depends on / 依赖: map_le_lineMap_iff_slope_le_slope_right
-/
theorem lineMap_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r <= f c ↔ slope f c b <= slope f a b :=
  map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_lt_lineMap_iff_slope_lt_slope_right` / 定理 `map_lt_lineMap_iff_slope_lt_slope_right`

English:
theorem map_lt_lineMap_iff_slope_lt_slope_right
  given: (h : 0 < (1 - r) * (b - a))
  proof: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)

中文:
定理 map_lt_lineMap_iff_slope_lt_slope_right
  条件: (h : 0 < (1 - r) * (b - a))
  证明: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)

Depends on / 依赖: lineMap_le_map_iff_slope_le_slope_right, lt_iff_lt_of_le_iff_le, map_le_lineMap_iff_slope_le_slope_right
-/
theorem map_lt_lineMap_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a b < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_map_iff_slope_lt_slope_right` / 定理 `lineMap_lt_map_iff_slope_lt_slope_right`

English:
theorem lineMap_lt_map_iff_slope_lt_slope_right
  given: (h : 0 < (1 - r) * (b - a))
  proof: map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

中文:
定理 lineMap_lt_map_iff_slope_lt_slope_right
  条件: (h : 0 < (1 - r) * (b - a))
  证明: map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

Depends on / 依赖: map_lt_lineMap_iff_slope_lt_slope_right
-/
theorem lineMap_lt_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a b :=
  map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_le_lineMap_iff_slope_le_slope` / 定理 `map_le_lineMap_iff_slope_le_slope`

English:
theorem map_le_lineMap_iff_slope_le_slope
  given: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  proof: by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab))]; rw [←
    lineMap_slope_lineMap_slope_lineMap f a b r]; rw [right_le_lineMap_iff_le h₁]

中文:
定理 map_le_lineMap_iff_slope_le_slope
  条件: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  证明: by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab))]; rw [←
    lineMap_slope_lineMap_slope_lineMap f a b r]; rw [right_le_lineMap_iff_le h₁]

Depends on / 依赖: lineMap_slope_lineMap_slope_lineMap, map_le_lineMap_iff_slope_le_slope_left, mul_pos, right_le_lineMap_iff_le, sub_pos
-/
theorem map_le_lineMap_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c <= lineMap (f a) (f b) r ↔ slope f a c <= slope f c b := by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab))]; rw [←
    lineMap_slope_lineMap_slope_lineMap f a b r]; rw [right_le_lineMap_iff_le h₁]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_le_map_iff_slope_le_slope` / 定理 `lineMap_le_map_iff_slope_le_slope`

English:
theorem lineMap_le_map_iff_slope_le_slope
  given: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  proof: map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁

中文:
定理 lineMap_le_map_iff_slope_le_slope
  条件: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  证明: map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁

Depends on / 依赖: map_le_lineMap_iff_slope_le_slope
-/
theorem lineMap_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r <= f c ↔ slope f c b <= slope f a c :=
  map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_lt_lineMap_iff_slope_lt_slope` / 定理 `map_lt_lineMap_iff_slope_lt_slope`

English:
theorem map_lt_lineMap_iff_slope_lt_slope
  given: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  proof: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)

中文:
定理 map_lt_lineMap_iff_slope_lt_slope
  条件: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  证明: lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)

Depends on / 依赖: lineMap_le_map_iff_slope_le_slope, lt_iff_lt_of_le_iff_le, map_le_lineMap_iff_slope_le_slope
-/
theorem map_lt_lineMap_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_lt_map_iff_slope_lt_slope` / 定理 `lineMap_lt_map_iff_slope_lt_slope`

English:
theorem lineMap_lt_map_iff_slope_lt_slope
  given: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  proof: map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

中文:
定理 lineMap_lt_map_iff_slope_lt_slope
  条件: (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1)
  证明: map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

Depends on / 依赖: map_lt_lineMap_iff_slope_lt_slope
-/
theorem lineMap_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

end LinearOrderedField


/--
lemma `slope_pos_iff` / 引理 `slope_pos_iff`

English:
lemma slope_pos_iff
  statement: {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  simp [slope, hb]

中文:
引理 slope_pos_iff
  结论: {𝕜} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  simp [slope, hb]
-/
lemma slope_pos_iff {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 -> 𝕜} {x₀ b : 𝕜} (hb : x₀ < b) :
    0 < slope f x₀ b ↔ f x₀ < f b := by
  simp [slope, hb]

/--
lemma `slope_pos_iff_gt` / 引理 `slope_pos_iff_gt`

English:
lemma slope_pos_iff_gt
  statement: {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  rw [slope_comm]; rw [slope_pos_iff hb]

中文:
引理 slope_pos_iff_gt
  结论: {𝕜} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  rw [slope_comm]; rw [slope_pos_iff hb]

Depends on / 依赖: slope_comm, slope_pos_iff
-/
lemma slope_pos_iff_gt {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 -> 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm]; rw [slope_pos_iff hb]

/--
lemma `pos_of_slope_pos` / 引理 `pos_of_slope_pos`

English:
lemma pos_of_slope_pos
  statement: {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  simp_all [slope]

中文:
引理 pos_of_slope_pos
  结论: {𝕜} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  simp_all [slope]
-/
lemma pos_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 -> 𝕜} {x₀ b : 𝕜}
    (hb : x₀ < b) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : 0 < f b := by
  simp_all [slope]

/--
lemma `neg_of_slope_pos` / 引理 `neg_of_slope_pos`

English:
lemma neg_of_slope_pos
  statement: {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb

中文:
引理 neg_of_slope_pos
  结论: {𝕜} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb

Depends on / 依赖: slope_pos_iff_gt
-/
lemma neg_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 -> 𝕜} {x₀ b : 𝕜}
    (hb : b < x₀) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : f b < 0 := by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb
