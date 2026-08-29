/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Data.NNReal.Defs

/-!
# WithZero

In this file we provide some basic API lemmas for the `WithZero` construction and we define
the morphism `WithZeroMultInt.toNNReal`.

## Main Definitions

* `WithZeroMultInt.toNNReal` : The `MonoidWithZeroHom` from `ℤᵐ⁰ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^((WithZero.unzero hx).toAdd)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `WithZeroMultInt.toNNReal_strictMono` : The map `withZeroMultIntToNNReal` is strictly
  monotone whenever `1 < e`.

## Tags

WithZero, multiplicative, nnreal
-/

@[expose] public section

assert_not_exists Finset

noncomputable section

open scoped NNReal

open Multiplicative WithZero

namespace WithZeroMulInt

/--
Definition of `toNNReal` / `toNNReal` 的定义

English:
definition toNNReal
  signature: {e : Real>=0} (he : e != 0)
  body: fun x => if hx : x = 0 then 0 else e ^ (WithZero.unzero hx).toAdd
  map_zero' := rfl
  map_one' := by rw [dif_neg one_ne_zero, unzero_coe (x := 1), toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      -- either x = 0 or y = 0
    

中文:
定义 toNN实数
  签名: {e : 实数>=0} (he : e != 0)
  定义体: fun x => if hx : x = 0 then 0 else e ^ (WithZero.unzero hx).toAdd
  map_zero' := rfl
  map_one' := by rw [dif_neg one_ne_zero, unzero_coe (x := 1), toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      -- either x = 0 or y = 0
    

Depends on / 依赖: WithZero, WithZero.unzero, unzero
-/
def toNNReal {e : Real>=0} (he : e != 0) : Intᵐ⁰ ->*₀ Real>=0 where
  toFun := fun x => if hx : x = 0 then 0 else e ^ (WithZero.unzero hx).toAdd
  map_zero' := rfl
  map_one' := by rw [dif_neg one_ne_zero, unzero_coe (x := 1), toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      -- either x = 0 or y = 0
      · rw [dif_pos hxy, dif_pos hx, zero_mul]
      · rw [dif_pos hxy, dif_pos hy, mul_zero]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      -- x ≠ 0 and y ≠ 0
      rw [dif_neg hxy]; rw [dif_neg hx]; rw [dif_neg hy]; rw [← zpow_add' (Or.inl he)]; rw [← toAdd_mul]
      congr
      rw [← WithZero.coe_inj]; rw [WithZero.coe_mul]; rw [coe_unzero hx]; rw [coe_unzero hy]; rw [coe_unzero hxy]

/--
theorem `toNNReal_pos_apply` / 定理 `toNNReal_pos_apply`

English:
theorem toNNReal_pos_apply
  given: {e : Real>=0} (he : e != 0) {x : Intᵐ⁰} (hx : x = 0)
  proof: by
  simp [toNNReal, hx]

中文:
定理 toNN实数_pos_apply
  条件: {e : 实数>=0} (he : e != 0) {x : 整数ᵐ⁰} (hx : x = 0)
  证明: by
  simp [toNNReal, hx]

Depends on / 依赖: toNNReal
-/
theorem toNNReal_pos_apply {e : Real>=0} (he : e != 0) {x : Intᵐ⁰} (hx : x = 0) :
    toNNReal he x = 0 := by
  simp [toNNReal, hx]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toNNReal_neg_apply` / 定理 `toNNReal_neg_apply`

English:
theorem toNNReal_neg_apply
  given: {e : Real>=0} (he : e != 0) {x : Intᵐ⁰} (hx : x != 0)
  proof: by
  simp [toNNReal, hx]

中文:
定理 toNN实数_neg_apply
  条件: {e : 实数>=0} (he : e != 0) {x : 整数ᵐ⁰} (hx : x != 0)
  证明: by
  simp [toNNReal, hx]

Depends on / 依赖: toNNReal
-/
theorem toNNReal_neg_apply {e : Real>=0} (he : e != 0) {x : Intᵐ⁰} (hx : x != 0) :
    toNNReal he x = e ^ (WithZero.unzero hx).toAdd := by
  simp [toNNReal, hx]

/--
theorem `toNNReal_ne_zero` / 定理 `toNNReal_ne_zero`

English:
theorem toNNReal_ne_zero
  given: {e : Real>=0} {m : Intᵐ⁰} (he : e != 0) (hm : m != 0)
  statement: toNNReal he m != 0
  proof: by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

中文:
定理 toNN实数_ne_zero
  条件: {e : 实数>=0} {m : 整数ᵐ⁰} (he : e != 0) (hm : m != 0)
  结论: toNN实数 he m != 0
  证明: by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

Depends on / 依赖: map_eq_zero, ne_eq, not_false_eq_true
-/
theorem toNNReal_ne_zero {e : Real>=0} {m : Intᵐ⁰} (he : e != 0) (hm : m != 0) : toNNReal he m != 0 := by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

/--
theorem `toNNReal_pos` / 定理 `toNNReal_pos`

English:
theorem toNNReal_pos
  given: {e : Real>=0} {m : Intᵐ⁰} (he : e != 0) (hm : m != 0)
  statement: 0 < toNNReal he m
  proof: (toNNReal_ne_zero he hm).pos

中文:
定理 toNN实数_pos
  条件: {e : 实数>=0} {m : 整数ᵐ⁰} (he : e != 0) (hm : m != 0)
  结论: 0 < toNN实数 he m
  证明: (toNNReal_ne_zero he hm).pos

Depends on / 依赖: toNNReal_ne_zero
-/
theorem toNNReal_pos {e : Real>=0} {m : Intᵐ⁰} (he : e != 0) (hm : m != 0) : 0 < toNNReal he m :=
  (toNNReal_ne_zero he hm).pos

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toNNReal_strictMono` / 定理 `toNNReal_strictMono`

English:
theorem toNNReal_strictMono
  given: {e : Real>=0} (he : 1 < e)
  proof: by
  intro x y
  cases y
  · simp
  cases x
  · simpa using! zpow_pos he.pos _
  · simp [toNNReal, he]

中文:
定理 toNN实数_strictMono
  条件: {e : 实数>=0} (he : 1 < e)
  证明: by
  intro x y
  cases y
  · simp
  cases x
  · simpa using! zpow_pos he.pos _
  · simp [toNNReal, he]

Depends on / 依赖: he.pos, toNNReal, zpow_pos
-/
theorem toNNReal_strictMono {e : Real>=0} (he : 1 < e) :
    StrictMono (toNNReal he.ne_zero) := by
  intro x y
  cases y
  · simp
  cases x
  · simpa using! zpow_pos he.pos _
  · simp [toNNReal, he]

/--
theorem `toNNReal_eq_one_iff` / 定理 `toNNReal_eq_one_iff`

English:
theorem toNNReal_eq_one_iff
  given: {e : Real>=0} (m : Intᵐ⁰) (he0 : e != 0) (he1 : e != 1)
  proof: by
  by_cases hm : m = 0
  · simp only [hm, map_zero, zero_ne_one]
  · refine ⟨fun h1 => ?_, fun h1 => h1 ▸ map_one _⟩
    rw [toNNReal_neg_apply he0 hm]; rw [zpow_eq_one_iff_right₀ _root_.zero_le he1]; rw [toAdd_eq_zero] at h1
    rw [← WithZero.coe_unzero hm]; rw [h1]; rw [coe_one]

中文:
定理 toNN实数_eq_one_iff
  条件: {e : 实数>=0} (m : 整数ᵐ⁰) (he0 : e != 0) (he1 : e != 1)
  证明: by
  by_cases hm : m = 0
  · simp only [hm, map_zero, zero_ne_one]
  · refine ⟨fun h1 => ?_, fun h1 => h1 ▸ map_one _⟩
    rw [toNNReal_neg_apply he0 hm]; rw [zpow_eq_one_iff_right₀ _root_.zero_le he1]; rw [toAdd_eq_zero] at h1
    rw [← WithZero.coe_unzero hm]; rw [h1]; rw [coe_one]

Depends on / 依赖: WithZero, WithZero.coe_unzero, _root_, _root_.zero_le, coe_one, coe_unzero, map_one, map_zero, toAdd_eq_zero, toNNReal_neg_apply, zero_le, zero_ne_one
-/
theorem toNNReal_eq_one_iff {e : Real>=0} (m : Intᵐ⁰) (he0 : e != 0) (he1 : e != 1) :
    toNNReal he0 m = 1 ↔ m = 1 := by
  by_cases hm : m = 0
  · simp only [hm, map_zero, zero_ne_one]
  · refine ⟨fun h1 => ?_, fun h1 => h1 ▸ map_one _⟩
    rw [toNNReal_neg_apply he0 hm]; rw [zpow_eq_one_iff_right₀ _root_.zero_le he1]; rw [toAdd_eq_zero] at h1
    rw [← WithZero.coe_unzero hm]; rw [h1]; rw [coe_one]

/--
theorem `toNNReal_lt_one_iff` / 定理 `toNNReal_lt_one_iff`

English:
theorem toNNReal_lt_one_iff
  given: {e : Real>=0} {m : Intᵐ⁰} (he : 1 < e)
  proof: by
  rw [← (toNNReal_strictMono he).lt_iff_lt]; rw [map_one]

中文:
定理 toNN实数_lt_one_iff
  条件: {e : 实数>=0} {m : 整数ᵐ⁰} (he : 1 < e)
  证明: by
  rw [← (toNNReal_strictMono he).lt_iff_lt]; rw [map_one]

Depends on / 依赖: lt_iff_lt, map_one, toNNReal_strictMono
-/
theorem toNNReal_lt_one_iff {e : Real>=0} {m : Intᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m < 1 ↔ m < 1 := by
  rw [← (toNNReal_strictMono he).lt_iff_lt]; rw [map_one]

/--
theorem `toNNReal_le_one_iff` / 定理 `toNNReal_le_one_iff`

English:
theorem toNNReal_le_one_iff
  given: {e : Real>=0} {m : Intᵐ⁰} (he : 1 < e)
  proof: by
  rw [← (toNNReal_strictMono he).le_iff_le]; rw [map_one]

中文:
定理 toNN实数_le_one_iff
  条件: {e : 实数>=0} {m : 整数ᵐ⁰} (he : 1 < e)
  证明: by
  rw [← (toNNReal_strictMono he).le_iff_le]; rw [map_one]

Depends on / 依赖: le_iff_le, map_one, toNNReal_strictMono
-/
theorem toNNReal_le_one_iff {e : Real>=0} {m : Intᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m <= 1 ↔ m <= 1 := by
  rw [← (toNNReal_strictMono he).le_iff_le]; rw [map_one]

end WithZeroMulInt
