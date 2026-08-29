/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `GaussianInt.toComplex` into the complex numbers is also defined in this file.

## See also

See `NumberTheory.Zsqrtd.QuadraticReciprocity` for:
* `prime_iff_mod_four_eq_three_of_nat_prime`:
  A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notation

This file uses the local notation `ℤ[i]` for `GaussianInt`

## Implementation notes

Gaussian integers are implemented using the more general definition `Zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `Zsqrtd` can easily be used.
-/

@[expose] public section


open Zsqrtd Complex

open scoped ComplexConjugate

/--
Definition of `GaussianInt` / `GaussianInt` 的定义

English:
abbreviation GaussianInt
  signature: : Type
  body: Zsqrtd (-1)

local notation "Int[i]" => GaussianInt

中文:
缩写 GaussianInt
  签名: : Type
  定义体: Zsqrtd (-1)

local notation "Int[i]" => GaussianInt

Depends on / 依赖: Zsqrtd
-/
abbrev GaussianInt : Type :=
  Zsqrtd (-1)

local notation "Int[i]" => GaussianInt

namespace GaussianInt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr Int[i]
  body: ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

中文:
实例 :
  签名: Repr 整数[i]
  定义体: ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

Depends on / 依赖: x.im, x.re
-/
instance : Repr Int[i] :=
  ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing Int[i]
  body: Zsqrtd.commRing

中文:
实例 instCommRing
  签名: : CommRing 整数[i]
  定义体: Zsqrtd.commRing

Depends on / 依赖: Zsqrtd, Zsqrtd.commRing, commRing
-/
instance instCommRing : CommRing Int[i] :=
  Zsqrtd.commRing

section

attribute [-instance] Complex.instField -- Avoid making things noncomputable unnecessarily.

/--
Definition of `toComplex` / `toComplex` 的定义

English:
definition toComplex
  signature: : Int[i] ->+* Complex
  body: Zsqrtd.lift ⟨I, by simp⟩

中文:
定义 toComplex
  签名: : 整数[i] ->+* Complex
  定义体: Zsqrtd.lift ⟨I, by simp⟩

Depends on / 依赖: Zsqrtd, Zsqrtd.lift
-/
def toComplex : Int[i] ->+* Complex :=
  Zsqrtd.lift ⟨I, by simp⟩

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Int[i] Complex
  body: ⟨toComplex⟩

中文:
实例 :
  签名: Coe 整数[i] Complex
  定义体: ⟨toComplex⟩

Depends on / 依赖: toComplex
-/
instance : Coe Int[i] Complex :=
  ⟨toComplex⟩

/--
theorem `toComplex_def` / 定理 `toComplex_def`

English:
theorem toComplex_def
  given: (x : Int[i])
  statement: (x : Complex) = x.re + x.im * I
  proof: rfl

中文:
定理 toComplex_def
  条件: (x : 整数[i])
  结论: (x : Complex) = x.re + x.im * I
  证明: rfl
-/
theorem toComplex_def (x : Int[i]) : (x : Complex) = x.re + x.im * I :=
  rfl

/--
theorem `toComplex_def'` / 定理 `toComplex_def'`

English:
theorem toComplex_def'
  given: (x y : Int)
  statement: ((⟨x, y⟩ : Int[i]) : Complex) = x + y * I
  proof: by simp [toComplex_def]

中文:
定理 toComplex_def'
  条件: (x y : 整数)
  结论: ((⟨x, y⟩ : 整数[i]) : Complex) = x + y * I
  证明: by simp [toComplex_def]

Depends on / 依赖: toComplex_def
-/
theorem toComplex_def' (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex) = x + y * I := by simp [toComplex_def]

/--
theorem `toComplex_def₂` / 定理 `toComplex_def₂`

English:
theorem toComplex_def₂
  given: (x : Int[i])
  statement: (x : Complex) = ⟨x.re, x.im⟩
  proof: by
  apply Complex.ext <;> simp [toComplex_def]

@[simp]

中文:
定理 toComplex_def₂
  条件: (x : 整数[i])
  结论: (x : Complex) = ⟨x.re, x.im⟩
  证明: by
  apply Complex.ext <;> simp [toComplex_def]

@[simp]

Depends on / 依赖: Complex.ext, Kernel, isFiniteKernel_of_isFiniteKernel_snd, toComplex_def
-/
theorem toComplex_def₂ (x : Int[i]) : (x : Complex) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [toComplex_def]

@[simp]
/--
theorem `intCast_re` / 定理 `intCast_re`

English:
theorem intCast_re
  given: (x : Int[i])
  statement: ((x.re : Int) : Real) = (x : Complex).re
  proof: by simp [toComplex_def]

@[simp]

中文:
定理 intCast_re
  条件: (x : 整数[i])
  结论: ((x.re : 整数) : 实数) = (x : Complex).re
  证明: by simp [toComplex_def]

@[simp]

Depends on / 依赖: toComplex_def
-/
theorem intCast_re (x : Int[i]) : ((x.re : Int) : Real) = (x : Complex).re := by simp [toComplex_def]

@[simp]
/--
theorem `intCast_im` / 定理 `intCast_im`

English:
theorem intCast_im
  given: (x : Int[i])
  statement: ((x.im : Int) : Real) = (x : Complex).im
  proof: by simp [toComplex_def]

@[simp]

中文:
定理 intCast_im
  条件: (x : 整数[i])
  结论: ((x.im : 整数) : 实数) = (x : Complex).im
  证明: by simp [toComplex_def]

@[simp]

Depends on / 依赖: toComplex_def
-/
theorem intCast_im (x : Int[i]) : ((x.im : Int) : Real) = (x : Complex).im := by simp [toComplex_def]

@[simp]
/--
theorem `re_toComplex` / 定理 `re_toComplex`

English:
theorem re_toComplex
  given: (x y : Int)
  statement: ((⟨x, y⟩ : Int[i]) : Complex).re = x
  proof: by simp [toComplex_def]

@[simp]

中文:
定理 re_toComplex
  条件: (x y : 整数)
  结论: ((⟨x, y⟩ : 整数[i]) : Complex).re = x
  证明: by simp [toComplex_def]

@[simp]

Depends on / 依赖: toComplex_def
-/
theorem re_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex).re = x := by simp [toComplex_def]

@[simp]
/--
theorem `im_toComplex` / 定理 `im_toComplex`

English:
theorem im_toComplex
  given: (x y : Int)
  statement: ((⟨x, y⟩ : Int[i]) : Complex).im = y
  proof: by simp [toComplex_def]

中文:
定理 im_toComplex
  条件: (x y : 整数)
  结论: ((⟨x, y⟩ : 整数[i]) : Complex).im = y
  证明: by simp [toComplex_def]

Depends on / 依赖: toComplex_def
-/
theorem im_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex).im = y := by simp [toComplex_def]

/--
theorem `toComplex_add` / 定理 `toComplex_add`

English:
theorem toComplex_add
  given: (x y : Int[i])
  statement: ((x + y : Int[i]) : Complex) = x + y
  proof: toComplex.map_add _ _

中文:
定理 toComplex_add
  条件: (x y : 整数[i])
  结论: ((x + y : 整数[i]) : Complex) = x + y
  证明: toComplex.map_add _ _

Depends on / 依赖: map_add, toComplex, toComplex.map_add
-/
theorem toComplex_add (x y : Int[i]) : ((x + y : Int[i]) : Complex) = x + y :=
  toComplex.map_add _ _

/--
theorem `toComplex_mul` / 定理 `toComplex_mul`

English:
theorem toComplex_mul
  given: (x y : Int[i])
  statement: ((x * y : Int[i]) : Complex) = x * y
  proof: toComplex.map_mul _ _

中文:
定理 toComplex_mul
  条件: (x y : 整数[i])
  结论: ((x * y : 整数[i]) : Complex) = x * y
  证明: toComplex.map_mul _ _

Depends on / 依赖: map_mul, toComplex, toComplex.map_mul
-/
theorem toComplex_mul (x y : Int[i]) : ((x * y : Int[i]) : Complex) = x * y :=
  toComplex.map_mul _ _

/--
theorem `toComplex_one` / 定理 `toComplex_one`

English:
theorem toComplex_one
  statement: ((1 : Int[i]) : Complex) = 1
  proof: toComplex.map_one

中文:
定理 toComplex_one
  结论: ((1 : 整数[i]) : Complex) = 1
  证明: toComplex.map_one

Depends on / 依赖: map_one, toComplex, toComplex.map_one
-/
theorem toComplex_one : ((1 : Int[i]) : Complex) = 1 :=
  toComplex.map_one

/--
theorem `toComplex_zero` / 定理 `toComplex_zero`

English:
theorem toComplex_zero
  statement: ((0 : Int[i]) : Complex) = 0
  proof: toComplex.map_zero

中文:
定理 toComplex_zero
  结论: ((0 : 整数[i]) : Complex) = 0
  证明: toComplex.map_zero

Depends on / 依赖: infer_instance, map_zero, toComplex, toComplex.map_zero
-/
theorem toComplex_zero : ((0 : Int[i]) : Complex) = 0 :=
  toComplex.map_zero

/--
theorem `toComplex_neg` / 定理 `toComplex_neg`

English:
theorem toComplex_neg
  given: (x : Int[i])
  statement: ((-x : Int[i]) : Complex) = -x
  proof: toComplex.map_neg _

中文:
定理 toComplex_neg
  条件: (x : 整数[i])
  结论: ((-x : 整数[i]) : Complex) = -x
  证明: toComplex.map_neg _

Depends on / 依赖: infer_instance, map_neg, toComplex, toComplex.map_neg
-/
theorem toComplex_neg (x : Int[i]) : ((-x : Int[i]) : Complex) = -x :=
  toComplex.map_neg _

/--
theorem `toComplex_sub` / 定理 `toComplex_sub`

English:
theorem toComplex_sub
  given: (x y : Int[i])
  statement: ((x - y : Int[i]) : Complex) = x - y
  proof: toComplex.map_sub _ _

@[simp]

中文:
定理 toComplex_sub
  条件: (x y : 整数[i])
  结论: ((x - y : 整数[i]) : Complex) = x - y
  证明: toComplex.map_sub _ _

@[simp]

Depends on / 依赖: infer_instance, map_sub, toComplex, toComplex.map_sub
-/
theorem toComplex_sub (x y : Int[i]) : ((x - y : Int[i]) : Complex) = x - y :=
  toComplex.map_sub _ _

@[simp]
/--
theorem `toComplex_star` / 定理 `toComplex_star`

English:
theorem toComplex_star
  given: (x : Int[i])
  statement: ((star x : Int[i]) : Complex) = conj (x : Complex)
  proof: by
  rw [toComplex_def₂]; rw [toComplex_def₂]
  exact congr_arg₂ _ rfl (Int.cast_neg _)

@[simp]

中文:
定理 toComplex_star
  条件: (x : 整数[i])
  结论: ((star x : 整数[i]) : Complex) = conj (x : Complex)
  证明: by
  rw [toComplex_def₂]; rw [toComplex_def₂]
  exact congr_arg₂ _ rfl (Int.cast_neg _)

@[simp]

Depends on / 依赖: Int.cast_neg, cast_neg, infer_instance
-/
theorem toComplex_star (x : Int[i]) : ((star x : Int[i]) : Complex) = conj (x : Complex) := by
  rw [toComplex_def₂]; rw [toComplex_def₂]
  exact congr_arg₂ _ rfl (Int.cast_neg _)

@[simp]
/--
theorem `toComplex_inj` / 定理 `toComplex_inj`

English:
theorem toComplex_inj
  given: {x y : Int[i]}
  statement: (x : Complex) = y ↔ x = y
  proof: by
  cases x; cases y; simp [toComplex_def₂]

中文:
定理 toComplex_inj
  条件: {x y : 整数[i]}
  结论: (x : Complex) = y ↔ x = y
  证明: by
  cases x; cases y; simp [toComplex_def₂]

Depends on / 依赖: infer_instance, sectL_apply
-/
theorem toComplex_inj {x y : Int[i]} : (x : Complex) = y ↔ x = y := by
  cases x; cases y; simp [toComplex_def₂]

/--
lemma `toComplex_injective` / 引理 `toComplex_injective`

English:
lemma toComplex_injective
  statement: Function.Injective GaussianInt.toComplex
  proof: fun ⦃_ _⦄ => toComplex_inj.mp

@[simp]

中文:
引理 toComplex_injective
  结论: Function.Injective Gaussian整数.toComplex
  证明: fun ⦃_ _⦄ => toComplex_inj.mp

@[simp]

Depends on / 依赖: IsMarkovKernel, Kernel, toComplex_inj, toComplex_inj.mp
-/
lemma toComplex_injective : Function.Injective GaussianInt.toComplex :=
  fun ⦃_ _⦄ => toComplex_inj.mp

@[simp]
/--
theorem `toComplex_eq_zero` / 定理 `toComplex_eq_zero`

English:
theorem toComplex_eq_zero
  given: {x : Int[i]}
  statement: (x : Complex) = 0 ↔ x = 0
  proof: by
  rw [← toComplex_zero]; rw [toComplex_inj]

@[simp]

中文:
定理 toComplex_eq_zero
  条件: {x : 整数[i]}
  结论: (x : Complex) = 0 ↔ x = 0
  证明: by
  rw [← toComplex_zero]; rw [toComplex_inj]

@[simp]

Depends on / 依赖: toComplex_inj, toComplex_zero
-/
theorem toComplex_eq_zero {x : Int[i]} : (x : Complex) = 0 ↔ x = 0 := by
  rw [← toComplex_zero]; rw [toComplex_inj]

@[simp]
/--
theorem `intCast_real_norm` / 定理 `intCast_real_norm`

English:
theorem intCast_real_norm
  given: (x : Int[i])
  statement: (x.norm : Real) = Complex.normSq (x : Complex)
  proof: by
  rw [Zsqrtd.norm]; rw [normSq]; simp

@[simp]

中文:
定理 intCast_real_norm
  条件: (x : 整数[i])
  结论: (x.norm : 实数) = Complex.normSq (x : Complex)
  证明: by
  rw [Zsqrtd.norm]; rw [normSq]; simp

@[simp]

Depends on / 依赖: Zsqrtd, Zsqrtd.norm, normSq
-/
theorem intCast_real_norm (x : Int[i]) : (x.norm : Real) = Complex.normSq (x : Complex) := by
  rw [Zsqrtd.norm]; rw [normSq]; simp

@[simp]
/--
theorem `intCast_complex_norm` / 定理 `intCast_complex_norm`

English:
theorem intCast_complex_norm
  given: (x : Int[i])
  statement: (x.norm : Complex) = Complex.normSq (x : Complex)
  proof: by
  cases x; rw [Zsqrtd.norm, normSq]; simp

中文:
定理 intCast_complex_norm
  条件: (x : 整数[i])
  结论: (x.norm : Complex) = Complex.normSq (x : Complex)
  证明: by
  cases x; rw [Zsqrtd.norm, normSq]; simp

Depends on / 依赖: Zsqrtd, Zsqrtd.norm, normSq
-/
theorem intCast_complex_norm (x : Int[i]) : (x.norm : Complex) = Complex.normSq (x : Complex) := by
  cases x; rw [Zsqrtd.norm, normSq]; simp

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (x : Int[i])
  statement: 0 <= norm x
  proof: Zsqrtd.norm_nonneg (by simp) _

@[simp]

中文:
定理 norm_nonneg
  条件: (x : 整数[i])
  结论: 0 <= norm x
  证明: Zsqrtd.norm_nonneg (by simp) _

@[simp]

Depends on / 依赖: Zsqrtd, Zsqrtd.norm_nonneg, norm_nonneg
-/
theorem norm_nonneg (x : Int[i]) : 0 <= norm x :=
  Zsqrtd.norm_nonneg (by simp) _

@[simp]
/--
theorem `norm_eq_zero` / 定理 `norm_eq_zero`

English:
theorem norm_eq_zero
  given: {x : Int[i]}
  statement: norm x = 0 ↔ x = 0
  proof: by rw [← Int.cast_inj (α := Real)]; simp

中文:
定理 norm_eq_zero
  条件: {x : 整数[i]}
  结论: norm x = 0 ↔ x = 0
  证明: by rw [← Int.cast_inj (α := Real)]; simp

Depends on / 依赖: Int.cast_inj, cast_inj, infer_instance
-/
theorem norm_eq_zero {x : Int[i]} : norm x = 0 ↔ x = 0 := by rw [← Int.cast_inj (α := Real)]; simp

/--
theorem `norm_pos` / 定理 `norm_pos`

English:
theorem norm_pos
  given: {x : Int[i]}
  statement: 0 < norm x ↔ x != 0
  proof: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; rw [norm_eq_zero]; simp [norm_nonneg]

中文:
定理 norm_pos
  条件: {x : 整数[i]}
  结论: 0 < norm x ↔ x != 0
  证明: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; rw [norm_eq_zero]; simp [norm_nonneg]

Depends on / 依赖: eq_comm, infer_instance, lt_iff_le_and_ne, norm_eq_zero, norm_nonneg
-/
theorem norm_pos {x : Int[i]} : 0 < norm x ↔ x != 0 := by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; rw [norm_eq_zero]; simp [norm_nonneg]

/--
theorem `abs_natCast_norm` / 定理 `abs_natCast_norm`

English:
theorem abs_natCast_norm
  given: (x : Int[i])
  statement: (x.norm.natAbs : Int) = x.norm
  proof: Int.natAbs_of_nonneg (norm_nonneg _)

中文:
定理 abs_natCast_norm
  条件: (x : 整数[i])
  结论: (x.norm.natAbs : 整数) = x.norm
  证明: Int.natAbs_of_nonneg (norm_nonneg _)

Depends on / 依赖: Int.natAbs_of_nonneg, infer_instance, natAbs_of_nonneg, norm_nonneg
-/
theorem abs_natCast_norm (x : Int[i]) : (x.norm.natAbs : Int) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

/--
theorem `natCast_natAbs_norm` / 定理 `natCast_natAbs_norm`

English:
theorem natCast_natAbs_norm
  given: {α : Type*} [AddGroupWithOne α] (x : Int[i])
  proof: by
  simp

中文:
定理 natCast_natAbs_norm
  条件: {α : 类型} [AddGroupWithOne α] (x : 整数[i])
  证明: by
  simp

Depends on / 依赖: infer_instance
-/
theorem natCast_natAbs_norm {α : Type*} [AddGroupWithOne α] (x : Int[i]) :
    (x.norm.natAbs : α) = x.norm := by
  simp

/--
theorem `natAbs_norm_eq` / 定理 `natAbs_norm_eq`

English:
theorem natAbs_norm_eq
  given: (x : Int[i])
  proof: by
  zify
  rw [abs_norm (by simp)]
  simp [Zsqrtd.norm]

中文:
定理 natAbs_norm_eq
  条件: (x : 整数[i])
  证明: by
  zify
  rw [abs_norm (by simp)]
  simp [Zsqrtd.norm]

Depends on / 依赖: Zsqrtd, Zsqrtd.norm, abs_norm, infer_instance, sectR_apply
-/
theorem natAbs_norm_eq (x : Int[i]) :
    x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs := by
  zify
  rw [abs_norm (by simp)]
  simp [Zsqrtd.norm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div Int[i]
  body: ⟨fun x y =>
    let n := (norm y : Rat)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : Rat), round ((x * c).im * n : Rat)⟩⟩

中文:
实例 :
  签名: Div 整数[i]
  定义体: ⟨fun x y =>
    let n := (norm y : Rat)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : Rat), round ((x * c).im * n : Rat)⟩⟩

Depends on / 依赖: IsMarkovKernel, Kernel
-/
instance : Div Int[i] :=
  ⟨fun x y =>
    let n := (norm y : Rat)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : Rat), round ((x * c).im * n : Rat)⟩⟩

/--
theorem `div_def` / 定理 `div_def`

English:
theorem div_def
  given: (x y : Int[i])
  proof: show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]

中文:
定理 div_def
  条件: (x y : 整数[i])
  证明: show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]

Depends on / 依赖: Zsqrtd, Zsqrtd.mk, div_eq_mul_inv
-/
theorem div_def (x y : Int[i]) :
    x / y = ⟨round ((x * star y).re / norm y : Rat), round ((x * star y).im / norm y : Rat)⟩ :=
  show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]

/--
theorem `toComplex_re_div` / 定理 `toComplex_re_div`

English:
theorem toComplex_re_div
  given: (x y : Int[i])
  statement: ((x / y : Int[i]) : Complex).re = round (x / y : Complex).re
  proof: by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

中文:
定理 toComplex_re_div
  条件: (x y : 整数[i])
  结论: ((x / y : 整数[i]) : Complex).re = round (x / y : Complex).re
  证明: by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

Depends on / 依赖: Rat.round_cast, add_mul, div_def, div_eq_mul_inv, mul_assoc, round_cast
-/
theorem toComplex_re_div (x y : Int[i]) : ((x / y : Int[i]) : Complex).re = round (x / y : Complex).re := by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

/--
theorem `toComplex_im_div` / 定理 `toComplex_im_div`

English:
theorem toComplex_im_div
  given: (x y : Int[i])
  statement: ((x / y : Int[i]) : Complex).im = round (x / y : Complex).im
  proof: by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

中文:
定理 toComplex_im_div
  条件: (x y : 整数[i])
  结论: ((x / y : 整数[i]) : Complex).im = round (x / y : Complex).im
  证明: by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

Depends on / 依赖: Rat.round_cast, add_mul, div_def, div_eq_mul_inv, mul_assoc, round_cast
-/
theorem toComplex_im_div (x y : Int[i]) : ((x / y : Int[i]) : Complex).im = round (x / y : Complex).im := by
  rw [div_def]; rw [← @Rat.round_cast Real _ _]; rw [← @Rat.round_cast Real _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

/--
theorem `normSq_le_normSq_of_re_le_of_im_le` / 定理 `normSq_le_normSq_of_re_le_of_im_le`

English:
theorem normSq_le_normSq_of_re_le_of_im_le
  statement: {x y : Complex} (hre : |x.re| <= |y.re|)
  proof: by
  simp only [normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

中文:
定理 normSq_le_normSq_of_re_le_of_im_le
  结论: {x y : Complex} (hre : |x.re| <= |y.re|)
  证明: by
  simp only [normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

Depends on / 依赖: normSq_apply, sq_le_sq, sq_le_sq.mpr
-/
theorem normSq_le_normSq_of_re_le_of_im_le {x y : Complex} (hre : |x.re| <= |y.re|)
    (him : |x.im| <= |y.im|) : normSq x <= normSq y := by
  simp only [normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

/--
theorem `normSq_div_sub_div_lt_one` / 定理 `normSq_div_sub_div_lt_one`

English:
theorem normSq_div_sub_div_lt_one
  given: (x y : Int[i])
  proof: calc
    Complex.normSq ((x / y : Complex) - ((x / y : Int[i]) : Complex))
    _ = Complex.normSq
      ((x / y : Complex).re - ((x / y : Int[i]) : Complex).re + ((x / y : Complex).im - ((x / y : Int[i]) : Complex).im) *
        I : Complex) :=
congr_arg _ by apply Complex.ext <;> simp
    _ <= Comp

中文:
定理 normSq_div_sub_div_lt_one
  条件: (x y : 整数[i])
  证明: calc
    Complex.normSq ((x / y : Complex) - ((x / y : Int[i]) : Complex))
    _ = Complex.normSq
      ((x / y : Complex).re - ((x / y : Int[i]) : Complex).re + ((x / y : Complex).im - ((x / y : Int[i]) : Complex).im) *
        I : Complex) :=
congr_arg _ by apply Complex.ext <;> simp
    _ <= Comp

Depends on / 依赖: Complex.ext, Complex.normSq, abs_of_nonneg, abs_sub_round, congr_arg, normSq, normSq_le_normSq_of_re_le_of_im_le, toComplex_re_div
-/
theorem normSq_div_sub_div_lt_one (x y : Int[i]) :
    Complex.normSq ((x / y : Complex) - ((x / y : Int[i]) : Complex)) < 1 :=
  calc
    Complex.normSq ((x / y : Complex) - ((x / y : Int[i]) : Complex))
    _ = Complex.normSq
      ((x / y : Complex).re - ((x / y : Int[i]) : Complex).re + ((x / y : Complex).im - ((x / y : Int[i]) : Complex).im) *
        I : Complex) :=
congr_arg _ by apply Complex.ext <;> simp
    _ <= Complex.normSq (1 / 2 + 1 / 2 * I) := by
      have : |(2⁻¹ : Real)| = 2⁻¹ := abs_of_nonneg (by simp)
      exact normSq_le_normSq_of_re_le_of_im_le
        (by rw [toComplex_re_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : Complex).re)
        (by rw [toComplex_im_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : Complex).im)
    _ < 1 := by simp [normSq]; norm_num

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mod Int[i]
  body: ⟨fun x y => x - y * (x / y)⟩

中文:
实例 :
  签名: Mod 整数[i]
  定义体: ⟨fun x y => x - y * (x / y)⟩
-/
instance : Mod Int[i] :=
  ⟨fun x y => x - y * (x / y)⟩

/--
theorem `mod_def` / 定理 `mod_def`

English:
theorem mod_def
  given: (x y : Int[i])
  statement: x % y = x - y * (x / y)
  proof: rfl

中文:
定理 mod_def
  条件: (x y : 整数[i])
  结论: x % y = x - y * (x / y)
  证明: rfl
-/
theorem mod_def (x y : Int[i]) : x % y = x - y * (x / y) :=
  rfl

/--
theorem `norm_mod_lt` / 定理 `norm_mod_lt`

English:
theorem norm_mod_lt
  given: (x : Int[i]) {y : Int[i]} (hy : y != 0)
  statement: (x % y).norm < y.norm
  proof: have : (y : Complex) != 0 := by rwa [Ne, ← toComplex_zero, toComplex_inj]
(@Int.cast_lt Real _ _ _ _).1
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : Int[i]) : Complex) := by simp [mod_def]
      _ = Complex.normSq (y : Complex) * Complex.normSq (x / y - (x / y : Int[i]) :

中文:
定理 norm_mod_lt
  条件: (x : 整数[i]) {y : 整数[i]} (hy : y != 0)
  结论: (x % y).norm < y.norm
  证明: have : (y : Complex) != 0 := by rwa [Ne, ← toComplex_zero, toComplex_inj]
(@Int.cast_lt Real _ _ _ _).1
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : Int[i]) : Complex) := by simp [mod_def]
      _ = Complex.normSq (y : Complex) * Complex.normSq (x / y - (x / y : Int[i]) :

Depends on / 依赖: Complex.normSq, Int.cast_lt, Zsqrtd, Zsqrtd.norm, cast_lt, mod_def, mul_lt_mul_of_pos_left, mul_sub, normSq, normSq_div_sub_div_lt_one, normSq_mul, normSq_pos, toComplex_inj, toComplex_zero
-/
theorem norm_mod_lt (x : Int[i]) {y : Int[i]} (hy : y != 0) : (x % y).norm < y.norm :=
  have : (y : Complex) != 0 := by rwa [Ne, ← toComplex_zero, toComplex_inj]
(@Int.cast_lt Real _ _ _ _).1
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : Int[i]) : Complex) := by simp [mod_def]
      _ = Complex.normSq (y : Complex) * Complex.normSq (x / y - (x / y : Int[i]) : Complex) := by
        rw [← normSq_mul]; rw [mul_sub]; rw [mul_div_cancel₀ _ this]
      _ < Complex.normSq (y : Complex) * 1 :=
        (mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one _ _) (normSq_pos.2 this))
      _ = Zsqrtd.norm y := by simp

/--
theorem `natAbs_norm_mod_lt` / 定理 `natAbs_norm_mod_lt`

English:
theorem natAbs_norm_mod_lt
  given: (x : Int[i]) {y : Int[i]} (hy : y != 0)
  proof: Int.ofNat_lt.1 by simp [norm_mod_lt x hy]

中文:
定理 natAbs_norm_mod_lt
  条件: (x : 整数[i]) {y : 整数[i]} (hy : y != 0)
  证明: Int.ofNat_lt.1 by simp [norm_mod_lt x hy]

Depends on / 依赖: Int.ofNat_lt, norm_mod_lt, ofNat_lt
-/
theorem natAbs_norm_mod_lt (x : Int[i]) {y : Int[i]} (hy : y != 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
Int.ofNat_lt.1 by simp [norm_mod_lt x hy]

/--
theorem `norm_le_norm_mul_left` / 定理 `norm_le_norm_mul_left`

English:
theorem norm_le_norm_mul_left
  given: (x : Int[i]) {y : Int[i]} (hy : y != 0)
  proof: by
  rw [Zsqrtd.norm_mul]; rw [Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))

中文:
定理 norm_le_norm_mul_left
  条件: (x : 整数[i]) {y : 整数[i]} (hy : y != 0)
  证明: by
  rw [Zsqrtd.norm_mul]; rw [Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))

Depends on / 依赖: Int.add_one_le_of_lt, Int.natAbs_mul, Int.ofNat_le, Nat.zero_le, Zsqrtd, Zsqrtd.norm_mul, abs_natCast_norm, add_one_le_of_lt, le_mul_of_one_le_right, natAbs_mul, norm_mul, norm_pos, ofNat_le, zero_le
-/
theorem norm_le_norm_mul_left (x : Int[i]) {y : Int[i]} (hy : y != 0) :
    (norm x).natAbs <= (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul]; rw [Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial Int[i]
  body: ⟨⟨0, 1, by decide⟩⟩

中文:
实例 instNontrivial
  签名: : Nontrivial 整数[i]
  定义体: ⟨⟨0, 1, by decide⟩⟩
-/
instance instNontrivial : Nontrivial Int[i] :=
  ⟨⟨0, 1, by decide⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EuclideanDomain Int[i]
  body: { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainde

中文:
实例 :
  签名: EuclideanDomain 整数[i]
  定义体: { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainde

Depends on / 依赖: GaussianInt, GaussianInt.instCommRing, GaussianInt.instNontrivial, Int.natAbs, div_def, instCommRing, instNontrivial, measure, mod_def, mul_left_not_lt, natAbs, natAbs_norm_mod_lt, norm_le_norm_mul_left, not_lt_of_ge, quotient, quotient_mul_add_remainder_eq, quotient_zero, r_wellFounded, remainder, remainder_lt
-/
instance : EuclideanDomain Int[i] :=
  { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
mul_left_not_lt := fun a _ hb0 => not_lt_of_ge norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

/--
theorem `sq_add_sq_of_nat_prime_of_not_irreducible` / 定理 `sq_add_sq_of_nat_prime_of_not_irreducible`

English:
theorem sq_add_sq_of_nat_prime_of_not_irreducible
  statement: (p : Nat) [hp : Fact p.Prime]
  proof: have hpu : ¬IsUnit (p : Int[i]) :=
mt norm_eq_one_iff.2 by
      rw [norm_natCast]; rw [Int.natAbs_mul]; rw [mul_eq_one]
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : exists a b, (p : Int[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_o

中文:
定理 sq_add_sq_of_nat_prime_of_not_irreducible
  结论: (p : 自然数) [hp : Fact p.Prime]
  证明: have hpu : ¬IsUnit (p : Int[i]) :=
mt norm_eq_one_iff.2 by
      rw [norm_natCast]; rw [Int.natAbs_mul]; rw [mul_eq_one]
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : exists a b, (p : Int[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_o

Depends on / 依赖: Int.natAbs_mul, Int.natCast_inj, Int.natCast_pow, IsUnit, irreducible_iff, mul_eq_one, mul_eq_prime_sq_iff, natAbs, natAbs_mul, natCast_inj, natCast_pow, ne_of_lt, norm_eq_one_iff, norm_natCast, not_forall, not_or, one_lt
-/
theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : Nat) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : Int[i])) : exists a b, a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : Int[i]) :=
mt norm_eq_one_iff.2 by
      rw [norm_natCast]; rw [Int.natAbs_mul]; rw [mul_eq_one]
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : exists a b, (p : Int[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.natCast_inj]; rw [Int.natCast_pow]; rw [sq]; rw [← @norm_natCast (-1)]; rw [hpab]; simp).1
  ⟨a.re.natAbs, a.im.natAbs, by simpa [natAbs_norm_eq, sq] using hnap⟩

end GaussianInt
