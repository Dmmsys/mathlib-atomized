/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.NormTrace

/-!

# Fractional ideal norms

This file defines the absolute ideal norm of a fractional ideal `I : FractionalIdeal R⁰ K` where
`K` is a fraction field of `R`. The norm is defined by
`FractionalIdeal.absNorm I = Ideal.absNorm I.num / |Algebra.norm ℤ I.den|` where `I.num` is an
ideal of `R` and `I.den` an element of `R⁰` such that `I.den • I = I.num`.

## Main definitions and results

* `FractionalIdeal.absNorm`: the norm as a zero-preserving morphism with values in `ℚ`.
* `FractionalIdeal.absNorm_eq'`: the value of the norm does not depend on the choice of
  `I.num` and `I.den`.
* `FractionalIdeal.abs_det_basis_change`: the norm is given by the determinant
  of the basis change matrix.
* `FractionalIdeal.absNorm_span_singleton`: the norm of a principal fractional ideal is the
  norm of its generator
-/

@[expose] public section

open Module
open scoped Pointwise nonZeroDivisors

namespace FractionalIdeal
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int R]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/--
theorem `absNorm_div_norm_eq_absNorm_div_norm` / 定理 `absNorm_div_norm_eq_absNorm_div_norm`

English:
theorem absNorm_div_norm_eq_absNorm_div_norm
  statement: {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
  proof: by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [← Submodule.ideal_span_singleton_smul]; rw [← Submodule.ideal_span_singleton_smul]; rw 

中文:
定理 absNorm_div_norm_eq_absNorm_div_norm
  结论: {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
  证明: by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [← Submodule.ideal_span_singleton_smul]; rw [← Submodule.ideal_span_singleton_smul]; rw 

Depends on / 依赖: I.den, Ideal.absNorm_span_singleton, LinearMap, LinearMap.map_injective, Nat.cast_mul, Nat.cast_natAbs, Submodule, Submodule.ideal_span_singleton_smul, Submodule.map_smul, Submonoid, Submonoid.smul_def, absNorm_span_singleton, cast_mul, cast_natAbs, congr_arg, den_mul_self_eq_num, div_eq_div_iff, eq_iff, ideal_span_singleton_smul, map_injective
-/
theorem absNorm_div_norm_eq_absNorm_div_norm {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)| =
      (Ideal.absNorm I₀ : Rat) / |Algebra.norm Int (a : R)| := by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [← Submodule.ideal_span_singleton_smul]; rw [← Submodule.ideal_span_singleton_smul]; rw [← Submodule.map_smul'']; rw [← Submodule.map_smul'']; rw [(LinearMap.map_injective ?_).eq_iff]; rw [smul_eq_mul]; rw [smul_eq_mul] at h'
    · simp_rw [← Nat.cast_natAbs, ← Nat.cast_mul, ← Ideal.absNorm_span_singleton]
      rw [← map_mul]; rw [← map_mul]; rw [mul_comm]; rw [← h']; rw [mul_comm]
    · exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective R K)
  all_goals simp [Algebra.norm_eq_zero_iff]

/--
Definition of `absNorm` / `absNorm` 的定义

English:
definition absNorm
  signature: : FractionalIdeal R⁰ K ->*₀ Rat where
  body: (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)|
  map_zero' := by
    rw [num_zero_eq]; rw [Submodule.zero_eq_bot]; rw [Ideal.absNorm_bot]; rw [Nat.cast_zero]; rw [zero_div]
    exact IsFractionRing.injective R K
  map_one' := by
    rw [absNorm_div_norm_eq_absNorm_div_norm 1 ⊤ (by simp

中文:
定义 absNorm
  签名: : FractionalIdeal R⁰ K ->*₀ Rat where
  定义体: (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)|
  map_zero' := by
    rw [num_zero_eq]; rw [Submodule.zero_eq_bot]; rw [Ideal.absNorm_bot]; rw [Nat.cast_zero]; rw [zero_div]
    exact IsFractionRing.injective R K
  map_one' := by
    rw [absNorm_div_norm_eq_absNorm_div_norm 1 ⊤ (by simp

Depends on / 依赖: Algebra, Algebra.norm, I.den, I.num, Ideal.absNorm, absNorm
-/
noncomputable def absNorm : FractionalIdeal R⁰ K ->*₀ Rat where
  toFun I := (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)|
  map_zero' := by
    rw [num_zero_eq]; rw [Submodule.zero_eq_bot]; rw [Ideal.absNorm_bot]; rw [Nat.cast_zero]; rw [zero_div]
    exact IsFractionRing.injective R K
  map_one' := by
    rw [absNorm_div_norm_eq_absNorm_div_norm 1 ⊤ (by simp [Submodule.one_eq_range]),
      Ideal.absNorm_top, Nat.cast_one, OneMemClass.coe_one, map_one, abs_one,
      Int.cast_one,
      one_div_one]
  map_mul' I J := by
    rw [absNorm_div_norm_eq_absNorm_div_norm (I.den * J.den) (I.num * J.num) (by
        have : Algebra.linearMap R K = (IsScalarTower.toAlgHom R R K).toLinearMap := rfl
        rw [coe_mul]; rw [this]; rw [Submodule.map_mul]; rw [← this]; rw [← den_mul_self_eq_num]; rw [← den_mul_self_eq_num]
        exact Submodule.mul_smul_mul_eq_smul_mul_smul _ _ _ _),
      Submonoid.coe_mul, map_mul, map_mul, Nat.cast_mul, div_mul_div_comm,
      Int.cast_abs, Int.cast_abs, Int.cast_abs, ← abs_mul, Int.cast_mul]

/--
theorem `absNorm_eq` / 定理 `absNorm_eq`

English:
theorem absNorm_eq
  given: (I : FractionalIdeal R⁰ K)
  proof: rfl

中文:
定理 absNorm_eq
  条件: (I : FractionalIdeal R⁰ K)
  证明: rfl
-/
theorem absNorm_eq (I : FractionalIdeal R⁰ K) :
    absNorm I = (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)| := rfl

/--
theorem `absNorm_eq'` / 定理 `absNorm_eq'`

English:
theorem absNorm_eq'
  statement: {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
  proof: by
  rw [absNorm]; rw [← absNorm_div_norm_eq_absNorm_div_norm a I₀ h]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]

中文:
定理 absNorm_eq'
  结论: {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
  证明: by
  rw [absNorm]; rw [← absNorm_div_norm_eq_absNorm_div_norm a I₀ h]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, absNorm, absNorm_div_norm_eq_absNorm_div_norm, coe_mk
-/
theorem absNorm_eq' {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    absNorm I = (Ideal.absNorm I₀ : Rat) / |Algebra.norm Int (a : R)| := by
  rw [absNorm]; rw [← absNorm_div_norm_eq_absNorm_div_norm a I₀ h]; rw [MonoidWithZeroHom.coe_mk]; rw [ZeroHom.coe_mk]

/--
theorem `absNorm_nonneg` / 定理 `absNorm_nonneg`

English:
theorem absNorm_nonneg
  given: (I : FractionalIdeal R⁰ K)
  statement: 0 <= absNorm I
  proof: by dsimp [absNorm]; positivity

中文:
定理 absNorm_nonneg
  条件: (I : FractionalIdeal R⁰ K)
  结论: 0 <= absNorm I
  证明: by dsimp [absNorm]; positivity

Depends on / 依赖: absNorm
-/
theorem absNorm_nonneg (I : FractionalIdeal R⁰ K) : 0 <= absNorm I := by dsimp [absNorm]; positivity

/--
theorem `absNorm_bot` / 定理 `absNorm_bot`

English:
theorem absNorm_bot
  statement: absNorm (⊥ : FractionalIdeal R⁰ K) = 0
  proof: absNorm.map_zero'

中文:
定理 absNorm_bot
  结论: absNorm (⊥ : FractionalIdeal R⁰ K) = 0
  证明: absNorm.map_zero'

Depends on / 依赖: absNorm, absNorm.map_zero, map_zero
-/
theorem absNorm_bot : absNorm (⊥ : FractionalIdeal R⁰ K) = 0 := absNorm.map_zero'

/--
theorem `absNorm_one` / 定理 `absNorm_one`

English:
theorem absNorm_one
  statement: absNorm (1 : FractionalIdeal R⁰ K) = 1
  proof: by convert! absNorm.map_one'

中文:
定理 absNorm_one
  结论: absNorm (1 : FractionalIdeal R⁰ K) = 1
  证明: by convert! absNorm.map_one'

Depends on / 依赖: absNorm, absNorm.map_one, convert, map_one
-/
theorem absNorm_one : absNorm (1 : FractionalIdeal R⁰ K) = 1 := by convert! absNorm.map_one'

/--
theorem `absNorm_eq_zero_iff` / 定理 `absNorm_eq_zero_iff`

English:
theorem absNorm_eq_zero_iff
  given: [IsDomain K] {I : FractionalIdeal R⁰ K}
  proof: by
  refine ⟨fun h => zero_of_num_eq_bot zero_notMem_nonZeroDivisors ?_, fun h => h ▸ absNorm_bot⟩
  rw [absNorm_eq]; rw [div_eq_zero_iff] at h
refine Ideal.absNorm_eq_zero_iff.mp Nat.cast_eq_zero.mp h.resolve_right ?_
  simp [Algebra.norm_eq_zero_iff]

中文:
定理 absNorm_eq_zero_iff
  条件: [IsDomain K] {I : FractionalIdeal R⁰ K}
  证明: by
  refine ⟨fun h => zero_of_num_eq_bot zero_notMem_nonZeroDivisors ?_, fun h => h ▸ absNorm_bot⟩
  rw [absNorm_eq]; rw [div_eq_zero_iff] at h
refine Ideal.absNorm_eq_zero_iff.mp Nat.cast_eq_zero.mp h.resolve_right ?_
  simp [Algebra.norm_eq_zero_iff]

Depends on / 依赖: Algebra, Algebra.norm_eq_zero_iff, Ideal.absNorm_eq_zero_iff.mp, Nat.cast_eq_zero.mp, absNorm_bot, absNorm_eq, absNorm_eq_zero_iff, cast_eq_zero, div_eq_zero_iff, h.resolve_right, norm_eq_zero_iff, resolve_right, zero_notMem_nonZeroDivisors, zero_of_num_eq_bot
-/
theorem absNorm_eq_zero_iff [IsDomain K] {I : FractionalIdeal R⁰ K} :
    absNorm I = 0 ↔ I = 0 := by
  refine ⟨fun h => zero_of_num_eq_bot zero_notMem_nonZeroDivisors ?_, fun h => h ▸ absNorm_bot⟩
  rw [absNorm_eq]; rw [div_eq_zero_iff] at h
refine Ideal.absNorm_eq_zero_iff.mp Nat.cast_eq_zero.mp h.resolve_right ?_
  simp [Algebra.norm_eq_zero_iff]

/--
theorem `coeIdeal_absNorm` / 定理 `coeIdeal_absNorm`

English:
theorem coeIdeal_absNorm
  given: (I₀ : Ideal R)
  proof: by
  rw [absNorm_eq' 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one, map_one, abs_one,
    Int.cast_one, _root_.div_one]

中文:
定理 coeIdeal_absNorm
  条件: (I₀ : Ideal R)
  证明: by
  rw [absNorm_eq' 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one, map_one, abs_one,
    Int.cast_one, _root_.div_one]

Depends on / 依赖: Int.cast_one, OneMemClass, OneMemClass.coe_one, _root_, _root_.div_one, absNorm_eq, abs_one, cast_one, coe_one, div_one, map_one, one_smul
-/
theorem coeIdeal_absNorm (I₀ : Ideal R) :
    absNorm (I₀ : FractionalIdeal R⁰ K) = Ideal.absNorm I₀ := by
  rw [absNorm_eq' 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one, map_one, abs_one,
    Int.cast_one, _root_.div_one]

section IsLocalization

variable [IsLocalization (Algebra.algebraMapSubmonoid R Int⁰) K] [Algebra Rat K]

/--
theorem `abs_det_basis_change` / 定理 `abs_det_basis_change`

English:
theorem abs_det_basis_change
  statement: [IsDomain K] {ι : Type*} [Fintype ι]
  proof: by
  have := IsFractionRing.nontrivial R K
  let b₀ : Basis ι Rat K := b.localizationLocalization Rat Int⁰ K
  let bI.num : Basis ι Int I.num := bI.map
      ((equivNum (nonZeroDivisors.coe_ne_zero _)).restrictScalars Int)
  rw [absNorm_eq]; rw [← Ideal.natAbs_det_basis_change b I.num bI.num]; rw [N

中文:
定理 abs_det_basis_change
  结论: [IsDomain K] {ι : 类型} [Fintype ι]
  证明: by
  have := IsFractionRing.nontrivial R K
  let b₀ : Basis ι Rat K := b.localizationLocalization Rat Int⁰ K
  let bI.num : Basis ι Int I.num := bI.map
      ((equivNum (nonZeroDivisors.coe_ne_zero _)).restrictScalars Int)
  rw [absNorm_eq]; rw [← Ideal.natAbs_det_basis_change b I.num bI.num]; rw [N

Depends on / 依赖: Basis.det_apply, I.num, Ideal.natAbs_det_basis_change, Int.cast_abs, IsFractionRing, IsFractionRing.nontrivial, Nat.cast_natAbs, RingHom, RingHom.mapMatrix, RingHom.map_det, absNorm_eq, algebraMap, b.localizationLocalization, b.toMat, bI.map, bI.num, cast_abs, cast_natAbs, coe_ne_zero, det_apply
-/
theorem abs_det_basis_change [IsDomain K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι Int R) (I : FractionalIdeal R⁰ K) (bI : Basis ι Int I) :
    |(b.localizationLocalization Rat Int⁰ K).det ((↑) ∘ bI)| = absNorm I := by
  have := IsFractionRing.nontrivial R K
  let b₀ : Basis ι Rat K := b.localizationLocalization Rat Int⁰ K
  let bI.num : Basis ι Int I.num := bI.map
      ((equivNum (nonZeroDivisors.coe_ne_zero _)).restrictScalars Int)
  rw [absNorm_eq]; rw [← Ideal.natAbs_det_basis_change b I.num bI.num]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]; rw [Int.cast_abs]; rw [Basis.det_apply]; rw [Basis.det_apply]
  change _ = |algebraMap Int Rat _| / _
  rw [RingHom.map_det]; rw [show RingHom.mapMatrix (algebraMap Int Rat) (b.toMatrix ((↑) ∘ bI.num)) =
      b₀.toMatrix ((algebraMap R K (den I : R)) • ((↑) ∘ bI)) by
    ext : 2
    simp_rw [bI.num]; rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [← Basis.localizationLocalization_repr_algebraMap Rat Int⁰ K]; rw [Function.comp_apply]; rw [Basis.map_apply]; rw [LinearEquiv.restrictScalars_apply]; rw [equivNum_apply]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]
    rfl]
  rw [Basis.toMatrix_smul]; rw [Matrix.det_mul]; rw [abs_mul]; rw [← Algebra.norm_eq_matrix_det]; rw [Algebra.norm_localization Int Int⁰]; rw [show (Algebra.norm Int (den I : R) : Rat) =
    algebraMap Int Rat (Algebra.norm Int (den I : R)) by rfl]; rw [mul_div_assoc]; rw [mul_div_cancel₀ _ (by
    rw [ne_eq]; rw [abs_eq_zero]; rw [IsFractionRing.to_map_eq_zero_iff]; rw [Algebra.norm_eq_zero_iff_of_basis b]
    exact nonZeroDivisors.coe_ne_zero _)]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
@[simp]
/--
theorem `absNorm_span_singleton` / 定理 `absNorm_span_singleton`

English:
theorem absNorm_span_singleton
  given: [Module.Finite Rat K] (x : K)
  proof: by
  have : IsDomain K := IsFractionRing.isDomain R
  obtain ⟨d, ⟨r, hr⟩⟩ := IsLocalization.exists_integer_multiple R⁰ x
  rw [absNorm_eq' d (Ideal.span {r})]
  · rw [Ideal.absNorm_span_singleton]
    simp_rw [Nat.cast_natAbs, Int.cast_abs, show ((Algebra.norm Int _) : Rat) = algebraMap Int Rat
    

中文:
定理 absNorm_span_singleton
  条件: [Module.Finite Rat K] (x : K)
  证明: by
  have : IsDomain K := IsFractionRing.isDomain R
  obtain ⟨d, ⟨r, hr⟩⟩ := IsLocalization.exists_integer_multiple R⁰ x
  rw [absNorm_eq' d (Ideal.span {r})]
  · rw [Ideal.absNorm_span_singleton]
    simp_rw [Nat.cast_natAbs, Int.cast_abs, show ((Algebra.norm Int _) : Rat) = algebraMap Int Rat
    

Depends on / 依赖: Algebra, Algebra.norm, Algebra.norm_localization, Algebra.smul_def, Ideal.absNorm_span_singleton, Ideal.span, Int.cast_abs, IsDomain, IsFractionRing, IsFractionRing.isDomain, IsLocalization, IsLocalization.exists_integer_multiple, Nat.cast_natAbs, absNorm_eq, absNorm_span_singleton, abs_eq_zero, abs_mul, algebraMap, cast_abs, cast_natAbs
-/
theorem absNorm_span_singleton [Module.Finite Rat K] (x : K) :
    absNorm (spanSingleton R⁰ x) = |(Algebra.norm Rat x)| := by
  have : IsDomain K := IsFractionRing.isDomain R
  obtain ⟨d, ⟨r, hr⟩⟩ := IsLocalization.exists_integer_multiple R⁰ x
  rw [absNorm_eq' d (Ideal.span {r})]
  · rw [Ideal.absNorm_span_singleton]
    simp_rw [Nat.cast_natAbs, Int.cast_abs, show ((Algebra.norm Int _) : Rat) = algebraMap Int Rat
      (Algebra.norm Int _) by rfl, ← Algebra.norm_localization Int Int⁰ (Sₘ := K) _]
    rw [hr]; rw [Algebra.smul_def]; rw [map_mul]; rw [abs_mul]; rw [mul_div_assoc]; rw [mul_div_cancel₀ _ (by
      rw [ne_eq]; rw [abs_eq_zero]; rw [Algebra.norm_eq_zero_iff]; rw [IsFractionRing.to_map_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero _)]
  · ext
    simp_rw [Submodule.mem_smul_pointwise_iff_exists, mem_coe, mem_spanSingleton, Submodule.mem_map,
      Algebra.linearMap_apply, Submonoid.smul_def, Ideal.mem_span_singleton', exists_exists_eq_and,
      map_mul, hr, ← Algebra.smul_def, smul_comm (d : R)]

end IsLocalization

end FractionalIdeal
