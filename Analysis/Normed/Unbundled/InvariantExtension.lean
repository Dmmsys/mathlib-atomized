/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# algNormOfAlgEquiv and invariantExtension

Let `K` be a nonarchimedean normed field and `L/K` be a finite algebraic extension. In the comments,
`‖ ⬝ ‖` denotes any power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions

* `IsUltrametricDist.algNormOfAlgEquiv` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending
  `x : L` to `‖ σ x ‖` is a `K`-algebra norm on `L`.
* `IsUltrametricDist.invariantExtension` : the function `L → ℝ` sending `x : L` to the maximum of
  `‖ σ x ‖` over all `σ : L ≃ₐ[K] L` is a `K`-algebra norm on `L`.

## Main Results
* `IsUltrametricDist.isPowMul_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is nonarchimedean.
* `IsUltrametricDist.algNormOfAlgEquiv_extends` : `algNormOfAlgEquiv` extends the norm on `K`.
* `IsUltrametricDist.isPowMul_invariantExtension` : `invariantExtension` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_invariantExtension` : `invariantExtension` is nonarchimedean.
* `IsUltrametricDist.invariantExtension_extends` : `invariantExtension` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

algNormOfAlgEquiv, invariantExtension, norm, nonarchimedean
-/

@[expose] public section

open scoped NNReal

noncomputable section

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
  [h_fin : FiniteDimensional K L] [hu : IsUltrametricDist K]

namespace IsUltrametricDist
section algNormOfAlgEquiv

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `algNormOfAlgEquiv` / `algNormOfAlgEquiv` 的定义

English:
definition algNormOfAlgEquiv
  signature: (σ : L ≃ₐ[K] L)
  body: Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm) (σ x)
  map_zero' := by simp
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  s

中文:
定义 algNormOfAlgEquiv
  签名: (σ : L ≃ₐ[K] L)
  定义体: Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm) (σ x)
  map_zero' := by simp
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  s

Depends on / 依赖: Classical, Classical.choose, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
-/
def algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    AlgebraNorm K L where
  toFun x := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm) (σ x)
  map_zero' := by simp
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  smul' x y := by simp [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := EmbeddingLike.map_eq_zero_iff.mp (eq_zero_of_map_eq_zero _ hx)

/--
theorem `algNormOfAlgEquiv_apply` / 定理 `algNormOfAlgEquiv_apply`

English:
theorem algNormOfAlgEquiv_apply
  given: (σ : L ≃ₐ[K] L) (x : L)
  proof: rfl

中文:
定理 algNormOfAlgEquiv_apply
  条件: (σ : L ≃ₐ[K] L) (x : L)
  证明: rfl
-/
theorem algNormOfAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : L) :
    algNormOfAlgEquiv σ x =
      Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin
        hu.isNonarchimedean_norm) (σ x) := rfl

/--
theorem `isPowMul_algNormOfAlgEquiv` / 定理 `isPowMul_algNormOfAlgEquiv`

English:
theorem isPowMul_algNormOfAlgEquiv
  given: (σ : L ≃ₐ[K] L)
  proof: by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).1 _ hn

中文:
定理 isPowMul_algNormOfAlgEquiv
  条件: (σ : L ≃ₐ[K] L)
  证明: by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).1 _ hn

Depends on / 依赖: Classical, Classical.choose_spec, algNormOfAlgEquiv_apply, choose_spec, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional, h_fin, hu.isNonarchimedean_norm, isNonarchimedean_norm, map_pow
-/
theorem isPowMul_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsPowMul (algNormOfAlgEquiv σ) := by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).1 _ hn

/--
theorem `isNonarchimedean_algNormOfAlgEquiv` / 定理 `isNonarchimedean_algNormOfAlgEquiv`

English:
theorem isNonarchimedean_algNormOfAlgEquiv
  given: (σ : L ≃ₐ[K] L)
  proof: by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.2 _ _

中文:
定理 isNonarchimedean_algNormOfAlgEquiv
  条件: (σ : L ≃ₐ[K] L)
  证明: by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.2 _ _

Depends on / 依赖: Classical, Classical.choose_spec, algNormOfAlgEquiv_apply, choose_spec, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional, h_fin, hu.isNonarchimedean_norm, isNonarchimedean_norm, map_add
-/
theorem isNonarchimedean_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsNonarchimedean (algNormOfAlgEquiv σ) := by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.2 _ _

/--
theorem `algNormOfAlgEquiv_extends` / 定理 `algNormOfAlgEquiv_extends`

English:
theorem algNormOfAlgEquiv_extends
  given: (σ : L ≃ₐ[K] L) (x : K)
  proof: by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.1 _

中文:
定理 algNormOfAlgEquiv_extends
  条件: (σ : L ≃ₐ[K] L) (x : K)
  证明: by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.1 _

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, Classical, Classical.choose_spec, algNormOfAlgEquiv_apply, choose_spec, commutes, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional, h_fin, hu.isNonarchimedean_norm, isNonarchimedean_norm
-/
theorem algNormOfAlgEquiv_extends (σ : L ≃ₐ[K] L) (x : K) :
    (algNormOfAlgEquiv σ) ((algebraMap K L) x) = ‖x‖ := by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.1 _

end algNormOfAlgEquiv

section invariantExtension

variable (K L)

/--
Definition of `invariantExtension` / `invariantExtension` 的定义

English:
definition invariantExtension
  signature: : AlgebraNorm K L where
  body: iSup fun σ : L ≃ₐ[K] L => algNormOfAlgEquiv σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ => le_trans (map_add_le_add (algNormOfAlgEquiv σ) x y)
    (add_le_add (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
  neg' x := by simp only [map_

中文:
定义 invariantExtension
  签名: : AlgebraNorm K L where
  定义体: iSup fun σ : L ≃ₐ[K] L => algNormOfAlgEquiv σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ => le_trans (map_add_le_add (algNormOfAlgEquiv σ) x y)
    (add_le_add (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
  neg' x := by simp only [map_

Depends on / 依赖: algNormOfAlgEquiv
-/
def invariantExtension : AlgebraNorm K L where
  toFun x := iSup fun σ : L ≃ₐ[K] L => algNormOfAlgEquiv σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ => le_trans (map_add_le_add (algNormOfAlgEquiv σ) x y)
    (add_le_add (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun σ => le_trans (map_mul_le_mul (algNormOfAlgEquiv σ) x y)
    (mul_le_mul (Finite.le_ciSup_of_le σ le_rfl)
      (Finite.le_ciSup_of_le σ le_rfl) (apply_nonneg _ _)
      (Finite.le_ciSup_of_le σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx => ne_of_gt (lt_of_lt_of_le (map_pos_of_ne_zero _ hx)
      (Finite.le_ciSup (fun σ => (algNormOfAlgEquiv σ) x) AlgEquiv.refl))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]

@[simp]
/--
theorem `invariantExtension_apply` / 定理 `invariantExtension_apply`

English:
theorem invariantExtension_apply
  given: (x : L)
  proof: rfl

中文:
定理 invariantExtension_apply
  条件: (x : L)
  证明: rfl
-/
theorem invariantExtension_apply (x : L) :
    invariantExtension K L x = iSup fun σ : L ≃ₐ[K] L => algNormOfAlgEquiv σ x :=
  rfl

/--
theorem `isPowMul_invariantExtension` / 定理 `isPowMul_invariantExtension`

English:
theorem isPowMul_invariantExtension
  proof: by
  intro x n hn
  rw [invariantExtension_apply]; rw [invariantExtension_apply]; rw [Real.iSup_pow
    (fun σ => apply_nonneg (algNormOfAlgEquiv σ) x)]
  exact iSup_congr fun σ => isPowMul_algNormOfAlgEquiv σ _ hn

中文:
定理 isPowMul_invariantExtension
  证明: by
  intro x n hn
  rw [invariantExtension_apply]; rw [invariantExtension_apply]; rw [Real.iSup_pow
    (fun σ => apply_nonneg (algNormOfAlgEquiv σ) x)]
  exact iSup_congr fun σ => isPowMul_algNormOfAlgEquiv σ _ hn

Depends on / 依赖: Real.iSup_pow, algNormOfAlgEquiv, apply_nonneg, iSup_congr, iSup_pow, invariantExtension_apply, isPowMul_algNormOfAlgEquiv
-/
theorem isPowMul_invariantExtension :
    IsPowMul (invariantExtension K L) := by
  intro x n hn
  rw [invariantExtension_apply]; rw [invariantExtension_apply]; rw [Real.iSup_pow
    (fun σ => apply_nonneg (algNormOfAlgEquiv σ) x)]
  exact iSup_congr fun σ => isPowMul_algNormOfAlgEquiv σ _ hn

/--
theorem `isNonarchimedean_invariantExtension` / 定理 `isNonarchimedean_invariantExtension`

English:
theorem isNonarchimedean_invariantExtension
  proof: fun x y =>
  ciSup_le fun σ => le_trans (isNonarchimedean_algNormOfAlgEquiv σ x y)
    (max_le_max (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))

中文:
定理 isNonarchimedean_invariantExtension
  证明: fun x y =>
  ciSup_le fun σ => le_trans (isNonarchimedean_algNormOfAlgEquiv σ x y)
    (max_le_max (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
-/
theorem isNonarchimedean_invariantExtension :
    IsNonarchimedean (invariantExtension K L) := fun x y =>
  ciSup_le fun σ => le_trans (isNonarchimedean_algNormOfAlgEquiv σ x y)
    (max_le_max (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))

/--
theorem `invariantExtension_extends` / 定理 `invariantExtension_extends`

English:
theorem invariantExtension_extends
  given: (x : K)
  proof: by
  simp [algNormOfAlgEquiv_extends _ x, ciSup_const]

中文:
定理 invariantExtension_extends
  条件: (x : K)
  证明: by
  simp [algNormOfAlgEquiv_extends _ x, ciSup_const]

Depends on / 依赖: algNormOfAlgEquiv_extends, ciSup_const
-/
theorem invariantExtension_extends (x : K) :
    (invariantExtension K L) (algebraMap K L x) = ‖x‖ := by
  simp [algNormOfAlgEquiv_extends _ x, ciSup_const]

end invariantExtension

end IsUltrametricDist
