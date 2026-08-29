/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Determinant

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `LinearAlgebra/Charpoly/ToMatrix`.

## Main definition

* `LinearMap.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

@[expose] public section


universe u v w

open Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M ->ₗ[R] M)

section Basic

/--
Definition of `charpoly` / `charpoly` 的定义

English:
definition charpoly
  signature: : R[X]
  body: (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

中文:
定义 charpoly
  签名: : R[X]
  定义体: (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

Depends on / 依赖: charpoly, chooseBasis, toMatrix
-/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

/--
theorem `charpoly_def` / 定理 `charpoly_def`

English:
theorem charpoly_def
  statement: f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
  proof: rfl

中文:
定理 charpoly_def
  结论: f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
  证明: rfl
-/
theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl

/--
theorem `eval_charpoly` / 定理 `eval_charpoly`

English:
theorem eval_charpoly
  given: (t : R)
  proof: by
  rw [charpoly]; rw [Matrix.eval_charpoly]; rw [← LinearMap.det_toMatrix (chooseBasis R M)]; rw [map_sub]; rw [scalar_apply]; rw [toMatrix_algebraMap]; rw [scalar_apply]

@[simp]

中文:
定理 eval_charpoly
  条件: (t : R)
  证明: by
  rw [charpoly]; rw [Matrix.eval_charpoly]; rw [← LinearMap.det_toMatrix (chooseBasis R M)]; rw [map_sub]; rw [scalar_apply]; rw [toMatrix_algebraMap]; rw [scalar_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.eval_charpoly, charpoly, chooseBasis, det_toMatrix, eval_charpoly, map_sub, scalar_apply, toMatrix_algebraMap
-/
theorem eval_charpoly (t : R) :
    f.charpoly.eval t = (algebraMap _ _ t - f).det := by
  rw [charpoly]; rw [Matrix.eval_charpoly]; rw [← LinearMap.det_toMatrix (chooseBasis R M)]; rw [map_sub]; rw [scalar_apply]; rw [toMatrix_algebraMap]; rw [scalar_apply]

@[simp]
/--
theorem `charpoly_zero` / 定理 `charpoly_zero`

English:
theorem charpoly_zero
  given: [StrongRankCondition R]
  proof: by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex]

中文:
定理 charpoly_zero
  条件: [StrongRankCondition R]
  证明: by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex]

Depends on / 依赖: Module, Module.finrank_eq_card_chooseBasisIndex, charpoly, finrank_eq_card_chooseBasisIndex
-/
theorem charpoly_zero [StrongRankCondition R] :
    (0 : M ->ₗ[R] M).charpoly = X ^ Module.finrank R M := by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex]

/--
theorem `charpoly_one` / 定理 `charpoly_one`

English:
theorem charpoly_one
  given: [StrongRankCondition R]
  proof: by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex, Matrix.charpoly_one]

中文:
定理 charpoly_one
  条件: [StrongRankCondition R]
  证明: by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex, Matrix.charpoly_one]

Depends on / 依赖: Matrix, Matrix.charpoly_one, Module, Module.finrank_eq_card_chooseBasisIndex, charpoly, charpoly_one, finrank_eq_card_chooseBasisIndex
-/
theorem charpoly_one [StrongRankCondition R] :
    (1 : M ->ₗ[R] M).charpoly = (X - 1) ^ Module.finrank R M := by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex, Matrix.charpoly_one]

/--
theorem `charpoly_sub_smul` / 定理 `charpoly_sub_smul`

English:
theorem charpoly_sub_smul
  given: (f : Module.End R M) (μ : R)
  proof: by
  simpa [LinearMap.charpoly, smul_eq_mul_diagonal] using Matrix.charpoly_sub_scalar ..

中文:
定理 charpoly_sub_smul
  条件: (f : 模.End R M) (μ : R)
  证明: by
  simpa [LinearMap.charpoly, smul_eq_mul_diagonal] using Matrix.charpoly_sub_scalar ..

Depends on / 依赖: LinearMap, LinearMap.charpoly, Matrix, Matrix.charpoly_sub_scalar, charpoly, charpoly_sub_scalar, smul_eq_mul_diagonal
-/
theorem charpoly_sub_smul (f : Module.End R M) (μ : R) :
    (f - μ • 1).charpoly = f.charpoly.comp (X + C μ) := by
  simpa [LinearMap.charpoly, smul_eq_mul_diagonal] using Matrix.charpoly_sub_scalar ..

end Basic

section Coeff

/--
theorem `charpoly_monic` / 定理 `charpoly_monic`

English:
theorem charpoly_monic
  statement: f.charpoly.Monic
  proof: Matrix.charpoly_monic _

中文:
定理 charpoly_monic
  结论: f.charpoly.Monic
  证明: Matrix.charpoly_monic _

Depends on / 依赖: Matrix, Matrix.charpoly_monic, charpoly_monic
-/
theorem charpoly_monic : f.charpoly.Monic :=
  Matrix.charpoly_monic _

open Module in
/--
lemma `charpoly_natDegree` / 引理 `charpoly_natDegree`

English:
lemma charpoly_natDegree
  given: [StrongRankCondition R]
  proof: by
  have := nontrivial_of_invariantBasisNumber
  rw [charpoly]; rw [Matrix.charpoly_natDegree_eq_dim]; rw [finrank_eq_card_chooseBasisIndex]

中文:
引理 charpoly_natDegree
  条件: [StrongRankCondition R]
  证明: by
  have := nontrivial_of_invariantBasisNumber
  rw [charpoly]; rw [Matrix.charpoly_natDegree_eq_dim]; rw [finrank_eq_card_chooseBasisIndex]

Depends on / 依赖: Matrix, Matrix.charpoly_natDegree_eq_dim, charpoly, charpoly_natDegree_eq_dim, finrank_eq_card_chooseBasisIndex, nontrivial_of_invariantBasisNumber
-/
lemma charpoly_natDegree [StrongRankCondition R] :
    natDegree (charpoly f) = finrank R M := by
  have := nontrivial_of_invariantBasisNumber
  rw [charpoly]; rw [Matrix.charpoly_natDegree_eq_dim]; rw [finrank_eq_card_chooseBasisIndex]

end Coeff

section CayleyHamilton

/--
theorem `aeval_self_charpoly` / 定理 `aeval_self_charpoly`

English:
theorem aeval_self_charpoly
  statement: aeval f f.charpoly = 0
  proof: by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply]; rw [← AlgEquiv.coe_toAlgHom]; rw [← Polynomial.aeval_algHom_apply _ _ _]; rw [charpoly_def]
  exact Matrix.aeval_self_charpoly _

中文:
定理 aeval_self_charpoly
  结论: aeval f f.charpoly = 0
  证明: by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply]; rw [← AlgEquiv.coe_toAlgHom]; rw [← Polynomial.aeval_algHom_apply _ _ _]; rw [charpoly_def]
  exact Matrix.aeval_self_charpoly _

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.toLinearEquiv_apply, LinearEquiv, LinearEquiv.map_eq_zero_iff, Matrix, Matrix.aeval_self_charpoly, Polynomial, Polynomial.aeval_algHom_apply, aeval_algHom_apply, aeval_self_charpoly, algEquivMatrix, charpoly_def, chooseBasis, coe_toAlgHom, map_eq_zero_iff, toLinearEquiv, toLinearEquiv_apply
-/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply]; rw [← AlgEquiv.coe_toAlgHom]; rw [← Polynomial.aeval_algHom_apply _ _ _]; rw [charpoly_def]
  exact Matrix.aeval_self_charpoly _

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  statement: IsIntegral R f
  proof: ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

中文:
定理 is整数egral
  结论: 是整 R f
  证明: ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

Depends on / 依赖: aeval_self_charpoly, charpoly, charpoly_monic, f.charpoly
-/
theorem isIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

/--
theorem `minpoly_dvd_charpoly` / 定理 `minpoly_dvd_charpoly`

English:
theorem minpoly_dvd_charpoly
  statement: {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
  proof: minpoly.dvd _ _ (aeval_self_charpoly f)

中文:
定理 minpoly_dvd_charpoly
  结论: {K : 类型u} {M : 类型v} [域 K] [加法交换群 M] [模 K M]
  证明: minpoly.dvd _ _ (aeval_self_charpoly f)

Depends on / 依赖: aeval_self_charpoly, minpoly, minpoly.dvd
-/
theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : M ->ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)

/--
theorem `aeval_eq_aeval_mod_charpoly` / 定理 `aeval_eq_aeval_mod_charpoly`

English:
theorem aeval_eq_aeval_mod_charpoly
  given: (p : R[X])
  statement: aeval f p = aeval f (p %ₘ f.charpoly)
  proof: (aeval_modByMonic_eq_self_of_root f.aeval_self_charpoly).symm

中文:
定理 aeval_eq_aeval_mod_charpoly
  条件: (p : R[X])
  结论: aeval f p = aeval f (p %ₘ f.charpoly)
  证明: (aeval_modByMonic_eq_self_of_root f.aeval_self_charpoly).symm

Depends on / 依赖: aeval_modByMonic_eq_self_of_root, aeval_self_charpoly, f.aeval_self_charpoly
-/
theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_modByMonic_eq_self_of_root f.aeval_self_charpoly).symm

/--
theorem `pow_eq_aeval_mod_charpoly` / 定理 `pow_eq_aeval_mod_charpoly`

English:
theorem pow_eq_aeval_mod_charpoly
  given: (k : Nat)
  statement: f ^ k = aeval f (X ^ k %ₘ f.charpoly)
  proof: by
  rw [← aeval_eq_aeval_mod_charpoly]; rw [map_pow]; rw [aeval_X]

中文:
定理 pow_eq_aeval_mod_charpoly
  条件: (k : 自然数)
  结论: f ^ k = aeval f (X ^ k %ₘ f.charpoly)
  证明: by
  rw [← aeval_eq_aeval_mod_charpoly]; rw [map_pow]; rw [aeval_X]

Depends on / 依赖: aeval_X, aeval_eq_aeval_mod_charpoly, map_pow
-/
theorem pow_eq_aeval_mod_charpoly (k : Nat) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly]; rw [map_pow]; rw [aeval_X]

variable {f}

/--
theorem `minpoly_coeff_zero_of_injective` / 定理 `minpoly_coeff_zero_of_injective`

English:
theorem minpoly_coeff_zero_of_injective
  given: [Nontrivial R] (hf : Function.Injective f)
  proof: by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP]; rw [mul_comm]
    refine degree_lt_degree_mul_X fun h => ?_
    rw [h]; rw [mul_zero] at hP
    exact minpoly.ne_zero (isIntegral f) hP
  have hPmonic : P.Monic := by
    suffices (minpoly R f).Monic by
      rwa [Monic.def, hP, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic (isIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, Module.End.mul_eq_comp, LinearMap.ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp,
    map_mul, zero_apply, Function.comp_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (LinearMap.ext hzero))

中文:
定理 minpoly_coeff_zero_of_injective
  条件: [非平凡 R] (hf : 函数.单射 f)
  证明: by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP]; rw [mul_comm]
    refine degree_lt_degree_mul_X fun h => ?_
    rw [h]; rw [mul_zero] at hP
    exact minpoly.ne_zero (isIntegral f) hP
  have hPmonic : P.Monic := by
    suffices (minpoly R f).Monic by
      rwa [Monic.def, hP, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic (isIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, Module.End.mul_eq_comp, LinearMap.ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp,
    map_mul, zero_apply, Function.comp_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (LinearMap.ext hzero))

Depends on / 依赖: LinearM, Module, Module.End.mul_eq_comp, Monic.def, P.Monic, P.degree, X_dvd_iff, degree, degree_lt_degree_mul_X, hPmonic, isIntegral, leadingCoeff_mul_X, minpoly, minpoly.aeval, minpoly.monic, minpoly.ne_zero, mul_comm, mul_eq_comp, mul_zero, ne_zero
-/
theorem minpoly_coeff_zero_of_injective [Nontrivial R] (hf : Function.Injective f) :
    (minpoly R f).coeff 0 != 0 := by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP]; rw [mul_comm]
    refine degree_lt_degree_mul_X fun h => ?_
    rw [h]; rw [mul_zero] at hP
    exact minpoly.ne_zero (isIntegral f) hP
  have hPmonic : P.Monic := by
    suffices (minpoly R f).Monic by
      rwa [Monic.def, hP, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic (isIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, Module.End.mul_eq_comp, LinearMap.ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp,
    map_mul, zero_apply, Function.comp_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (LinearMap.ext hzero))

end CayleyHamilton

end LinearMap

section Algebra
variable {R M} [CommRing R] [Ring M] [Algebra R M]
  [Module.Finite R M] [Module.Free R M]

/--
theorem `Algebra.aeval_self_charpoly_lmul` / 定理 `Algebra.aeval_self_charpoly_lmul`

English:
theorem Algebra.aeval_self_charpoly_lmul
  given: (α : M)
  proof: Algebra.lmul_injective (R := R) by
simpa [← aeval_algHom_apply] using LinearMap.aeval_self_charpoly Algebra.lmul _ _ α

中文:
定理 代数.aeval_self_charpoly_lmul
  条件: (α : M)
  证明: Algebra.lmul_injective (R := R) by
simpa [← aeval_algHom_apply] using LinearMap.aeval_self_charpoly Algebra.lmul _ _ α

Depends on / 依赖: Algebra, Algebra.lmul, Algebra.lmul_injective, LinearMap, LinearMap.aeval_self_charpoly, aeval_algHom_apply, aeval_self_charpoly, lmul_injective
-/
theorem Algebra.aeval_self_charpoly_lmul (α : M) :
    aeval α (Algebra.lmul R M α).charpoly = 0 :=
Algebra.lmul_injective (R := R) by
simpa [← aeval_algHom_apply] using LinearMap.aeval_self_charpoly Algebra.lmul _ _ α

end Algebra
