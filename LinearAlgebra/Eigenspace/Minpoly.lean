/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Eigenvalues are the roots of the minimal polynomial.

## Tags

eigenvalue, minimal polynomial
-/

public section


universe u v w

namespace Module

namespace End

open Polynomial Module

open scoped Polynomial

section CommSemiring

variable {R : Type v} {M : Type w} [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
theorem `ker_aeval_ring_hom'_unit_polynomial` / 定理 `ker_aeval_ring_hom'_unit_polynomial`

English:
theorem ker_aeval_ring_hom'_unit_polynomial
  given: (f : End R M) (c : R[X]ˣ)
  proof: LinearMap.ker_eq_bot'.mpr fun m hm => by
    simpa [← mul_apply, ← aeval_mul] using congr(c⁻¹.1.aeval f $hm)

中文:
定理 ker_aeval_ring_hom'_unit_polynomial
  条件: (f : End R M) (c : R[X]ˣ)
  证明: LinearMap.ker_eq_bot'.mpr fun m hm => by
    simpa [← mul_apply, ← aeval_mul] using congr(c⁻¹.1.aeval f $hm)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, aeval_mul, ker_eq_bot, mul_apply
-/
theorem ker_aeval_ring_hom'_unit_polynomial (f : End R M) (c : R[X]ˣ) :
    LinearMap.ker (aeval f (c : R[X])) = ⊥ :=
  LinearMap.ker_eq_bot'.mpr fun m hm => by
    simpa [← mul_apply, ← aeval_mul] using congr(c⁻¹.1.aeval f $hm)

end CommSemiring

section CommRing

variable {R : Type v} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M] {f : End R M} {μ : R}
  {x : M} {p : R[X]}

/--
theorem `aeval_apply_of_hasEigenvector` / 定理 `aeval_apply_of_hasEigenvector`

English:
theorem aeval_apply_of_hasEigenvector
  given: (h : f.HasEigenvector μ x)
  proof: by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm]; rw [pow_succ']; rw [mul_assoc]; rw [map_mul]; rw [Module.End.mul_apply]; rw [mul_comm]; rw [hna]
    simp only [mem_eigenspace_iff.1 h

中文:
定理 aeval_apply_of_hasEigenvector
  条件: (h : f.HasEigenvector μ x)
  证明: by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm]; rw [pow_succ']; rw [mul_assoc]; rw [map_mul]; rw [Module.End.mul_apply]; rw [mul_comm]; rw [hna]
    simp only [mem_eigenspace_iff.1 h

Depends on / 依赖: Module, Module.End.mul_apply, Module.algebraMap_end_apply, RingHom, RingHom.id_apply, add_smul, aeval_X, algebraMap_end_apply, eval_C, eval_X, eval_mul, eval_pow, id_apply, induction_on, map_mul, mem_eigenspace_iff, mul_apply, mul_assoc, mul_comm, p.induction_on
-/
theorem aeval_apply_of_hasEigenvector (h : f.HasEigenvector μ x) :
    aeval f p x = p.eval μ • x := by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm]; rw [pow_succ']; rw [mul_assoc]; rw [map_mul]; rw [Module.End.mul_apply]; rw [mul_comm]; rw [hna]
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      map_smulₛₗ, RingHom.id_apply, mul_comm]

/--
lemma `aeval_apply_of_mem_apply_eq_smul` / 引理 `aeval_apply_of_mem_apply_eq_smul`

English:
lemma aeval_apply_of_mem_apply_eq_smul
  given: (hx : f x = μ • x)
  proof: by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

中文:
引理 aeval_apply_of_mem_apply_eq_smul
  条件: (hx : f x = μ • x)
  证明: by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

Depends on / 依赖: aeval_apply_of_hasEigenvector, eq_or_ne, mem_eigenspace_iff, mem_eigenspace_iff.mpr
-/
lemma aeval_apply_of_mem_apply_eq_smul (hx : f x = μ • x) :
    aeval f p x = p.eval μ • x := by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

/--
theorem `isRoot_of_hasEigenvalue` / 定理 `isRoot_of_hasEigenvalue`

English:
theorem isRoot_of_hasEigenvalue
  statement: [IsDomain R] [IsTorsionFree R M] {f : End R M} {μ : R}
  proof: by
  rcases (Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine Or.resolve_right (smul_eq_zero.1 ?_) ne0
  rw [← aeval_apply_of_hasEigenvector ⟨H]; rw [ne0⟩]
  simp

中文:
定理 isRoot_of_hasEigenvalue
  结论: [是整环 R] [是无挠 R M] {f : End R M} {μ : R}
  证明: by
  rcases (Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine Or.resolve_right (smul_eq_zero.1 ?_) ne0
  rw [← aeval_apply_of_hasEigenvector ⟨H]; rw [ne0⟩]
  simp

Depends on / 依赖: Or.resolve_right, Submodule, Submodule.ne_bot_iff, aeval_apply_of_hasEigenvector, ne_bot_iff, resolve_right, smul_eq_zero
-/
theorem isRoot_of_hasEigenvalue [IsDomain R] [IsTorsionFree R M] {f : End R M} {μ : R}
    (h : f.HasEigenvalue μ) : (minpoly R f).IsRoot μ := by
  rcases (Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine Or.resolve_right (smul_eq_zero.1 ?_) ne0
  rw [← aeval_apply_of_hasEigenvector ⟨H]; rw [ne0⟩]
  simp

section IsDomain

variable [IsDomain R] [Module.Finite R M]

/--
theorem `hasEigenvalue_of_isRoot` / 定理 `hasEigenvalue_of_isRoot`

English:
theorem hasEigenvalue_of_isRoot
  given: (h : (minpoly R f).IsRoot μ)
  statement: f.HasEigenvalue μ
  proof: by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : exists v : M, q.aeval f v != 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq]; rw [d

中文:
定理 hasEigenvalue_of_isRoot
  条件: (h : (minpoly R f).IsRoot μ)
  结论: f.HasEigenvalue μ
  证明: by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : exists v : M, q.aeval f v != 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq]; rw [d

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, LinearMap, LinearMap.ext, Module, Module.End.hasEigenvalue_of_hasEi, degree_X_sub_C, degree_eq_natDegree, degree_mul, dvd_iff_isRoot, dvd_iff_isRoot.mpr, h_contra, hasEigenvalue_of_hasEi, isIntegral, minpoly, minpoly.min, minpoly.monic, minpoly.ne_zero, monic_X_sub_C
-/
theorem hasEigenvalue_of_isRoot (h : (minpoly R f).IsRoot μ) : f.HasEigenvalue μ := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : exists v : M, q.aeval f v != 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq]; rw [degree_mul]; rw [degree_X_sub_C]; rw [degree_eq_natDegree] at this
    · norm_cast at this; grind
    · rintro rfl
      exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral f) (mul_zero (X - C μ) ▸ hq)
  refine Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_iff.mpr ⟨?_, hv⟩)
  simpa [sub_eq_zero, hq] using congr($(minpoly.aeval R f) v)

variable [IsTorsionFree R M]

/--
theorem `hasEigenvalue_iff_isRoot` / 定理 `hasEigenvalue_iff_isRoot`

English:
theorem hasEigenvalue_iff_isRoot
  statement: f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ
  proof: ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩

中文:
定理 hasEigenvalue_iff_isRoot
  结论: f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ
  证明: ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩

Depends on / 依赖: hasEigenvalue_of_isRoot, isRoot_of_hasEigenvalue
-/
theorem hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ :=
  ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩

variable (f)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `finite_hasEigenvalue` / 引理 `finite_hasEigenvalue`

English:
lemma finite_hasEigenvalue
  statement: Set.Finite {μ | f.HasEigenvalue μ}
  proof: by
  have h : minpoly R f != 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := R) f)
  refine ((minpoly R f).rootSet_finite R).subset ?_
  simp [Set.subset_def, hasEigenvalue_iff_isRoot, mem_rootSet, h]

中文:
引理 finite_hasEigenvalue
  结论: 集合.有限 {μ | f.HasEigenvalue μ}
  证明: by
  have h : minpoly R f != 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := R) f)
  refine ((minpoly R f).rootSet_finite R).subset ?_
  simp [Set.subset_def, hasEigenvalue_iff_isRoot, mem_rootSet, h]

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, Set.subset_def, hasEigenvalue_iff_isRoot, isIntegral, mem_rootSet, minpoly, minpoly.ne_zero, ne_zero, rootSet_finite, subset, subset_def
-/
lemma finite_hasEigenvalue : Set.Finite {μ | f.HasEigenvalue μ} := by
  have h : minpoly R f != 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := R) f)
  refine ((minpoly R f).rootSet_finite R).subset ?_
  simp [Set.subset_def, hasEigenvalue_iff_isRoot, mem_rootSet, h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype f.Eigenvalues
  body: Set.Finite.fintype f.finite_hasEigenvalue

中文:
实例 :
  签名: 有限类型 f.Eigenvalues
  定义体: Set.Finite.fintype f.finite_hasEigenvalue

Depends on / 依赖: Finite, Set.Finite.fintype, f.finite_hasEigenvalue, finite_hasEigenvalue, fintype
-/
noncomputable instance : Fintype f.Eigenvalues :=
  Set.Finite.fintype f.finite_hasEigenvalue

end IsDomain

end CommRing

section Field

variable {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]

/--
theorem `eigenspace_aeval_polynomial_degree_1` / 定理 `eigenspace_aeval_polynomial_degree_1`

English:
theorem eigenspace_aeval_polynomial_degree_1
  given: (f : End K V) (q : K[X]) (hq : degree q = 1)
  proof: calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          apply eigenspace_div
          rw [Ne]; rw [leadingCoeff_eq_zero_iff_deg_eq_bot]; rw [hq]
          exact WithBot.one_ne_bot
    _ = LinearMap.ker (aev

中文:
定理 eigenspace_aeval_polynomial_degree_1
  条件: (f : End K V) (q : K[X]) (hq : degree q = 1)
  证明: calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          apply eigenspace_div
          rw [Ne]; rw [leadingCoeff_eq_zero_iff_deg_eq_bot]; rw [hq]
          exact WithBot.one_ne_bot
    _ = LinearMap.ker (aev

Depends on / 依赖: Algebra, Algebra.algebraMap, C_mul, LinearMap, LinearMap.ker, WithBot, WithBot.one_ne_bot, aeval_def, algebraMap, eigenspace, eigenspace_div, eq_X_add_C_of_degree_eq_one, leadingCoeff, leadingCoeff_eq_zero_iff_deg_eq_bot, one_ne_bot, q.coeff, q.leadingCoeff
-/
theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = LinearMap.ker (aeval f q) :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          apply eigenspace_div
          rw [Ne]; rw [leadingCoeff_eq_zero_iff_deg_eq_bot]; rw [hq]
          exact WithBot.one_ne_bot
    _ = LinearMap.ker (aeval f (C q.leadingCoeff * X + C (q.coeff 0))) := by
          rw [C_mul']; rw [aeval_def]; simp [algebraMap, Algebra.algebraMap]
    _ = LinearMap.ker (aeval f q) := by rwa [← eq_X_add_C_of_degree_eq_one]

end Field

end End

end Module

section FiniteSpectrum

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Module.End.finite_spectrum` / 定理 `Module.End.finite_spectrum`

English:
theorem Module.End.finite_spectrum
  statement: {K : Type v} {V : Type w} [Field K] [AddCommGroup V]
  proof: by
  convert! f.finite_hasEigenvalue using 1
  ext x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

中文:
定理 模.End.finite_spectrum
  结论: {K : 类型v} {V : 类型 w} [域 K] [加法交换群 V]
  证明: by
  convert! f.finite_hasEigenvalue using 1
  ext x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

Depends on / 依赖: Module, Module.End.hasEigenvalue_iff_mem_spectrum.symm, convert, f.finite_hasEigenvalue, finite_hasEigenvalue, hasEigenvalue_iff_mem_spectrum
-/
theorem Module.End.finite_spectrum {K : Type v} {V : Type w} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) :
    Set.Finite (spectrum K f) := by
  convert! f.finite_hasEigenvalue using 1
  ext x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

variable {n R : Type*} [Field R] [Fintype n] [DecidableEq n]

/--
theorem `Matrix.finite_spectrum` / 定理 `Matrix.finite_spectrum`

English:
theorem Matrix.finite_spectrum
  given: (A : Matrix n n R)
  statement: Set.Finite (spectrum R A)
  proof: by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _

中文:
定理 矩阵.finite_spectrum
  条件: (A : 矩阵 n n R)
  结论: 集合.有限 (spectrum R A)
  证明: by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Matrix, Matrix.toLinAlgEquiv, Module, Module.End.finite_spectrum, Pi.basisFun, basisFun, finite_spectrum, spectrum_eq, toLinAlgEquiv
-/
theorem Matrix.finite_spectrum (A : Matrix n n R) : Set.Finite (spectrum R A) := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _

/--
Instance `Matrix.instFiniteSpectrum` / 实例 `Matrix.instFiniteSpectrum`

English:
instance Matrix.instFiniteSpectrum
  signature: (A : Matrix n n R)
  body: Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

中文:
实例 矩阵.instFiniteSpectrum
  签名: (A : 矩阵 n n R)
  定义体: Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

Depends on / 依赖: Matrix, Matrix.finite_spectrum, Set.finite_coe_iff.mpr, finite_coe_iff, finite_spectrum
-/
instance Matrix.instFiniteSpectrum (A : Matrix n n R) : Finite (spectrum R A) :=
  Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

end FiniteSpectrum
