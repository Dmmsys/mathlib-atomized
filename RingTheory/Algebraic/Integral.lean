/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Algebraic elements and integral elements

This file relates algebraic and integral elements of an algebra, by proving every integral element
is algebraic and that every algebraic element over a field is integral.

## Main results

* `IsIntegral.isAlgebraic`, `Algebra.IsIntegral.isAlgebraic`: integral implies algebraic.
* `isAlgebraic_iff_isIntegral`, `Algebra.isAlgebraic_iff_isIntegral`: integral iff algebraic
  over a field.
* `IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.of_finite`: finite-dimensional (as module) implies
  algebraic.
* `IsAlgebraic.exists_integral_multiple`: an algebraic element has a multiple which is integral
* `IsAlgebraic.iff_exists_smul_integral`: If `R` is reduced and `S` is an `R`-algebra with
  injective `algebraMap`, then an element of `S` is algebraic over `R` iff some `R`-multiple
  is integral over `R`.
* `Algebra.IsAlgebraic.trans`: If `A/S/R` is a tower of algebras and both `A/S` and `S/R` are
  algebraic, then `A/R` is also algebraic, provided that `S` has no zero divisors.
* `Subalgebra.algebraicClosure`: If `R` is a domain and `S` is an arbitrary `R`-algebra,
  then the elements of `S` that are algebraic over `R` form a subalgebra.
* `Transcendental.extendScalars`: an element of an `R`-algebra that is transcendental over `R`
  remains transcendental over any algebraic `R`-subalgebra that has no zero divisors.
-/

@[expose] public section

assert_not_exists IsLocalRing

universe u v w

open Polynomial

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/--
theorem `IsIntegral.isAlgebraic` / 定理 `IsIntegral.isAlgebraic`

English:
theorem IsIntegral.isAlgebraic
  given: [Nontrivial R] {x : A}
  statement: IsIntegral R x -> IsAlgebraic R x
  proof: fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

中文:
定理 是整.isAlgebraic
  条件: [非平凡 R] {x : A}
  结论: 是整 R x -> 是代数 R x
  证明: fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

Depends on / 依赖: hp.ne_zero, ne_zero
-/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x -> IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

/--
Instance `Algebra.IsIntegral.isAlgebraic` / 实例 `Algebra.IsIntegral.isAlgebraic`

English:
instance Algebra.IsIntegral.isAlgebraic
  signature: [Nontrivial R] [Algebra.IsIntegral R A]
  body: ⟨fun a => (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

中文:
实例 代数.是整.isAlgebraic
  签名: [非平凡 R] [代数.是整 R A]
  定义体: ⟨fun a => (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isAlgebraic, isIntegral
-/
instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a => (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/--
theorem `isAlgebraic_iff_isIntegral` / 定理 `isAlgebraic_iff_isIntegral`

English:
theorem isAlgebraic_iff_isIntegral
  given: {x : A}
  statement: IsAlgebraic K x ↔ IsIntegral K x
  proof: by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def]; rw [map_mul]; rw [hpx]; rw [zero_mul]

中文:
定理 isAlgebraic_iff_is整数egral
  条件: {x : A}
  结论: 是代数 K x ↔ 是整 K x
  证明: by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def]; rw [map_mul]; rw [hpx]; rw [zero_mul]

Depends on / 依赖: IsIntegral, IsIntegral.isAlgebraic, aeval_def, isAlgebraic, map_mul, monic_mul_leadingCoeff_inv, zero_mul
-/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def]; rw [map_mul]; rw [hpx]; rw [zero_mul]

/--
theorem `Algebra.isAlgebraic_iff_isIntegral` / 定理 `Algebra.isAlgebraic_iff_isIntegral`

English:
theorem Algebra.isAlgebraic_iff_isIntegral
  proof: by
  rw [Algebra.isAlgebraic_def]; rw [Algebra.isIntegral_def]; rw [forall_congr' fun _ => isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

中文:
定理 代数.isAlgebraic_iff_is整数egral
  证明: by
  rw [Algebra.isAlgebraic_def]; rw [Algebra.isIntegral_def]; rw [forall_congr' fun _ => isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral
-/
protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def]; rw [Algebra.isIntegral_def]; rw [forall_congr' fun _ => isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/--
Instance `Algebra.IsAlgebraic.isIntegral` / 实例 `Algebra.IsAlgebraic.isIntegral`

English:
instance Algebra.IsAlgebraic.isIntegral
  signature: [Algebra.IsAlgebraic K A]
  body: Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

中文:
实例 代数.是代数.is整数egral
  签名: [代数.是代数 K A]
  定义体: Algebra.isAlgebraic_iff_isIntegral.mp ‹_›
-/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

/--
theorem `Algebra.IsAlgebraic.of_isIntegralClosure` / 定理 `Algebra.IsAlgebraic.of_isIntegralClosure`

English:
theorem Algebra.IsAlgebraic.of_isIntegralClosure
  statement: (R B C : Type*) [CommRing R] [Nontrivial R]
  proof: have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

中文:
定理 代数.是代数.of_is整数egralClosure
  结论: (R B C : 类型) [交换环 R] [非平凡 R]
  证明: have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, isIntegral_algebra
-/
theorem Algebra.IsAlgebraic.of_isIntegralClosure (R B C : Type*) [CommRing R] [Nontrivial R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [IsIntegralClosure B R C] : Algebra.IsAlgebraic R B :=
  have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

end Field

section

variable (K L R : Type*) {A : Type*}

section Ring

variable [CommRing R] [Nontrivial R] [Ring A] [Algebra R A]

/--
theorem `IsAlgebraic.of_finite` / 定理 `IsAlgebraic.of_finite`

English:
theorem IsAlgebraic.of_finite
  given: (e : A) [Module.Finite R A]
  statement: IsAlgebraic R e
  proof: (IsIntegral.of_finite R e).isAlgebraic

中文:
定理 是代数.of_finite
  条件: (e : A) [模.有限 R A]
  结论: 是代数 R e
  证明: (IsIntegral.of_finite R e).isAlgebraic

Depends on / 依赖: IsIntegral, IsIntegral.of_finite, isAlgebraic, of_finite
-/
theorem IsAlgebraic.of_finite (e : A) [Module.Finite R A] : IsAlgebraic R e :=
  (IsIntegral.of_finite R e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
/--
Instance `Algebra.IsAlgebraic.of_finite` / 实例 `Algebra.IsAlgebraic.of_finite`

English:
instance Algebra.IsAlgebraic.of_finite
  signature: [Module.Finite R A]
  body: (IsIntegral.of_finite R A).isAlgebraic

中文:
实例 代数.是代数.of_finite
  签名: [模.有限 R A]
  定义体: (IsIntegral.of_finite R A).isAlgebraic

Depends on / 依赖: IsIntegral, IsIntegral.of_finite, isAlgebraic, of_finite
-/
instance Algebra.IsAlgebraic.of_finite [Module.Finite R A] : Algebra.IsAlgebraic R A :=
  (IsIntegral.of_finite R A).isAlgebraic

end Ring

section Field

variable {K L} [Field K] [Ring A] [Algebra K A]

/-- If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over `K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`. -/
@[simp]
/--
theorem `transcendental_aeval_iff` / 定理 `transcendental_aeval_iff`

English:
theorem transcendental_aeval_iff
  given: {r : A} {f : K[X]}
  proof: by
  refine ⟨fun h => ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ => h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

中文:
定理 transcendental_aeval_iff
  条件: {r : A} {f : K[X]}
  证明: by
  refine ⟨fun h => ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ => h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

Depends on / 依赖: Transcendental, aeval_mem_adjoin_singleton, aeval_of_transcendental, contrapose, fg_adjoin_singleton, h.fg_adjoin_singleton, h.of_aeval, h1.aeval_of_transcendental, isAlgebraic_iff_isIntegral, of_aeval, of_mem_of_fg
-/
theorem transcendental_aeval_iff {r : A} {f : K[X]} :
    Transcendental K (Polynomial.aeval r f) ↔ Transcendental K r ∧ Transcendental K f := by
  refine ⟨fun h => ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ => h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

variable [Field L] [Algebra K L]

variable (K L) in
/--
Definition of `algEquivEquivAlgHom` / `algEquivEquivAlgHom` 的定义

English:
abbreviation algEquivEquivAlgHom
  signature: [FiniteDimensional K L]
  body: Algebra.IsAlgebraic.algEquivEquivAlgHom K L

中文:
缩写 algEquivEquivAlgHom
  签名: [有限维 K L]
  定义体: Algebra.IsAlgebraic.algEquivEquivAlgHom K L

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.algEquivEquivAlgHom, IsAlgebraic, algEquivEquivAlgHom
-/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L ->ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {z : A} {z' : S}

namespace IsAlgebraic

/--
theorem `exists_integral_multiple` / 定理 `exists_integral_multiple`

English:
theorem exists_integral_multiple
  given: (hz : IsAlgebraic R z)
  statement: exists y != (0 : R), IsIntegral R (y • z)
  proof: by
  by_cases inj : Function.Injective (algebraMap R A); swap
  · rw [injective_iff_map_eq_zero] at inj; push Not at inj
    have ⟨r, eq, ne⟩ := inj
    exact ⟨r, ne, by simpa [← algebraMap_smul A, eq, zero_smul] using isIntegral_zero⟩
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have

中文:
定理 存在_integral_multiple
  条件: (hz : 是代数 R z)
  结论: 存在 y != (0 : R), 是整 R (y • z)
  证明: by
  by_cases inj : Function.Injective (algebraMap R A); swap
  · rw [injective_iff_map_eq_zero] at inj; push Not at inj
    have ⟨r, eq, ne⟩ := inj
    exact ⟨r, ne, by simpa [← algebraMap_smul A, eq, zero_smul] using isIntegral_zero⟩
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have

Depends on / 依赖: Function, Function.Injective, Injective, IsIntegral, Polynomial, Polynomial.leadingCoeff_eq_zero.mp, a_ne_zero, algebraMap, algebraMap_smul, injective_iff_map_eq_zero, integralNormalization, integralNormalization_aev, isIntegral_zero, leadingCoeff, leadingCoeff_eq_zero, monic_integralNormalization, p.integralNormalization, p.leadingCoeff, p_ne_zero, x_integral
-/
theorem exists_integral_multiple (hz : IsAlgebraic R z) : exists y != (0 : R), IsIntegral R (y • z) := by
  by_cases inj : Function.Injective (algebraMap R A); swap
  · rw [injective_iff_map_eq_zero] at inj; push Not at inj
    have ⟨r, eq, ne⟩ := inj
    exact ⟨r, ne, by simpa [← algebraMap_smul A, eq, zero_smul] using isIntegral_zero⟩
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have a_ne_zero : a != 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (algebraMap R A a * z) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px fun _ => (map_eq_zero_iff _ inj).mp⟩
  exact ⟨_, a_ne_zero, Algebra.smul_def a z ▸ x_integral⟩

variable (R) in
/--
theorem `_root_.Algebra.IsAlgebraic.exists_integral_multiples` / 定理 `_root_.Algebra.IsAlgebraic.exists_integral_multiples`

English:
theorem _root_.Algebra.IsAlgebraic.exists_integral_multiples
  statement: [NoZeroDivisors R]
  proof: by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x => (alg.1 x).exists_integral_multiple
  refine ⟨∏ x in s, r x, Finset.prod_ne_zero_iff.mpr fun _ _ => hr _, fun _ h => ?_⟩
  classical rw [← Finset.prod_erase_mul _ _ h, mul_smul]
  exact (int _).smul _

中文:
定理 _root_.代数.是代数.存在_integral_multiples
  结论: [无零因子 R]
  证明: by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x => (alg.1 x).exists_integral_multiple
  refine ⟨∏ x in s, r x, Finset.prod_ne_zero_iff.mpr fun _ _ => hr _, fun _ h => ?_⟩
  classical rw [← Finset.prod_erase_mul _ _ h, mul_smul]
  exact (int _).smul _

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.nontrivial, Finset, Finset.prod_erase_mul, Finset.prod_ne_zero_iff.mpr, IsAlgebraic, classical, exists_integral_multiple, mul_smul, nontrivial, prod_erase_mul, prod_ne_zero_iff
-/
theorem _root_.Algebra.IsAlgebraic.exists_integral_multiples [NoZeroDivisors R]
    [alg : Algebra.IsAlgebraic R A] (s : Finset A) :
    exists y != (0 : R), forall z in s, IsIntegral R (y • z) := by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x => (alg.1 x).exists_integral_multiple
  refine ⟨∏ x in s, r x, Finset.prod_ne_zero_iff.mpr fun _ _ => hr _, fun _ h => ?_⟩
  classical rw [← Finset.prod_erase_mul _ _ h, mul_smul]
  exact (int _).smul _

/--
theorem `of_smul_isIntegral` / 定理 `of_smul_isIntegral`

English:
theorem of_smul_isIntegral
  statement: {y : R} (hy : ¬ IsNilpotent y)
  proof: by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h => ?_, by simpa [aeval_comp, Algebra.smul_def] using! eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y != 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero]; rw [← mul_one p.natDegree]; rw [← natDegree_C_mul_X y hy0]; r

中文:
定理 of_smul_is整数egral
  结论: {y : R} (hy : ¬ 是幂零 y)
  证明: by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h => ?_, by simpa [aeval_comp, Algebra.smul_def] using! eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y != 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero]; rw [← mul_one p.natDegree]; rw [← natDegree_C_mul_X y hy0]; r

Depends on / 依赖: Algebra, Algebra.smul_def, aeval_comp, apply_fun, coeff_comp_degree_mul_degree, coeff_zero, leadingCoeff_C_mul_X, mul_one, natDegree, natDegree_C_mul_X, one_mul, p.comp, p.natDegree, smul_def
-/
theorem of_smul_isIntegral {y : R} (hy : ¬ IsNilpotent y)
    (h : IsIntegral R (y • z)) : IsAlgebraic R z := by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h => ?_, by simpa [aeval_comp, Algebra.smul_def] using! eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y != 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero]; rw [← mul_one p.natDegree]; rw [← natDegree_C_mul_X y hy0]; rw [coeff_comp_degree_mul_degree]; rw [monic]; rw [one_mul]; rw [leadingCoeff_C_mul_X] at h
  · exact hy ⟨_, h⟩
  · rw [natDegree_C_mul_X _ hy0]; rintro ⟨⟩

/--
theorem `of_smul` / 定理 `of_smul`

English:
theorem of_smul
  statement: {y : R} (hy : y in nonZeroDivisors R)
  proof: have ⟨p, hp, eval0⟩ := h
  ⟨_, mt (comp_C_mul_X_eq_zero_iff hy).mp hp, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩

中文:
定理 of_smul
  结论: {y : R} (hy : y in nonZeroDivisors R)
  证明: have ⟨p, hp, eval0⟩ := h
  ⟨_, mt (comp_C_mul_X_eq_zero_iff hy).mp hp, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩

Depends on / 依赖: Algebra, Algebra.smul_def, aeval_comp, comp_C_mul_X_eq_zero_iff, smul_def
-/
theorem of_smul {y : R} (hy : y in nonZeroDivisors R)
    (h : IsAlgebraic R (y • z)) : IsAlgebraic R z :=
  have ⟨p, hp, eval0⟩ := h
  ⟨_, mt (comp_C_mul_X_eq_zero_iff hy).mp hp, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩

/--
theorem `iff_exists_smul_integral` / 定理 `iff_exists_smul_integral`

English:
theorem iff_exists_smul_integral
  given: [IsReduced R]
  proof: ⟨(exists_integral_multiple ·), fun ⟨_, hy, int⟩ =>
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

中文:
定理 iff_存在_smul_integral
  条件: [是既约 R]
  证明: ⟨(exists_integral_multiple ·), fun ⟨_, hy, int⟩ =>
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

Depends on / 依赖: exists_integral_multiple, isNilpotent_iff_eq_zero, of_smul_isIntegral
-/
theorem iff_exists_smul_integral [IsReduced R] :
    IsAlgebraic R z ↔ exists y != (0 : R), IsIntegral R (y • z) :=
  ⟨(exists_integral_multiple ·), fun ⟨_, hy, int⟩ =>
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

section integralClosure

variable {K : Type*} [CommRing K] [Algebra S K] [Algebra R K] [IsIntegralClosure S R K]

variable (S)

omit [Algebra R S] in
/--
lemma `exists_smul_eq` / 引理 `exists_smul_eq`

English:
lemma exists_smul_eq
  given: {x : K} (hx : IsAlgebraic R x)
  proof: by
  obtain ⟨r, hr, h⟩ := hx.exists_integral_multiple
.mp h obtain ⟨s, hs⟩ := IsIntegralClosure.isIntegral_iff (A := S)
  exact ⟨r, s, hr, hs.symm⟩

中文:
引理 存在_smul_eq
  条件: {x : K} (hx : 是代数 R x)
  证明: by
  obtain ⟨r, hr, h⟩ := hx.exists_integral_multiple
.mp h obtain ⟨s, hs⟩ := IsIntegralClosure.isIntegral_iff (A := S)
  exact ⟨r, s, hr, hs.symm⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_iff, exists_integral_multiple, hs.symm, hx.exists_integral_multiple, isIntegral_iff
-/
lemma exists_smul_eq {x : K} (hx : IsAlgebraic R x) :
    exists (r : R) (s : S), r != 0 ∧ r • x = algebraMap S K s := by
  obtain ⟨r, hr, h⟩ := hx.exists_integral_multiple
.mp h obtain ⟨s, hs⟩ := IsIntegralClosure.isIntegral_iff (A := S)
  exact ⟨r, s, hr, hs.symm⟩

/--
lemma `exists_nsmul_eq` / 引理 `exists_nsmul_eq`

English:
lemma exists_nsmul_eq
  given: [IsIntegralClosure S Int K] {x : K} (hx : IsAlgebraic Int x)
  proof: by
  obtain ⟨a, s, ha, h⟩ := hx.exists_smul_eq S
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · exact ⟨n, s, mod_cast ha, mod_cast h⟩
  · exact ⟨n, -s, by simpa using ha, by simp [← h]⟩

中文:
引理 存在_nsmul_eq
  条件: [是整闭包 S 整数 K] {x : K} (hx : 是代数 整数 x)
  证明: by
  obtain ⟨a, s, ha, h⟩ := hx.exists_smul_eq S
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · exact ⟨n, s, mod_cast ha, mod_cast h⟩
  · exact ⟨n, -s, by simpa using ha, by simp [← h]⟩

Depends on / 依赖: a.eq_nat_or_neg, eq_nat_or_neg, exists_smul_eq, hx.exists_smul_eq, mod_cast
-/
lemma exists_nsmul_eq [IsIntegralClosure S Int K] {x : K} (hx : IsAlgebraic Int x) :
    exists (m : Nat) (s : S), m != 0 ∧ m • x = algebraMap S K s := by
  obtain ⟨a, s, ha, h⟩ := hx.exists_smul_eq S
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · exact ⟨n, s, mod_cast ha, mod_cast h⟩
  · exact ⟨n, -s, by simpa using ha, by simp [← h]⟩

end integralClosure

section restrictScalars

variable (R) [NoZeroDivisors S]


/--
theorem `restrictScalars_of_isIntegral` / 定理 `restrictScalars_of_isIntegral`

English:
theorem restrictScalars_of_isIntegral
  statement: [int : Algebra.IsIntegral R S]
  proof: by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple
  cases su

中文:
定理 restrictScalars_of_is整数egral
  结论: [int : 代数.是整 R S]
  证明: by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple
  cases su

Depends on / 依赖: Algebra, Algebra.isAlgebraic_of_not_injective, Function, Function.Injective, Injective, IsScalarTower, IsScalarTower.algebraMap_eq, Module, Module.subsingleton, algebraMap, algebraMap_eq, exists_integral_multiple, exists_nonzero_dvd, h.exists_integral_multiple, hRS.noZeroDivisors, int_s, isAlgebraic, isAlgebraic.exists_nonzero_dvd, isAlgebraic_of_not_injective, is_transcendental_of_subsingleton
-/
theorem restrictScalars_of_isIntegral [int : Algebra.IsIntegral R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R S
    exact (is_transcendental_of_subsingleton _ _ h).elim
  have ⟨r, hr, _, e⟩ := (int.1 s).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hs)
  refine .of_smul_isIntegral (y := r) (by rwa [isNilpotent_iff_eq_zero]) ?_
  rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [e]; rw [← Algebra.smul_def]; rw [mul_comm]; rw [mul_smul]
  exact isIntegral_trans _ (int_s.smul _)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `restrictScalars` / 定理 `restrictScalars`

English:
theorem restrictScalars
  statement: [Algebra.IsAlgebraic R S]
  proof: by
  have ⟨p, hp, eval0⟩ := h
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  rw [← faithfulSMul_iff_algebraMap_injective] at hRS
  have := NoZeroDivisors.of_faithfulS

中文:
定理 restrictScalars
  结论: [代数.是代数 R S]
  证明: by
  have ⟨p, hp, eval0⟩ := h
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  rw [← faithfulSMul_iff_algebraMap_injective] at hRS
  have := NoZeroDivisors.of_faithfulS

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.exists_integral_multiples, Algebra.isAlgebraic_of_not_injective, Algebra.nontrivial_of_isAlgebraic, Function, Function.Injective, Injective, IsAlgebraic, IsDomain, IsScalarTower, IsScalarTower.algebraMap_eq, NoZeroDivisors, NoZeroDivisors.of_faithfulSMul, NoZeroDivisors.to_isDomain, algebraMap, algebraMap_eq, classical, exists_integral_multiples, faithfulSMul_iff_algebraMap_injective, isAlgebraic_of_not_injective
-/
theorem restrictScalars [Algebra.IsAlgebraic R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  have ⟨p, hp, eval0⟩ := h
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
fun h => hRS .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  rw [← faithfulSMul_iff_algebraMap_injective] at hRS
  have := NoZeroDivisors.of_faithfulSMul R S
  have := Algebra.nontrivial_of_isAlgebraic R S
  have : IsDomain R := NoZeroDivisors.to_isDomain _
  classical
  have ⟨r, hr, int⟩ := Algebra.IsAlgebraic.exists_integral_multiples R (p.support.image (coeff p))
  let p := (r • p).toSubring (integralClosure R S).toSubring fun s hs => by
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hs
    exact int _ (Finset.mem_image_of_mem _ <| support_smul _ _ hn)
  have : IsAlgebraic (integralClosure R S) a := by
    refine ⟨p, ?_, ?_⟩
    · simpa only [← Polynomial.map_ne_zero_iff (f := Subring.subtype _) (p := p)
        Subtype.val_injective, p, map_toSubring, smul_ne_zero_iff] using And.intro hr hp
    rw [← eval_map_algebraMap]; rw [Subalgebra.algebraMap_eq]; rw [← map_map]; rw [← Subalgebra.toSubring_subtype]; rw [map_toSubring]; rw [eval_map_algebraMap]; rw [← AlgHom.restrictScalars_apply R]; rw [map_smul]; rw [AlgHom.restrictScalars_apply]; rw [eval0]; rw [smul_zero]
  exact restrictScalars_of_isIntegral _ this

/--
theorem `_root_.IsIntegral.trans_isAlgebraic` / 定理 `_root_.IsIntegral.trans_isAlgebraic`

English:
theorem _root_.IsIntegral.trans_isAlgebraic
  statement: [alg : Algebra.IsAlgebraic R S]
  proof: by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _

中文:
定理 _root_.是整.trans_isAlgebraic
  结论: [alg : 代数.是代数 R S]
  证明: by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.nontrivial, IsAlgebraic, Module, Module.nontrivial, Subsingleton, Subsingleton.elim, h.isAlgebraic.restrictScalars, isAlgebraic, isAlgebraic_zero, nontrivial, restrictScalars, subsingleton_or_nontrivial
-/
theorem _root_.IsIntegral.trans_isAlgebraic [alg : Algebra.IsAlgebraic R S]
    {a : A} (h : IsIntegral S a) : IsAlgebraic R a := by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _

end restrictScalars

section Ring

variable (s : S) {a : A} (ha : IsAlgebraic R a)
include ha

/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  statement: IsAlgebraic R (-a)
  proof: have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩

中文:
引理 neg
  结论: 是代数 R (-a)
  证明: have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩
-/
protected lemma neg : IsAlgebraic R (-a) :=
  have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (r : R)
  statement: IsAlgebraic R (r • a)
  proof: have ⟨_, hp, eval0⟩ := ha
  ⟨_, scaleRoots_ne_zero hp r, Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩

中文:
引理 smul
  条件: (r : R)
  结论: 是代数 R (r • a)
  证明: have ⟨_, hp, eval0⟩ := ha
  ⟨_, scaleRoots_ne_zero hp r, Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩
-/
protected lemma smul (r : R) : IsAlgebraic R (r • a) :=
  have ⟨_, hp, eval0⟩ := ha
  ⟨_, scaleRoots_ne_zero hp r, Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩

/--
lemma `nsmul` / 引理 `nsmul`

English:
lemma nsmul
  given: (n : Nat)
  statement: IsAlgebraic R (n • a)
  proof: Nat.cast_smul_eq_nsmul R n a ▸ ha.smul _

中文:
引理 nsmul
  条件: (n : 自然数)
  结论: 是代数 R (n • a)
  证明: Nat.cast_smul_eq_nsmul R n a ▸ ha.smul _
-/
protected lemma nsmul (n : Nat) : IsAlgebraic R (n • a) :=
  Nat.cast_smul_eq_nsmul R n a ▸ ha.smul _

/--
lemma `zsmul` / 引理 `zsmul`

English:
lemma zsmul
  given: (n : Int)
  statement: IsAlgebraic R (n • a)
  proof: Int.cast_smul_eq_zsmul R n a ▸ ha.smul _

omit [Algebra S A] [IsScalarTower R S A] in

中文:
引理 zsmul
  条件: (n : 整数)
  结论: 是代数 R (n • a)
  证明: Int.cast_smul_eq_zsmul R n a ▸ ha.smul _

omit [Algebra S A] [IsScalarTower R S A] in
-/
protected lemma zsmul (n : Int) : IsAlgebraic R (n • a) :=
  Int.cast_smul_eq_zsmul R n a ▸ ha.smul _

omit [Algebra S A] [IsScalarTower R S A] in
/--
lemma `tmul` / 引理 `tmul`

English:
lemma tmul
  given: [FaithfulSMul R S]
  statement: IsAlgebraic S (s otimesₜ[R] a)
  proof: by
  rw [← mul_one s]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
  have ⟨p, h, eval0⟩ := ha
  refine .smul ⟨p.map (algebraMap R S),
    (Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective ..).mpr h, ?_⟩ _
  rw [← Algebra.TensorProduct.includeRight_apply]; rw [← AlgHom.coe_toRi

中文:
引理 tmul
  条件: [忠实标量乘法 R S]
  结论: 是代数 S (s otimesₜ[R] a)
  证明: by
  rw [← mul_one s]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
  have ⟨p, h, eval0⟩ := ha
  refine .smul ⟨p.map (algebraMap R S),
    (Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective ..).mpr h, ?_⟩ _
  rw [← Algebra.TensorProduct.includeRight_apply]; rw [← AlgHom.coe_toRi

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Algebra, Algebra.TensorProduct.includeRight_apply, FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_ne_zero_iff, TensorProduct, TensorProduct.smul_tmul, algebraMap, algebraMap_injective, coe_toRingHom, includeRight_apply, map_aeval_eq_aeval_map, map_ne_zero_iff, map_zero, mul_one, p.map, smul_eq_mul
-/
lemma tmul [FaithfulSMul R S] : IsAlgebraic S (s otimesₜ[R] a) := by
  rw [← mul_one s]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
  have ⟨p, h, eval0⟩ := ha
  refine .smul ⟨p.map (algebraMap R S),
    (Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective ..).mpr h, ?_⟩ _
  rw [← Algebra.TensorProduct.includeRight_apply]; rw [← AlgHom.coe_toRingHom (A := A)]; rw [← map_aeval_eq_aeval_map (by ext; simp)]; rw [eval0]; rw [map_zero]

end Ring

section CommRing

variable [NoZeroDivisors R] {a b : S} (ha : IsAlgebraic R a) (hb : IsAlgebraic R b)
include ha hb

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  statement: IsAlgebraic R (a * b)
  proof: by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b

中文:
引理 mul
  结论: 是代数 R (a * b)
  证明: by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b
-/
protected lemma mul : IsAlgebraic R (a * b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: IsAlgebraic R (a + b)
  proof: by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add]; rw [mul_smul]; rw [mul_comm]; rw [mul_smul]
  exact (int_a.smul _).add (int_b.smul _)

中文:
引理 add
  结论: 是代数 R (a + b)
  证明: by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add]; rw [mul_smul]; rw [mul_comm]; rw [mul_smul]
  exact (int_a.smul _).add (int_b.smul _)
-/
protected lemma add : IsAlgebraic R (a + b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add]; rw [mul_smul]; rw [mul_comm]; rw [mul_smul]
  exact (int_a.smul _).add (int_b.smul _)

/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  statement: IsAlgebraic R (a - b)
  proof: sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb

中文:
引理 sub
  结论: 是代数 R (a - b)
  证明: sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
-/
protected lemma sub : IsAlgebraic R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: (n : Nat)
  statement: IsAlgebraic R (a ^ n)
  proof: have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h => pow_succ a _ ▸ h.mul ha

中文:
引理 pow
  条件: (n : 自然数)
  结论: 是代数 R (a ^ n)
  证明: have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h => pow_succ a _ ▸ h.mul ha
-/
protected lemma pow (n : Nat) : IsAlgebraic R (a ^ n) :=
  have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h => pow_succ a _ ▸ h.mul ha

end CommRing

end IsAlgebraic

namespace Algebra

variable (R S A) [NoZeroDivisors S]

/--
theorem `IsAlgebraic.trans` / 定理 `IsAlgebraic.trans`

English:
theorem IsAlgebraic.trans
  given: [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A]
  proof: ⟨fun _ => (alg.1 _).restrictScalars _⟩

中文:
定理 是代数.trans
  条件: [代数.是代数 R S] [alg : 代数.是代数 S A]
  证明: ⟨fun _ => (alg.1 _).restrictScalars _⟩
-/
@[stacks 09GJ] theorem IsAlgebraic.trans [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ => (alg.1 _).restrictScalars _⟩

/--
theorem `IsIntegral.trans_isAlgebraic` / 定理 `IsIntegral.trans_isAlgebraic`

English:
theorem IsIntegral.trans_isAlgebraic
  given: [Algebra.IsIntegral R S] [alg : Algebra.IsAlgebraic S A]
  proof: ⟨fun _ => (alg.1 _).restrictScalars_of_isIntegral _⟩

中文:
定理 是整.trans_isAlgebraic
  条件: [代数.是整 R S] [alg : 代数.是代数 S A]
  证明: ⟨fun _ => (alg.1 _).restrictScalars_of_isIntegral _⟩

Depends on / 依赖: restrictScalars_of_isIntegral
-/
theorem IsIntegral.trans_isAlgebraic [Algebra.IsIntegral R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ => (alg.1 _).restrictScalars_of_isIntegral _⟩

/--
theorem `IsAlgebraic.trans_isIntegral` / 定理 `IsAlgebraic.trans_isIntegral`

English:
theorem IsAlgebraic.trans_isIntegral
  given: [Algebra.IsAlgebraic R S] [int : Algebra.IsIntegral S A]
  proof: ⟨fun _ => (int.1 _).trans_isAlgebraic _⟩

中文:
定理 是代数.trans_is整数egral
  条件: [代数.是代数 R S] [int : 代数.是整 S A]
  证明: ⟨fun _ => (int.1 _).trans_isAlgebraic _⟩

Depends on / 依赖: trans_isAlgebraic
-/
theorem IsAlgebraic.trans_isIntegral [Algebra.IsAlgebraic R S] [int : Algebra.IsIntegral S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ => (int.1 _).trans_isAlgebraic _⟩

variable {A}

/--
theorem `IsIntegral.isAlgebraic_iff` / 定理 `IsIntegral.isAlgebraic_iff`

English:
theorem IsIntegral.isAlgebraic_iff
  statement: [Algebra.IsIntegral R S] [FaithfulSMul R S]
  proof: ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars_of_isIntegral _⟩

中文:
定理 是整.isAlgebraic_iff
  结论: [代数.是整 R S] [忠实标量乘法 R S]
  证明: ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars_of_isIntegral _⟩
-/
protected theorem IsIntegral.isAlgebraic_iff [Algebra.IsIntegral R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars_of_isIntegral _⟩

/--
theorem `IsIntegral.isAlgebraic_iff_top` / 定理 `IsIntegral.isAlgebraic_iff_top`

English:
theorem IsIntegral.isAlgebraic_iff_top
  statement: [Algebra.IsIntegral R S]
  proof: by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsIntegral.isAlgebraic_iff R S]

中文:
定理 是整.isAlgebraic_iff_top
  结论: [代数.是整 R S]
  证明: by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsIntegral.isAlgebraic_iff R S]

Depends on / 依赖: Algebra, Algebra.IsIntegral.isAlgebraic_iff, Algebra.isAlgebraic_def, IsIntegral, isAlgebraic_def, isAlgebraic_iff, simp_rw
-/
theorem IsIntegral.isAlgebraic_iff_top [Algebra.IsIntegral R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsIntegral.isAlgebraic_iff R S]

/--
theorem `IsAlgebraic.isAlgebraic_iff` / 定理 `IsAlgebraic.isAlgebraic_iff`

English:
theorem IsAlgebraic.isAlgebraic_iff
  statement: [Algebra.IsAlgebraic R S] [FaithfulSMul R S]
  proof: ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars _⟩

中文:
定理 是代数.isAlgebraic_iff
  结论: [代数.是代数 R S] [忠实标量乘法 R S]
  证明: ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars _⟩
-/
protected theorem IsAlgebraic.isAlgebraic_iff [Algebra.IsAlgebraic R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars _⟩

/--
theorem `IsAlgebraic.isAlgebraic_iff_top` / 定理 `IsAlgebraic.isAlgebraic_iff_top`

English:
theorem IsAlgebraic.isAlgebraic_iff_top
  statement: [Algebra.IsAlgebraic R S]
  proof: by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsAlgebraic.isAlgebraic_iff R S]

中文:
定理 是代数.isAlgebraic_iff_top
  结论: [代数.是代数 R S]
  证明: by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsAlgebraic.isAlgebraic_iff R S]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic_iff, Algebra.isAlgebraic_def, IsAlgebraic, isAlgebraic_def, isAlgebraic_iff, simp_rw
-/
theorem IsAlgebraic.isAlgebraic_iff_top [Algebra.IsAlgebraic R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsAlgebraic.isAlgebraic_iff R S]

/--
theorem `IsAlgebraic.isAlgebraic_iff_bot` / 定理 `IsAlgebraic.isAlgebraic_iff_bot`

English:
theorem IsAlgebraic.isAlgebraic_iff_bot
  given: [Algebra.IsAlgebraic S A] [FaithfulSMul S A]
  proof: ⟨fun _ => .tower_bot_of_injective (FaithfulSMul.algebraMap_injective S A), fun _ => .trans R S A⟩

中文:
定理 是代数.isAlgebraic_iff_bot
  条件: [代数.是代数 S A] [忠实标量乘法 S A]
  证明: ⟨fun _ => .tower_bot_of_injective (FaithfulSMul.algebraMap_injective S A), fun _ => .trans R S A⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, tower_bot_of_injective
-/
theorem IsAlgebraic.isAlgebraic_iff_bot [Algebra.IsAlgebraic S A] [FaithfulSMul S A] :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R S :=
  ⟨fun _ => .tower_bot_of_injective (FaithfulSMul.algebraMap_injective S A), fun _ => .trans R S A⟩

end Algebra

variable (R S)
/--
Definition of `Subalgebra.algebraicClosure` / `Subalgebra.algebraicClosure` 的定义

English:
definition Subalgebra.algebraicClosure
  signature: [IsDomain R]
  body: {s | IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

中文:
定义 子代数.algebraicClosure
  签名: [是整环 R]
  定义体: {s | IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

Depends on / 依赖: IsAlgebraic
-/
def Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where
  carrier := {s | IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

/--
theorem `Subalgebra.mem_algebraicClosure` / 定理 `Subalgebra.mem_algebraicClosure`

English:
theorem Subalgebra.mem_algebraicClosure
  given: [IsDomain R] {x : S}
  proof: Iff.rfl

中文:
定理 子代数.mem_algebraicClosure
  条件: [是整环 R] {x : S}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Subalgebra.mem_algebraicClosure [IsDomain R] {x : S} :
    x in algebraicClosure R S ↔ IsAlgebraic R x := Iff.rfl

/--
theorem `integralClosure_le_algebraicClosure` / 定理 `integralClosure_le_algebraicClosure`

English:
theorem integralClosure_le_algebraicClosure
  given: [IsDomain R]
  proof: fun _ => IsIntegral.isAlgebraic

中文:
定理 integralClosure_le_algebraicClosure
  条件: [是整环 R]
  证明: fun _ => IsIntegral.isAlgebraic

Depends on / 依赖: IsIntegral, IsIntegral.isAlgebraic, isAlgebraic
-/
theorem integralClosure_le_algebraicClosure [IsDomain R] :
    integralClosure R S <= Subalgebra.algebraicClosure R S :=
  fun _ => IsIntegral.isAlgebraic

/--
theorem `Subalgebra.algebraicClosure_eq_integralClosure` / 定理 `Subalgebra.algebraicClosure_eq_integralClosure`

English:
theorem Subalgebra.algebraicClosure_eq_integralClosure
  given: {K} [Field K] [Algebra K S]
  proof: SetLike.ext fun _ => isAlgebraic_iff_isIntegral

中文:
定理 子代数.algebraicClosure_eq_integralClosure
  条件: {K} [域 K] [代数 K S]
  证明: SetLike.ext fun _ => isAlgebraic_iff_isIntegral

Depends on / 依赖: SetLike, SetLike.ext, isAlgebraic_iff_isIntegral
-/
theorem Subalgebra.algebraicClosure_eq_integralClosure {K} [Field K] [Algebra K S] :
    algebraicClosure K S = integralClosure K S :=
  SetLike.ext fun _ => isAlgebraic_iff_isIntegral

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] : Algebra.IsAlgebraic R (Subalgebra.algebraicClosure R S)
  body: (Subalgebra.isAlgebraic_iff _).mp fun _ => id

中文:
实例 [是整环
  签名: R] : 代数.是代数 R (子代数.algebraicClosure R S)
  定义体: (Subalgebra.isAlgebraic_iff _).mp fun _ => id

Depends on / 依赖: Subalgebra, Subalgebra.isAlgebraic_iff, isAlgebraic_iff
-/
instance [IsDomain R] : Algebra.IsAlgebraic R (Subalgebra.algebraicClosure R S) :=
  (Subalgebra.isAlgebraic_iff _).mp fun _ => id

variable {R S}

/--
theorem `Algebra.isAlgebraic_adjoin_iff` / 定理 `Algebra.isAlgebraic_adjoin_iff`

English:
theorem Algebra.isAlgebraic_adjoin_iff
  given: [IsDomain R] {s : Set S}
  proof: Algebra.adjoin_le_iff (S := Subalgebra.algebraicClosure R S)

中文:
定理 代数.isAlgebraic_adjoin_iff
  条件: [是整环 R] {s : 集合 S}
  证明: Algebra.adjoin_le_iff (S := Subalgebra.algebraicClosure R S)

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Subalgebra, Subalgebra.algebraicClosure, adjoin_le_iff, algebraicClosure
-/
theorem Algebra.isAlgebraic_adjoin_iff [IsDomain R] {s : Set S} :
    (adjoin R s).IsAlgebraic ↔ forall x in s, IsAlgebraic R x :=
  Algebra.adjoin_le_iff (S := Subalgebra.algebraicClosure R S)

/--
theorem `Algebra.isAlgebraic_adjoin_of_nonempty` / 定理 `Algebra.isAlgebraic_adjoin_of_nonempty`

English:
theorem Algebra.isAlgebraic_adjoin_of_nonempty
  given: [NoZeroDivisors R] {s : Set S} (hs : s.Nonempty)
  proof: ⟨fun h x hx => h _ (subset_adjoin hx), fun h =>
    have ⟨x, hx⟩ := hs
    have := (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨‹_›, (h x hx).nontrivial⟩
    isAlgebraic_adjoin_iff.mpr h⟩

中文:
定理 代数.isAlgebraic_adjoin_of_nonempty
  条件: [无零因子 R] {s : 集合 S} (hs : s.非空)
  证明: ⟨fun h x hx => h _ (subset_adjoin hx), fun h =>
    have ⟨x, hx⟩ := hs
    have := (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨‹_›, (h x hx).nontrivial⟩
    isAlgebraic_adjoin_iff.mpr h⟩

Depends on / 依赖: isAlgebraic_adjoin_iff, isAlgebraic_adjoin_iff.mpr, isDomain_iff_noZeroDivisors_and_nontrivial, nontrivial, subset_adjoin
-/
theorem Algebra.isAlgebraic_adjoin_of_nonempty [NoZeroDivisors R] {s : Set S} (hs : s.Nonempty) :
    (adjoin R s).IsAlgebraic ↔ forall x in s, IsAlgebraic R x :=
  ⟨fun h x hx => h _ (subset_adjoin hx), fun h =>
    have ⟨x, hx⟩ := hs
    have := (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨‹_›, (h x hx).nontrivial⟩
    isAlgebraic_adjoin_iff.mpr h⟩

/--
theorem `Algebra.isAlgebraic_adjoin_singleton_iff` / 定理 `Algebra.isAlgebraic_adjoin_singleton_iff`

English:
theorem Algebra.isAlgebraic_adjoin_singleton_iff
  given: [NoZeroDivisors R] {s : S}
  proof: (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq

中文:
定理 代数.isAlgebraic_adjoin_singleton_iff
  条件: [无零因子 R] {s : S}
  证明: (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq

Depends on / 依赖: Set.singleton_nonempty, forall_eq, isAlgebraic_adjoin_of_nonempty, singleton_nonempty
-/
theorem Algebra.isAlgebraic_adjoin_singleton_iff [NoZeroDivisors R] {s : S} :
    (adjoin R {s}).IsAlgebraic ↔ IsAlgebraic R s :=
  (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq

/--
theorem `IsAlgebraic.of_mul` / 定理 `IsAlgebraic.of_mul`

English:
theorem IsAlgebraic.of_mul
  statement: [NoZeroDivisors R] {y z : S} (hy : y in nonZeroDivisors S)
  proof: by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm]; rw [eq]; rw [← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

中文:
定理 是代数.of_mul
  结论: [无零因子 R] {y z : S} (hy : y in nonZeroDivisors S)
  证明: by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm]; rw [eq]; rw [← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

Depends on / 依赖: Algebra, Algebra.isAlgebraic_adjoin_singleton_iff.mpr, Algebra.smul_def, alg_y, alg_y.exists_nonzero_eq_adjoin_mul, alg_yz, alg_yz.mul, exists_nonzero_eq_adjoin_mul, isAlgebraic_adjoin_singleton_iff, mem_nonZeroDivisors_of_ne_zero, mul_right_comm, of_smul, smul_def, this.of_smul
-/
theorem IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy : y in nonZeroDivisors S)
    (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z := by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm]; rw [eq]; rw [← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

open Algebra in
omit [Algebra R A] [IsScalarTower R S A] in
/--
theorem `IsAlgebraic.adjoin_of_forall_isAlgebraic` / 定理 `IsAlgebraic.adjoin_of_forall_isAlgebraic`

English:
theorem IsAlgebraic.adjoin_of_forall_isAlgebraic
  statement: [NoZeroDivisors S] {s t : Set S}
  proof: by
  set Rs := adjoin R s
  set Rt := adjoin R t
  let Rts := adjoin Rt s
  let _ : Algebra Rs Rts := (Subalgebra.inclusion
(T := Rts.restrictScalars R) adjoin_le by apply subset_adjoin).toAlgebra
  have : IsScalarTower Rs Rts A := .of_algebraMap_eq fun ⟨a, _⟩ => rfl
  have : Algebra.IsAlgebraic Rt 

中文:
定理 是代数.adjoin_of_对任意_isAlgebraic
  结论: [无零因子 S] {s t : 集合 S}
  证明: by
  set Rs := adjoin R s
  set Rt := adjoin R t
  let Rts := adjoin Rt s
  let _ : Algebra Rs Rts := (Subalgebra.inclusion
(T := Rts.restrictScalars R) adjoin_le by apply subset_adjoin).toAlgebra
  have : IsScalarTower Rs Rts A := .of_algebraMap_eq fun ⟨a, _⟩ => rfl
  have : Algebra.IsAlgebraic Rt 

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, IsAlgebraic, IsScalarTower, Rts.restrictScalars, Subalgebra, Subalgebra.inclusion, Subalgebra.isAlgebraic_if, Subtype, Subtype.val_injective, adjoin, adjoin_le, ha.nontrivial, inclusion, isAlgebraic_if, isDomain_iff_noZeroDivisors_and_nontrivial, nontrivial, of_algebraMap_eq, restrictScalars, subset_adjoin
-/
theorem IsAlgebraic.adjoin_of_forall_isAlgebraic [NoZeroDivisors S] {s t : Set S}
    (alg : forall x in s \ t, IsAlgebraic (adjoin R t) x) {a : A}
    (ha : IsAlgebraic (adjoin R s) a) : IsAlgebraic (adjoin R t) a := by
  set Rs := adjoin R s
  set Rt := adjoin R t
  let Rts := adjoin Rt s
  let _ : Algebra Rs Rts := (Subalgebra.inclusion
(T := Rts.restrictScalars R) adjoin_le by apply subset_adjoin).toAlgebra
  have : IsScalarTower Rs Rts A := .of_algebraMap_eq fun ⟨a, _⟩ => rfl
  have : Algebra.IsAlgebraic Rt Rts := by
    have := ha.nontrivial
    have := Subtype.val_injective (p := (· in Rs)).nontrivial
    have := (isDomain_iff_noZeroDivisors_and_nontrivial Rt).mpr ⟨inferInstance, inferInstance⟩
    rw [← Subalgebra.isAlgebraic_iff]; rw [isAlgebraic_adjoin_iff]
    intro x hs
    by_cases ht : x in t
    · exact isAlgebraic_algebraMap (⟨x, subset_adjoin ht⟩ : Rt)
    exact alg _ ⟨hs, ht⟩
  have : IsAlgebraic Rts a := ha.extendScalars (by apply Subalgebra.inclusion_injective)
  exact this.restrictScalars Rt

namespace Transcendental

section

variable (S) [NoZeroDivisors S] {a : A} (ha : Transcendental R a)
include ha

/--
lemma `extendScalars_of_isIntegral` / 引理 `extendScalars_of_isIntegral`

English:
lemma extendScalars_of_isIntegral
  given: [Algebra.IsIntegral R S]
  proof: by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _

中文:
引理 extendScalars_of_is整数egral
  条件: [代数.是整 R S]
  证明: by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _

Depends on / 依赖: Transcendental, contrapose, ha.restrictScalars_of_isIntegral, not_not, restrictScalars_of_isIntegral
-/
lemma extendScalars_of_isIntegral [Algebra.IsIntegral R S] :
    Transcendental S a := by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _

/--
lemma `extendScalars` / 引理 `extendScalars`

English:
lemma extendScalars
  given: [Algebra.IsAlgebraic R S]
  statement: Transcendental S a
  proof: by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars _

中文:
引理 extendScalars
  条件: [代数.是代数 R S]
  结论: 超越 S a
  证明: by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars _

Depends on / 依赖: Transcendental, contrapose, ha.restrictScalars, not_not, restrictScalars
-/
lemma extendScalars [Algebra.IsAlgebraic R S] : Transcendental S a := by
  contrapose ha
  rw [Transcendental]; rw [not_not] at ha ⊢
  exact ha.restrictScalars _

end

variable [NoZeroDivisors S] {a : S} (ha : Transcendental R a)
include ha

/--
lemma `integralClosure` / 引理 `integralClosure`

English:
lemma integralClosure
  statement: Transcendental (integralClosure R S) a
  proof: ha.extendScalars_of_isIntegral _

中文:
引理 integralClosure
  结论: 超越 (integralClosure R S) a
  证明: ha.extendScalars_of_isIntegral _
-/
protected lemma integralClosure : Transcendental (integralClosure R S) a :=
  ha.extendScalars_of_isIntegral _

/--
lemma `subalgebraAlgebraicClosure` / 引理 `subalgebraAlgebraicClosure`

English:
lemma subalgebraAlgebraicClosure
  given: [IsDomain R]
  proof: ha.extendScalars _

中文:
引理 subalgebraAlgebraicClosure
  条件: [是整环 R]
  证明: ha.extendScalars _

Depends on / 依赖: extendScalars, ha.extendScalars
-/
lemma subalgebraAlgebraicClosure [IsDomain R] :
    Transcendental (Subalgebra.algebraicClosure R S) a := ha.extendScalars _

end Transcendental

namespace Algebra

variable (R S) [NoZeroDivisors S] [FaithfulSMul R S] {a : A}

/--
theorem `IsIntegral.transcendental_iff` / 定理 `IsIntegral.transcendental_iff`

English:
theorem IsIntegral.transcendental_iff
  given: [Algebra.IsIntegral R S]
  proof: ⟨(·.extendScalars_of_isIntegral _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

中文:
定理 是整.transcendental_iff
  条件: [代数.是整 R S]
  证明: ⟨(·.extendScalars_of_isIntegral _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
-/
protected theorem IsIntegral.transcendental_iff [Algebra.IsIntegral R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars_of_isIntegral _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

/--
theorem `IsAlgebraic.transcendental_iff` / 定理 `IsAlgebraic.transcendental_iff`

English:
theorem IsAlgebraic.transcendental_iff
  given: [Algebra.IsAlgebraic R S]
  proof: ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

中文:
定理 是代数.transcendental_iff
  条件: [代数.是代数 R S]
  证明: ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
-/
protected theorem IsAlgebraic.transcendental_iff [Algebra.IsAlgebraic R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

end Algebra

open scoped nonZeroDivisors

namespace Algebra.IsAlgebraic

section IsFractionRing

variable (R S) (R' S' : Type*) [CommRing S'] [FaithfulSMul R S] [alg : Algebra.IsAlgebraic R S]
  [NoZeroDivisors S] [Algebra S S'] [IsFractionRing S S']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (algebraMapSubmonoid S R⁰) S'
  body: have := (FaithfulSMul.algebraMap_injective R S).noZeroDivisors _ (map_zero _) (map_mul _)
  (IsLocalization.iff_of_le_of_exists_dvd _ S⁰
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ..) le_rfl)
    fun s hs => have ⟨r, ne, eq⟩ := (alg.1 s).exists_nonzero_dvd hs
    ⟨

中文:
实例 :
  签名: 是Localization (algebraMapSubmonoid S R⁰) S'
  定义体: have := (FaithfulSMul.algebraMap_injective R S).noZeroDivisors _ (map_zero _) (map_mul _)
  (IsLocalization.iff_of_le_of_exists_dvd _ S⁰
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ..) le_rfl)
    fun s hs => have ⟨r, ne, eq⟩ := (alg.1 s).exists_nonzero_dvd hs
    ⟨

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsLocalization, IsLocalization.iff_of_le_of_exists_dvd, algebraMap_injective, exists_nonzero_dvd, iff_of_le_of_exists_dvd, le_rfl, map_le_nonZeroDivisors_of_injective, map_mul, map_zero, mem_nonZeroDivisors_of_ne_zero, noZeroDivisors
-/
instance : IsLocalization (algebraMapSubmonoid S R⁰) S' :=
  have := (FaithfulSMul.algebraMap_injective R S).noZeroDivisors _ (map_zero _) (map_mul _)
  (IsLocalization.iff_of_le_of_exists_dvd _ S⁰
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ..) le_rfl)
    fun s hs => have ⟨r, ne, eq⟩ := (alg.1 s).exists_nonzero_dvd hs
    ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

variable [Algebra R S'] [IsScalarTower R S S']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalizedModule R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap
  body: isLocalizedModule_iff_isLocalization.mpr inferInstance

中文:
实例 :
  签名: 是Localized模 R⁰ (标量塔.toAlgHom R S S').toLinearMap
  定义体: isLocalizedModule_iff_isLocalization.mpr inferInstance

Depends on / 依赖: isLocalizedModule_iff_isLocalization, isLocalizedModule_iff_isLocalization.mpr
-/
instance : IsLocalizedModule R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

variable [CommRing R'] [Algebra R R'] [IsFractionRing R R']

/--
theorem `isBaseChange_of_isFractionRing` / 定理 `isBaseChange_of_isFractionRing`

English:
theorem isBaseChange_of_isFractionRing
  given: [Module R' S'] [IsScalarTower R R' S']
  proof: (isLocalizedModule_iff_isBaseChange R⁰ ..).mp inferInstance

中文:
定理 isBaseChange_of_isFractionRing
  条件: [模 R' S'] [标量塔 R R' S']
  证明: (isLocalizedModule_iff_isBaseChange R⁰ ..).mp inferInstance

Depends on / 依赖: isLocalizedModule_iff_isBaseChange
-/
theorem isBaseChange_of_isFractionRing [Module R' S'] [IsScalarTower R R' S'] :
    IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap :=
  (isLocalizedModule_iff_isBaseChange R⁰ ..).mp inferInstance

variable [Algebra R' S'] [IsScalarTower R R' S']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPushout R R' S S'
  body: (isPushout_iff ..).mpr isBaseChange_of_isFractionRing ..

中文:
实例 :
  签名: 是推出 R R' S S'
  定义体: (isPushout_iff ..).mpr isBaseChange_of_isFractionRing ..

Depends on / 依赖: isBaseChange_of_isFractionRing, isPushout_iff
-/
instance : IsPushout R R' S S' := (isPushout_iff ..).mpr isBaseChange_of_isFractionRing ..
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPushout R S R' S'
  body: .symm inferInstance

中文:
实例 :
  签名: 是推出 R S R' S'
  定义体: .symm inferInstance
-/
instance : IsPushout R S R' S' := .symm inferInstance

end IsFractionRing

variable (R) (R' : Type*) (S : Type u) [CommRing R'] [CommRing S] [Algebra R S]
  [Algebra R R'] [IsFractionRing R R'] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]

section

variable [NoZeroDivisors S] (S' : Type v) [CommRing S'] [Algebra R S'] [Algebra S S'] [Module R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S']

/--
theorem `lift_rank_of_isFractionRing` / 定理 `lift_rank_of_isFractionRing`

English:
theorem lift_rank_of_isFractionRing
  proof: by
  rw [IsLocalization.rank_eq R' R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap le_rfl]

@[deprecated (since := "2026-07-13")] alias finrank_of_isFractionRing := IsFractionRing.finrank_eq

中文:
定理 lift_rank_of_isFractionRing
  证明: by
  rw [IsLocalization.rank_eq R' R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap le_rfl]

@[deprecated (since := "2026-07-13")] alias finrank_of_isFractionRing := IsFractionRing.finrank_eq

Depends on / 依赖: IsLocalization, IsLocalization.rank_eq, IsLocalizedModule, IsLocalizedModule.lift_rank_eq, IsScalarTower, IsScalarTower.toAlgHom, le_rfl, lift_rank_eq, rank_eq, toAlgHom, toLinearMap
-/
theorem lift_rank_of_isFractionRing :
    Cardinal.lift.{u} (Module.rank R' S') = Cardinal.lift.{v} (Module.rank R S) := by
  rw [IsLocalization.rank_eq R' R⁰ le_rfl]; rw [IsLocalizedModule.lift_rank_eq R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap le_rfl]

@[deprecated (since := "2026-07-13")] alias finrank_of_isFractionRing := IsFractionRing.finrank_eq

/--
theorem `rank_of_isFractionRing` / 定理 `rank_of_isFractionRing`

English:
theorem rank_of_isFractionRing
  statement: (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
  proof: by
  simpa using lift_rank_of_isFractionRing R R' S S'

中文:
定理 rank_of_isFractionRing
  结论: (S' : 类型u) [交换环 S'] [代数 R S'] [代数 S S']
  证明: by
  simpa using lift_rank_of_isFractionRing R R' S S'

Depends on / 依赖: lift_rank_of_isFractionRing
-/
theorem rank_of_isFractionRing (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [Module R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S'] :
    Module.rank R' S' = Module.rank R S := by
  simpa using lift_rank_of_isFractionRing R R' S S'

end

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `rank_fractionRing` / 定理 `rank_fractionRing`

English:
theorem rank_fractionRing
  given: [IsDomain S]
  proof: rank_of_isFractionRing ..

中文:
定理 rank_fractionRing
  条件: [是整环 S]
  证明: rank_of_isFractionRing ..

Depends on / 依赖: rank_of_isFractionRing
-/
theorem rank_fractionRing [IsDomain S] :
    Module.rank (FractionRing R) (FractionRing S) = Module.rank R S :=
  rank_of_isFractionRing ..

end Algebra.IsAlgebraic

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `Module.finrank_mul_finrank'` / 定理 `Module.finrank_mul_finrank'`

English:
theorem Module.finrank_mul_finrank'
  statement: (T : Type*) [CommRing T] [IsDomain T]
  proof: by
  by_cases h : FaithfulSMul R S
  · have : FaithfulSMul R T := .trans R S T
    have : IsDomain R := (FaithfulSMul.algebraMap_injective R T).isDomain
    have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain
    rw [← IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)

中文:
定理 模.finrank_mul_finrank'
  结论: (T : 类型) [交换环 T] [是整环 T]
  证明: by
  by_cases h : FaithfulSMul R S
  · have : FaithfulSMul R T := .trans R S T
    have : IsDomain R := (FaithfulSMul.algebraMap_injective R T).isDomain
    have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain
    rw [← IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsDomain, IsFractionRing, IsFractionRing.finrank_eq, Module, Module.finrank_mul_finrank, algebraMap_injective, finrank_eq, finrank_mul_finrank, isDomain
-/
theorem Module.finrank_mul_finrank' (T : Type*) [CommRing T] [IsDomain T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] [FaithfulSMul S T] :
    Module.finrank R S * Module.finrank S T = Module.finrank R T := by
  by_cases h : FaithfulSMul R S
  · have : FaithfulSMul R T := .trans R S T
    have : IsDomain R := (FaithfulSMul.algebraMap_injective R T).isDomain
    have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain
    rw [← IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)]; rw [← IsFractionRing.finrank_eq S (FractionRing S) T (FractionRing T)]; rw [← IsFractionRing.finrank_eq R (FractionRing R) T (FractionRing T)]; rw [Module.finrank_mul_finrank (FractionRing R) (FractionRing S) (FractionRing T)]
  · rw [Module.finrank_eq_zero_of_not_faithfulSMul h, zero_mul,
      Module.finrank_eq_zero_of_not_faithfulSMul]
    exact fun _ => h (FaithfulSMul.tower_bot R S T)

section Polynomial

attribute [local instance] Polynomial.algebra MvPolynomial.algebraMvPolynomial

section

variable (R S) [NoZeroDivisors R]

-- TODO: `PolynomialModule` version
/--
theorem `rank_polynomial_polynomial` / 定理 `rank_polynomial_polynomial`

English:
theorem rank_polynomial_polynomial
  statement: Module.rank R[X] S[X] = Module.rank R S
  proof: ((Algebra.isPushout_iff ..).mp inferInstance).rank_eq

中文:
定理 rank_polynomial_polynomial
  结论: 模.rank R[X] S[X] = 模.rank R S
  证明: ((Algebra.isPushout_iff ..).mp inferInstance).rank_eq

Depends on / 依赖: Algebra, Algebra.isPushout_iff, isPushout_iff, rank_eq
-/
theorem rank_polynomial_polynomial : Module.rank R[X] S[X] = Module.rank R S :=
  ((Algebra.isPushout_iff ..).mp inferInstance).rank_eq

/--
theorem `rank_mvPolynomial_mvPolynomial` / 定理 `rank_mvPolynomial_mvPolynomial`

English:
theorem rank_mvPolynomial_mvPolynomial
  given: (σ : Type u)
  proof: by
  have := Algebra.isPushout_iff R (MvPolynomial σ R) S (MvPolynomial σ S)
.lift_rank_eq .mp inferInstance
  rwa [Cardinal.lift_id', Cardinal.lift_umax] at this

中文:
定理 rank_mvPolynomial_mvPolynomial
  条件: (σ : 类型u)
  证明: by
  have := Algebra.isPushout_iff R (MvPolynomial σ R) S (MvPolynomial σ S)
.lift_rank_eq .mp inferInstance
  rwa [Cardinal.lift_id', Cardinal.lift_umax] at this

Depends on / 依赖: Algebra, Algebra.isPushout_iff, Cardinal, Cardinal.lift_id, Cardinal.lift_umax, MvPolynomial, isPushout_iff, lift_id, lift_rank_eq, lift_umax
-/
theorem rank_mvPolynomial_mvPolynomial (σ : Type u) :
    Module.rank (MvPolynomial σ R) (MvPolynomial σ S) = Cardinal.lift.{u} (Module.rank R S) := by
  have := Algebra.isPushout_iff R (MvPolynomial σ R) S (MvPolynomial σ S)
.lift_rank_eq .mp inferInstance
  rwa [Cardinal.lift_id', Cardinal.lift_umax] at this

end

variable [alg : Algebra.IsAlgebraic R S]

section Pushout

variable (R S) (R' : Type*) [CommRing R'] [Algebra R R'] [NoZeroDivisors R'] [FaithfulSMul R R']

open TensorProduct in
/--
Instance `Algebra.IsAlgebraic.tensorProduct` / 实例 `Algebra.IsAlgebraic.tensorProduct`

English:
instance Algebra.IsAlgebraic.tensorProduct
  signature: : Algebra.IsAlgebraic R' (R' otimes[R] S) where
  body: have := IsAlgebraic.nontrivial R S
    have := (FaithfulSMul.algebraMap_injective R R').nontrivial
    p.induction_on isAlgebraic_zero (fun _ s => .tmul _ <| alg.1 s) (fun _ _ => .add)

中文:
实例 代数.是代数.tensorProduct
  签名: : 代数.是代数 R' (R' otimes[R] S) where
  定义体: have := IsAlgebraic.nontrivial R S
    have := (FaithfulSMul.algebraMap_injective R R').nontrivial
    p.induction_on isAlgebraic_zero (fun _ s => .tmul _ <| alg.1 s) (fun _ _ => .add)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsAlgebraic, IsAlgebraic.nontrivial, algebraMap_injective, induction_on, isAlgebraic_zero, nontrivial, p.induction_on
-/
instance Algebra.IsAlgebraic.tensorProduct : Algebra.IsAlgebraic R' (R' otimes[R] S) where
  isAlgebraic p :=
    have := IsAlgebraic.nontrivial R S
    have := (FaithfulSMul.algebraMap_injective R R').nontrivial
    p.induction_on isAlgebraic_zero (fun _ s => .tmul _ <| alg.1 s) (fun _ _ => .add)

variable (S' : Type*) [CommRing S'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S']

/--
theorem `Algebra.IsPushout.isAlgebraic'` / 定理 `Algebra.IsPushout.isAlgebraic'`

English:
theorem Algebra.IsPushout.isAlgebraic'
  given: [IsPushout R R' S S']
  statement: Algebra.IsAlgebraic R' S'
  proof: (equiv R R' S S').isAlgebraic

中文:
定理 代数.是推出.isAlgebraic'
  条件: [是推出 R R' S S']
  结论: 代数.是代数 R' S'
  证明: (equiv R R' S S').isAlgebraic

Depends on / 依赖: isAlgebraic
-/
theorem Algebra.IsPushout.isAlgebraic' [IsPushout R R' S S'] : Algebra.IsAlgebraic R' S' :=
  (equiv R R' S S').isAlgebraic

/--
theorem `Algebra.IsPushout.isAlgebraic` / 定理 `Algebra.IsPushout.isAlgebraic`

English:
theorem Algebra.IsPushout.isAlgebraic
  given: [h : IsPushout R S R' S']
  statement: Algebra.IsAlgebraic R' S'
  proof: have := h.symm; (equiv R R' S S').isAlgebraic

中文:
定理 代数.是推出.isAlgebraic
  条件: [h : 是推出 R S R' S']
  结论: 代数.是代数 R' S'
  证明: have := h.symm; (equiv R R' S S').isAlgebraic

Depends on / 依赖: h.symm, isAlgebraic
-/
theorem Algebra.IsPushout.isAlgebraic [h : IsPushout R S R' S'] : Algebra.IsAlgebraic R' S' :=
  have := h.symm; (equiv R R' S S').isAlgebraic

end Pushout

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : Algebra.IsAlgebraic R[X] S[X]
  body: Algebra.IsPushout.isAlgebraic R S ..

中文:
实例 [无零因子
  签名: R] : 代数.是代数 R[X] S[X]
  定义体: Algebra.IsPushout.isAlgebraic R S ..

Depends on / 依赖: Algebra, Algebra.IsPushout.isAlgebraic, IsPushout, isAlgebraic
-/
instance [NoZeroDivisors R] : Algebra.IsAlgebraic R[X] S[X] := Algebra.IsPushout.isAlgebraic R S ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: S] : Algebra.IsAlgebraic R[X] S[X]
  body: by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← Polynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

中文:
实例 [无零因子
  签名: S] : 代数.是代数 R[X] S[X]
  定义体: by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← Polynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

Depends on / 依赖: Algebra, Algebra.isAlgebraic_of_not_injective, Function, Function.Injective, Injective, Polynomial, Polynomial.map_injective_iff, algebraMap, h.noZeroDivisors, infer_instance, isAlgebraic_of_not_injective, map_injective_iff, map_mul, map_zero, noZeroDivisors
-/
instance [NoZeroDivisors S] : Algebra.IsAlgebraic R[X] S[X] := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← Polynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

/--
theorem `Polynomial.exists_dvd_map_of_isAlgebraic` / 定理 `Polynomial.exists_dvd_map_of_isAlgebraic`

English:
theorem Polynomial.exists_dvd_map_of_isAlgebraic
  given: [NoZeroDivisors S] {f : S[X]} (hf : f != 0)
  proof: (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

中文:
定理 多项式.存在_dvd_map_of_isAlgebraic
  条件: [无零因子 S] {f : S[X]} (hf : f != 0)
  证明: (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, exists_nonzero_dvd, isAlgebraic, mem_nonZeroDivisors_of_ne_zero
-/
theorem Polynomial.exists_dvd_map_of_isAlgebraic [NoZeroDivisors S] {f : S[X]} (hf : f != 0) :
    exists g : R[X], g != 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

instance {σ} [NoZeroDivisors R] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isAlgebraic R S ..

instance {σ} [NoZeroDivisors S] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← MvPolynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

/--
theorem `MvPolynomial.exists_dvd_map_of_isAlgebraic` / 定理 `MvPolynomial.exists_dvd_map_of_isAlgebraic`

English:
theorem MvPolynomial.exists_dvd_map_of_isAlgebraic
  statement: {σ}
  proof: (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

中文:
定理 多元多项式.存在_dvd_map_of_isAlgebraic
  结论: {σ}
  证明: (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, exists_nonzero_dvd, isAlgebraic, mem_nonZeroDivisors_of_ne_zero
-/
theorem MvPolynomial.exists_dvd_map_of_isAlgebraic {σ}
    [NoZeroDivisors S] {f : MvPolynomial σ S} (hf : f != 0) :
    exists g : MvPolynomial σ R, g != 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

variable [IsDomain S] [FaithfulSMul R S]

attribute [local instance] FractionRing.liftAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R (FractionRing R[X]) S (FractionRing S[X])
  body: (Algebra.IsPushout.comp_iff _ R[X] _ S[X]).mpr inferInstance

中文:
实例 :
  签名: 代数.是推出 R (FractionRing R[X]) S (FractionRing S[X])
  定义体: (Algebra.IsPushout.comp_iff _ R[X] _ S[X]).mpr inferInstance

Depends on / 依赖: Algebra, Algebra.IsPushout.comp_iff, IsPushout, comp_iff
-/
instance : Algebra.IsPushout R (FractionRing R[X]) S (FractionRing S[X]) :=
  (Algebra.IsPushout.comp_iff _ R[X] _ S[X]).mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R S (FractionRing R[X]) (FractionRing S[X])
  body: .symm inferInstance

中文:
实例 :
  签名: 代数.是推出 R S (FractionRing R[X]) (FractionRing S[X])
  定义体: .symm inferInstance
-/
instance : Algebra.IsPushout R S (FractionRing R[X]) (FractionRing S[X]) := .symm inferInstance

instance {σ : Type*} :
    Algebra.IsPushout R (FractionRing (MvPolynomial σ R)) S (FractionRing (MvPolynomial σ S)) :=
  (Algebra.IsPushout.comp_iff _ (MvPolynomial σ R) _ (MvPolynomial σ S)).mpr inferInstance

instance {σ : Type*} :
    Algebra.IsPushout R S (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) :=
  .symm inferInstance

namespace Algebra.IsAlgebraic

/--
theorem `rank_fractionRing_polynomial` / 定理 `rank_fractionRing_polynomial`

English:
theorem rank_fractionRing_polynomial
  proof: by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_polynomial_polynomial]

中文:
定理 rank_fractionRing_polynomial
  证明: by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_polynomial_polynomial]
-/
@[stacks 0G1M] theorem rank_fractionRing_polynomial :
    Module.rank (FractionRing R[X]) (FractionRing S[X]) = Module.rank R S := by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_polynomial_polynomial]

open Cardinal in
/--
theorem `rank_fractionRing_mvPolynomial` / 定理 `rank_fractionRing_mvPolynomial`

English:
theorem rank_fractionRing_mvPolynomial
  given: (σ : Type u)
  proof: by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_mvPolynomial_mvPolynomial]

中文:
定理 rank_fractionRing_mvPolynomial
  条件: (σ : 类型u)
  证明: by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_mvPolynomial_mvPolynomial]
-/
@[stacks 0G1M] theorem rank_fractionRing_mvPolynomial (σ : Type u) :
    Module.rank (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) =
    lift.{u} (Module.rank R S) := by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing]; rw [rank_mvPolynomial_mvPolynomial]

end Algebra.IsAlgebraic

end Polynomial

section FractionRing

open Algebra Module
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] [IsDomain S] [IsTorsionFree R S] [Module.Finite R S] :
  body: by
  obtain ⟨_, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
exact Module.finite_def.mpr
    (span_eq_top_localization_localization (FractionRing R) R⁰ (FractionRing S) hs) ▸
      Submodule.fg_span (Set.toFinite _)

中文:
实例 [是整环
  签名: R] [是整环 S] [是无挠 R S] [模.有限 R S] :
  定义体: by
  obtain ⟨_, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
exact Module.finite_def.mpr
    (span_eq_top_localization_localization (FractionRing R) R⁰ (FractionRing S) hs) ▸
      Submodule.fg_span (Set.toFinite _)

Depends on / 依赖: Finite, FractionRing, Module, Module.Finite.exists_fin, Module.finite_def.mpr, Set.toFinite, Submodule, Submodule.fg_span, exists_fin, fg_span, finite_def, span_eq_top_localization_localization, toFinite
-/
instance [IsDomain R] [IsDomain S] [IsTorsionFree R S] [Module.Finite R S] :
    FiniteDimensional (FractionRing R) (FractionRing S) := by
  obtain ⟨_, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
exact Module.finite_def.mpr
    (span_eq_top_localization_localization (FractionRing R) R⁰ (FractionRing S) hs) ▸
      Submodule.fg_span (Set.toFinite _)

end FractionRing
