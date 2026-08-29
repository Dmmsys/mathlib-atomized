/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`,
every element `a : A` defines
an ideal `Polynomial.annIdeal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ Polynomial.annIdeal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `FieldTheory.Minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[AddCommGroup M] [Module R M]`)
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

@[expose] public section


open Polynomial

namespace Polynomial

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R) in
/--
Definition of `annIdeal` / `annIdeal` 的定义

English:
definition annIdeal
  signature: (a : A)
  body: RingHom.ker ((aeval a).toRingHom : R[X] ->+* A)

中文:
定义 annIdeal
  签名: (a : A)
  定义体: RingHom.ker ((aeval a).toRingHom : R[X] ->+* A)

Depends on / 依赖: RingHom, RingHom.ker, toRingHom
-/
noncomputable def annIdeal (a : A) : Ideal R[X] :=
  RingHom.ker ((aeval a).toRingHom : R[X] ->+* A)

/--
theorem `mem_annIdeal_iff_aeval_eq_zero` / 定理 `mem_annIdeal_iff_aeval_eq_zero`

English:
theorem mem_annIdeal_iff_aeval_eq_zero
  given: {a : A} {p : R[X]}
  statement: p in annIdeal R a ↔ aeval a p = 0
  proof: Iff.rfl

中文:
定理 mem_annIdeal_iff_aeval_eq_zero
  条件: {a : A} {p : R[X]}
  结论: p in annIdeal R a ↔ aeval a p = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_annIdeal_iff_aeval_eq_zero {a : A} {p : R[X]} : p in annIdeal R a ↔ aeval a p = 0 :=
  Iff.rfl

end Semiring

section Field

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
variable (𝕜)

open Submodule

/--
Definition of `annIdealGenerator` / `annIdealGenerator` 的定义

English:
definition annIdealGenerator
  signature: (a : A)
  body: let g := IsPrincipal.generator annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

中文:
定义 annIdealGenerator
  签名: (a : A)
  定义体: let g := IsPrincipal.generator annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

Depends on / 依赖: IsPrincipal, IsPrincipal.generator, annIdeal, g.leadingCoeff, generator, leadingCoeff
-/
noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
let g := IsPrincipal.generator annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

section

variable {𝕜}

@[simp]
/--
theorem `annIdealGenerator_eq_zero_iff` / 定理 `annIdealGenerator_eq_zero_iff`

English:
theorem annIdealGenerator_eq_zero_iff
  given: {a : A}
  statement: annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥
  proof: by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]

中文:
定理 annIdealGenerator_eq_zero_iff
  条件: {a : A}
  结论: annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥
  证明: by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]

Depends on / 依赖: C_eq_zero, IsPrincipal, IsPrincipal.eq_bot_iff_generator_eq_zero, Polynomial, Polynomial.C_eq_zero, Polynomial.leadingCoeff_eq_zero, annIdealGenerator, eq_bot_iff_generator_eq_zero, inv_eq_zero, leadingCoeff_eq_zero, mul_eq_zero, or_self_iff
-/
theorem annIdealGenerator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥ := by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]

end

/-- `annIdealGenerator 𝕜 a` is indeed a generator. -/
@[simp]
/--
theorem `span_singleton_annIdealGenerator` / 定理 `span_singleton_annIdealGenerator`

English:
theorem span_singleton_annIdealGenerator
  given: (a : A)
  proof: by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero

中文:
定理 span_singleton_annIdealGenerator
  条件: (a : A)
  证明: by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero

Depends on / 依赖: Ideal.span_singleton_generator, Ideal.span_singleton_mul_right_unit, Ideal.span_zero, IsUnit, IsUnit.mk0, Polynomial, Polynomial.isUnit_C.mpr, Polynomial.leadingCoeff_eq_zero.not.mpr, Set.singleton_zero, annIdealGenerator, annIdealGenerator_eq_zero_iff, annIdealGenerator_eq_zero_iff.mp, inv_eq_zero, inv_eq_zero.not.mpr, isUnit_C, leadingCoeff_eq_zero, mul_ne_zero_iff, mul_ne_zero_iff.mp, singleton_zero, span_singleton_generator
-/
theorem span_singleton_annIdealGenerator (a : A) :
    Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero.not.mpr
    apply Polynomial.leadingCoeff_eq_zero.not.mpr
    apply (mul_ne_zero_iff.mp h).1

/--
theorem `annIdealGenerator_mem` / 定理 `annIdealGenerator_mem`

English:
theorem annIdealGenerator_mem
  given: (a : A)
  statement: annIdealGenerator 𝕜 a in annIdeal 𝕜 a
  proof: Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)

中文:
定理 annIdealGenerator_mem
  条件: (a : A)
  结论: annIdealGenerator 𝕜 a in annIdeal 𝕜 a
  证明: Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)

Depends on / 依赖: Ideal.mul_mem_right, IsPrincipal, Submodule, Submodule.IsPrincipal.generator_mem, generator_mem, mul_mem_right
-/
theorem annIdealGenerator_mem (a : A) : annIdealGenerator 𝕜 a in annIdeal 𝕜 a :=
  Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)

/--
theorem `mem_iff_eq_smul_annIdealGenerator` / 定理 `mem_iff_eq_smul_annIdealGenerator`

English:
theorem mem_iff_eq_smul_annIdealGenerator
  given: {p : 𝕜[X]} (a : A)
  proof: by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a]

中文:
定理 mem_iff_eq_smul_annIdealGenerator
  条件: {p : 𝕜[X]} (a : A)
  证明: by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a]

Depends on / 依赖: eq_comm, mem_span_singleton, simp_rw, span_singleton_annIdealGenerator
-/
theorem mem_iff_eq_smul_annIdealGenerator {p : 𝕜[X]} (a : A) :
    p in annIdeal 𝕜 a ↔ exists s : 𝕜[X], p = s • annIdealGenerator 𝕜 a := by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a]

/--
theorem `monic_annIdealGenerator` / 定理 `monic_annIdealGenerator`

English:
theorem monic_annIdealGenerator
  given: (a : A) (hg : annIdealGenerator 𝕜 a != 0)
  proof: monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1

中文:
定理 monic_annIdealGenerator
  条件: (a : A) (hg : annIdealGenerator 𝕜 a != 0)
  证明: monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1

Depends on / 依赖: monic_mul_leadingCoeff_inv, mul_ne_zero_iff, mul_ne_zero_iff.mp
-/
theorem monic_annIdealGenerator (a : A) (hg : annIdealGenerator 𝕜 a != 0) :
    Monic (annIdealGenerator 𝕜 a) :=
  monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1



/--
theorem `annIdealGenerator_aeval_eq_zero` / 定理 `annIdealGenerator_aeval_eq_zero`

English:
theorem annIdealGenerator_aeval_eq_zero
  given: (a : A)
  statement: aeval a (annIdealGenerator 𝕜 a) = 0
  proof: mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)

中文:
定理 annIdealGenerator_aeval_eq_zero
  条件: (a : A)
  结论: aeval a (annIdealGenerator 𝕜 a) = 0
  证明: mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)

Depends on / 依赖: annIdealGenerator_mem, mem_annIdeal_iff_aeval_eq_zero, mem_annIdeal_iff_aeval_eq_zero.mp
-/
theorem annIdealGenerator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0 :=
  mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)

variable {𝕜}

/--
theorem `mem_iff_annIdealGenerator_dvd` / 定理 `mem_iff_annIdealGenerator_dvd`

English:
theorem mem_iff_annIdealGenerator_dvd
  given: {p : 𝕜[X]} {a : A}
  proof: by
  rw [← Ideal.mem_span_singleton]; rw [span_singleton_annIdealGenerator]

中文:
定理 mem_iff_annIdealGenerator_dvd
  条件: {p : 𝕜[X]} {a : A}
  证明: by
  rw [← Ideal.mem_span_singleton]; rw [span_singleton_annIdealGenerator]

Depends on / 依赖: Ideal.mem_span_singleton, mem_span_singleton, span_singleton_annIdealGenerator
-/
theorem mem_iff_annIdealGenerator_dvd {p : 𝕜[X]} {a : A} :
    p in annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p := by
  rw [← Ideal.mem_span_singleton]; rw [span_singleton_annIdealGenerator]

/--
theorem `degree_annIdealGenerator_le_of_mem` / 定理 `degree_annIdealGenerator_le_of_mem`

English:
theorem degree_annIdealGenerator_le_of_mem
  statement: (a : A) (p : 𝕜[X]) (hp : p in annIdeal 𝕜 a)
  proof: degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0

中文:
定理 degree_annIdealGenerator_le_of_mem
  结论: (a : A) (p : 𝕜[X]) (hp : p in annIdeal 𝕜 a)
  证明: degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0

Depends on / 依赖: degree_le_of_dvd, mem_iff_annIdealGenerator_dvd
-/
theorem degree_annIdealGenerator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p in annIdeal 𝕜 a)
    (hpn0 : p != 0) : degree (annIdealGenerator 𝕜 a) <= degree p :=
  degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0

variable (𝕜)

/--
theorem `annIdealGenerator_eq_minpoly` / 定理 `annIdealGenerator_eq_minpoly`

English:
theorem annIdealGenerator_eq_minpoly
  given: (a : A)
  statement: annIdealGenerator 𝕜 a = minpoly 𝕜 a
  proof: by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_ann

中文:
定理 annIdealGenerator_eq_minpoly
  条件: (a : A)
  结论: annIdealGenerator 𝕜 a = minpoly 𝕜 a
  证明: by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_ann

Depends on / 依赖: Ideal.mem_bot.mp, annIdealGenerator, annIdealGenerator_aeval_eq_zero, annIdealGenerator_eq_zero_iff, annIdealGenerator_eq_zero_iff.mp, degree_annIdealGenerator_le_of_mem, eq_zero, mem_annIdeal_iff_aeval_eq_zero, mem_annIdeal_iff_aeval_eq_zero.mpr, mem_bot, minpoly, minpoly.eq_zero, minpoly.unique, monic_annIdealGenerator, ne_zero, p_monic, p_monic.ne_zero, q_monic, q_monic.ne_zero, unique
-/
theorem annIdealGenerator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_annIdealGenerator _ _ h) (annIdealGenerator_aeval_eq_zero _ _)
      fun q q_monic hq =>
        degree_annIdealGenerator_le_of_mem a q (mem_annIdeal_iff_aeval_eq_zero.mpr hq)
          q_monic.ne_zero

/--
theorem `monic_generator_eq_minpoly` / 定理 `monic_generator_eq_minpoly`

English:
theorem monic_generator_eq_minpoly
  statement: (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
  proof: by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGener

中文:
定理 monic_generator_eq_minpoly
  结论: (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
  证明: by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGener

Depends on / 依赖: Associated, Associated.ne_zero_iff, Ideal.span_singleton_eq_bot.mpr, Ideal.span_singleton_eq_span_singleton, annIdealGenerator_eq_zero_iff, eq_comm, eq_of_monic_of_associated, monic_annIdealGenerator, ne_zero_iff, p_gen, p_monic, span_singleton_annIdealGenerator, span_singleton_eq_bot, span_singleton_eq_span_singleton
-/
theorem monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
    (p_gen : Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p := by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGenerator _ _ ((Associated.ne_zero_iff p_gen).mp h)

/--
theorem `span_minpoly_eq_annihilator` / 定理 `span_minpoly_eq_annihilator`

English:
theorem span_minpoly_eq_annihilator
  given: {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M)
  proof: by
  rw [← annIdealGenerator_eq_minpoly]; rw [span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero]; rw [DFunLike.ext_iff]; rw [Module.mem_annihilator]; rfl

中文:
定理 span_minpoly_eq_annihilator
  条件: {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M)
  证明: by
  rw [← annIdealGenerator_eq_minpoly]; rw [span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero]; rw [DFunLike.ext_iff]; rw [Module.mem_annihilator]; rfl

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Module, Module.mem_annihilator, annIdealGenerator_eq_minpoly, ext_iff, mem_annIdeal_iff_aeval_eq_zero, mem_annihilator, span_singleton_annIdealGenerator
-/
theorem span_minpoly_eq_annihilator {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M) :
    Ideal.span {minpoly 𝕜 f} = Module.annihilator 𝕜[X] (Module.AEval' f) := by
  rw [← annIdealGenerator_eq_minpoly]; rw [span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero]; rw [DFunLike.ext_iff]; rw [Module.mem_annihilator]; rfl

end Field

end Polynomial
