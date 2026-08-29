/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Denominators of elements of an algebra

For an element `x` of an `R`-algebra `S`, with `R` a principal ideal ring, the **denominator**
`Algebra.denominator R x` is a generator of the colon ideal `(integralClosure R S).colon {x}`,
that is, of the ideal of scalars `r : R` clearing the denominators of `x`, in the sense that
`r • x` is integral over `R`. When `R = ℤ`, its absolute value is the natural-number denominator
`Algebra.natDenominator x`.

The definition needs no hypothesis on `x`, but it is only meaningful for `x` algebraic over `R`:
`IsAlgebraic.denominator_ne_zero` shows the denominator is then nonzero, whereas no nonzero
multiple of a transcendental element is integral, so that the colon ideal is trivial and the
denominator is `0`. See the `example` below, taking `x` to be the variable in `ℤ[X]`.

## Main definitions

* `Algebra.denominator`: the denominator of an element, over a principal ideal ring
* `Algebra.natDenominator`: the natural-number denominator of an element, over `ℤ`

## Main results

* `Algebra.denominator_dvd_iff`: `denominator R x` divides exactly the `r : R` with `r • x`
  integral over `R`
* `IsAlgebraic.denominator_ne_zero`: the denominator of an algebraic element is nonzero
-/

public section

variable (R : Type*) {S : Type*} [CommRing R]
variable [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
namespace Algebra

/--
Definition of `denominator` / `denominator` 的定义

English:
definition denominator
  signature: (x : S)
  body: Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

中文:
定义 denominator
  签名: (x : S)
  定义体: Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

Depends on / 依赖: IsPrincipal, Submodule, Submodule.IsPrincipal.generator, generator, integralClosure, toSubmodule, toSubmodule.colon
-/
noncomputable def denominator (x : S) : R :=
  Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

/--
lemma `denominator_def` / 引理 `denominator_def`

English:
lemma denominator_def
  given: (x : S)
  proof: by
  rfl

中文:
引理 denominator_def
  条件: (x : S)
  证明: by
  rfl
-/
lemma denominator_def (x : S) :
    denominator R x =
      Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x}) := by
  rfl

variable {R}

/--
theorem `denominator_dvd_iff` / 定理 `denominator_dvd_iff`

English:
theorem denominator_dvd_iff
  given: {r : R} {x : S}
  proof: by
  rw [denominator_def]; rw [← Submodule.IsPrincipal.mem_iff_generator_dvd]; rw [Submodule.mem_colon_singleton]; rw [Subalgebra.mem_toSubmodule]; rw [mem_integralClosure_iff]

中文:
定理 denominator_dvd_iff
  条件: {r : R} {x : S}
  证明: by
  rw [denominator_def]; rw [← Submodule.IsPrincipal.mem_iff_generator_dvd]; rw [Submodule.mem_colon_singleton]; rw [Subalgebra.mem_toSubmodule]; rw [mem_integralClosure_iff]

Depends on / 依赖: IsPrincipal, Subalgebra, Subalgebra.mem_toSubmodule, Submodule, Submodule.IsPrincipal.mem_iff_generator_dvd, Submodule.mem_colon_singleton, denominator_def, mem_colon_singleton, mem_iff_generator_dvd, mem_integralClosure_iff, mem_toSubmodule
-/
theorem denominator_dvd_iff {r : R} {x : S} :
    denominator R x ∣ r ↔ IsIntegral R (r • x) := by
  rw [denominator_def]; rw [← Submodule.IsPrincipal.mem_iff_generator_dvd]; rw [Submodule.mem_colon_singleton]; rw [Subalgebra.mem_toSubmodule]; rw [mem_integralClosure_iff]

/--
theorem `isIntegral_denominator_smul` / 定理 `isIntegral_denominator_smul`

English:
theorem isIntegral_denominator_smul
  given: (x : S)
  statement: IsIntegral R (denominator R x • x)
  proof: denominator_dvd_iff.mp dvd_rfl

中文:
定理 isIntegral_denominator_smul
  条件: (x : S)
  结论: Is整数egral R (denominator R x • x)
  证明: denominator_dvd_iff.mp dvd_rfl

Depends on / 依赖: denominator_dvd_iff, denominator_dvd_iff.mp, dvd_rfl
-/
theorem isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x) :=
  denominator_dvd_iff.mp dvd_rfl

/--
Definition of `natDenominator` / `natDenominator` 的定义

English:
definition natDenominator
  signature: (x : S)
  body: (denominator Int x).natAbs

中文:
定义 natDenominator
  签名: (x : S)
  定义体: (denominator Int x).natAbs

Depends on / 依赖: denominator, natAbs
-/
noncomputable def natDenominator (x : S) : Nat :=
  (denominator Int x).natAbs

/--
theorem `natDenominator_def` / 定理 `natDenominator_def`

English:
theorem natDenominator_def
  given: (x : S)
  statement: natDenominator x = (denominator Int x).natAbs
  proof: by
  rfl

中文:
定理 natDenominator_def
  条件: (x : S)
  结论: natDenominator x = (denominator 整数 x).natAbs
  证明: by
  rfl
-/
theorem natDenominator_def (x : S) : natDenominator x = (denominator Int x).natAbs := by
  rfl

/--
theorem `natDenominator_dvd_iff` / 定理 `natDenominator_dvd_iff`

English:
theorem natDenominator_dvd_iff
  given: {n : Nat} {x : S}
  proof: by
  rw [natDenominator_def]; rw [← Int.ofNat_dvd_right]; rw [denominator_dvd_iff]; rw [natCast_zsmul]

中文:
定理 natDenominator_dvd_iff
  条件: {n : 自然数} {x : S}
  证明: by
  rw [natDenominator_def]; rw [← Int.ofNat_dvd_right]; rw [denominator_dvd_iff]; rw [natCast_zsmul]

Depends on / 依赖: Int.ofNat_dvd_right, denominator_dvd_iff, natCast_zsmul, natDenominator_def, ofNat_dvd_right
-/
theorem natDenominator_dvd_iff {n : Nat} {x : S} :
    natDenominator x ∣ n ↔ IsIntegral Int (n • x) := by
  rw [natDenominator_def]; rw [← Int.ofNat_dvd_right]; rw [denominator_dvd_iff]; rw [natCast_zsmul]

/--
theorem `isIntegral_natDenominator_smul` / 定理 `isIntegral_natDenominator_smul`

English:
theorem isIntegral_natDenominator_smul
  given: (x : S)
  statement: IsIntegral Int (natDenominator x • x)
  proof: natDenominator_dvd_iff.mp dvd_rfl

中文:
定理 isIntegral_natDenominator_smul
  条件: (x : S)
  结论: Is整数egral 整数 (natDenominator x • x)
  证明: natDenominator_dvd_iff.mp dvd_rfl

Depends on / 依赖: dvd_rfl, natDenominator_dvd_iff, natDenominator_dvd_iff.mp
-/
theorem isIntegral_natDenominator_smul (x : S) : IsIntegral Int (natDenominator x • x) :=
  natDenominator_dvd_iff.mp dvd_rfl

end Algebra

namespace IsAlgebraic

/--
theorem `denominator_ne_zero` / 定理 `denominator_ne_zero`

English:
theorem denominator_ne_zero
  given: {x : S} (hx : IsAlgebraic R x)
  statement: Algebra.denominator R x != 0
  proof: by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (Algebra.denominator_dvd_iff.mpr hr)

中文:
定理 denominator_ne_zero
  条件: {x : S} (hx : IsAlgebraic R x)
  结论: Algebra.denominator R x != 0
  证明: by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (Algebra.denominator_dvd_iff.mpr hr)

Depends on / 依赖: Algebra, Algebra.denominator_dvd_iff.mpr, denominator_dvd_iff, exists_integral_multiple, hx.exists_integral_multiple, ne_zero_of_dvd_ne_zero
-/
theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : Algebra.denominator R x != 0 := by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (Algebra.denominator_dvd_iff.mpr hr)

/--
theorem `natDenominator_ne_zero` / 定理 `natDenominator_ne_zero`

English:
theorem natDenominator_ne_zero
  given: {x : S} (hx : IsAlgebraic Int x)
  statement: Algebra.natDenominator x != 0
  proof: by
  rw [Algebra.natDenominator_def]; rw [Int.natAbs_ne_zero]
  exact hx.denominator_ne_zero

中文:
定理 natDenominator_ne_zero
  条件: {x : S} (hx : IsAlgebraic 整数 x)
  结论: Algebra.natDenominator x != 0
  证明: by
  rw [Algebra.natDenominator_def]; rw [Int.natAbs_ne_zero]
  exact hx.denominator_ne_zero

Depends on / 依赖: Algebra, Algebra.natDenominator_def, Int.natAbs_ne_zero, denominator_ne_zero, hx.denominator_ne_zero, natAbs_ne_zero, natDenominator_def
-/
theorem natDenominator_ne_zero {x : S} (hx : IsAlgebraic Int x) : Algebra.natDenominator x != 0 := by
  rw [Algebra.natDenominator_def]; rw [Int.natAbs_ne_zero]
  exact hx.denominator_ne_zero

end IsAlgebraic

/- The algebraicity hypothesis in `IsAlgebraic.denominator_ne_zero` cannot be dropped: the
variable `X` of `ℤ[X]` is transcendental over `ℤ`, so no nonzero multiple of it is integral and
its denominator vanishes. -/
example : Algebra.denominator Int (Polynomial.X : Polynomial Int) = 0 := by
  by_contra h
  exact Polynomial.transcendental_X Int
    ((Algebra.isIntegral_denominator_smul _).isAlgebraic.of_smul
      (mem_nonZeroDivisors_of_ne_zero h))
