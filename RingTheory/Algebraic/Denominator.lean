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

/-- The denominator of an element `x` of an `R`-algebra: a generator of the ideal of scalars
`r : R` such that `r • x` is integral over `R`. It is nonzero as soon as `x` is algebraic over
`R`; see `IsAlgebraic.denominator_ne_zero`. -/
/-
**Algebra.denominator** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：denominator (x : S) : R
参数：x : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The denominator of an element `x` of an `R`-algebra: a generator of the ideal of
 scalars
`r : R` such that `r • x` is integral over `R`. It is nonzero as soon as `x` is 
algebraic over
`R`; see `IsAlgebraic.denominator_ne_zero`.
-/
noncomputable def denominator (x : S) : R :=
  Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})
/-
**Algebra.denominator_def** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：denominator_def (x : S) : denominator R x = Submodule.IsPrincipal.generato
r ((integralClosure R S).toSubmodule.colon {x})
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma denominator_def (x : S) :
    denominator R x =
      Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x}) := by
  rfl

variable {R}
/-
**Algebra.denominator_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：denominator_dvd_iff {r : R} {x : S} : denominator R x ∣ r ↔ IsIntegral R (
r • x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.denominator_def`：denominator_def (x : S) : denominator R x = Sub
module.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
· 使用定理 `Subalgebra.mem_toSubmodule`：mem_toSubmodule {x} : x in (toSubmodule S) ↔
 x in S
· 使用定理 `mem_integralClosure_iff`：mem_integralClosure_iff {a : A} : a in integral
Closure R A ↔ IsIntegral R a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem denominator_dvd_iff {r : R} {x : S} :
    denominator R x ∣ r ↔ IsIntegral R (r • x) := by
  rw [denominator_def, ← Submodule.IsPrincipal.mem_iff_generator_dvd,
    Submodule.mem_colon_singleton, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
/-
**Algebra.isIntegral_denominator_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x)
参数：x : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.denominator_dvd_iff`：denominator_dvd_iff {r : R} {x : S} : denom
inator R x ∣ r ↔ IsIntegral R (r • x)
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x) :=
  denominator_dvd_iff.mp dvd_rfl

/-- The natural-number denominator of an element `x` of a ring: it is the absolute value of the
denominator of `x` over `ℤ`. -/
/-
**Algebra.natDenominator** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：natDenominator (x : S) : Nat
参数：x : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R

--- 原说明 ---
The natural-number denominator of an element `x` of a ring: it is the absolute v
alue of the
denominator of `x` over `ℤ`.
-/
noncomputable def natDenominator (x : S) : ℕ :=
  (denominator ℤ x).natAbs
/-
**Algebra.natDenominator_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：natDenominator_def (x : S) : natDenominator x = (denominator Int x).natAbs
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natDenominator_def (x : S) : natDenominator x = (denominator ℤ x).natAbs := by
  rfl
/-
**Algebra.natDenominator_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：natDenominator_dvd_iff {n : Nat} {x : S} : natDenominator x ∣ n ↔ IsIntegr
al Int (n • x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.natDenominator_def`：natDenominator_def (x : S) : natDenominator 
x = (denominator Int x).natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_dvd_right`：∀ {n : ℕ} {z : ℤ}, z ∣ ↑n ↔ z.natAbs ∣ n
· 使用定理 `Algebra.denominator_dvd_iff`：denominator_dvd_iff {r : R} {x : S} : denom
inator R x ∣ r ↔ IsIntegral R (r • x)
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natDenominator_dvd_iff {n : ℕ} {x : S} :
    natDenominator x ∣ n ↔ IsIntegral ℤ (n • x) := by
  rw [natDenominator_def, ← Int.ofNat_dvd_right, denominator_dvd_iff, natCast_zsmul]
/-
**Algebra.isIntegral_natDenominator_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isIntegral_natDenominator_smul (x : S) : IsIntegral Int (natDenominator x 
• x)
参数：x : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.natDenominator_dvd_iff`：natDenominator_dvd_iff {n : Nat} {x : S}
 : natDenominator x ∣ n ↔ IsIntegral Int (n • x)
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem isIntegral_natDenominator_smul (x : S) : IsIntegral ℤ (natDenominator x • x) :=
  natDenominator_dvd_iff.mp dvd_rfl

end Algebra

namespace IsAlgebraic

/-
**IsAlgebraic.denominator_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : Algebra.denominator R
 x != 0
参数：hx : IsAlgebraic R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.denominator_dvd_iff`：denominator_dvd_iff {r : R} {x : S} : denom
inator R x ∣ r ↔ IsIntegral R (r • x)
-/
theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : Algebra.denominator R x ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (Algebra.denominator_dvd_iff.mpr hr)
/-
**IsAlgebraic.natDenominator_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：natDenominator_ne_zero {x : S} (hx : IsAlgebraic Int x) : Algebra.natDenom
inator x != 0
参数：hx : IsAlgebraic Int x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.natDenominator_def`：natDenominator_def (x : S) : natDenominator 
x = (denominator Int x).natAbs
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `IsAlgebraic.denominator_ne_zero`：denominator_ne_zero {x : S} (hx : IsAlg
ebraic R x) : Algebra.denominator R x != 0
-/
theorem natDenominator_ne_zero {x : S} (hx : IsAlgebraic ℤ x) : Algebra.natDenominator x ≠ 0 := by
  rw [Algebra.natDenominator_def, Int.natAbs_ne_zero]
  exact hx.denominator_ne_zero

end IsAlgebraic

/- The algebraicity hypothesis in `IsAlgebraic.denominator_ne_zero` cannot be dropped: the
variable `X` of `ℤ[X]` is transcendental over `ℤ`, so no nonzero multiple of it is integral and
its denominator vanishes. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebraicity hypothesis in `IsAlgebraic.denominator_ne_zero` cannot be dropp
ed: the
variable `X` of `ℤ[X]` is transcendental over `ℤ`, so no nonzero multiple of it 
is integral and
its denominator vanishes.
-/
example : Algebra.denominator ℤ (Polynomial.X : Polynomial ℤ) = 0 := by
  by_contra h
  exact Polynomial.transcendental_X ℤ
    ((Algebra.isIntegral_denominator_smul _).isAlgebraic.of_smul
      (mem_nonZeroDivisors_of_ne_zero h))
