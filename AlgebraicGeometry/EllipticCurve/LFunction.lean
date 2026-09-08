/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The L-function of a Weierstrass curve

In this file, we define the L-function of a Weierstrass curve.

## Main definitions

* `WeierstrassCurve.LFunction`: the L-function of a Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

@[expose] public section

namespace WeierstrassCurve

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

open Classical Polynomial in
/-- The local polynomial associated to a Weierstrass curve `W` over a nonarchimedean local field.
In the case of good reduction it is given by `1 - a T + q T ^ 2` where `q` is the cardinality of the
residue field `κ` and `a = q + 1 - |W(κ)|`. Note that `q` (and also `|W(κ)|`) is defined via
`Nat.card`, so `q` has junk value `0` when the residue field is infinite. -/
/-
**WeierstrassCurve.localPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：localPolynomial : Int[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `WeierstrassCurve.instIsMinimalMinimal`：∀ (R : Type u_1) [inst : CommRing
 R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_2}   
[inst_3 : Field K] [inst_4 …

--- 原说明 ---
The local polynomial associated to a Weierstrass curve `W` over a nonarchimedean
 local field.
In the case of good reduction it is given by `1 - a T + q T ^ 2` where `q` is th
e cardinality of the
residue field `κ` and `a = q + 1 - |W(κ)|`. Note that `q` (and also `|W(κ)|`) is
 defined via
`Nat.card`, so `q` has junk value `0` when the residue field is infinite.
-/
noncomputable def localPolynomial : ℤ[X] :=
  letI W' := W.minimal R
  letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
  letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduction R then 1 + X
  else 1

/-- The local power series associated to a Weierstrass curve over a nonarchimedean local field. -/
/-
**WeierstrassCurve.localPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`
。
形式化陈述：localPowerSeries : PowerSeries Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The local power series associated to a Weierstrass curve over a nonarchimedean l
ocal field.
-/
noncomputable def localPowerSeries : PowerSeries ℤ :=
  PowerSeries.invOfUnit (W.localPolynomial R) 1

/-- The local Euler factor associated to a Weierstrass curve over a nonarchimedean local field. -/
/-
**WeierstrassCurve.localEulerFactor** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`
。
形式化陈述：localEulerFactor : ArithmeticFunction Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R

--- 原说明 ---
The local Euler factor associated to a Weierstrass curve over a nonarchimedean l
ocal field.
-/
noncomputable def localEulerFactor : ArithmeticFunction ℤ :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) (W.localPowerSeries R)

end LocalField

section NumberField

open ArithmeticFunction IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of a Weierstrass curve `W` over a number field `K` as a formal Dirichlet series.

For each prime ideal `p` of the ring of integers of `K` with norm `‖p‖` residue field `κ_p`,
we define the local polynomial `fₚ(T)` as:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` where `aₚ = ‖p‖ + 1 - |W(κ_p)|` if `W` has good reduction at `p`,
* `fₚ = 1 - T` if `W` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `W` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `W` has additive reduction at `p`.
Then the L-function of `W` is the formal Dirichlet series defined as the product of `1 / fₚ(‖p‖⁻ˢ)`
as `p` ranges over all prime ideals of the ring of integers of `K`.
-/
/-
**WeierstrassCurve.LFunction** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：LFunction : ArithmeticFunction Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K

--- 原说明 ---
The L-function of a Weierstrass curve `W` over a number field `K` as a formal Di
richlet series.

For each prime ideal `p` of the ring of integers of `K` with norm `‖p‖` residue 
field `κ_p`,
we define the local polynomial `fₚ(T)` as:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` where `aₚ = ‖p‖ + 1 - |W(κ_p)|` if `W` has good re
duction at `p`,
* `fₚ = 1 - T` if `W` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `W` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `W` has additive reduction at `p`.
Then the L-function of `W` is the formal Dirichlet series defined as the product
 of `1 / fₚ(‖p‖⁻ˢ)`
as `p` ranges over all prime ideals of the ring of integers of `K`.
-/
noncomputable def LFunction : ArithmeticFunction ℤ :=
  eulerProduct fun p : HeightOneSpectrum (𝓞 K) ↦
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

/-- The L-series of a Weierstrass curve over a number field. -/
/-
**WeierstrassCurve.LSeries** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：{K : Type u_1} → [inst : Field K] → [NumberField K] → WeierstrassCurve K →
 ℂ → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The L-series of a Weierstrass curve over a number field.
-/
protected noncomputable def LSeries (W : WeierstrassCurve K) (s : ℂ) :=
  LSeries ((↑) ∘ W.LFunction) s

end NumberField

end WeierstrassCurve

