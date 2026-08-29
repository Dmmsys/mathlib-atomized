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
/--
Definition of `localPolynomial` / `localPolynomial` 的定义

English:
definition localPolynomial
  signature: : Int[X]
  body: letI W' := W.minimal R
  letI q : Int := Nat.card (IsLocalRing.ResidueField R)
  letI a : Int := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduct

中文:
定义 localPolynomial
  签名: : 整数[X]
  定义体: letI W' := W.minimal R
  letI q : Int := Nat.card (IsLocalRing.ResidueField R)
  letI a : Int := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduct

Depends on / 依赖: HasGoodReduction, HasMultiplicativeReduction, HasSplitMultiplicativeReduction, IsLocalRing, IsLocalRing.ResidueField, Nat.card, ResidueField, W.minimal, minimal, reduction, toAffine, toAffine.Point
-/
noncomputable def localPolynomial : Int[X] :=
  letI W' := W.minimal R
  letI q : Int := Nat.card (IsLocalRing.ResidueField R)
  letI a : Int := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduction R then 1 + X
  else 1

/--
Definition of `localPowerSeries` / `localPowerSeries` 的定义

English:
definition localPowerSeries
  signature: : PowerSeries Int
  body: PowerSeries.invOfUnit (W.localPolynomial R) 1

中文:
定义 localPowerSeries
  签名: : 幂级数 整数
  定义体: PowerSeries.invOfUnit (W.localPolynomial R) 1

Depends on / 依赖: PowerSeries, PowerSeries.invOfUnit, W.localPolynomial, invOfUnit, localPolynomial
-/
noncomputable def localPowerSeries : PowerSeries Int :=
  PowerSeries.invOfUnit (W.localPolynomial R) 1

/--
Definition of `localEulerFactor` / `localEulerFactor` 的定义

English:
definition localEulerFactor
  signature: : ArithmeticFunction Int
  body: .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) (W.localPowerSeries R)

中文:
定义 localEulerFactor
  签名: : ArithmeticFunction 整数
  定义体: .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) (W.localPowerSeries R)

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField, Nat.card, ResidueField, W.localPowerSeries, X.property, localPowerSeries, ofPowerSeries, property
-/
noncomputable def localEulerFactor : ArithmeticFunction Int :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) (W.localPowerSeries R)

end LocalField

section NumberField

open ArithmeticFunction IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/--
Definition of `LFunction` / `LFunction` 的定义

English:
definition LFunction
  signature: : ArithmeticFunction Int
  body: eulerProduct fun p : HeightOneSpectrum (𝓞 K) =>
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

中文:
定义 L函数
  签名: : ArithmeticFunction 整数
  定义体: eulerProduct fun p : HeightOneSpectrum (𝓞 K) =>
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

Depends on / 依赖: HeightOneSpectrum, W.baseChange, X.property, adicCompletion, adicCompletionIntegers, baseChange, eulerProduct, localEulerFactor, p.adicCompletion, p.adicCompletionIntegers, property
-/
noncomputable def LFunction : ArithmeticFunction Int :=
  eulerProduct fun p : HeightOneSpectrum (𝓞 K) =>
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def LSeries (W : WeierstrassCurve K) (s : Complex)
  body: LSeries ((↑) ∘ W.LFunction) s

中文:
定义 noncomputable
  签名: def LSeries (W : WeierstrassCurve K) (s : 复形)
  定义体: LSeries ((↑) ∘ W.LFunction) s
-/
protected noncomputable def LSeries (W : WeierstrassCurve K) (s : Complex) :=
  LSeries ((↑) ∘ W.LFunction) s

end NumberField

end WeierstrassCurve
