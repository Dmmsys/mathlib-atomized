/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# L-series of Dirichlet characters and arithmetic functions

We collect some results on L-series of specific (arithmetic) functions, for example,
the Möbius function `μ` or the von Mangoldt function `Λ`. In particular, we show that
`L ↗Λ` is the negative of the logarithmic derivative of the Riemann zeta function
on `re s > 1`; see `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

We also prove some general results on L-series associated to Dirichlet characters
(i.e., Dirichlet L-series). For example, we show that the abscissa of absolute convergence
equals `1` (see `DirichletCharacter.absicssaOfAbsConv_eq_one`) and that the L-series does not
vanish on the open half-plane `re s > 1` (see `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`).

We deduce results on the Riemann zeta function (which is `L 1` or `L ↗ζ` on `re s > 1`)
as special cases.

## Tags

Dirichlet L-series, Möbius function, von Mangoldt function, Riemann zeta function
-/

public section

open scoped LSeries.notation

/--
lemma `ArithmeticFunction.one_eq_delta` / 引理 `ArithmeticFunction.one_eq_delta`

English:
lemma ArithmeticFunction.one_eq_delta
  statement: ↗(1 : ArithmeticFunction Complex) = δ
  proof: by
  ext
  simp [one_apply, LSeries.delta]

中文:
引理 ArithmeticFunction.one_eq_delta
  结论: ↗(1 : ArithmeticFunction 复形) = δ
  证明: by
  ext
  simp [one_apply, LSeries.delta]

Depends on / 依赖: LSeries, LSeries.delta, one_apply
-/
lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction Complex) = δ := by
  ext
  simp [one_apply, LSeries.delta]


section Moebius

/-!
### The L-series of the Möbius function

We show that `L μ s` converges absolutely if and only if `re s > 1`.
-/

namespace ArithmeticFunction

-- access notation `μ`
open scoped Moebius

open LSeries Nat Complex

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `not_LSeriesSummable_moebius_at_one` / 引理 `not_LSeriesSummable_moebius_at_one`

English:
lemma not_LSeriesSummable_moebius_at_one
  statement: ¬ LSeriesSummable ↗μ 1
  proof: by
refine fun h => not_summable_one_div_on_primes summable_ofReal.mp .of_neg ?_
  refine (h.indicator {n | n.Prime}).congr fun n => ?_
  by_cases hn : n.Prime
  · simp [hn, hn.ne_zero, moebius_apply_prime hn, push_cast, neg_div]
  · simp [hn]

中文:
引理 not_LSeriesSummable_moebius_at_one
  结论: ¬ LSeriesSummable ↗μ 1
  证明: by
refine fun h => not_summable_one_div_on_primes summable_ofReal.mp .of_neg ?_
  refine (h.indicator {n | n.Prime}).congr fun n => ?_
  by_cases hn : n.Prime
  · simp [hn, hn.ne_zero, moebius_apply_prime hn, push_cast, neg_div]
  · simp [hn]

Depends on / 依赖: h.indicator, hn.ne_zero, indicator, moebius_apply_prime, n.Prime, ne_zero, neg_div, not_summable_one_div_on_primes, of_neg, summable_ofReal, summable_ofReal.mp
-/
lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
refine fun h => not_summable_one_div_on_primes summable_ofReal.mp .of_neg ?_
  refine (h.indicator {n | n.Prime}).congr fun n => ?_
  by_cases hn : n.Prime
  · simp [hn, hn.ne_zero, moebius_apply_prime hn, push_cast, neg_div]
  · simp [hn]

/--
lemma `LSeriesSummable_moebius_iff` / 引理 `LSeriesSummable_moebius_iff`

English:
lemma LSeriesSummable_moebius_iff
  given: {s : Complex}
  statement: LSeriesSummable ↗μ s ↔ 1 < s.re
  proof: by
  refine ⟨fun H => ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ => ?_⟩
  · by_contra! h
exact not_LSeriesSummable_moebius_at_one LSeriesSummable.of_re_le_re (by simpa) H
  · norm_cast
    exact abs_moebius_le_one

中文:
引理 LSeriesSummable_moebius_iff
  条件: {s : 复形}
  结论: LSeriesSummable ↗μ s ↔ 1 < s.re
  证明: by
  refine ⟨fun H => ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ => ?_⟩
  · by_contra! h
exact not_LSeriesSummable_moebius_at_one LSeriesSummable.of_re_le_re (by simpa) H
  · norm_cast
    exact abs_moebius_le_one

Depends on / 依赖: LSeriesSummable, LSeriesSummable.of_re_le_re, LSeriesSummable_of_bounded_of_one_lt_re, abs_moebius_le_one, not_LSeriesSummable_moebius_at_one, of_re_le_re
-/
lemma LSeriesSummable_moebius_iff {s : Complex} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
  refine ⟨fun H => ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ => ?_⟩
  · by_contra! h
exact not_LSeriesSummable_moebius_at_one LSeriesSummable.of_re_le_re (by simpa) H
  · norm_cast
    exact abs_moebius_le_one

/--
lemma `abscissaOfAbsConv_moebius` / 引理 `abscissaOfAbsConv_moebius`

English:
lemma abscissaOfAbsConv_moebius
  statement: abscissaOfAbsConv ↗μ = 1
  proof: by
  simpa [abscissaOfAbsConv, LSeriesSummable_moebius_iff, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

中文:
引理 abscissaOfAbsConv_moebius
  结论: abscissaOfAbsConv ↗μ = 1
  证明: by
  simpa [abscissaOfAbsConv, LSeriesSummable_moebius_iff, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

Depends on / 依赖: EReal.coe_lt_top, EReal.image_coe_Ioi, Ioi_def, LSeriesSummable_moebius_iff, Set.Ioi_def, abscissaOfAbsConv, coe_lt_top, csInf_Ioo, image_coe_Ioi
-/
lemma abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1 := by
  simpa [abscissaOfAbsConv, LSeriesSummable_moebius_iff, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

end ArithmeticFunction

end Moebius


/-!
### L-series of Dirichlet characters
-/

open Nat

open scoped ArithmeticFunction.zeta in
/--
lemma `ArithmeticFunction.const_one_eq_zeta` / 引理 `ArithmeticFunction.const_one_eq_zeta`

English:
lemma ArithmeticFunction.const_one_eq_zeta
  given: {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0)
  proof: by
  simp [hn]

中文:
引理 ArithmeticFunction.const_one_eq_zeta
  条件: {R : 类型} [加法带幺幺半群 R] {n : 自然数} (hn : n != 0)
  证明: by
  simp [hn]
-/
lemma ArithmeticFunction.const_one_eq_zeta {R : Type*} [AddMonoidWithOne R] {n : Nat} (hn : n != 0) :
    (1 : Nat -> R) n = (ζ ·) n := by
  simp [hn]

/--
lemma `LSeries.one_convolution_eq_zeta_convolution` / 引理 `LSeries.one_convolution_eq_zeta_convolution`

English:
lemma LSeries.one_convolution_eq_zeta_convolution
  given: {R : Type*} [Semiring R] (f : Nat -> R)
  proof: convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ => rfl

中文:
引理 LSeries.one_convolution_eq_zeta_convolution
  条件: {R : 类型} [半环 R] (f : 自然数 -> R)
  证明: convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ => rfl

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.const_one_eq_zeta, const_one_eq_zeta, convolution_congr
-/
lemma LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : Nat -> R) :
    (1 : Nat -> R) ⍟ f = ((ArithmeticFunction.zeta ·) : Nat -> R) ⍟ f :=
  convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ => rfl

/--
lemma `LSeries.convolution_one_eq_convolution_zeta` / 引理 `LSeries.convolution_one_eq_convolution_zeta`

English:
lemma LSeries.convolution_one_eq_convolution_zeta
  given: {R : Type*} [Semiring R] (f : Nat -> R)
  proof: convolution_congr (fun _ => rfl) ArithmeticFunction.const_one_eq_zeta

中文:
引理 LSeries.convolution_one_eq_convolution_zeta
  条件: {R : 类型} [半环 R] (f : 自然数 -> R)
  证明: convolution_congr (fun _ => rfl) ArithmeticFunction.const_one_eq_zeta

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.const_one_eq_zeta, const_one_eq_zeta, convolution_congr
-/
lemma LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : Nat -> R) :
    f ⍟ (1 : Nat -> R) = f ⍟ ((ArithmeticFunction.zeta ·) : Nat -> R) :=
  convolution_congr (fun _ => rfl) ArithmeticFunction.const_one_eq_zeta

/-- `χ₁` is (local) notation for the (necessarily trivial) Dirichlet character modulo `1`. -/
local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter Complex 1)

namespace DirichletCharacter

open ArithmeticFunction in
/--
lemma `isMultiplicative_toArithmeticFunction` / 引理 `isMultiplicative_toArithmeticFunction`

English:
lemma isMultiplicative_toArithmeticFunction
  statement: {N : Nat} {R : Type*} [CommMonoidWithZero R]
  proof: by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ => ?_⟩
  · simp [toArithmeticFunction]
  · simp [toArithmeticFunction, hm, hn]

中文:
引理 isMultiplicative_toArithmeticFunction
  结论: {N : 自然数} {R : 类型} [带零交换幺半群 R]
  证明: by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ => ?_⟩
  · simp [toArithmeticFunction]
  · simp [toArithmeticFunction, hm, hn]

Depends on / 依赖: IsMultiplicative, IsMultiplicative.iff_ne_zero.mpr, iff_ne_zero, toArithmeticFunction
-/
lemma isMultiplicative_toArithmeticFunction {N : Nat} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) :
    (toArithmeticFunction (χ ·)).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ => ?_⟩
  · simp [toArithmeticFunction]
  · simp [toArithmeticFunction, hm, hn]

/--
lemma `apply_eq_toArithmeticFunction_apply` / 引理 `apply_eq_toArithmeticFunction_apply`

English:
lemma apply_eq_toArithmeticFunction_apply
  statement: {N : Nat} {R : Type*} [CommMonoidWithZero R]
  proof: by
  simp [toArithmeticFunction, hn]

中文:
引理 apply_eq_toArithmeticFunction_apply
  结论: {N : 自然数} {R : 类型} [带零交换幺半群 R]
  证明: by
  simp [toArithmeticFunction, hn]

Depends on / 依赖: toArithmeticFunction
-/
lemma apply_eq_toArithmeticFunction_apply {N : Nat} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) {n : Nat} (hn : n != 0) :
    χ n = toArithmeticFunction (χ ·) n := by
  simp [toArithmeticFunction, hn]

open LSeries Nat Complex

/--
lemma `mul_convolution_distrib` / 引理 `mul_convolution_distrib`

English:
lemma mul_convolution_distrib
  statement: {R : Type*} [CommSemiring R] {n : Nat} (χ : DirichletCharacter R n)
  proof: by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm]; rw [cast_mul]; rw [map_mul]
  exact mul_mul_mul_comm ..

中文:
引理 mul_convolution_distrib
  结论: {R : 类型} [交换半环 R] {n : 自然数} (χ : DirichletCharacter R n)
  证明: by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm]; rw [cast_mul]; rw [map_mul]
  exact mul_mul_mul_comm ..

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, LSeries, LSeries.convolution_def, Pi.mul_apply, cast_mul, convolution_def, map_mul, mem_divisorsAntidiagonal, mem_divisorsAntidiagonal.mp, mul_apply, mul_mul_mul_comm, mul_sum, sum_congr
-/
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : Nat} (χ : DirichletCharacter R n)
    (f g : Nat -> R) :
    (((χ ·) : Nat -> R) * f) ⍟ (((χ ·) : Nat -> R) * g) = ((χ ·) : Nat -> R) * (f ⍟ g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm]; rw [cast_mul]; rw [map_mul]
  exact mul_mul_mul_comm ..

/--
lemma `mul_delta` / 引理 `mul_delta`

English:
lemma mul_delta
  given: {n : Nat} (χ : DirichletCharacter Complex n)
  statement: ↗χ * δ = δ
  proof: LSeries.mul_delta by rw [cast_one, map_one]

中文:
引理 mul_delta
  条件: {n : 自然数} (χ : DirichletCharacter 复形 n)
  结论: ↗χ * δ = δ
  证明: LSeries.mul_delta by rw [cast_one, map_one]

Depends on / 依赖: LSeries, LSeries.mul_delta, cast_one, map_one, mul_delta
-/
lemma mul_delta {n : Nat} (χ : DirichletCharacter Complex n) : ↗χ * δ = δ :=
LSeries.mul_delta by rw [cast_one, map_one]

/--
lemma `delta_mul` / 引理 `delta_mul`

English:
lemma delta_mul
  given: {n : Nat} (χ : DirichletCharacter Complex n)
  statement: δ * ↗χ = δ
  proof: mul_comm δ _ ▸ mul_delta ..

中文:
引理 delta_mul
  条件: {n : 自然数} (χ : DirichletCharacter 复形 n)
  结论: δ * ↗χ = δ
  证明: mul_comm δ _ ▸ mul_delta ..

Depends on / 依赖: mul_comm, mul_delta
-/
lemma delta_mul {n : Nat} (χ : DirichletCharacter Complex n) : δ * ↗χ = δ :=
  mul_comm δ _ ▸ mul_delta ..

open ArithmeticFunction in
open scoped Moebius in -- access notation `μ`
/--
lemma `convolution_mul_moebius` / 引理 `convolution_mul_moebius`

English:
lemma convolution_mul_moebius
  given: {n : Nat} (χ : DirichletCharacter Complex n)
  statement: ↗χ ⍟ (↗χ * ↗μ) = δ
  proof: by
  have : (1 : Nat -> Complex) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution]; rw [← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _

中文:
引理 convolution_mul_moebius
  条件: {n : 自然数} (χ : DirichletCharacter 复形 n)
  结论: ↗χ ⍟ (↗χ * ↗μ) = δ
  证明: by
  have : (1 : Nat -> Complex) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution]; rw [← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _

Depends on / 依赖: coe_mul, coe_zeta_mul_coe_moebius, intCoe_apply, mul_convolution_distrib, mul_delta, mul_one, natCoe_apply, nth_rewrite, one_convolution_eq_zeta_convolution, one_eq_delta, simp_rw
-/
lemma convolution_mul_moebius {n : Nat} (χ : DirichletCharacter Complex n) : ↗χ ⍟ (↗χ * ↗μ) = δ := by
  have : (1 : Nat -> Complex) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution]; rw [← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _

/--
lemma `modZero_eq_delta` / 引理 `modZero_eq_delta`

English:
lemma modZero_eq_delta
  given: {χ : DirichletCharacter Complex 0}
  statement: ↗χ = δ
  proof: by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, reduceCtorEq, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp [delta]
have : ¬ IsUnit (n : ZMod 0) := fun h => hn' ZMod.eq_one_of_isUnit_natCast h
  simp_all [χ.map_nonunit this, delt

中文:
引理 modZero_eq_delta
  条件: {χ : DirichletCharacter 复形 0}
  结论: ↗χ = δ
  证明: by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, reduceCtorEq, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp [delta]
have : ¬ IsUnit (n : ZMod 0) := fun h => hn' ZMod.eq_one_of_isUnit_natCast h
  simp_all [χ.map_nonunit this, delt

Depends on / 依赖: IsUnit, ZMod.eq_one_of_isUnit_natCast, cast_zero, eq_one_of_isUnit_natCast, eq_or_ne, if_false, map_nonunit, not_isUnit_zero, reduceCtorEq, simp_rw
-/
lemma modZero_eq_delta {χ : DirichletCharacter Complex 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, reduceCtorEq, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp [delta]
have : ¬ IsUnit (n : ZMod 0) := fun h => hn' ZMod.eq_one_of_isUnit_natCast h
  simp_all [χ.map_nonunit this, delta]

/--
lemma `modOne_eq_one` / 引理 `modOne_eq_one`

English:
lemma modOne_eq_one
  given: {R : Type*} [CommMonoidWithZero R] {χ : DirichletCharacter R 1}
  proof: by
  ext
  rw [χ.level_one]; rw [MulChar.one_apply (isUnit_of_subsingleton _)]; rw [Pi.one_apply]

中文:
引理 modOne_eq_one
  条件: {R : 类型} [带零交换幺半群 R] {χ : DirichletCharacter R 1}
  证明: by
  ext
  rw [χ.level_one]; rw [MulChar.one_apply (isUnit_of_subsingleton _)]; rw [Pi.one_apply]

Depends on / 依赖: MulChar, MulChar.one_apply, Pi.one_apply, isUnit_of_subsingleton, level_one, one_apply
-/
lemma modOne_eq_one {R : Type*} [CommMonoidWithZero R] {χ : DirichletCharacter R 1} :
    ((χ ·) : Nat -> R) = 1 := by
  ext
  rw [χ.level_one]; rw [MulChar.one_apply (isUnit_of_subsingleton _)]; rw [Pi.one_apply]

/--
lemma `LSeries_modOne_eq` / 引理 `LSeries_modOne_eq`

English:
lemma LSeries_modOne_eq
  statement: L ↗χ₁ = L 1
  proof: congr_arg L modOne_eq_one

中文:
引理 LSeries_modOne_eq
  结论: L ↗χ₁ = L 1
  证明: congr_arg L modOne_eq_one

Depends on / 依赖: congr_arg, modOne_eq_one
-/
lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
  congr_arg L modOne_eq_one

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `not_LSeriesSummable_at_one` / 引理 `not_LSeriesSummable_at_one`

English:
lemma not_LSeriesSummable_at_one
  given: {N : Nat} (hN : N != 0) (χ : DirichletCharacter Complex N)
  proof: by
  refine fun h => (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m => Set.indicator_apply_nonneg (fun _ => by positivity))
    (fun n => ?_)
  simp only [norm_term_eq, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with h₁ h₂
  · simp [h₂]
  · simp [h₁, 

中文:
引理 not_LSeriesSummable_at_one
  条件: {N : 自然数} (hN : N != 0) (χ : DirichletCharacter 复形 N)
  证明: by
  refine fun h => (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m => Set.indicator_apply_nonneg (fun _ => by positivity))
    (fun n => ?_)
  simp only [norm_term_eq, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with h₁ h₂
  · simp [h₂]
  · simp [h₁, 

Depends on / 依赖: Real.not_summable_indicator_one_div_natCast, Set.indicator, Set.indicator_apply_nonneg, Set.mem_ofPred_eq, all_goals, h.norm.of_nonneg_of_le, indicator, indicator_apply_nonneg, map_one, mem_ofPred_eq, norm_term_eq, not_summable_indicator_one_div_natCast, of_nonneg_of_le, split_ifs
-/
lemma not_LSeriesSummable_at_one {N : Nat} (hN : N != 0) (χ : DirichletCharacter Complex N) :
    ¬ LSeriesSummable ↗χ 1 := by
  refine fun h => (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m => Set.indicator_apply_nonneg (fun _ => by positivity))
    (fun n => ?_)
  simp only [norm_term_eq, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with h₁ h₂
  · simp [h₂]
  · simp [h₁, χ.map_one]
  all_goals positivity

/--
lemma `LSeriesSummable_of_one_lt_re` / 引理 `LSeriesSummable_of_one_lt_re`

English:
lemma LSeriesSummable_of_one_lt_re
  given: {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
  proof: LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => χ.norm_le_one _) hs

中文:
引理 LSeriesSummable_of_one_lt_re
  条件: {N : 自然数} (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < s.re)
  证明: LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => χ.norm_le_one _) hs

Depends on / 依赖: LSeriesSummable_of_bounded_of_one_lt_re, norm_le_one
-/
lemma LSeriesSummable_of_one_lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    LSeriesSummable ↗χ s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => χ.norm_le_one _) hs

/--
lemma `LSeriesSummable_iff` / 引理 `LSeriesSummable_iff`

English:
lemma LSeriesSummable_iff
  given: {N : Nat} (hN : N != 0) (χ : DirichletCharacter Complex N) {s : Complex}
  proof: by
  refine ⟨fun H => ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
exact not_LSeriesSummable_at_one hN χ LSeriesSummable.of_re_le_re (by simp [h]) H

中文:
引理 LSeriesSummable_iff
  条件: {N : 自然数} (hN : N != 0) (χ : DirichletCharacter 复形 N) {s : 复形}
  证明: by
  refine ⟨fun H => ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
exact not_LSeriesSummable_at_one hN χ LSeriesSummable.of_re_le_re (by simp [h]) H

Depends on / 依赖: LSeriesSummable, LSeriesSummable.of_re_le_re, LSeriesSummable_of_one_lt_re, not_LSeriesSummable_at_one, of_re_le_re
-/
lemma LSeriesSummable_iff {N : Nat} (hN : N != 0) (χ : DirichletCharacter Complex N) {s : Complex} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H => ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
exact not_LSeriesSummable_at_one hN χ LSeriesSummable.of_re_le_re (by simp [h]) H

/--
lemma `absicssaOfAbsConv_eq_one` / 引理 `absicssaOfAbsConv_eq_one`

English:
lemma absicssaOfAbsConv_eq_one
  given: {N : Nat} (hn : N != 0) (χ : DirichletCharacter Complex N)
  proof: by
  simpa [abscissaOfAbsConv, LSeriesSummable_iff hn χ, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

中文:
引理 absicssaOfAbsConv_eq_one
  条件: {N : 自然数} (hn : N != 0) (χ : DirichletCharacter 复形 N)
  证明: by
  simpa [abscissaOfAbsConv, LSeriesSummable_iff hn χ, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

Depends on / 依赖: EReal.coe_lt_top, EReal.image_coe_Ioi, Ioi_def, LSeriesSummable_iff, Set.Ioi_def, abscissaOfAbsConv, coe_lt_top, csInf_Ioo, image_coe_Ioi
-/
lemma absicssaOfAbsConv_eq_one {N : Nat} (hn : N != 0) (χ : DirichletCharacter Complex N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa [abscissaOfAbsConv, LSeriesSummable_iff hn χ, Set.Ioi_def, EReal.image_coe_Ioi]
using csInf_Ioo EReal.coe_lt_top 1

/--
lemma `LSeriesSummable_mul` / 引理 `LSeriesSummable_mul`

English:
lemma LSeriesSummable_mul
  statement: {N : Nat} (χ : DirichletCharacter Complex N) {f : Nat -> Complex} {s : Complex}
  proof: by
refine .of_norm h.norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => norm_term_le s ?_
simpa using mul_le_of_le_one_left (norm_nonneg <| f n) χ.norm_le_one n

中文:
引理 LSeriesSummable_mul
  结论: {N : 自然数} (χ : DirichletCharacter 复形 N) {f : 自然数 -> 复形} {s : 复形}
  证明: by
refine .of_norm h.norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => norm_term_le s ?_
simpa using mul_le_of_le_one_left (norm_nonneg <| f n) χ.norm_le_one n

Depends on / 依赖: h.norm.of_nonneg_of_le, mul_le_of_le_one_left, norm_le_one, norm_nonneg, norm_term_le, of_nonneg_of_le, of_norm
-/
lemma LSeriesSummable_mul {N : Nat} (χ : DirichletCharacter Complex N) {f : Nat -> Complex} {s : Complex}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
refine .of_norm h.norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => norm_term_le s ?_
simpa using mul_le_of_le_one_left (norm_nonneg <| f n) χ.norm_le_one n

open scoped ArithmeticFunction.Moebius in
/--
lemma `LSeries.mul_mu_eq_one` / 引理 `LSeries.mul_mu_eq_one`

English:
lemma LSeries.mul_mu_eq_one
  statement: {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
  proof: by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
LSeriesSummable_mul χ ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs]; rw [convolution_mul_moebius]; rw [LSeries_delta]; rw [Pi.one_apply]

中文:
引理 LSeries.mul_mu_eq_one
  结论: {N : 自然数} (χ : DirichletCharacter 复形 N) {s : 复形}
  证明: by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
LSeriesSummable_mul χ ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs]; rw [convolution_mul_moebius]; rw [LSeries_delta]; rw [Pi.one_apply]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.LSeriesSummable_moebius_iff.mpr, LSeriesSummable_moebius_iff, LSeriesSummable_mul, LSeriesSummable_of_one_lt_re, LSeries_convolution, LSeries_delta, Pi.one_apply, convolution_mul_moebius, one_apply
-/
lemma LSeries.mul_mu_eq_one {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
LSeriesSummable_mul χ ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs]; rw [convolution_mul_moebius]; rw [LSeries_delta]; rw [Pi.one_apply]


/-!
### L-series of Dirichlet characters do not vanish on re s > 1
-/

/--
lemma `LSeries_ne_zero_of_one_lt_re` / 引理 `LSeries_ne_zero_of_one_lt_re`

English:
lemma LSeries_ne_zero_of_one_lt_re
  given: {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
  proof: fun h => by simpa [h] using LSeries.mul_mu_eq_one χ hs

中文:
引理 LSeries_ne_zero_of_one_lt_re
  条件: {N : 自然数} (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < s.re)
  证明: fun h => by simpa [h] using LSeries.mul_mu_eq_one χ hs

Depends on / 依赖: LSeries, LSeries.mul_mu_eq_one, mul_mu_eq_one
-/
lemma LSeries_ne_zero_of_one_lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    L ↗χ s != 0 :=
  fun h => by simpa [h] using LSeries.mul_mu_eq_one χ hs

end DirichletCharacter


section zeta

/-!
### The L-series of the constant sequence 1 / the arithmetic function ζ

Both give the same L-series (since the difference in values at zero has no effect;
see `ArithmeticFunction.LSeries_zeta_eq`), which agrees with the Riemann zeta function
on `re s > 1`. We state most results in two versions, one for `1` and one for `↗ζ`.
-/

open LSeries Nat Complex DirichletCharacter

/--
lemma `LSeries.abscissaOfAbsConv_one` / 引理 `LSeries.abscissaOfAbsConv_one`

English:
lemma LSeries.abscissaOfAbsConv_one
  statement: abscissaOfAbsConv 1 = 1
  proof: modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁

中文:
引理 LSeries.abscissaOfAbsConv_one
  结论: abscissaOfAbsConv 1 = 1
  证明: modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁

Depends on / 依赖: absicssaOfAbsConv_eq_one, modOne_eq_one, one_ne_zero
-/
lemma LSeries.abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1 :=
  modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁

/--
theorem `LSeriesSummable_one_iff` / 定理 `LSeriesSummable_one_iff`

English:
theorem LSeriesSummable_one_iff
  given: {s : Complex}
  statement: LSeriesSummable 1 s ↔ 1 < s.re
  proof: modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁

中文:
定理 LSeriesSummable_one_iff
  条件: {s : 复形}
  结论: LSeriesSummable 1 s ↔ 1 < s.re
  证明: modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁

Depends on / 依赖: LSeriesSummable_iff, modOne_eq_one, one_ne_zero
-/
theorem LSeriesSummable_one_iff {s : Complex} : LSeriesSummable 1 s ↔ 1 < s.re :=
  modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁


namespace ArithmeticFunction

-- access notation `ζ` and `μ`
open scoped zeta Moebius

/--
lemma `LSeries_zeta_eq` / 引理 `LSeries_zeta_eq`

English:
lemma LSeries_zeta_eq
  statement: L ↗ζ = L 1
  proof: by
  ext s
  exact (LSeries_congr const_one_eq_zeta s).symm

中文:
引理 LSeries_zeta_eq
  结论: L ↗ζ = L 1
  证明: by
  ext s
  exact (LSeries_congr const_one_eq_zeta s).symm

Depends on / 依赖: LSeries_congr, const_one_eq_zeta
-/
lemma LSeries_zeta_eq : L ↗ζ = L 1 := by
  ext s
  exact (LSeries_congr const_one_eq_zeta s).symm

/--
theorem `LSeriesSummable_zeta_iff` / 定理 `LSeriesSummable_zeta_iff`

English:
theorem LSeriesSummable_zeta_iff
  given: {s : Complex}
  statement: LSeriesSummable (ζ ·) s ↔ 1 < s.re
  proof: (LSeriesSummable_congr s const_one_eq_zeta).symm.trans LSeriesSummable_one_iff

中文:
定理 LSeriesSummable_zeta_iff
  条件: {s : 复形}
  结论: LSeriesSummable (ζ ·) s ↔ 1 < s.re
  证明: (LSeriesSummable_congr s const_one_eq_zeta).symm.trans LSeriesSummable_one_iff

Depends on / 依赖: LSeriesSummable_congr, LSeriesSummable_one_iff, const_one_eq_zeta, symm.trans
-/
theorem LSeriesSummable_zeta_iff {s : Complex} : LSeriesSummable (ζ ·) s ↔ 1 < s.re :=
(LSeriesSummable_congr s const_one_eq_zeta).symm.trans LSeriesSummable_one_iff

/--
lemma `abscissaOfAbsConv_zeta` / 引理 `abscissaOfAbsConv_zeta`

English:
lemma abscissaOfAbsConv_zeta
  statement: abscissaOfAbsConv ↗ζ = 1
  proof: by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn => by simp [hn], abscissaOfAbsConv_one]

中文:
引理 abscissaOfAbsConv_zeta
  结论: abscissaOfAbsConv ↗ζ = 1
  证明: by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn => by simp [hn], abscissaOfAbsConv_one]

Depends on / 依赖: Finset, Finset.mem_Icc, List.mem_range, List.mem_toFinset, Nat.lt_succ_iff, abscissaOfAbsConv_congr, abscissaOfAbsConv_one, add_comm, lt_succ_iff, mem_Icc, mem_range, mem_toFinset
-/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1 := by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn => by simp [hn], abscissaOfAbsConv_one]

/--
lemma `LSeries_zeta_eq_riemannZeta` / 引理 `LSeries_zeta_eq_riemannZeta`

English:
lemma LSeries_zeta_eq_riemannZeta
  given: {s : Complex} (hs : 1 < s.re)
  statement: L ↗ζ s = riemannZeta s
  proof: by
  suffices ∑' n, term (fun n => if n = 0 then 0 else 1) s n = ∑' n : Nat, 1 / (n : Complex) ^ s by
    simpa [LSeries, zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, ne_zero_of_one_lt_re hs]

中文:
引理 LSeries_zeta_eq_riemannZeta
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L ↗ζ s = riemannZeta s
  证明: by
  suffices ∑' n, term (fun n => if n = 0 then 0 else 1) s n = ∑' n : Nat, 1 / (n : Complex) ^ s by
    simpa [LSeries, zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, ne_zero_of_one_lt_re hs]

Depends on / 依赖: LSeries, eq_or_ne, ne_zero_of_one_lt_re, tsum_congr, zeta_eq_tsum_one_div_nat_cpow
-/
lemma LSeries_zeta_eq_riemannZeta {s : Complex} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s := by
  suffices ∑' n, term (fun n => if n = 0 then 0 else 1) s n = ∑' n : Nat, 1 / (n : Complex) ^ s by
    simpa [LSeries, zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, ne_zero_of_one_lt_re hs]

/--
lemma `LSeriesHasSum_zeta` / 引理 `LSeriesHasSum_zeta`

English:
lemma LSeriesHasSum_zeta
  given: {s : Complex} (hs : 1 < s.re)
  statement: LSeriesHasSum ↗ζ s (riemannZeta s)
  proof: LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum

中文:
引理 LSeriesHasSum_zeta
  条件: {s : 复形} (hs : 1 < s.re)
  结论: LSeriesHasSum ↗ζ s (riemannZeta s)
  证明: LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum

Depends on / 依赖: LSeriesHasSum, LSeriesSummable_zeta_iff, LSeriesSummable_zeta_iff.mpr, LSeries_zeta_eq_riemannZeta
-/
lemma LSeriesHasSum_zeta {s : Complex} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (riemannZeta s) :=
  LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum

/--
lemma `LSeries_zeta_mul_Lseries_moebius` / 引理 `LSeries_zeta_mul_Lseries_moebius`

English:
lemma LSeries_zeta_mul_Lseries_moebius
  given: {s : Complex} (hs : 1 < s.re)
  statement: L ↗ζ s * L ↗μ s = 1
  proof: by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp [← natCoe_apply, ← intCoe_apply, coe_mul, one_eq_delta, LSeries_delta, -zeta_apply]

中文:
引理 LSeries_zeta_mul_Lseries_moebius
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L ↗ζ s * L ↗μ s = 1
  证明: by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp [← natCoe_apply, ← intCoe_apply, coe_mul, one_eq_delta, LSeries_delta, -zeta_apply]

Depends on / 依赖: LSeriesSummable_moebius_iff, LSeriesSummable_moebius_iff.mpr, LSeriesSummable_zeta_iff, LSeriesSummable_zeta_iff.mpr, LSeries_convolution, LSeries_delta, coe_mul, intCoe_apply, natCoe_apply, one_eq_delta, zeta_apply
-/
lemma LSeries_zeta_mul_Lseries_moebius {s : Complex} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp [← natCoe_apply, ← intCoe_apply, coe_mul, one_eq_delta, LSeries_delta, -zeta_apply]

/--
lemma `LSeries_zeta_ne_zero_of_one_lt_re` / 引理 `LSeries_zeta_ne_zero_of_one_lt_re`

English:
lemma LSeries_zeta_ne_zero_of_one_lt_re
  given: {s : Complex} (hs : 1 < s.re)
  statement: L ↗ζ s != 0
  proof: fun h => by simpa [h, -zeta_apply] using LSeries_zeta_mul_Lseries_moebius hs

中文:
引理 LSeries_zeta_ne_zero_of_one_lt_re
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L ↗ζ s != 0
  证明: fun h => by simpa [h, -zeta_apply] using LSeries_zeta_mul_Lseries_moebius hs

Depends on / 依赖: LSeries_zeta_mul_Lseries_moebius, zeta_apply
-/
lemma LSeries_zeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : L ↗ζ s != 0 :=
  fun h => by simpa [h, -zeta_apply] using LSeries_zeta_mul_Lseries_moebius hs

end ArithmeticFunction

open ArithmeticFunction

/--
lemma `LSeries_one_eq_riemannZeta` / 引理 `LSeries_one_eq_riemannZeta`

English:
lemma LSeries_one_eq_riemannZeta
  given: {s : Complex} (hs : 1 < s.re)
  statement: L 1 s = riemannZeta s
  proof: LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

中文:
引理 LSeries_one_eq_riemannZeta
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L 1 s = riemannZeta s
  证明: LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

Depends on / 依赖: LSeries_zeta_eq, LSeries_zeta_eq_riemannZeta
-/
lemma LSeries_one_eq_riemannZeta {s : Complex} (hs : 1 < s.re) : L 1 s = riemannZeta s :=
  LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

/--
lemma `LSeriesHasSum_one` / 引理 `LSeriesHasSum_one`

English:
lemma LSeriesHasSum_one
  given: {s : Complex} (hs : 1 < s.re)
  statement: LSeriesHasSum 1 s (riemannZeta s)
  proof: LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum

中文:
引理 LSeriesHasSum_one
  条件: {s : 复形} (hs : 1 < s.re)
  结论: LSeriesHasSum 1 s (riemannZeta s)
  证明: LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum

Depends on / 依赖: LSeriesHasSum, LSeriesSummable_one_iff, LSeriesSummable_one_iff.mpr, LSeries_one_eq_riemannZeta
-/
lemma LSeriesHasSum_one {s : Complex} (hs : 1 < s.re) : LSeriesHasSum 1 s (riemannZeta s) :=
  LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum

open scoped Moebius in -- access notation `μ`
/--
lemma `LSeries_one_mul_Lseries_moebius` / 引理 `LSeries_one_mul_Lseries_moebius`

English:
lemma LSeries_one_mul_Lseries_moebius
  given: {s : Complex} (hs : 1 < s.re)
  statement: L 1 s * L ↗μ s = 1
  proof: LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs

中文:
引理 LSeries_one_mul_Lseries_moebius
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L 1 s * L ↗μ s = 1
  证明: LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs

Depends on / 依赖: LSeries_zeta_eq, LSeries_zeta_mul_Lseries_moebius
-/
lemma LSeries_one_mul_Lseries_moebius {s : Complex} (hs : 1 < s.re) : L 1 s * L ↗μ s = 1 :=
  LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs

/--
lemma `LSeries_one_ne_zero_of_one_lt_re` / 引理 `LSeries_one_ne_zero_of_one_lt_re`

English:
lemma LSeries_one_ne_zero_of_one_lt_re
  given: {s : Complex} (hs : 1 < s.re)
  statement: L 1 s != 0
  proof: LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs

中文:
引理 LSeries_one_ne_zero_of_one_lt_re
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L 1 s != 0
  证明: LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs

Depends on / 依赖: LSeries_zeta_eq, LSeries_zeta_ne_zero_of_one_lt_re
-/
lemma LSeries_one_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : L 1 s != 0 :=
  LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs

/--
lemma `riemannZeta_ne_zero_of_one_lt_re` / 引理 `riemannZeta_ne_zero_of_one_lt_re`

English:
lemma riemannZeta_ne_zero_of_one_lt_re
  given: {s : Complex} (hs : 1 < s.re)
  statement: riemannZeta s != 0
  proof: LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs

中文:
引理 riemannZeta_ne_zero_of_one_lt_re
  条件: {s : 复形} (hs : 1 < s.re)
  结论: riemannZeta s != 0
  证明: LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs

Depends on / 依赖: LSeries_one_eq_riemannZeta, LSeries_one_ne_zero_of_one_lt_re
-/
lemma riemannZeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : riemannZeta s != 0 :=
  LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs

section ComplexOrderLemmas

open scoped ComplexOrder

/--
lemma `riemannZeta_pos_of_one_lt` / 引理 `riemannZeta_pos_of_one_lt`

English:
lemma riemannZeta_pos_of_one_lt
  given: {x : Real} (hx : 1 < x)
  statement: 0 < riemannZeta x
  proof: by
  have hx' : 1 < (x : Complex).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx']
  refine LSeries.positive (fun _ => by simp) (by simp) ?_
  simpa [LSeries.abscissaOfAbsConv_one] using (by exact_mod_cast hx : (1 : EReal) < x)

中文:
引理 riemannZeta_pos_of_one_lt
  条件: {x : 实数} (hx : 1 < x)
  结论: 0 < riemannZeta x
  证明: by
  have hx' : 1 < (x : Complex).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx']
  refine LSeries.positive (fun _ => by simp) (by simp) ?_
  simpa [LSeries.abscissaOfAbsConv_one] using (by exact_mod_cast hx : (1 : EReal) < x)

Depends on / 依赖: LSeries, LSeries.abscissaOfAbsConv_one, LSeries.positive, LSeries_one_eq_riemannZeta, abscissaOfAbsConv_one, positive
-/
lemma riemannZeta_pos_of_one_lt {x : Real} (hx : 1 < x) : 0 < riemannZeta x := by
  have hx' : 1 < (x : Complex).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx']
  refine LSeries.positive (fun _ => by simp) (by simp) ?_
  simpa [LSeries.abscissaOfAbsConv_one] using (by exact_mod_cast hx : (1 : EReal) < x)

/--
lemma `riemannZeta_re_pos_of_one_lt` / 引理 `riemannZeta_re_pos_of_one_lt`

English:
lemma riemannZeta_re_pos_of_one_lt
  given: {x : Real} (hx : 1 < x)
  statement: 0 < (riemannZeta x).re
  proof: (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).1

中文:
引理 riemannZeta_re_pos_of_one_lt
  条件: {x : 实数} (hx : 1 < x)
  结论: 0 < (riemannZeta x).re
  证明: (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).1

Depends on / 依赖: Complex.pos_iff.mp, pos_iff, riemannZeta_pos_of_one_lt
-/
lemma riemannZeta_re_pos_of_one_lt {x : Real} (hx : 1 < x) : 0 < (riemannZeta x).re :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).1

/--
lemma `riemannZeta_im_eq_zero_of_one_lt` / 引理 `riemannZeta_im_eq_zero_of_one_lt`

English:
lemma riemannZeta_im_eq_zero_of_one_lt
  given: {x : Real} (hx : 1 < x)
  statement: (riemannZeta x).im = 0
  proof: (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).2.symm

中文:
引理 riemannZeta_im_eq_zero_of_one_lt
  条件: {x : 实数} (hx : 1 < x)
  结论: (riemannZeta x).im = 0
  证明: (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).2.symm

Depends on / 依赖: Complex.pos_iff.mp, pos_iff, riemannZeta_pos_of_one_lt
-/
lemma riemannZeta_im_eq_zero_of_one_lt {x : Real} (hx : 1 < x) : (riemannZeta x).im = 0 :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).2.symm

end ComplexOrderLemmas

end zeta


section vonMangoldt

/-!
### The L-series of the von Mangoldt function
-/

open LSeries Nat Complex ArithmeticFunction

namespace ArithmeticFunction

-- access notation `ζ`
open scoped zeta

/--
lemma `convolution_vonMangoldt_zeta` / 引理 `convolution_vonMangoldt_zeta`

English:
lemma convolution_vonMangoldt_zeta
  statement: ↗Λ ⍟ ↗ζ = ↗Complex.log
  proof: by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n) vonMangoldt_mul_zeta

中文:
引理 convolution_vonMangoldt_zeta
  结论: ↗Λ ⍟ ↗ζ = ↗复形.log
  证明: by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n) vonMangoldt_mul_zeta

Depends on / 依赖: LSeries, LSeries.convolution_def, apply_ite, congr_arg, convolution_def, ofReal, vonMangoldt_mul_zeta
-/
lemma convolution_vonMangoldt_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log := by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n) vonMangoldt_mul_zeta

/--
lemma `convolution_vonMangoldt_const_one` / 引理 `convolution_vonMangoldt_const_one`

English:
lemma convolution_vonMangoldt_const_one
  statement: ↗Λ ⍟ 1 = ↗Complex.log
  proof: (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta

中文:
引理 convolution_vonMangoldt_const_one
  结论: ↗Λ ⍟ 1 = ↗复形.log
  证明: (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta

Depends on / 依赖: convolution_one_eq_convolution_zeta, convolution_vonMangoldt_zeta
-/
lemma convolution_vonMangoldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log :=
  (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta

/--
lemma `LSeriesSummable_vonMangoldt` / 引理 `LSeriesSummable_vonMangoldt`

English:
lemma LSeriesSummable_vonMangoldt
  given: {s : Complex} (hs : 1 < s.re)
  statement: LSeriesSummable ↗Λ s
  proof: by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  refine hf.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le s ?_)
  have hΛ : ‖↗Λ n‖ <= ‖Com

中文:
引理 LSeriesSummable_vonMangoldt
  条件: {s : 复形} (hs : 1 < s.re)
  结论: LSeriesSummable ↗Λ s
  证明: by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  refine hf.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le s ?_)
  have hΛ : ‖↗Λ n‖ <= ‖Com

Depends on / 依赖: Complex.log, LSeriesSummable, LSeriesSummable_logMul_of_lt_re, Real.log_natCast_nonneg, abs_of_nonneg, abscissaOfAbsConv, abscissaOfAbsConv_one, hf.of_nonneg_of_le, log_natCast_nonneg, natCast_log, norm_nonneg, norm_term_le, of_nonneg_of_le, s.re, summable_norm_iff, vonMangoldt_le_log, vonMangoldt_nonneg
-/
lemma LSeriesSummable_vonMangoldt {s : Complex} (hs : 1 < s.re) : LSeriesSummable ↗Λ s := by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  refine hf.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le s ?_)
  have hΛ : ‖↗Λ n‖ <= ‖Complex.log n‖ := by
    simpa [abs_of_nonneg, vonMangoldt_nonneg, ← natCast_log, Real.log_natCast_nonneg]
      using vonMangoldt_le_log
exact hΛ.trans by simp

end ArithmeticFunction

namespace DirichletCharacter

/--
lemma `convolution_twist_vonMangoldt` / 引理 `convolution_twist_vonMangoldt`

English:
lemma convolution_twist_vonMangoldt
  given: {N : Nat} (χ : DirichletCharacter Complex N)
  proof: by
  rw [← convolution_vonMangoldt_const_one]; rw [← χ.mul_convolution_distrib]; rw [mul_one]

中文:
引理 convolution_twist_vonMangoldt
  条件: {N : 自然数} (χ : DirichletCharacter 复形 N)
  证明: by
  rw [← convolution_vonMangoldt_const_one]; rw [← χ.mul_convolution_distrib]; rw [mul_one]

Depends on / 依赖: convolution_vonMangoldt_const_one, mul_convolution_distrib, mul_one
-/
lemma convolution_twist_vonMangoldt {N : Nat} (χ : DirichletCharacter Complex N) :
    (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Complex.log := by
  rw [← convolution_vonMangoldt_const_one]; rw [← χ.mul_convolution_distrib]; rw [mul_one]

/--
lemma `LSeriesSummable_twist_vonMangoldt` / 引理 `LSeriesSummable_twist_vonMangoldt`

English:
lemma LSeriesSummable_twist_vonMangoldt
  statement: {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
  proof: LSeriesSummable_mul χ LSeriesSummable_vonMangoldt hs

中文:
引理 LSeriesSummable_twist_vonMangoldt
  结论: {N : 自然数} (χ : DirichletCharacter 复形 N) {s : 复形}
  证明: LSeriesSummable_mul χ LSeriesSummable_vonMangoldt hs

Depends on / 依赖: LSeriesSummable_mul, LSeriesSummable_vonMangoldt
-/
lemma LSeriesSummable_twist_vonMangoldt {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) :
    LSeriesSummable (↗χ * ↗Λ) s :=
LSeriesSummable_mul χ LSeriesSummable_vonMangoldt hs

/--
lemma `LSeries_twist_vonMangoldt_eq` / 引理 `LSeries_twist_vonMangoldt_eq`

English:
lemma LSeries_twist_vonMangoldt_eq
  given: {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
  proof: by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [modZero_eq_delta, delta_mul_eq_smul_delta, LSeries_delta]
  -- now `N ≠ 0`
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, ERea

中文:
引理 LSeries_twist_vonMangoldt_eq
  条件: {N : 自然数} (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < s.re)
  证明: by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [modZero_eq_delta, delta_mul_eq_smul_delta, LSeries_delta]
  -- now `N ≠ 0`
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, ERea

Depends on / 依赖: LSeries_delta, delta_mul_eq_smul_delta, eq_or_ne, modZero_eq_delta
-/
lemma LSeries_twist_vonMangoldt_eq {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / L ↗χ s := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [modZero_eq_delta, delta_mul_eq_smul_delta, LSeries_delta]
  -- now `N ≠ 0`
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  have hΛ : LSeriesSummable (↗χ * ↗Λ) s := LSeriesSummable_twist_vonMangoldt χ hs
  rw [eq_div_iff <| LSeries_ne_zero_of_one_lt_re χ hs]; rw [← LSeries_convolution' hΛ hχ]; rw [convolution_twist_vonMangoldt]; rw [LSeries_deriv hs']; rw [neg_neg]
  exact LSeries_congr (fun _ => by simp [mul_comm, logMul]) s

end DirichletCharacter

namespace ArithmeticFunction

open DirichletCharacter in
/--
lemma `LSeries_vonMangoldt_eq` / 引理 `LSeries_vonMangoldt_eq`

English:
lemma LSeries_vonMangoldt_eq
  given: {s : Complex} (hs : 1 < s.re)
  statement: L ↗Λ s = - deriv (L 1) s / L 1 s
  proof: by
refine (LSeries_congr (fun {n} _ => ?_) s).trans
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp [Subsingleton.eq_one (α := ZMod 1)]

中文:
引理 LSeries_vonMangoldt_eq
  条件: {s : 复形} (hs : 1 < s.re)
  结论: L ↗Λ s = - deriv (L 1) s / L 1 s
  证明: by
refine (LSeries_congr (fun {n} _ => ?_) s).trans
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp [Subsingleton.eq_one (α := ZMod 1)]

Depends on / 依赖: LSeries_congr, LSeries_modOne_eq, LSeries_twist_vonMangoldt_eq, Subsingleton, Subsingleton.eq_one, eq_one
-/
lemma LSeries_vonMangoldt_eq {s : Complex} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s := by
refine (LSeries_congr (fun {n} _ => ?_) s).trans
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp [Subsingleton.eq_one (α := ZMod 1)]

/--
lemma `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` / 引理 `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`

English:
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  given: {s : Complex} (hs : 1 < s.re)
  proof: by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs]; rw [← LSeries_one_eq_riemannZeta hs]; rw [this]
refine Filter.EventuallyEq.deriv_eq Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    

中文:
引理 LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  条件: {s : 复形} (hs : 1 < s.re)
  证明: by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs]; rw [← LSeries_one_eq_riemannZeta hs]; rw [this]
refine Filter.EventuallyEq.deriv_eq Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.deriv_eq, Filter.eventuallyEq_iff_exists_mem.mpr, LSeries_one_eq_riemannZeta, LSeries_vonMangoldt_eq, continuous_const, continuous_re, deriv_eq, eventuallyEq_iff_exists_mem, isOpen_lt, mem_nhds, riemannZeta, z.re
-/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : Complex} (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s := by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs]; rw [← LSeries_one_eq_riemannZeta hs]; rw [this]
refine Filter.EventuallyEq.deriv_eq Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    fun _ => LSeries_one_eq_riemannZeta⟩

end ArithmeticFunction

end vonMangoldt
