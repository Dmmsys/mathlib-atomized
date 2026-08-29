/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Hensel's lemma on `ℤ_p`

This file proves Hensel's lemma on `ℤ_p`, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/

public section


noncomputable section

open Topology

-- We begin with some general lemmas that are used below in the computation.
/--
theorem `padic_polynomial_dist` / 定理 `padic_polynomial_dist`

English:
theorem padic_polynomial_dist
  statement: {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
  proof: by
  let ⟨z, hz⟩ := (F.map (algebraMap R Int_[p])).evalSubFactor x y
  simp only [Polynomial.eval_map_algebraMap] at hz
  calc
    ‖F.aeval x - F.aeval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ <= 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

中文:
定理 padic_polynomial_dist
  结论: {p : 自然数} [Fact p.素] {R : 类型} [交换半环 R] [代数 R 整数_[p]]
  证明: by
  let ⟨z, hz⟩ := (F.map (algebraMap R Int_[p])).evalSubFactor x y
  simp only [Polynomial.eval_map_algebraMap] at hz
  calc
    ‖F.aeval x - F.aeval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ <= 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

Depends on / 依赖: F.aeval, F.map, Int_, PadicInt, PadicInt.norm_le_one, Polynomial, Polynomial.eval_map_algebraMap, algebraMap, evalSubFactor, eval_map_algebraMap, norm_le_one
-/
theorem padic_polynomial_dist {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
    (F : Polynomial R) (x y : Int_[p]) :
    ‖F.aeval x - F.aeval y‖ <= ‖x - y‖ := by
  let ⟨z, hz⟩ := (F.map (algebraMap R Int_[p])).evalSubFactor x y
  simp only [Polynomial.eval_map_algebraMap] at hz
  calc
    ‖F.aeval x - F.aeval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ <= 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

open Filter Metric

/--
theorem `comp_tendsto_lim` / 定理 `comp_tendsto_lim`

English:
theorem comp_tendsto_lim
  statement: {p : Nat} [Fact p.Prime] {F : Polynomial Int_[p]}
  proof: Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit

中文:
定理 comp_tendsto_lim
  结论: {p : 自然数} [Fact p.素] {F : 多项式 整数_[p]}
  证明: Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit
-/
private theorem comp_tendsto_lim {p : Nat} [Fact p.Prime] {F : Polynomial Int_[p]}
    (ncs : CauSeq Int_[p] norm) : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 (F.eval ncs.lim)) :=
  Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit

section

variable {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
  {ncs : CauSeq Int_[p] norm} {F : Polynomial R}
  {a : Int_[p]} (ncs_der_val : forall n, ‖F.derivative.aeval (ncs n)‖ = ‖F.derivative.aeval a‖)

/--
theorem `ncs_tendsto_lim` / 定理 `ncs_tendsto_lim`

English:
theorem ncs_tendsto_lim
  proof: by
  refine Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) ?_
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

include ncs_der_val

中文:
定理 ncs_tendsto_lim
  证明: by
  refine Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) ?_
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

include ncs_der_val
-/
private theorem ncs_tendsto_lim :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval ncs.lim‖) := by
  refine Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) ?_
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

include ncs_der_val

/--
theorem `ncs_tendsto_const` / 定理 `ncs_tendsto_const`

English:
theorem ncs_tendsto_const
  proof: by
  convert! @tendsto_const_nhds Real _ Nat _ _; rw [ncs_der_val]

中文:
定理 ncs_tendsto_const
  证明: by
  convert! @tendsto_const_nhds Real _ Nat _ _; rw [ncs_der_val]
-/
private theorem ncs_tendsto_const :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval a‖) := by
  convert! @tendsto_const_nhds Real _ Nat _ _; rw [ncs_der_val]

/--
theorem `norm_deriv_eq` / 定理 `norm_deriv_eq`

English:
theorem norm_deriv_eq
  statement: ‖F.derivative.aeval ncs.lim‖ = ‖F.derivative.aeval a‖
  proof: tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)

中文:
定理 norm_deriv_eq
  结论: ‖F.derivative.aeval ncs.lim‖ = ‖F.derivative.aeval a‖
  证明: tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)
-/
private theorem norm_deriv_eq : ‖F.derivative.aeval ncs.lim‖ = ‖F.derivative.aeval a‖ :=
  tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)

end

section


variable {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
  {ncs : CauSeq Int_[p] norm} {F : Polynomial R}
  (hnorm : Tendsto (fun i => ‖F.aeval (ncs i)‖) atTop (𝓝 0))
include hnorm

/--
theorem `tendsto_zero_of_norm_tendsto_zero` / 定理 `tendsto_zero_of_norm_tendsto_zero`

English:
theorem tendsto_zero_of_norm_tendsto_zero
  proof: tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)

中文:
定理 tendsto_zero_of_norm_tendsto_zero
  证明: tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)
-/
private theorem tendsto_zero_of_norm_tendsto_zero :
    Tendsto (fun i => F.aeval (ncs i)) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)

/--
theorem `limit_zero_of_norm_tendsto_zero` / 定理 `limit_zero_of_norm_tendsto_zero`

English:
theorem limit_zero_of_norm_tendsto_zero
  statement: F.aeval ncs.lim = 0
  proof: by
  refine tendsto_nhds_unique ?_ (tendsto_zero_of_norm_tendsto_zero hnorm)
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

中文:
定理 limit_zero_of_norm_tendsto_zero
  结论: F.aeval ncs.lim = 0
  证明: by
  refine tendsto_nhds_unique ?_ (tendsto_zero_of_norm_tendsto_zero hnorm)
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

Depends on / 依赖: Polynomial, Polynomial.eval_map_algebraMap, comp_tendsto_lim, eval_map_algebraMap, tendsto_nhds_unique, tendsto_zero_of_norm_tendsto_zero
-/
theorem limit_zero_of_norm_tendsto_zero : F.aeval ncs.lim = 0 := by
  refine tendsto_nhds_unique ?_ (tendsto_zero_of_norm_tendsto_zero hnorm)
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

end

/--
theorem `a_soln_is_unique` / 定理 `a_soln_is_unique`

English:
theorem a_soln_is_unique
  statement: {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R]
  proof: by
  let h := z' - a
  let ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion a h
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hq
  have : (F.derivative.aeval a + q * h) * h = 0 := by calc
    _ = F.aeval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
    _ = _ := show F.aeval (a + (z' - a)) = 0 by simp [hz']
  have : h = 0 := by_contra fun hne =>
    have : F.derivative.aeval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
    have : F.derivative.aeval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
    lt_irrefl ‖F.derivative.aeval a‖
      (calc
        ‖F.derivative.aeval a‖ = ‖q‖ * ‖h‖ := by simp [this]
        _ <= 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
        _ < ‖F.derivative.aeval a‖ := by simpa)
  exact eq_of_sub_eq_zero (by rw [← this])

中文:
定理 a_soln_is_unique
  结论: {p : 自然数} [Fact p.素] {R : 类型} [交换半环 R]
  证明: by
  let h := z' - a
  let ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion a h
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hq
  have : (F.derivative.aeval a + q * h) * h = 0 := by calc
    _ = F.aeval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
    _ = _ := show F.aeval (a + (z' - a)) = 0 by simp [hz']
  have : h = 0 := by_contra fun hne =>
    have : F.derivative.aeval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
    have : F.derivative.aeval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
    lt_irrefl ‖F.derivative.aeval a‖
      (calc
        ‖F.derivative.aeval a‖ = ‖q‖ * ‖h‖ := by simp [this]
        _ <= 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
        _ < ‖F.derivative.aeval a‖ := by simpa)
  exact eq_of_sub_eq_zero (by rw [← this])
-/
private theorem a_soln_is_unique {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R]
    [Algebra R Int_[p]] {F : Polynomial R} {a : Int_[p]} (ha : F.aeval a = 0) (z' : Int_[p])
    (hz' : F.aeval z' = 0) (hnormz' : ‖z' - a‖ < ‖F.derivative.aeval a‖) : z' = a := by
  let h := z' - a
  let ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion a h
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hq
  have : (F.derivative.aeval a + q * h) * h = 0 := by calc
    _ = F.aeval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
    _ = _ := show F.aeval (a + (z' - a)) = 0 by simp [hz']
  have : h = 0 := by_contra fun hne =>
    have : F.derivative.aeval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
    have : F.derivative.aeval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
    lt_irrefl ‖F.derivative.aeval a‖
      (calc
        ‖F.derivative.aeval a‖ = ‖q‖ * ‖h‖ := by simp [this]
        _ <= 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
        _ < ‖F.derivative.aeval a‖ := by simpa)
  exact eq_of_sub_eq_zero (by rw [← this])

section Hensel

open Nat

variable (p : Nat) [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
  (F : Polynomial R) (a : Int_[p])

/--
Definition of `T_gen` / `T_gen` 的定义

English:
definition T_gen
  signature: : Real
  body: ‖F.aeval a / ((F.derivative.aeval a ^ 2 : Int_[p]) : Rat_[p])‖

local notation "T" => @T_gen p _ _ _ _ F a

中文:
定义 T_gen
  签名: : 实数
  定义体: ‖F.aeval a / ((F.derivative.aeval a ^ 2 : Int_[p]) : Rat_[p])‖

local notation "T" => @T_gen p _ _ _ _ F a
-/
private def T_gen : Real := ‖F.aeval a / ((F.derivative.aeval a ^ 2 : Int_[p]) : Rat_[p])‖

local notation "T" => @T_gen p _ _ _ _ F a

variable {p F a}

/--
theorem `T_def` / 定理 `T_def`

English:
theorem T_def
  statement: T = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ ^ 2
  proof: by
  simp [T_gen]

中文:
定理 T_def
  结论: T = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ ^ 2
  证明: by
  simp [T_gen]
-/
private theorem T_def : T = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ ^ 2 := by
  simp [T_gen]

/--
theorem `T_nonneg` / 定理 `T_nonneg`

English:
theorem T_nonneg
  statement: 0 <= T
  proof: norm_nonneg _

中文:
定理 T_nonneg
  结论: 0 <= T
  证明: norm_nonneg _
-/
private theorem T_nonneg : 0 <= T := norm_nonneg _

/--
theorem `T_pow_nonneg` / 定理 `T_pow_nonneg`

English:
theorem T_pow_nonneg
  given: (n : Nat)
  statement: 0 <= T ^ n
  proof: pow_nonneg T_nonneg _

中文:
定理 T_pow_nonneg
  条件: (n : 自然数)
  结论: 0 <= T ^ n
  证明: pow_nonneg T_nonneg _
-/
private theorem T_pow_nonneg (n : Nat) : 0 <= T ^ n := pow_nonneg T_nonneg _

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm

/--
theorem `deriv_sq_norm_pos` / 定理 `deriv_sq_norm_pos`

English:
theorem deriv_sq_norm_pos
  statement: 0 < ‖F.derivative.aeval a‖ ^ 2
  proof: lt_of_le_of_lt (norm_nonneg _) hnorm

中文:
定理 deriv_sq_norm_pos
  结论: 0 < ‖F.derivative.aeval a‖ ^ 2
  证明: lt_of_le_of_lt (norm_nonneg _) hnorm
-/
private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.aeval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm

/--
theorem `deriv_sq_norm_ne_zero` / 定理 `deriv_sq_norm_ne_zero`

English:
theorem deriv_sq_norm_ne_zero
  statement: ‖F.derivative.aeval a‖ ^ 2 != 0
  proof: ne_of_gt (deriv_sq_norm_pos hnorm)

中文:
定理 deriv_sq_norm_ne_zero
  结论: ‖F.derivative.aeval a‖ ^ 2 != 0
  证明: ne_of_gt (deriv_sq_norm_pos hnorm)
-/
private theorem deriv_sq_norm_ne_zero : ‖F.derivative.aeval a‖ ^ 2 != 0 :=
  ne_of_gt (deriv_sq_norm_pos hnorm)

/--
theorem `deriv_norm_ne_zero` / 定理 `deriv_norm_ne_zero`

English:
theorem deriv_norm_ne_zero
  statement: ‖F.derivative.aeval a‖ != 0
  proof: fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])

中文:
定理 deriv_norm_ne_zero
  结论: ‖F.derivative.aeval a‖ != 0
  证明: fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])
-/
private theorem deriv_norm_ne_zero : ‖F.derivative.aeval a‖ != 0 := fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])

/--
theorem `deriv_norm_pos` / 定理 `deriv_norm_pos`

English:
theorem deriv_norm_pos
  statement: 0 < ‖F.derivative.aeval a‖
  proof: lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))

中文:
定理 deriv_norm_pos
  结论: 0 < ‖F.derivative.aeval a‖
  证明: lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))
-/
private theorem deriv_norm_pos : 0 < ‖F.derivative.aeval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))

/--
theorem `deriv_ne_zero` / 定理 `deriv_ne_zero`

English:
theorem deriv_ne_zero
  statement: F.derivative.aeval a != 0
  proof: mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)

中文:
定理 deriv_ne_zero
  结论: F.derivative.aeval a != 0
  证明: mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)
-/
private theorem deriv_ne_zero : F.derivative.aeval a != 0 :=
  mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)


/--
theorem `T_lt_one` / 定理 `T_lt_one`

English:
theorem T_lt_one
  statement: T < 1
  proof: by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h

中文:
定理 T_lt_one
  结论: T < 1
  证明: by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h
-/
private theorem T_lt_one : T < 1 := by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h

/--
theorem `T_pow` / 定理 `T_pow`

English:
theorem T_pow
  given: {n : Nat} (hn : n != 0)
  statement: T ^ n < 1
  proof: pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn

中文:
定理 T_pow
  条件: {n : 自然数} (hn : n != 0)
  结论: T ^ n < 1
  证明: pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn
-/
private theorem T_pow {n : Nat} (hn : n != 0) : T ^ n < 1 := pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn

/--
theorem `T_pow'` / 定理 `T_pow'`

English:
theorem T_pow'
  given: (n : Nat)
  statement: T ^ 2 ^ n < 1
  proof: T_pow hnorm (pow_ne_zero _ two_ne_zero)

中文:
定理 T_pow'
  条件: (n : 自然数)
  结论: T ^ 2 ^ n < 1
  证明: T_pow hnorm (pow_ne_zero _ two_ne_zero)
-/
private theorem T_pow' (n : Nat) : T ^ 2 ^ n < 1 := T_pow hnorm (pow_ne_zero _ two_ne_zero)

/--
Definition of `ih_gen` / `ih_gen` 的定义

English:
definition ih_gen
  signature: (n : Nat) (z : Int_[p])
  body: ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ ‖F.aeval z‖ <=
    ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => @ih_gen p _ _ _ _ F a

中文:
定义 ih_gen
  签名: (n : 自然数) (z : 整数_[p])
  定义体: ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ ‖F.aeval z‖ <=
    ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => @ih_gen p _ _ _ _ F a
-/
private def ih_gen (n : Nat) (z : Int_[p]) : Prop :=
  ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ ‖F.aeval z‖ <=
    ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => @ih_gen p _ _ _ _ F a

/--
theorem `ih_0` / 定理 `ih_0`

English:
theorem ih_0
  statement: ih 0 a
  proof: ⟨rfl, by simp [T_def, mul_div_cancel₀ _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩

中文:
定理 ih_0
  结论: ih 0 a
  证明: ⟨rfl, by simp [T_def, mul_div_cancel₀ _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩
-/
private theorem ih_0 : ih 0 a :=
  ⟨rfl, by simp [T_def, mul_div_cancel₀ _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩

/--
theorem `calc_norm_le_one` / 定理 `calc_norm_le_one`

English:
theorem calc_norm_le_one
  given: {n : Nat} {z : Int_[p]} (hz : ih n z)
  proof: calc
    ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ =
        ‖(↑(F.aeval z) : Rat_[p])‖ / ‖(↑(F.derivative.aeval z) : Rat_[p])‖ :=
      norm_div _ _
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := by simp [hz.1]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ <= 1 := mul_le_one₀ (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' hnorm _))

中文:
定理 calc_norm_le_one
  条件: {n : 自然数} {z : 整数_[p]} (hz : ih n z)
  证明: calc
    ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ =
        ‖(↑(F.aeval z) : Rat_[p])‖ / ‖(↑(F.derivative.aeval z) : Rat_[p])‖ :=
      norm_div _ _
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := by simp [hz.1]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ <= 1 := mul_le_one₀ (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' hnorm _))
-/
private theorem calc_norm_le_one {n : Nat} {z : Int_[p]} (hz : ih n z) :
    ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1 :=
  calc
    ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ =
        ‖(↑(F.aeval z) : Rat_[p])‖ / ‖(↑(F.derivative.aeval z) : Rat_[p])‖ :=
      norm_div _ _
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := by simp [hz.1]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ <= 1 := mul_le_one₀ (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' hnorm _))


/--
theorem `calc_deriv_dist` / 定理 `calc_deriv_dist`

English:
theorem calc_deriv_dist
  statement: {z z' z1 : Int_[p]} (hz' : z' = z - z1)
  proof: calc
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ <= ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := hz1
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.aeval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)

中文:
定理 calc_deriv_dist
  结论: {z z' z1 : 整数_[p]} (hz' : z' = z - z1)
  证明: calc
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ <= ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := hz1
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.aeval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)
-/
private theorem calc_deriv_dist {z z' z1 : Int_[p]} (hz' : z' = z - z1)
    (hz1 : ‖z1‖ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖) {n} (hz : ih n z) :
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
  calc
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ <= ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := hz1
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.aeval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)


set_option backward.isDefEq.respectTransparency false in
/--
Definition of `calc_eval_z'` / `calc_eval_z'` 的定义

English:
definition calc_eval_z'
  signature: {z z' z1 : Int_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
  body: by
  have hdzne : F.derivative.aeval z != 0 :=
    mt norm_eq_zero.2 (by rw [hz.1]; apply deriv_norm_ne_zero; assumption)
  have hdzne' : (↑(F.derivative.aeval z) : Rat_[p]) != 0 := fun h => hdzne (Subtype.ext_iff.2 h)
  obtain ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion z (-z1)
  have : ‖(↑(F.derivative.aeval z) * (↑(F.aeval z) / ↑(F.derivative.aeval z)) : Rat_[p])‖ <= 1 := by
    simpa using mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.aeval z * -z1 = -F.aeval z := by
    calc
      F.derivative.aeval z * -z1 =
          F.derivative.aeval z * -⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩ := by rw [hzeq]
      _ = -(F.derivative.aeval z * ⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩) := mul_neg _ _
      _ = -⟨F.derivative.aeval z * (F.aeval z / (F.derivative.aeval z : Int_[p]) : Rat_[p]), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul])
      _ = -F.aeval z := by simp only [mul_div_cancel₀ _ hdzne', Subtype.coe_eta]
  exact ⟨q, by simpa [sub_eq_add_neg, neg_mul_eq_mul_neg, this, hz'] using hq⟩

中文:
定义 calc_eval_z'
  签名: {z z' z1 : 整数_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
  定义体: by
  have hdzne : F.derivative.aeval z != 0 :=
    mt norm_eq_zero.2 (by rw [hz.1]; apply deriv_norm_ne_zero; assumption)
  have hdzne' : (↑(F.derivative.aeval z) : Rat_[p]) != 0 := fun h => hdzne (Subtype.ext_iff.2 h)
  obtain ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion z (-z1)
  have : ‖(↑(F.derivative.aeval z) * (↑(F.aeval z) / ↑(F.derivative.aeval z)) : Rat_[p])‖ <= 1 := by
    simpa using mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.aeval z * -z1 = -F.aeval z := by
    calc
      F.derivative.aeval z * -z1 =
          F.derivative.aeval z * -⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩ := by rw [hzeq]
      _ = -(F.derivative.aeval z * ⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩) := mul_neg _ _
      _ = -⟨F.derivative.aeval z * (F.aeval z / (F.derivative.aeval z : Int_[p]) : Rat_[p]), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul])
      _ = -F.aeval z := by simp only [mul_div_cancel₀ _ hdzne', Subtype.coe_eta]
  exact ⟨q, by simpa [sub_eq_add_neg, neg_mul_eq_mul_neg, this, hz'] using hq⟩
-/
private def calc_eval_z' {z z' z1 : Int_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
    (h1 : ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1) (hzeq : z1 = ⟨_, h1⟩) :
    { q : Int_[p] // F.aeval z' = q * z1 ^ 2 } := by
  have hdzne : F.derivative.aeval z != 0 :=
    mt norm_eq_zero.2 (by rw [hz.1]; apply deriv_norm_ne_zero; assumption)
  have hdzne' : (↑(F.derivative.aeval z) : Rat_[p]) != 0 := fun h => hdzne (Subtype.ext_iff.2 h)
  obtain ⟨q, hq⟩ := (F.map (algebraMap R Int_[p])).binomExpansion z (-z1)
  have : ‖(↑(F.derivative.aeval z) * (↑(F.aeval z) / ↑(F.derivative.aeval z)) : Rat_[p])‖ <= 1 := by
    simpa using mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.aeval z * -z1 = -F.aeval z := by
    calc
      F.derivative.aeval z * -z1 =
          F.derivative.aeval z * -⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩ := by rw [hzeq]
      _ = -(F.derivative.aeval z * ⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩) := mul_neg _ _
      _ = -⟨F.derivative.aeval z * (F.aeval z / (F.derivative.aeval z : Int_[p]) : Rat_[p]), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul])
      _ = -F.aeval z := by simp only [mul_div_cancel₀ _ hdzne', Subtype.coe_eta]
  exact ⟨q, by simpa [sub_eq_add_neg, neg_mul_eq_mul_neg, this, hz'] using hq⟩

set_option linter.defProp false in
/--
Definition of `calc_eval_z'_norm` / `calc_eval_z'_norm` 的定义

English:
definition calc_eval_z'_norm
  signature: {z z' z1 : Int_[p]} {n} (hz : ih n z) {q}
  body: by
  calc
    ‖F.aeval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ <= 1 * ‖z1‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.aeval z‖ ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ <= (‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.aeval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.aeval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]

中文:
定义 calc_eval_z'_norm
  签名: {z z' z1 : 整数_[p]} {n} (hz : ih n z) {q}
  定义体: by
  calc
    ‖F.aeval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ <= 1 * ‖z1‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.aeval z‖ ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ <= (‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.aeval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.aeval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]
-/
private def calc_eval_z'_norm {z z' z1 : Int_[p]} {n} (hz : ih n z) {q}
    (heq : F.aeval z' = q * z1 ^ 2)
    (h1 : ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1) (hzeq : z1 = ⟨_, h1⟩) :
    ‖F.aeval z'‖ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by
  calc
    ‖F.aeval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ <= 1 * ‖z1‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.aeval z‖ ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ <= (‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.aeval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.aeval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]


/--
Definition of `ih_n` / `ih_n` 的定义

English:
definition ih_n
  signature: {n : Nat} {z : Int_[p]} (hz : ih n z)
  body: have h1 : ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1 := calc_norm_le_one hnorm hz
  let z1 : Int_[p] := ⟨_, h1⟩
  let z' : Int_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
      calc_deriv_dist hnorm rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.aeval z'‖ = ‖F.derivative.aeval a‖ := by
      rw [sub_eq_add_neg]; rw [← hz.1]; rw [← norm_neg (F.derivative.aeval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm rfl hz h1 rfl
    have hnle : ‖F.aeval z'‖ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz heq h1 rfl
    ⟨hfeq, hnle⟩⟩

中文:
定义 ih_n
  签名: {n : 自然数} {z : 整数_[p]} (hz : ih n z)
  定义体: have h1 : ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1 := calc_norm_le_one hnorm hz
  let z1 : Int_[p] := ⟨_, h1⟩
  let z' : Int_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
      calc_deriv_dist hnorm rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.aeval z'‖ = ‖F.derivative.aeval a‖ := by
      rw [sub_eq_add_neg]; rw [← hz.1]; rw [← norm_neg (F.derivative.aeval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm rfl hz h1 rfl
    have hnle : ‖F.aeval z'‖ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz heq h1 rfl
    ⟨hfeq, hnle⟩⟩
-/
private def ih_n {n : Nat} {z : Int_[p]} (hz : ih n z) : { z' : Int_[p] // ih (n + 1) z' } :=
  have h1 : ‖(↑(F.aeval z) : Rat_[p]) / ↑(F.derivative.aeval z)‖ <= 1 := calc_norm_le_one hnorm hz
  let z1 : Int_[p] := ⟨_, h1⟩
  let z' : Int_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
      calc_deriv_dist hnorm rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.aeval z'‖ = ‖F.derivative.aeval a‖ := by
      rw [sub_eq_add_neg]; rw [← hz.1]; rw [← norm_neg (F.derivative.aeval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm rfl hz h1 rfl
    have hnle : ‖F.aeval z'‖ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz heq h1 rfl
    ⟨hfeq, hnle⟩⟩

/--
Definition of `newton_seq_aux` / `newton_seq_aux` 的定义

English:
definition newton_seq_aux
  signature: : forall n : Nat, { z : Int_[p] // ih n z }

中文:
定义 newton_seq_aux
  签名: : 对任意 n : 自然数, { z : 整数_[p] // ih n z }
-/
private def newton_seq_aux : forall n : Nat, { z : Int_[p] // ih n z }
  | 0 => ⟨a, ih_0 hnorm⟩
  | k + 1 => ih_n hnorm (newton_seq_aux k).2

/--
Definition of `newton_seq_gen` / `newton_seq_gen` 的定义

English:
definition newton_seq_gen
  signature: (n : Nat)
  body: (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm

中文:
定义 newton_seq_gen
  签名: (n : 自然数)
  定义体: (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm
-/
private def newton_seq_gen (n : Nat) : Int_[p] :=
  (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm

/--
theorem `newton_seq_deriv_norm` / 定理 `newton_seq_deriv_norm`

English:
theorem newton_seq_deriv_norm
  given: (n : Nat)
  proof: (newton_seq_aux hnorm n).2.1

中文:
定理 newton_seq_deriv_norm
  条件: (n : 自然数)
  证明: (newton_seq_aux hnorm n).2.1
-/
private theorem newton_seq_deriv_norm (n : Nat) :
    ‖F.derivative.aeval (newton_seq n)‖ = ‖F.derivative.aeval a‖ :=
  (newton_seq_aux hnorm n).2.1

/--
theorem `newton_seq_norm_le` / 定理 `newton_seq_norm_le`

English:
theorem newton_seq_norm_le
  given: (n : Nat)
  proof: (newton_seq_aux hnorm n).2.2

中文:
定理 newton_seq_norm_le
  条件: (n : 自然数)
  证明: (newton_seq_aux hnorm n).2.2
-/
private theorem newton_seq_norm_le (n : Nat) :
    ‖F.aeval (newton_seq n)‖ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux hnorm n).2.2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `newton_seq_norm_eq` / 定理 `newton_seq_norm_eq`

English:
theorem newton_seq_norm_eq
  given: (n : Nat)
  proof: by
  rw [newton_seq_gen]; rw [newton_seq_gen]; rw [newton_seq_aux]; rw [ih_n]
  simp [sub_eq_add_neg, add_comm]

中文:
定理 newton_seq_norm_eq
  条件: (n : 自然数)
  证明: by
  rw [newton_seq_gen]; rw [newton_seq_gen]; rw [newton_seq_aux]; rw [ih_n]
  simp [sub_eq_add_neg, add_comm]
-/
private theorem newton_seq_norm_eq (n : Nat) :
    ‖newton_seq (n + 1) - newton_seq n‖ =
    ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ := by
  rw [newton_seq_gen]; rw [newton_seq_gen]; rw [newton_seq_aux]; rw [ih_n]
  simp [sub_eq_add_neg, add_comm]

/--
theorem `newton_seq_succ_dist` / 定理 `newton_seq_succ_dist`

English:
theorem newton_seq_succ_dist
  given: (n : Nat)
  proof: calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ :=
      newton_seq_norm_eq hnorm _
    _ = ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval a‖ := by rw [newton_seq_deriv_norm]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply newton_seq_norm_le
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _

中文:
定理 newton_seq_succ_dist
  条件: (n : 自然数)
  证明: calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ :=
      newton_seq_norm_eq hnorm _
    _ = ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval a‖ := by rw [newton_seq_deriv_norm]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply newton_seq_norm_le
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
-/
private theorem newton_seq_succ_dist (n : Nat) :
    ‖newton_seq (n + 1) - newton_seq n‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
  calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ :=
      newton_seq_norm_eq hnorm _
    _ = ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval a‖ := by rw [newton_seq_deriv_norm]
    _ <= ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply newton_seq_norm_le
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _

/--
theorem `newton_seq_dist_aux` / 定理 `newton_seq_dist_aux`

English:
theorem newton_seq_dist_aux
  given: (n : Nat)
  proof: by
      apply pow_right_mono₀
      · simp
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ <= max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ <= max (‖F.derivative.aeval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.aeval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
max_eq_right
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)

中文:
定理 newton_seq_dist_aux
  条件: (n : 自然数)
  证明: by
      apply pow_right_mono₀
      · simp
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ <= max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ <= max (‖F.derivative.aeval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.aeval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
max_eq_right
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)
-/
private theorem newton_seq_dist_aux (n : Nat) :
    forall k : Nat, ‖newton_seq (n + k) - newton_seq n‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ n
  | 0 => by simp [T_pow_nonneg, mul_nonneg]
  | k + 1 =>
    have : 2 ^ n <= 2 ^ (n + k) := by
      apply pow_right_mono₀
      · simp
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ <= max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ <= max (‖F.derivative.aeval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.aeval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
max_eq_right
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)

/--
theorem `newton_seq_dist` / 定理 `newton_seq_dist`

English:
theorem newton_seq_dist
  given: {n k : Nat} (hnk : n <= k)
  proof: by
  have hex : exists m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux

中文:
定理 newton_seq_dist
  条件: {n k : 自然数} (hnk : n <= k)
  证明: by
  have hex : exists m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux
-/
private theorem newton_seq_dist {n k : Nat} (hnk : n <= k) :
    ‖newton_seq k - newton_seq n‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ n := by
  have hex : exists m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux

/--
theorem `bound'` / 定理 `bound'`

English:
theorem bound'
  statement: Tendsto (fun n : Nat => ‖F.derivative.aeval a‖ * T ^ 2 ^ n) atTop (𝓝 0)
  proof: by
  rw [← mul_zero ‖F.derivative.aeval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (T_lt_one hnorm))
        (tendsto_pow_atTop_atTop_of_one_lt (by simp)))

中文:
定理 bound'
  结论: 收敛 (fun n : 自然数 => ‖F.derivative.aeval a‖ * T ^ 2 ^ n) atTop (𝓝 0)
  证明: by
  rw [← mul_zero ‖F.derivative.aeval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (T_lt_one hnorm))
        (tendsto_pow_atTop_atTop_of_one_lt (by simp)))
-/
private theorem bound' : Tendsto (fun n : Nat => ‖F.derivative.aeval a‖ * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (T_lt_one hnorm))
        (tendsto_pow_atTop_atTop_of_one_lt (by simp)))

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  proof: fun hε =>
eventually_atTop.1 (bound' hnorm).eventually gt_mem_nhds hε

中文:
定理 bound
  证明: fun hε =>
eventually_atTop.1 (bound' hnorm).eventually gt_mem_nhds hε
-/
private theorem bound :
    forall {ε}, ε > 0 -> exists N : Nat, forall {n}, n >= N -> ‖F.derivative.aeval a‖ * T ^ 2 ^ n < ε := fun hε =>
eventually_atTop.1 (bound' hnorm).eventually gt_mem_nhds hε

/--
theorem `bound'_sq` / 定理 `bound'_sq`

English:
theorem bound'_sq
  proof: by
  rw [← mul_zero ‖F.derivative.aeval a‖]; rw [sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption

中文:
定理 bound'_sq
  证明: by
  rw [← mul_zero ‖F.derivative.aeval a‖]; rw [sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption
-/
private theorem bound'_sq :
    Tendsto (fun n : Nat => ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖]; rw [sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption

/--
theorem `newton_seq_is_cauchy` / 定理 `newton_seq_is_cauchy`

English:
theorem newton_seq_is_cauchy
  statement: IsCauSeq norm newton_seq
  proof: fun _ε hε =>
(bound hnorm hε).imp fun _N hN _j hj => (newton_seq_dist hnorm hj).trans_lt hN le_rfl

中文:
定理 newton_seq_is_cauchy
  结论: IsCauSeq norm newton_seq
  证明: fun _ε hε =>
(bound hnorm hε).imp fun _N hN _j hj => (newton_seq_dist hnorm hj).trans_lt hN le_rfl
-/
private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq := fun _ε hε =>
(bound hnorm hε).imp fun _N hN _j hj => (newton_seq_dist hnorm hj).trans_lt hN le_rfl

/--
Definition of `newton_cau_seq` / `newton_cau_seq` 的定义

English:
definition newton_cau_seq
  signature: : CauSeq Int_[p] norm
  body: ⟨_, newton_seq_is_cauchy hnorm⟩

中文:
定义 newton_cau_seq
  签名: : CauSeq 整数_[p] norm
  定义体: ⟨_, newton_seq_is_cauchy hnorm⟩
-/
private def newton_cau_seq : CauSeq Int_[p] norm := ⟨_, newton_seq_is_cauchy hnorm⟩

/--
Definition of `soln_gen` / `soln_gen` 的定义

English:
definition soln_gen
  signature: : Int_[p]
  body: (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm

中文:
定义 soln_gen
  签名: : 整数_[p]
  定义体: (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm
-/
private def soln_gen : Int_[p] := (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm

/--
theorem `soln_spec` / 定理 `soln_spec`

English:
theorem soln_spec
  given: {ε : Real} (hε : ε > 0)
  proof: Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε

中文:
定理 soln_spec
  条件: {ε : 实数} (hε : ε > 0)
  证明: Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε
-/
private theorem soln_spec {ε : Real} (hε : ε > 0) :
    exists N : Nat, forall {i : Nat}, i >= N -> ‖soln - newton_cau_seq hnorm i‖ < ε :=
  Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε

/--
theorem `soln_deriv_norm` / 定理 `soln_deriv_norm`

English:
theorem soln_deriv_norm
  statement: ‖F.derivative.aeval soln‖ = ‖F.derivative.aeval a‖
  proof: norm_deriv_eq (newton_seq_deriv_norm hnorm)

中文:
定理 soln_deriv_norm
  结论: ‖F.derivative.aeval soln‖ = ‖F.derivative.aeval a‖
  证明: norm_deriv_eq (newton_seq_deriv_norm hnorm)
-/
private theorem soln_deriv_norm : ‖F.derivative.aeval soln‖ = ‖F.derivative.aeval a‖ :=
  norm_deriv_eq (newton_seq_deriv_norm hnorm)

/--
theorem `newton_seq_norm_tendsto_zero` / 定理 `newton_seq_norm_tendsto_zero`

English:
theorem newton_seq_norm_tendsto_zero
  proof: squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)

中文:
定理 newton_seq_norm_tendsto_zero
  证明: squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)
-/
private theorem newton_seq_norm_tendsto_zero :
    Tendsto (fun i => ‖F.aeval (newton_cau_seq hnorm i)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)

/--
theorem `newton_seq_dist_tendsto'` / 定理 `newton_seq_dist_tendsto'`

English:
theorem newton_seq_dist_tendsto'
  proof: (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)

中文:
定理 newton_seq_dist_tendsto'
  证明: (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)
-/
private theorem newton_seq_dist_tendsto' :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖) atTop (𝓝 ‖soln - a‖) :=
  (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)

/--
theorem `eval_soln` / 定理 `eval_soln`

English:
theorem eval_soln
  statement: F.aeval soln = 0
  proof: limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)

中文:
定理 eval_soln
  结论: F.aeval soln = 0
  证明: limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)
-/
private theorem eval_soln : F.aeval soln = 0 :=
  limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)

variable (hnsol : F.aeval a != 0)
include hnsol

/--
theorem `T_pos` / 定理 `T_pos`

English:
theorem T_pos
  statement: T > 0
  proof: by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)

中文:
定理 T_pos
  结论: T > 0
  证明: by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)
-/
private theorem T_pos : T > 0 := by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)

/--
theorem `newton_seq_succ_dist_weak` / 定理 `newton_seq_succ_dist_weak`

English:
theorem newton_seq_succ_dist_weak
  given: (n : Nat)
  proof: have : 2 <= 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 <= 2) (Nat.le_add_left _ _ : 1 <= n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ <= ‖F.derivative.aeval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.aeval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by norm_num)) (deriv_norm_pos hnorm))
    _ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ := by
      rw [T_gen]; rw [sq]; rw [pow_one]; rw [norm_div]; rw [← mul_div_assoc]; rw [PadicInt.padic_norm_e_of_padicInt]; rw [PadicInt.coe_mul]; rw [norm_mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero; assumption

中文:
定理 newton_seq_succ_dist_weak
  条件: (n : 自然数)
  证明: have : 2 <= 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 <= 2) (Nat.le_add_left _ _ : 1 <= n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ <= ‖F.derivative.aeval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.aeval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by norm_num)) (deriv_norm_pos hnorm))
    _ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ := by
      rw [T_gen]; rw [sq]; rw [pow_one]; rw [norm_div]; rw [← mul_div_assoc]; rw [PadicInt.padic_norm_e_of_padicInt]; rw [PadicInt.coe_mul]; rw [norm_mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero; assumption
-/
private theorem newton_seq_succ_dist_weak (n : Nat) :
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ < ‖F.aeval a‖ / ‖F.derivative.aeval a‖ :=
  have : 2 <= 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 <= 2) (Nat.le_add_left _ _ : 1 <= n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ <= ‖F.derivative.aeval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ <= ‖F.derivative.aeval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.aeval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by norm_num)) (deriv_norm_pos hnorm))
    _ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ := by
      rw [T_gen]; rw [sq]; rw [pow_one]; rw [norm_div]; rw [← mul_div_assoc]; rw [PadicInt.padic_norm_e_of_padicInt]; rw [PadicInt.coe_mul]; rw [norm_mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero; assumption

set_option backward.isDefEq.respectTransparency false in
/--
theorem `newton_seq_dist_to_a` / 定理 `newton_seq_dist_to_a`

English:
theorem newton_seq_dist_to_a
  proof: by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ != ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = ‖Polynomial.aeval a F‖ / ‖Polynomial.aeval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)

中文:
定理 newton_seq_dist_to_a
  证明: by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ != ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = ‖Polynomial.aeval a F‖ / ‖Polynomial.aeval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)
-/
private theorem newton_seq_dist_to_a :
    forall n : Nat, 0 < n -> ‖newton_seq n - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖
  | 1, _h => by simp [sub_eq_add_neg, add_assoc, newton_seq_gen, newton_seq_aux, ih_n]
  | k + 2, _h =>
    have hlt : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ < ‖newton_seq (k + 1) - a‖ := by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ != ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = ‖Polynomial.aeval a F‖ / ‖Polynomial.aeval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)

/--
theorem `newton_seq_dist_tendsto` / 定理 `newton_seq_dist_tendsto`

English:
theorem newton_seq_dist_tendsto
  proof: tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)

中文:
定理 newton_seq_dist_tendsto
  证明: tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)
-/
private theorem newton_seq_dist_tendsto :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖)
    atTop (𝓝 (‖F.aeval a‖ / ‖F.derivative.aeval a‖)) :=
  tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)

/--
theorem `soln_dist_to_a` / 定理 `soln_dist_to_a`

English:
theorem soln_dist_to_a
  statement: ‖soln - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖
  proof: tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)

中文:
定理 soln_dist_to_a
  结论: ‖soln - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖
  证明: tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)
-/
private theorem soln_dist_to_a : ‖soln - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ :=
  tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)

/--
theorem `soln_dist_to_a_lt_deriv` / 定理 `soln_dist_to_a_lt_deriv`

English:
theorem soln_dist_to_a_lt_deriv
  statement: ‖soln - a‖ < ‖F.derivative.aeval a‖
  proof: by
  rw [soln_dist_to_a]; rw [div_lt_iff₀ (deriv_norm_pos _)]; rw [← sq] <;> assumption

中文:
定理 soln_dist_to_a_lt_deriv
  结论: ‖soln - a‖ < ‖F.derivative.aeval a‖
  证明: by
  rw [soln_dist_to_a]; rw [div_lt_iff₀ (deriv_norm_pos _)]; rw [← sq] <;> assumption
-/
private theorem soln_dist_to_a_lt_deriv : ‖soln - a‖ < ‖F.derivative.aeval a‖ := by
  rw [soln_dist_to_a]; rw [div_lt_iff₀ (deriv_norm_pos _)]; rw [← sq] <;> assumption

/--
theorem `soln_unique` / 定理 `soln_unique`

English:
theorem soln_unique
  statement: (z : Int_[p]) (hev : F.aeval z = 0)
  proof: by
  have hsoln : ‖z - soln‖ < ‖F.derivative.aeval soln‖ := by
    rw [soln_deriv_norm]
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ <= max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.aeval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  exact a_soln_is_unique (eval_soln hnorm) z hev hsoln

中文:
定理 soln_unique
  结论: (z : 整数_[p]) (hev : F.aeval z = 0)
  证明: by
  have hsoln : ‖z - soln‖ < ‖F.derivative.aeval soln‖ := by
    rw [soln_deriv_norm]
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ <= max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.aeval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  exact a_soln_is_unique (eval_soln hnorm) z hev hsoln
-/
private theorem soln_unique (z : Int_[p]) (hev : F.aeval z = 0)
    (hnlt : ‖z - a‖ < ‖F.derivative.aeval a‖) : z = soln := by
  have hsoln : ‖z - soln‖ < ‖F.derivative.aeval soln‖ := by
    rw [soln_deriv_norm]
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ <= max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.aeval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  exact a_soln_is_unique (eval_soln hnorm) z hev hsoln

end Hensel

variable {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R Int_[p]]
  {F : Polynomial R} {a : Int_[p]}

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm

/--
theorem `a_is_soln` / 定理 `a_is_soln`

English:
theorem a_is_soln
  given: (ha : F.aeval a = 0)
  proof: ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩

中文:
定理 a_is_soln
  条件: (ha : F.aeval a = 0)
  证明: ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩
-/
private theorem a_is_soln (ha : F.aeval a = 0) :
    F.aeval a = 0 ∧
      ‖a - a‖ < ‖F.derivative.aeval a‖ ∧
        ‖F.derivative.aeval a‖ = ‖F.derivative.aeval a‖ ∧
          forall z', F.aeval z' = 0 -> ‖z' - a‖ < ‖F.derivative.aeval a‖ -> z' = a :=
  ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩

/--
theorem `hensels_lemma` / 定理 `hensels_lemma`

English:
theorem hensels_lemma
  proof: by
  classical
  exact if ha : F.aeval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩

中文:
定理 hensels_lemma
  证明: by
  classical
  exact if ha : F.aeval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩

Depends on / 依赖: F.aeval, a_is_soln, classical, eval_soln, soln_deriv_norm, soln_dist_to_a_lt_deriv, soln_gen, soln_unique
-/
theorem hensels_lemma :
    exists z : Int_[p],
      F.aeval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.aeval a‖ ∧
          ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧
            forall z', F.aeval z' = 0 -> ‖z' - a‖ < ‖F.derivative.aeval a‖ -> z' = z := by
  classical
  exact if ha : F.aeval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩
