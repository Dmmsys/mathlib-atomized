/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill, Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Formal derivatives of univariate power series

This file defines `PowerSeries.derivative`, the formal derivative of a univariate
power series, as a `Derivation R R⟦X⟧ R⟦X⟧`.

See also `MvPowerSeries.pderiv` for the multivariate setting.

## Main definitions

- `PowerSeries.derivative`: the formal derivative, as a derivation.

## Main results

- `PowerSeries.coeff_derivative`: coefficient formula
  `coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)`.
- `PowerSeries.derivative_coe`: compatibility with `Polynomial.derivative`.
- `PowerSeries.trunc_derivative`: truncation commutes with differentiation.
- `PowerSeries.derivative.ext`: a power series is determined by its constant term and derivative.
- `PowerSeries.derivative_pow`: power rule.
- `PowerSeries.derivative_inv`, `PowerSeries.derivative_inv'`: derivative of an inverse.
- `PowerSeries.derivative_subst`: chain rule for power series substitution.
-/

@[expose] public section

namespace PowerSeries

open Polynomial Derivation Nat

variable {R : Type*}

section CommutativeSemiring

variable [CommSemiring R]

variable (R) in
/--
Definition of `derivative` / `derivative` 的定义

English:
definition derivative
  signature: : Derivation R R⟦X⟧ R⟦X⟧
  body: MvPowerSeries.pderiv R ()

中文:
定义 derivative
  签名: : Derivation R R⟦X⟧ R⟦X⟧
  定义体: MvPowerSeries.pderiv R ()

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv, pderiv
-/
noncomputable def derivative : Derivation R R⟦X⟧ R⟦X⟧ :=
  MvPowerSeries.pderiv R ()

/-- Abbreviation of `PowerSeries.derivative`, the formal derivative on `R⟦X⟧` -/
scoped notation "d⁄dX" => derivative

/--
theorem `derivative_C` / 定理 `derivative_C`

English:
theorem derivative_C
  given: {r : R}
  statement: d⁄dX R (C r) = 0
  proof: MvPowerSeries.pderiv_C

中文:
定理 derivative_C
  条件: {r : R}
  结论: d⁄dX R (C r) = 0
  证明: MvPowerSeries.pderiv_C
-/
@[simp] theorem derivative_C {r : R} : d⁄dX R (C r) = 0 := MvPowerSeries.pderiv_C

/--
theorem `derivative_one` / 定理 `derivative_one`

English:
theorem derivative_one
  statement: d⁄dX R 1 = 0
  proof: MvPowerSeries.pderiv_one

中文:
定理 derivative_one
  结论: d⁄dX R 1 = 0
  证明: MvPowerSeries.pderiv_one

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv_one, pderiv_one
-/
theorem derivative_one : d⁄dX R 1 = 0 := MvPowerSeries.pderiv_one

/--
theorem `coeff_derivative` / 定理 `coeff_derivative`

English:
theorem coeff_derivative
  given: (f : R⟦X⟧) (n : Nat)
  proof: by
  simp [coeff, derivative, MvPowerSeries.coeff_pderiv]

中文:
定理 coeff_derivative
  条件: (f : R⟦X⟧) (n : 自然数)
  证明: by
  simp [coeff, derivative, MvPowerSeries.coeff_pderiv]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_pderiv, coeff_pderiv, derivative
-/
theorem coeff_derivative (f : R⟦X⟧) (n : Nat) :
    coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1) := by
  simp [coeff, derivative, MvPowerSeries.coeff_pderiv]

/--
theorem `coeff_iterate_derivative` / 定理 `coeff_iterate_derivative`

English:
theorem coeff_iterate_derivative
  given: (f : R⟦X⟧) (n k : Nat)
  proof: by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih]; rw [Nat.ascFactorial_succ]; rw [← Nat.succ_ascFactorial]
    grind

中文:
定理 coeff_iterate_derivative
  条件: (f : R⟦X⟧) (n k : 自然数)
  证明: by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih]; rw [Nat.ascFactorial_succ]; rw [← Nat.succ_ascFactorial]
    grind

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.ascFactorial_succ, Nat.succ_ascFactorial, ascFactorial_succ, coeff_derivative, generalizing, iterate_succ_apply, succ_ascFactorial
-/
theorem coeff_iterate_derivative (f : R⟦X⟧) (n k : Nat) :
    coeff k ((d⁄dX R)^[n] f) = (k + 1).ascFactorial n * coeff (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih]; rw [Nat.ascFactorial_succ]; rw [← Nat.succ_ascFactorial]
    grind

/--
theorem `constantCoeff_iterate_derivative` / 定理 `constantCoeff_iterate_derivative`

English:
theorem constantCoeff_iterate_derivative
  given: (f : R⟦X⟧) (n : Nat)
  proof: by
  simpa using coeff_iterate_derivative f n 0

中文:
定理 constantCoeff_iterate_derivative
  条件: (f : R⟦X⟧) (n : 自然数)
  证明: by
  simpa using coeff_iterate_derivative f n 0

Depends on / 依赖: coeff_iterate_derivative
-/
theorem constantCoeff_iterate_derivative (f : R⟦X⟧) (n : Nat) :
    constantCoeff ((d⁄dX R)^[n] f) = n ! * coeff n f := by
  simpa using coeff_iterate_derivative f n 0

/--
theorem `derivative_coe` / 定理 `derivative_coe`

English:
theorem derivative_coe
  given: (f : R[X])
  statement: d⁄dX R f = Polynomial.derivative f
  proof: by
  ext
  rw [coeff_derivative]; rw [coeff_coe]; rw [coeff_coe]; rw [Polynomial.coeff_derivative]

中文:
定理 derivative_coe
  条件: (f : R[X])
  结论: d⁄dX R f = Polynomial.derivative f
  证明: by
  ext
  rw [coeff_derivative]; rw [coeff_coe]; rw [coeff_coe]; rw [Polynomial.coeff_derivative]

Depends on / 依赖: Polynomial, Polynomial.coeff_derivative, coeff_coe, coeff_derivative
-/
theorem derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f := by
  ext
  rw [coeff_derivative]; rw [coeff_coe]; rw [coeff_coe]; rw [Polynomial.coeff_derivative]

/--
theorem `derivative_X` / 定理 `derivative_X`

English:
theorem derivative_X
  statement: d⁄dX R (X : R⟦X⟧) = 1
  proof: MvPowerSeries.pderiv_X_self

中文:
定理 derivative_X
  结论: d⁄dX R (X : R⟦X⟧) = 1
  证明: MvPowerSeries.pderiv_X_self
-/
@[simp] theorem derivative_X : d⁄dX R (X : R⟦X⟧) = 1 :=
  MvPowerSeries.pderiv_X_self

-- We can't use `MvPowerSeries.trunc_pderiv` in the following proof,
-- since `PowerSeries.trunc` is not defined in terms of `MvPowerSeries.trunc`.
/--
theorem `trunc_derivative` / 定理 `trunc_derivative`

English:
theorem trunc_derivative
  given: (f : R⟦X⟧) (n : Nat)
  proof: by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative]; rw [Polynomial.coeff_derivative]; rw [coeff_trunc]; rw [if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [Polynomial.coeff_derivative]; rw [coeff_tru

中文:
定理 trunc_derivative
  条件: (f : R⟦X⟧) (n : 自然数)
  证明: by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative]; rw [Polynomial.coeff_derivative]; rw [coeff_trunc]; rw [if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [Polynomial.coeff_derivative]; rw [coeff_tru

Depends on / 依赖: Polynomial, Polynomial.coeff_derivative, coeff_derivative, coeff_trunc, if_neg, if_pos, split_ifs, succ_lt_succ_iff, zero_mul
-/
theorem trunc_derivative (f : R⟦X⟧) (n : Nat) :
    trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f) := by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative]; rw [Polynomial.coeff_derivative]; rw [coeff_trunc]; rw [if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [Polynomial.coeff_derivative]; rw [coeff_trunc]; rw [if_neg this]; rw [zero_mul]

/--
theorem `trunc_derivative'` / 定理 `trunc_derivative'`

English:
theorem trunc_derivative'
  given: (f : R⟦X⟧) (n : Nat)
  proof: by
  cases n <;> simp [trunc_derivative]

中文:
定理 trunc_derivative'
  条件: (f : R⟦X⟧) (n : 自然数)
  证明: by
  cases n <;> simp [trunc_derivative]

Depends on / 依赖: trunc_derivative
-/
theorem trunc_derivative' (f : R⟦X⟧) (n : Nat) :
    trunc (n - 1) (d⁄dX R f) = Polynomial.derivative (trunc n f) := by
  cases n <;> simp [trunc_derivative]

/--
theorem `derivative_pow` / 定理 `derivative_pow`

English:
theorem derivative_pow
  given: (g : R⟦X⟧) (n : Nat)
  proof: MvPowerSeries.pderiv_pow g n

中文:
定理 derivative_pow
  条件: (g : R⟦X⟧) (n : 自然数)
  证明: MvPowerSeries.pderiv_pow g n

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv_pow, pderiv_pow
-/
theorem derivative_pow (g : R⟦X⟧) (n : Nat) :
    d⁄dX R (g ^ n) = n * g ^ (n - 1) * d⁄dX R g :=
  MvPowerSeries.pderiv_pow g n

end CommutativeSemiring

/--
theorem `derivative.ext` / 定理 `derivative.ext`

English:
theorem derivative.ext
  statement: [CommRing R] [IsAddTorsionFree R] {f g} (hD : d⁄dX R f = d⁄dX R g)
  proof: MvPowerSeries.pderiv.ext (fun _ => hD) hc

@[simp]

中文:
定理 derivative.ext
  结论: [CommRing R] [IsAddTorsionFree R] {f g} (hD : d⁄dX R f = d⁄dX R g)
  证明: MvPowerSeries.pderiv.ext (fun _ => hD) hc

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv.ext, pderiv
-/
theorem derivative.ext [CommRing R] [IsAddTorsionFree R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff f = constantCoeff g) : f = g :=
  MvPowerSeries.pderiv.ext (fun _ => hD) hc

@[simp]
/--
theorem `derivative_inv` / 定理 `derivative_inv`

English:
theorem derivative_inv
  given: [CommRing R] (f : R⟦X⟧ˣ)
  proof: MvPowerSeries.pderiv_inv f

@[simp]

中文:
定理 derivative_inv
  条件: [CommRing R] (f : R⟦X⟧ˣ)
  证明: MvPowerSeries.pderiv_inv f

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv_inv, pderiv_inv
-/
theorem derivative_inv [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑f⁻¹ = -(↑f⁻¹ : R⟦X⟧) ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv f

@[simp]
/--
theorem `derivative_invOf` / 定理 `derivative_invOf`

English:
theorem derivative_invOf
  given: [CommRing R] (f : R⟦X⟧) [Invertible f]
  proof: MvPowerSeries.pderiv_invOf f

中文:
定理 derivative_invOf
  条件: [CommRing R] (f : R⟦X⟧) [Invertible f]
  证明: MvPowerSeries.pderiv_invOf f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.pderiv_invOf, pderiv_invOf
-/
theorem derivative_invOf [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R ⅟f = -⅟f ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_invOf f


/--
theorem `derivative_inv'` / 定理 `derivative_inv'`

English:
theorem derivative_inv'
  given: [Field R] (f : R⟦X⟧)
  statement: d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f
  proof: MvPowerSeries.pderiv_inv' f

中文:
定理 derivative_inv'
  条件: [Field R] (f : R⟦X⟧)
  结论: d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f
  证明: MvPowerSeries.pderiv_inv' f
-/
@[simp] theorem derivative_inv' [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv' f

/--
theorem `derivative_subst_coe` / 定理 `derivative_subst_coe`

English:
theorem derivative_subst_coe
  given: [CommRing R] (p : Polynomial R) {g : R⟦X⟧} (hg : HasSubst g)
  proof: by
  simp [subst_coe hg, derivative_coe, Derivation.comp_aeval_eq (a := g) (derivative R) p,
    smul_eq_mul]

中文:
定理 derivative_subst_coe
  条件: [CommRing R] (p : Polynomial R) {g : R⟦X⟧} (hg : HasSubst g)
  证明: by
  simp [subst_coe hg, derivative_coe, Derivation.comp_aeval_eq (a := g) (derivative R) p,
    smul_eq_mul]
-/
private theorem derivative_subst_coe [CommRing R] (p : Polynomial R) {g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R ((p : R⟦X⟧).subst g) = (d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g := by
  simp [subst_coe hg, derivative_coe, Derivation.comp_aeval_eq (a := g) (derivative R) p,
    smul_eq_mul]

/--
theorem `derivative_subst` / 定理 `derivative_subst`

English:
theorem derivative_subst
  given: [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g)
  proof: by
  ext n
  obtain ⟨m, hm⟩ := (hg.eventually_coeff_pow_eq_zero (n + 1)).exists_forall_of_atTop
  have : coeff (n + 1) (f.subst g) = coeff (n + 1) ((↑(trunc (m + 1) f) : R⟦X⟧).subst g) := by
    rw [coeff_subst' hg]; rw [coeff_subst' hg]
    refine finsum_congr fun d => ?_
    obtain hd | hd := lt_o

中文:
定理 derivative_subst
  条件: [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g)
  证明: by
  ext n
  obtain ⟨m, hm⟩ := (hg.eventually_coeff_pow_eq_zero (n + 1)).exists_forall_of_atTop
  have : coeff (n + 1) (f.subst g) = coeff (n + 1) ((↑(trunc (m + 1) f) : R⟦X⟧).subst g) := by
    rw [coeff_subst' hg]; rw [coeff_subst' hg]
    refine finsum_congr fun d => ?_
    obtain hd | hd := lt_o

Depends on / 依赖: Finset, Finset.sum_co, coeff_coe_trunc_of_lt, coeff_derivative, coeff_mul, coeff_subst, coeff_trunc, derivative_subst_coe, eventually_coeff_pow_eq_zero, exists_forall_of_atTop, f.subst, finsum_congr, hg.eventually_coeff_pow_eq_zero, lt_or_ge, sum_co
-/
theorem derivative_subst [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R (f.subst g) = (d⁄dX R f).subst g * d⁄dX R g := by
  ext n
  obtain ⟨m, hm⟩ := (hg.eventually_coeff_pow_eq_zero (n + 1)).exists_forall_of_atTop
  have : coeff (n + 1) (f.subst g) = coeff (n + 1) ((↑(trunc (m + 1) f) : R⟦X⟧).subst g) := by
    rw [coeff_subst' hg]; rw [coeff_subst' hg]
    refine finsum_congr fun d => ?_
    obtain hd | hd := lt_or_ge d m
    · rw [coeff_coe_trunc_of_lt (by lia)]
    · simp [coeff_trunc, hd, hm]
  rw [coeff_derivative]; rw [this]; rw [← coeff_derivative]; rw [derivative_subst_coe _ hg]; rw [coeff_mul]; rw [coeff_mul]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
  congr 1
  simp only [coeff_subst' hg, coeff_derivative, coeff_coe, coeff_trunc]
  exact finsum_congr fun d => by split_ifs <;> simp (disch := grind [Finset.mem_antidiagonal]) [hm]

section deprecated

variable [CommSemiring R]

/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `derivative` on `R⟦X⟧`.
-/
@[deprecated derivative (since := "2026-06-26")]
/--
Definition of `derivativeFun` / `derivativeFun` 的定义

English:
definition derivativeFun
  signature: (f : R⟦X⟧)
  body: (derivative R).toFun f

中文:
定义 derivativeFun
  签名: (f : R⟦X⟧)
  定义体: (derivative R).toFun f

Depends on / 依赖: derivative
-/
noncomputable def derivativeFun (f : R⟦X⟧) := (derivative R).toFun f

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_add" (since := "2026-06-26")]
/--
theorem `derivativeFun_add` / 定理 `derivativeFun_add`

English:
theorem derivativeFun_add
  given: (f g : R⟦X⟧)
  proof: (derivative R).map_add f g

中文:
定理 derivativeFun_add
  条件: (f g : R⟦X⟧)
  证明: (derivative R).map_add f g

Depends on / 依赖: derivative, map_add
-/
theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g :=
  (derivative R).map_add f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.leibniz" (since := "2026-06-26")]
/--
theorem `derivativeFun_mul` / 定理 `derivativeFun_mul`

English:
theorem derivativeFun_mul
  given: (f g : R⟦X⟧)
  proof: (derivative R).leibniz f g

中文:
定理 derivativeFun_mul
  条件: (f g : R⟦X⟧)
  证明: (derivative R).leibniz f g

Depends on / 依赖: derivative, leibniz
-/
theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun :=
  (derivative R).leibniz f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_one_eq_zero" (since := "2026-06-26")]
/--
theorem `derivativeFun_one` / 定理 `derivativeFun_one`

English:
theorem derivativeFun_one
  statement: derivativeFun (1 : R⟦X⟧) = 0
  proof: (derivative R).map_one_eq_zero

中文:
定理 derivativeFun_one
  结论: derivativeFun (1 : R⟦X⟧) = 0
  证明: (derivative R).map_one_eq_zero

Depends on / 依赖: derivative, map_one_eq_zero
-/
theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 :=
  (derivative R).map_one_eq_zero

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_smul" (since := "2026-06-26")]
/--
theorem `derivativeFun_smul` / 定理 `derivativeFun_smul`

English:
theorem derivativeFun_smul
  given: (r : R) (f : R⟦X⟧)
  statement: derivativeFun (r • f) = r • derivativeFun f
  proof: (derivative R).map_smul r f

@[deprecated (since := "2026-06-26")] alias derivativeFun_C := derivative_C

@[deprecated (since := "2026-06-26")] alias coeff_derivativeFun := coeff_derivative

@[deprecated (since := "2026-06-26")] alias derivativeFun_coe := derivative_coe

@[deprecated (since := "2026

中文:
定理 derivativeFun_smul
  条件: (r : R) (f : R⟦X⟧)
  结论: derivativeFun (r • f) = r • derivativeFun f
  证明: (derivative R).map_smul r f

@[deprecated (since := "2026-06-26")] alias derivativeFun_C := derivative_C

@[deprecated (since := "2026-06-26")] alias coeff_derivativeFun := coeff_derivative

@[deprecated (since := "2026-06-26")] alias derivativeFun_coe := derivative_coe

@[deprecated (since := "2026

Depends on / 依赖: derivative, map_smul
-/
theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f :=
  (derivative R).map_smul r f

@[deprecated (since := "2026-06-26")] alias derivativeFun_C := derivative_C

@[deprecated (since := "2026-06-26")] alias coeff_derivativeFun := coeff_derivative

@[deprecated (since := "2026-06-26")] alias derivativeFun_coe := derivative_coe

@[deprecated (since := "2026-06-26")] alias trunc_derivativeFun := trunc_derivative

end deprecated

end PowerSeries
