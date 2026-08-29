/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Binomial coefficients and factorial variants

This file proves asymptotic theorems for binomial coefficients and factorial variants.

## Main statements

* `isEquivalent_descFactorial` is the proof that `n.descFactorial k ~ n^k` as `n → ∞`.
* `isEquivalent_choose` is the proof that `n.choose k ~ n^k / k!` as `n → ∞`.
* `isTheta_choose` is the proof that `n.choose k = Θ(n^k)` as `n → ∞`.
-/

public section


open Asymptotics Filter Nat Topology

/--
lemma `isEquivalent_descFactorial` / 引理 `isEquivalent_descFactorial`

English:
lemma isEquivalent_descFactorial
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [descFactorial_succ, cast_mul, _root_.pow_succ']
    refine IsEquivalent.mul ?_ h
    have hz : forallᶠ (x : Nat) in atTop, (x : Real) != 0 :=
      eventually_atTop.mpr ⟨1, fun n hn => ne_of_gt (mod_cast hn)⟩
    rw [isEquivalent_iff_tendsto_one hz]; rw [← tendsto_add_atTop_iff_nat k]
    simpa using tendsto_natCast_div_add_atTop (k : Real)

中文:
引理 isEquivalent_descFactorial
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [descFactorial_succ, cast_mul, _root_.pow_succ']
    refine IsEquivalent.mul ?_ h
    have hz : forallᶠ (x : Nat) in atTop, (x : Real) != 0 :=
      eventually_atTop.mpr ⟨1, fun n hn => ne_of_gt (mod_cast hn)⟩
    rw [isEquivalent_iff_tendsto_one hz]; rw [← tendsto_add_atTop_iff_nat k]
    simpa using tendsto_natCast_div_add_atTop (k : Real)

Depends on / 依赖: IsEquivalent, IsEquivalent.mul, IsEquivalent.refl, _root_, _root_.pow_succ, cast_mul, descFactorial_succ, eventually_atTop, eventually_atTop.mpr, isEquivalent_iff_tendsto_one, mod_cast, ne_of_gt, pow_succ, simp_rw, tendsto_add_atTop_iff_nat, tendsto_natCast_div_add_atTop
-/
lemma isEquivalent_descFactorial (k : Nat) :
    (fun (n : Nat) => (n.descFactorial k : Real)) ~[atTop] (fun (n : Nat) => (n ^ k : Real)) := by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [descFactorial_succ, cast_mul, _root_.pow_succ']
    refine IsEquivalent.mul ?_ h
    have hz : forallᶠ (x : Nat) in atTop, (x : Real) != 0 :=
      eventually_atTop.mpr ⟨1, fun n hn => ne_of_gt (mod_cast hn)⟩
    rw [isEquivalent_iff_tendsto_one hz]; rw [← tendsto_add_atTop_iff_nat k]
    simpa using tendsto_natCast_div_add_atTop (k : Real)

/--
theorem `isEquivalent_choose` / 定理 `isEquivalent_choose`

English:
theorem isEquivalent_choose
  given: (k : Nat)
  proof: by
  conv_lhs =>
    intro n
    rw [choose_eq_descFactorial_div_factorial]; rw [cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

中文:
定理 isEquivalent_choose
  条件: (k : 自然数)
  证明: by
  conv_lhs =>
    intro n
    rw [choose_eq_descFactorial_div_factorial]; rw [cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

Depends on / 依赖: IsEquivalent, IsEquivalent.refl, cast_div, choose_eq_descFactorial_div_factorial, conv_lhs, factorial_dvd_descFactorial, factorial_ne_zero, isEquivalent_descFactorial, k.factorial_ne_zero, mod_cast, n.factorial_dvd_descFactorial
-/
theorem isEquivalent_choose (k : Nat) :
    (fun (n : Nat) => (n.choose k : Real)) ~[atTop] (fun (n : Nat) => (n ^ k / k.factorial : Real)) := by
  conv_lhs =>
    intro n
    rw [choose_eq_descFactorial_div_factorial]; rw [cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

/--
theorem `isTheta_choose` / 定理 `isTheta_choose`

English:
theorem isTheta_choose
  given: (k : Nat)
  proof: by
  apply (isEquivalent_choose k).trans_isTheta
  simp_rw [div_eq_mul_inv, mul_comm _ (_⁻¹)]
exact isTheta_rfl.const_mul_left inv_ne_zero (mod_cast k.factorial_ne_zero)

中文:
定理 isTheta_choose
  条件: (k : 自然数)
  证明: by
  apply (isEquivalent_choose k).trans_isTheta
  simp_rw [div_eq_mul_inv, mul_comm _ (_⁻¹)]
exact isTheta_rfl.const_mul_left inv_ne_zero (mod_cast k.factorial_ne_zero)

Depends on / 依赖: const_mul_left, div_eq_mul_inv, factorial_ne_zero, inv_ne_zero, isEquivalent_choose, isTheta_rfl, isTheta_rfl.const_mul_left, k.factorial_ne_zero, mod_cast, mul_comm, simp_rw, trans_isTheta
-/
theorem isTheta_choose (k : Nat) :
    (fun (n : Nat) => (n.choose k : Real)) =Θ[atTop] (fun (n : Nat) => (n ^ k : Real)) := by
  apply (isEquivalent_choose k).trans_isTheta
  simp_rw [div_eq_mul_inv, mul_comm _ (_⁻¹)]
exact isTheta_rfl.const_mul_left inv_ne_zero (mod_cast k.factorial_ne_zero)
