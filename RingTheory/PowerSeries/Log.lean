/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Logarithmic Power Series

This file defines the logarithmic power series `log A = ∑ (-1)^(n+1)/n · Xⁿ`
over ℚ-algebras and establishes its key properties.

## Main definitions

* `PowerSeries.log`: The power series `log(1+X) = X - X²/2 + X³/3 - ⋯`.

## Main results

* `PowerSeries.coeff_log`: The coefficient of `log A` at `n` is `(-1)^(n+1)/n` for `n ≥ 1`,
  and `0` for `n = 0`.
* `PowerSeries.constantCoeff_log`: The constant term of `log A` is `0`.
* `PowerSeries.map_log`: `log` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.coeff_one_log`: The coefficient of `log A` at `1` is `1`.
* `PowerSeries.order_log`: The order of `log A` is `1`.
* `PowerSeries.deriv_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
-/

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra Rat A]

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: : PowerSeries A
  body: mk fun n => if n = 0 then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)

中文:
定义 log
  签名: : 幂级数 A
  定义体: mk fun n => if n = 0 then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)

Depends on / 依赖: algebraMap
-/
def log : PowerSeries A :=
  mk fun n => if n = 0 then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)

variable {A}

@[simp]
/--
theorem `coeff_log` / 定理 `coeff_log`

English:
theorem coeff_log
  given: (n : Nat)
  proof: coeff_mk _ _

@[simp]

中文:
定理 coeff_log
  条件: (n : 自然数)
  证明: coeff_mk _ _

@[simp]

Depends on / 依赖: coeff_mk
-/
theorem coeff_log (n : Nat) :
    coeff n (log A) = if n = 0 then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n) :=
  coeff_mk _ _

@[simp]
/--
theorem `constantCoeff_log` / 定理 `constantCoeff_log`

English:
theorem constantCoeff_log
  statement: constantCoeff (log A) = 0
  proof: by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]

中文:
定理 constantCoeff_log
  结论: constantCoeff (log A) = 0
  证明: by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]

Depends on / 依赖: coeff_zero_eq_constantCoeff_apply
-/
theorem constantCoeff_log : constantCoeff (log A) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
/--
theorem `map_log` / 定理 `map_log`

English:
theorem map_log
  given: {A' : Type*} [CommRing A'] [Algebra Rat A'] (f : A ->+* A')
  proof: by
  ext n; simp only [coeff_map, coeff_log]; split_ifs <;> simp [RingHom.map_rat_algebraMap]

中文:
定理 map_log
  条件: {A' : 类型} [交换环 A'] [代数 有理数 A'] (f : A ->+* A')
  证明: by
  ext n; simp only [coeff_map, coeff_log]; split_ifs <;> simp [RingHom.map_rat_algebraMap]

Depends on / 依赖: RingHom, RingHom.map_rat_algebraMap, coeff_log, coeff_map, map_rat_algebraMap, split_ifs
-/
theorem map_log {A' : Type*} [CommRing A'] [Algebra Rat A'] (f : A ->+* A') :
    map f (log A) = log A' := by
  ext n; simp only [coeff_map, coeff_log]; split_ifs <;> simp [RingHom.map_rat_algebraMap]

/--
theorem `coeff_one_log` / 定理 `coeff_one_log`

English:
theorem coeff_one_log
  statement: coeff 1 (log A) = 1
  proof: by simp

中文:
定理 coeff_one_log
  结论: coeff 1 (log A) = 1
  证明: by simp
-/
theorem coeff_one_log : coeff 1 (log A) = 1 := by simp

/--
theorem `order_log` / 定理 `order_log`

English:
theorem order_log
  given: [Nontrivial A]
  statement: (log A).order = 1
  proof: order_eq_nat.mpr ⟨by simp, fun i hi => by simp [Nat.lt_one_iff.mp hi]⟩

中文:
定理 order_log
  条件: [非平凡 A]
  结论: (log A).order = 1
  证明: order_eq_nat.mpr ⟨by simp, fun i hi => by simp [Nat.lt_one_iff.mp hi]⟩

Depends on / 依赖: Nat.lt_one_iff.mp, lt_one_iff, order_eq_nat, order_eq_nat.mpr
-/
theorem order_log [Nontrivial A] : (log A).order = 1 :=
  order_eq_nat.mpr ⟨by simp, fun i hi => by simp [Nat.lt_one_iff.mp hi]⟩

/--
theorem `deriv_log` / 定理 `deriv_log`

English:
theorem deriv_log
  statement: d⁄dX A (log A) = mk fun n => algebraMap Rat A ((-1 : Rat) ^ n)
  proof: by
  ext n
  have : (n + 1) = algebraMap Rat A (n + 1) := by simp
  rw [coeff_derivative]; rw [coeff_log]; rw [coeff_mk]
  grind

中文:
定理 deriv_log
  结论: d⁄dX A (log A) = mk fun n => algebraMap 有理数 A ((-1 : 有理数) ^ n)
  证明: by
  ext n
  have : (n + 1) = algebraMap Rat A (n + 1) := by simp
  rw [coeff_derivative]; rw [coeff_log]; rw [coeff_mk]
  grind

Depends on / 依赖: algebraMap, coeff_derivative, coeff_log, coeff_mk
-/
theorem deriv_log : d⁄dX A (log A) = mk fun n => algebraMap Rat A ((-1 : Rat) ^ n) := by
  ext n
  have : (n + 1) = algebraMap Rat A (n + 1) := by simp
  rw [coeff_derivative]; rw [coeff_log]; rw [coeff_mk]
  grind


/--
theorem `HasSubst.log` / 定理 `HasSubst.log`

English:
theorem HasSubst.log
  statement: HasSubst (log A)
  proof: HasSubst.of_constantCoeff_zero' constantCoeff_log

中文:
定理 有Subst.log
  结论: 有Subst (log A)
  证明: HasSubst.of_constantCoeff_zero' constantCoeff_log

Depends on / 依赖: HasSubst, HasSubst.of_constantCoeff_zero, constantCoeff_log, of_constantCoeff_zero
-/
theorem HasSubst.log : HasSubst (log A) :=
  HasSubst.of_constantCoeff_zero' constantCoeff_log

/--
theorem `HasSubst.exp_sub_one` / 定理 `HasSubst.exp_sub_one`

English:
theorem HasSubst.exp_sub_one
  statement: HasSubst (exp A - 1)
  proof: HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

中文:
定理 有Subst.exp_sub_one
  结论: 有Subst (exp A - 1)
  证明: HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

Depends on / 依赖: HasSubst, HasSubst.of_constantCoeff_zero, constantCoeff_exp, of_constantCoeff_zero
-/
theorem HasSubst.exp_sub_one : HasSubst (exp A - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

/--
Definition of `logOf` / `logOf` 的定义

English:
definition logOf
  signature: (f : A⟦X⟧)
  body: (log A).subst (f - 1)

中文:
定义 logOf
  签名: (f : A⟦X⟧)
  定义体: (log A).subst (f - 1)
-/
noncomputable def logOf (f : A⟦X⟧) : A⟦X⟧ :=
  (log A).subst (f - 1)

/--
theorem `logOf_eq` / 定理 `logOf_eq`

English:
theorem logOf_eq
  given: (f : A⟦X⟧)
  statement: logOf f = (log A).subst (f - 1)
  proof: rfl

中文:
定理 logOf_eq
  条件: (f : A⟦X⟧)
  结论: logOf f = (log A).subst (f - 1)
  证明: rfl
-/
theorem logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f - 1) := rfl

/--
theorem `constantCoeff_logOf` / 定理 `constantCoeff_logOf`

English:
theorem constantCoeff_logOf
  given: {f : A⟦X⟧} (hf : constantCoeff f = 1)
  proof: by
  rw [logOf_eq]
  have h : MvPowerSeries.constantCoeff (f - 1 : A⟦X⟧) = 0 := by
    rw [map_sub]; rw [map_one]; rw [← constantCoeff_eq]; rw [hf]; rw [sub_self]
  exact constantCoeff_subst_eq_zero h _ constantCoeff_log

中文:
定理 constantCoeff_logOf
  条件: {f : A⟦X⟧} (hf : constantCoeff f = 1)
  证明: by
  rw [logOf_eq]
  have h : MvPowerSeries.constantCoeff (f - 1 : A⟦X⟧) = 0 := by
    rw [map_sub]; rw [map_one]; rw [← constantCoeff_eq]; rw [hf]; rw [sub_self]
  exact constantCoeff_subst_eq_zero h _ constantCoeff_log

Depends on / 依赖: MvPowerSeries, MvPowerSeries.constantCoeff, X.is_compact, constantCoeff, constantCoeff_eq, constantCoeff_log, constantCoeff_subst_eq_zero, is_compact, logOf_eq, map_one, map_sub, sub_self
-/
theorem constantCoeff_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (logOf f) = 0 := by
  rw [logOf_eq]
  have h : MvPowerSeries.constantCoeff (f - 1 : A⟦X⟧) = 0 := by
    rw [map_sub]; rw [map_one]; rw [← constantCoeff_eq]; rw [hf]; rw [sub_self]
  exact constantCoeff_subst_eq_zero h _ constantCoeff_log

variable (A) in
@[simp]
/--
theorem `logOf_one_add_X` / 定理 `logOf_one_add_X`

English:
theorem logOf_one_add_X
  statement: logOf (1 + X : A⟦X⟧) = log A
  proof: by
  rw [logOf_eq]; rw [add_sub_cancel_left]; rw [X_subst]

中文:
定理 logOf_one_add_X
  结论: logOf (1 + X : A⟦X⟧) = log A
  证明: by
  rw [logOf_eq]; rw [add_sub_cancel_left]; rw [X_subst]

Depends on / 依赖: X.is_hausdorff, X_subst, add_sub_cancel_left, is_hausdorff, logOf_eq
-/
theorem logOf_one_add_X : logOf (1 + X : A⟦X⟧) = log A := by
  rw [logOf_eq]; rw [add_sub_cancel_left]; rw [X_subst]

end PowerSeries

end
