/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu, Kamila Szewczyk
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.Prime

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/

@[expose] public section


noncomputable section

open Polynomial

namespace Real

/--
Definition of `goldenRatio` / `goldenRatio` 的定义

English:
abbreviation goldenRatio
  signature: : Real
  body: (1 + √5) / 2

中文:
缩写 goldenRatio
  签名: : 实数
  定义体: (1 + √5) / 2
-/
abbrev goldenRatio : Real := (1 + √5) / 2

/--
Definition of `goldenConj` / `goldenConj` 的定义

English:
abbreviation goldenConj
  signature: : Real
  body: (1 - √5) / 2

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio
@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

中文:
缩写 goldenConj
  签名: : 实数
  定义体: (1 - √5) / 2

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio
@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj
-/
abbrev goldenConj : Real := (1 - √5) / 2

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio
@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

open goldenRatio

/--
theorem `inv_goldenRatio` / 定理 `inv_goldenRatio`

English:
theorem inv_goldenRatio
  statement: φ⁻¹ = -ψ
  proof: by
  grind

中文:
定理 inv_goldenRatio
  结论: φ⁻¹ = -ψ
  证明: by
  grind
-/
theorem inv_goldenRatio : φ⁻¹ = -ψ := by
  grind

/--
theorem `inv_goldenConj` / 定理 `inv_goldenConj`

English:
theorem inv_goldenConj
  statement: ψ⁻¹ = -φ
  proof: by
  rw [inv_eq_iff_eq_inv]; rw [← neg_inv]; rw [← neg_eq_iff_eq_neg]
  exact inv_goldenRatio.symm

@[simp]

中文:
定理 inv_goldenConj
  结论: ψ⁻¹ = -φ
  证明: by
  rw [inv_eq_iff_eq_inv]; rw [← neg_inv]; rw [← neg_eq_iff_eq_neg]
  exact inv_goldenRatio.symm

@[simp]

Depends on / 依赖: inv_eq_iff_eq_inv, inv_goldenRatio, inv_goldenRatio.symm, neg_eq_iff_eq_neg, neg_inv
-/
theorem inv_goldenConj : ψ⁻¹ = -φ := by
  rw [inv_eq_iff_eq_inv]; rw [← neg_inv]; rw [← neg_eq_iff_eq_neg]
  exact inv_goldenRatio.symm

@[simp]
/--
theorem `goldenRatio_mul_goldenConj` / 定理 `goldenRatio_mul_goldenConj`

English:
theorem goldenRatio_mul_goldenConj
  statement: φ * ψ = -1
  proof: by
  grind

@[simp]

中文:
定理 goldenRatio_mul_goldenConj
  结论: φ * ψ = -1
  证明: by
  grind

@[simp]
-/
theorem goldenRatio_mul_goldenConj : φ * ψ = -1 := by
  grind

@[simp]
/--
theorem `goldenConj_mul_goldenRatio` / 定理 `goldenConj_mul_goldenRatio`

English:
theorem goldenConj_mul_goldenRatio
  statement: ψ * φ = -1
  proof: by
  rw [mul_comm]
  exact goldenRatio_mul_goldenConj

@[simp]

中文:
定理 goldenConj_mul_goldenRatio
  结论: ψ * φ = -1
  证明: by
  rw [mul_comm]
  exact goldenRatio_mul_goldenConj

@[simp]

Depends on / 依赖: goldenRatio_mul_goldenConj, mul_comm
-/
theorem goldenConj_mul_goldenRatio : ψ * φ = -1 := by
  rw [mul_comm]
  exact goldenRatio_mul_goldenConj

@[simp]
/--
theorem `goldenRatio_add_goldenConj` / 定理 `goldenRatio_add_goldenConj`

English:
theorem goldenRatio_add_goldenConj
  statement: φ + ψ = 1
  proof: by
  rw [goldenRatio]; rw [goldenConj]
  ring

中文:
定理 goldenRatio_add_goldenConj
  结论: φ + ψ = 1
  证明: by
  rw [goldenRatio]; rw [goldenConj]
  ring

Depends on / 依赖: goldenConj, goldenRatio
-/
theorem goldenRatio_add_goldenConj : φ + ψ = 1 := by
  rw [goldenRatio]; rw [goldenConj]
  ring

/--
theorem `one_sub_goldenConj` / 定理 `one_sub_goldenConj`

English:
theorem one_sub_goldenConj
  statement: 1 - φ = ψ
  proof: by
  linarith [goldenRatio_add_goldenConj]

中文:
定理 one_sub_goldenConj
  结论: 1 - φ = ψ
  证明: by
  linarith [goldenRatio_add_goldenConj]

Depends on / 依赖: goldenRatio_add_goldenConj
-/
theorem one_sub_goldenConj : 1 - φ = ψ := by
  linarith [goldenRatio_add_goldenConj]

/--
theorem `one_sub_goldenRatio` / 定理 `one_sub_goldenRatio`

English:
theorem one_sub_goldenRatio
  statement: 1 - ψ = φ
  proof: by
  linarith [goldenRatio_add_goldenConj]

@[simp]

中文:
定理 one_sub_goldenRatio
  结论: 1 - ψ = φ
  证明: by
  linarith [goldenRatio_add_goldenConj]

@[simp]

Depends on / 依赖: goldenRatio_add_goldenConj
-/
theorem one_sub_goldenRatio : 1 - ψ = φ := by
  linarith [goldenRatio_add_goldenConj]

@[simp]
/--
theorem `goldenRatio_sub_goldenConj` / 定理 `goldenRatio_sub_goldenConj`

English:
theorem goldenRatio_sub_goldenConj
  statement: φ - ψ = √5
  proof: by ring

中文:
定理 goldenRatio_sub_goldenConj
  结论: φ - ψ = √5
  证明: by ring
-/
theorem goldenRatio_sub_goldenConj : φ - ψ = √5 := by ring

/--
theorem `goldenRatio_pow_sub_goldenRatio_pow` / 定理 `goldenRatio_pow_sub_goldenRatio_pow`

English:
theorem goldenRatio_pow_sub_goldenRatio_pow
  given: (n : Nat)
  statement: φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n
  proof: by
  grind

@[simp 1200]

中文:
定理 goldenRatio_pow_sub_goldenRatio_pow
  条件: (n : 自然数)
  结论: φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n
  证明: by
  grind

@[simp 1200]
-/
theorem goldenRatio_pow_sub_goldenRatio_pow (n : Nat) : φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n := by
  grind

@[simp 1200]
/--
theorem `goldenRatio_sq` / 定理 `goldenRatio_sq`

English:
theorem goldenRatio_sq
  statement: φ ^ 2 = φ + 1
  proof: by
  grind

@[simp 1200]

中文:
定理 goldenRatio_sq
  结论: φ ^ 2 = φ + 1
  证明: by
  grind

@[simp 1200]
-/
theorem goldenRatio_sq : φ ^ 2 = φ + 1 := by
  grind

@[simp 1200]
/--
theorem `goldenConj_sq` / 定理 `goldenConj_sq`

English:
theorem goldenConj_sq
  statement: ψ ^ 2 = ψ + 1
  proof: by
  grind

中文:
定理 goldenConj_sq
  结论: ψ ^ 2 = ψ + 1
  证明: by
  grind
-/
theorem goldenConj_sq : ψ ^ 2 = ψ + 1 := by
  grind

/--
theorem `goldenRatio_pos` / 定理 `goldenRatio_pos`

English:
theorem goldenRatio_pos
  statement: 0 < φ
  proof: mul_pos (by apply add_pos <;> norm_num) inv_pos.2 zero_lt_two

中文:
定理 goldenRatio_pos
  结论: 0 < φ
  证明: mul_pos (by apply add_pos <;> norm_num) inv_pos.2 zero_lt_two

Depends on / 依赖: add_pos, inv_pos, mul_pos, zero_lt_two
-/
theorem goldenRatio_pos : 0 < φ :=
mul_pos (by apply add_pos <;> norm_num) inv_pos.2 zero_lt_two

/--
theorem `goldenRatio_ne_zero` / 定理 `goldenRatio_ne_zero`

English:
theorem goldenRatio_ne_zero
  statement: φ != 0
  proof: ne_of_gt goldenRatio_pos

中文:
定理 goldenRatio_ne_zero
  结论: φ != 0
  证明: ne_of_gt goldenRatio_pos

Depends on / 依赖: goldenRatio_pos, ne_of_gt
-/
theorem goldenRatio_ne_zero : φ != 0 :=
  ne_of_gt goldenRatio_pos

/--
theorem `one_lt_goldenRatio` / 定理 `one_lt_goldenRatio`

English:
theorem one_lt_goldenRatio
  statement: 1 < φ
  proof: by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt goldenRatio_pos)
  simp [← sq, zero_lt_one]

中文:
定理 one_lt_goldenRatio
  结论: 1 < φ
  证明: by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt goldenRatio_pos)
  simp [← sq, zero_lt_one]

Depends on / 依赖: goldenRatio_pos, le_of_lt, lt_of_mul_lt_mul_left, zero_lt_one
-/
theorem one_lt_goldenRatio : 1 < φ := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt goldenRatio_pos)
  simp [← sq, zero_lt_one]

/--
theorem `goldenRatio_lt_two` / 定理 `goldenRatio_lt_two`

English:
theorem goldenRatio_lt_two
  statement: φ < 2
  proof: by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

中文:
定理 goldenRatio_lt_two
  结论: φ < 2
  证明: by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

Depends on / 依赖: sqrt_lt
-/
theorem goldenRatio_lt_two : φ < 2 := by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

/--
theorem `goldenConj_neg` / 定理 `goldenConj_neg`

English:
theorem goldenConj_neg
  statement: ψ < 0
  proof: by
  linarith [one_sub_goldenConj, one_lt_goldenRatio]

中文:
定理 goldenConj_neg
  结论: ψ < 0
  证明: by
  linarith [one_sub_goldenConj, one_lt_goldenRatio]

Depends on / 依赖: one_lt_goldenRatio, one_sub_goldenConj
-/
theorem goldenConj_neg : ψ < 0 := by
  linarith [one_sub_goldenConj, one_lt_goldenRatio]

/--
theorem `goldenConj_ne_zero` / 定理 `goldenConj_ne_zero`

English:
theorem goldenConj_ne_zero
  statement: ψ != 0
  proof: ne_of_lt goldenConj_neg

中文:
定理 goldenConj_ne_zero
  结论: ψ != 0
  证明: ne_of_lt goldenConj_neg

Depends on / 依赖: goldenConj_neg, ne_of_lt
-/
theorem goldenConj_ne_zero : ψ != 0 :=
  ne_of_lt goldenConj_neg

/--
theorem `neg_one_lt_goldenConj` / 定理 `neg_one_lt_goldenConj`

English:
theorem neg_one_lt_goldenConj
  statement: -1 < ψ
  proof: by
  rw [neg_lt]; rw [← inv_goldenRatio]
  exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio

中文:
定理 neg_one_lt_goldenConj
  结论: -1 < ψ
  证明: by
  rw [neg_lt]; rw [← inv_goldenRatio]
  exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio

Depends on / 依赖: inv_goldenRatio, neg_lt, one_lt_goldenRatio
-/
theorem neg_one_lt_goldenConj : -1 < ψ := by
  rw [neg_lt]; rw [← inv_goldenRatio]
  exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio

/-!
## Irrationality
-/


/--
theorem `goldenRatio_irrational` / 定理 `goldenRatio_irrational`

English:
theorem goldenRatio_irrational
  statement: Irrational φ
  proof: by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_add 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

中文:
定理 goldenRatio_irrational
  结论: Irrational φ
  证明: by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_add 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

Depends on / 依赖: Nat.Prime, Nat.Prime.irrational_sqrt, convert, irrational_sqrt, ratCast_add, ratCast_mul, this.ratCast_add, this.ratCast_mul
-/
theorem goldenRatio_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_add 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

/--
theorem `goldenConj_irrational` / 定理 `goldenConj_irrational`

English:
theorem goldenConj_irrational
  statement: Irrational ψ
  proof: by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_sub 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

中文:
定理 goldenConj_irrational
  结论: Irrational ψ
  证明: by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_sub 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

Depends on / 依赖: Nat.Prime, Nat.Prime.irrational_sqrt, convert, irrational_sqrt, ratCast_mul, ratCast_sub, this.ratCast_mul, this.ratCast_sub
-/
theorem goldenConj_irrational : Irrational ψ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_sub 1
  convert! this.ratCast_mul (show (0.5 : Rat) != 0 by norm_num)
  simp
  ring

/-!
## Links with Fibonacci sequence
-/

section Fibrec

variable {α : Type*} [CommSemiring α]

/--
Definition of `fibRec` / `fibRec` 的定义

English:
definition fibRec
  signature: : LinearRecurrence α where
  body: 2
  coeffs := ![1, 1]

中文:
定义 fibRec
  签名: : LinearRecurrence α where
  定义体: 2
  coeffs := ![1, 1]
-/
def fibRec : LinearRecurrence α where
  order := 2
  coeffs := ![1, 1]

section Poly

open Polynomial

/--
theorem `fibRec_charPoly_eq` / 定理 `fibRec_charPoly_eq`

English:
theorem fibRec_charPoly_eq
  given: {β : Type*} [CommRing β]
  proof: by
  rw [fibRec]; rw [LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]

中文:
定理 fibRec_charPoly_eq
  条件: {β : 类型} [交换环 β]
  证明: by
  rw [fibRec]; rw [LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]

Depends on / 依赖: Finset, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, LinearRecurrence, LinearRecurrence.charPoly, charPoly, fibRec, smul_X_eq_monomial, sum_fin_eq_sum_range, sum_range_succ
-/
theorem fibRec_charPoly_eq {β : Type*} [CommRing β] :
    fibRec.charPoly = X ^ 2 - (X + (1 : β[X])) := by
  rw [fibRec]; rw [LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]

end Poly

/--
theorem `fib_isSol_fibRec` / 定理 `fib_isSol_fibRec`

English:
theorem fib_isSol_fibRec
  statement: fibRec.IsSolution (fun x => x.fib : Nat -> α)
  proof: by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two]; rw [add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

中文:
定理 fib_isSol_fibRec
  结论: fibRec.IsSolution (fun x => x.fib : 自然数 -> α)
  证明: by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two]; rw [add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

Depends on / 依赖: Finset, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.fib_add_two, add_comm, fibRec, fib_add_two, sum_fin_eq_sum_range, sum_range_succ
-/
theorem fib_isSol_fibRec : fibRec.IsSolution (fun x => x.fib : Nat -> α) := by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two]; rw [add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

/--
theorem `geom_goldenRatio_isSol_fibRec` / 定理 `geom_goldenRatio_isSol_fibRec`

English:
theorem geom_goldenRatio_isSol_fibRec
  statement: fibRec.IsSolution (φ ^ ·)
  proof: by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

中文:
定理 geom_goldenRatio_isSol_fibRec
  结论: fibRec.IsSolution (φ ^ ·)
  证明: by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

Depends on / 依赖: fibRec, fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq, geom_sol_iff_root_charPoly
-/
theorem geom_goldenRatio_isSol_fibRec : fibRec.IsSolution (φ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

/--
theorem `geom_goldenConj_isSol_fibRec` / 定理 `geom_goldenConj_isSol_fibRec`

English:
theorem geom_goldenConj_isSol_fibRec
  statement: fibRec.IsSolution (ψ ^ ·)
  proof: by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

中文:
定理 geom_goldenConj_isSol_fibRec
  结论: fibRec.IsSolution (ψ ^ ·)
  证明: by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

Depends on / 依赖: fibRec, fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq, geom_sol_iff_root_charPoly
-/
theorem geom_goldenConj_isSol_fibRec : fibRec.IsSolution (ψ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly]; rw [fibRec_charPoly_eq]
  simp

end Fibrec

/--
theorem `coe_fib_eq'` / 定理 `coe_fib_eq'`

English:
theorem coe_fib_eq'
  proof: by
  rw [fibRec.eq_iff_eqOn_range_order]
  · intro i hi
    norm_cast at hi
    fin_cases hi <;> simp
  · exact fib_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec
        ((fun n => (√5)⁻¹ * φ ^ n) - (fun n => (√5)⁻¹ * ψ ^ n)) by
      convert! this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec Real _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenRatio_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenConj_isSol_fibRec

中文:
定理 coe_fib_eq'
  证明: by
  rw [fibRec.eq_iff_eqOn_range_order]
  · intro i hi
    norm_cast at hi
    fin_cases hi <;> simp
  · exact fib_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec
        ((fun n => (√5)⁻¹ * φ ^ n) - (fun n => (√5)⁻¹ * ψ ^ n)) by
      convert! this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec Real _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenRatio_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenConj_isSol_fibRec

Depends on / 依赖: IsSolution, LinearRecurrence, LinearRecurrence.IsSolution, Pi.sub_apply, Submodule, Submodule.smul_mem, convert, eq_iff_eqOn_range_order, fibRec, fibRec.eq_iff_eqOn_range_order, fibRec.solSpace, fib_isSol_fibRec, fin_cases, geom_goldenConj_isSol_fibRec, geom_goldenRatio_isSol_fibRec, smul_mem, solSpace, solSpace.sub_mem, sub_apply, sub_mem
-/
theorem coe_fib_eq' :
    (fun n => Nat.fib n : Nat -> Real) = fun n => (φ ^ n - ψ ^ n) / √5 := by
  rw [fibRec.eq_iff_eqOn_range_order]
  · intro i hi
    norm_cast at hi
    fin_cases hi <;> simp
  · exact fib_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec
        ((fun n => (√5)⁻¹ * φ ^ n) - (fun n => (√5)⁻¹ * ψ ^ n)) by
      convert! this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec Real _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenRatio_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenConj_isSol_fibRec

/--
theorem `coe_fib_eq` / 定理 `coe_fib_eq`

English:
theorem coe_fib_eq
  statement: forall n, (Nat.fib n : Real) = (φ ^ n - ψ ^ n) / √5
  proof: by
  rw [← funext_iff]; rw [Real.coe_fib_eq']

中文:
定理 coe_fib_eq
  结论: 对任意 n, (自然数.fib n : 实数) = (φ ^ n - ψ ^ n) / √5
  证明: by
  rw [← funext_iff]; rw [Real.coe_fib_eq']

Depends on / 依赖: Real.coe_fib_eq, coe_fib_eq, funext_iff
-/
theorem coe_fib_eq : forall n, (Nat.fib n : Real) = (φ ^ n - ψ ^ n) / √5 := by
  rw [← funext_iff]; rw [Real.coe_fib_eq']

/--
theorem `coe_intFib_eq` / 定理 `coe_intFib_eq`

English:
theorem coe_intFib_eq
  given: (n : Int)
  statement: (Int.fib n : Real) = (φ ^ n - ψ ^ n) / √5
  proof: by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact coe_fib_eq n
  · simp only [Int.fib_neg, Int.even_coe_nat, Int.fib_natCast, Int.cast_ite, Int.cast_neg,
      Int.cast_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_goldenRatio, inv_goldenConj,
      ← neg_one_mul ψ, ← neg_one_mul φ, mul_pow, neg_one_pow_eq_ite]
    grind [coe_fib_eq]

中文:
定理 coe_intFib_eq
  条件: (n : 整数)
  结论: (整数.fib n : 实数) = (φ ^ n - ψ ^ n) / √5
  证明: by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact coe_fib_eq n
  · simp only [Int.fib_neg, Int.even_coe_nat, Int.fib_natCast, Int.cast_ite, Int.cast_neg,
      Int.cast_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_goldenRatio, inv_goldenConj,
      ← neg_one_mul ψ, ← neg_one_mul φ, mul_pow, neg_one_pow_eq_ite]
    grind [coe_fib_eq]

Depends on / 依赖: Int.cast_ite, Int.cast_natCast, Int.cast_neg, Int.even_coe_nat, Int.fib_natCast, Int.fib_neg, cast_ite, cast_natCast, cast_neg, coe_fib_eq, eq_nat_or_neg, even_coe_nat, fib_natCast, fib_neg, inv_goldenConj, inv_goldenRatio, inv_pow, mul_pow, n.eq_nat_or_neg, neg_one_mul
-/
theorem coe_intFib_eq (n : Int) : (Int.fib n : Real) = (φ ^ n - ψ ^ n) / √5 := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact coe_fib_eq n
  · simp only [Int.fib_neg, Int.even_coe_nat, Int.fib_natCast, Int.cast_ite, Int.cast_neg,
      Int.cast_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_goldenRatio, inv_goldenConj,
      ← neg_one_mul ψ, ← neg_one_mul φ, mul_pow, neg_one_pow_eq_ite]
    grind [coe_fib_eq]

/--
theorem `fib_succ_sub_goldenRatio_mul_fib` / 定理 `fib_succ_sub_goldenRatio_mul_fib`

English:
theorem fib_succ_sub_goldenRatio_mul_fib
  given: (n : Nat)
  statement: Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n
  proof: by
  repeat rw [coe_fib_eq]
  rw [mul_div]; rw [div_sub_div_same]; rw [mul_sub]; rw [← pow_succ']
  ring_nf
  have nz : √5 != 0 := by norm_num
  rw [← (mul_inv_cancel₀ nz).symm]; rw [one_mul]

中文:
定理 fib_succ_sub_goldenRatio_mul_fib
  条件: (n : 自然数)
  结论: 自然数.fib (n + 1) - φ * 自然数.fib n = ψ ^ n
  证明: by
  repeat rw [coe_fib_eq]
  rw [mul_div]; rw [div_sub_div_same]; rw [mul_sub]; rw [← pow_succ']
  ring_nf
  have nz : √5 != 0 := by norm_num
  rw [← (mul_inv_cancel₀ nz).symm]; rw [one_mul]

Depends on / 依赖: coe_fib_eq, div_sub_div_same, mul_div, mul_sub, one_mul, pow_succ, repeat, ring_nf
-/
theorem fib_succ_sub_goldenRatio_mul_fib (n : Nat) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n := by
  repeat rw [coe_fib_eq]
  rw [mul_div]; rw [div_sub_div_same]; rw [mul_sub]; rw [← pow_succ']
  ring_nf
  have nz : √5 != 0 := by norm_num
  rw [← (mul_inv_cancel₀ nz).symm]; rw [one_mul]

/--
lemma `goldenConj_mul_fib_succ_add_fib` / 引理 `goldenConj_mul_fib_succ_add_fib`

English:
lemma goldenConj_mul_fib_succ_add_fib
  given: (n : Nat)
  statement: ψ * Nat.fib (n + 1) + Nat.fib n = ψ ^ (n + 1)
  proof: by
  grind [fib_succ_sub_goldenRatio_mul_fib]

中文:
引理 goldenConj_mul_fib_succ_add_fib
  条件: (n : 自然数)
  结论: ψ * 自然数.fib (n + 1) + 自然数.fib n = ψ ^ (n + 1)
  证明: by
  grind [fib_succ_sub_goldenRatio_mul_fib]

Depends on / 依赖: fib_succ_sub_goldenRatio_mul_fib
-/
lemma goldenConj_mul_fib_succ_add_fib (n : Nat) : ψ * Nat.fib (n + 1) + Nat.fib n = ψ ^ (n + 1) := by
  grind [fib_succ_sub_goldenRatio_mul_fib]

/--
lemma `goldenRatio_mul_fib_succ_add_fib` / 引理 `goldenRatio_mul_fib_succ_add_fib`

English:
lemma goldenRatio_mul_fib_succ_add_fib
  given: (n : Nat)
  statement: φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub,
          Nat.cast_add, goldenRatio_sq, Nat.sub_zero]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring

中文:
引理 goldenRatio_mul_fib_succ_add_fib
  条件: (n : 自然数)
  结论: φ * 自然数.fib (n + 1) + 自然数.fib n = φ ^ (n + 1)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub,
          Nat.cast_add, goldenRatio_sq, Nat.sub_zero]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring

Depends on / 依赖: Nat.cast_add, Nat.fib, Nat.fib_add_one, Nat.sub_zero, Nat.succ_ne_zero, Nat.succ_sub_succ_eq_sub, add_comm, cast_add, fib_add_one, goldenRatio_sq, sub_zero, succ_ne_zero, succ_sub_succ_eq_sub
-/
lemma goldenRatio_mul_fib_succ_add_fib (n : Nat) : φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub,
          Nat.cast_add, goldenRatio_sq, Nat.sub_zero]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring

/--
theorem `fib_succ_sub_goldenConj_mul_fib` / 定理 `fib_succ_sub_goldenConj_mul_fib`

English:
theorem fib_succ_sub_goldenConj_mul_fib
  given: (n : Nat)
  statement: Nat.fib (n + 1) - ψ * Nat.fib n = φ ^ n
  proof: by
  grind [goldenRatio_mul_fib_succ_add_fib]

中文:
定理 fib_succ_sub_goldenConj_mul_fib
  条件: (n : 自然数)
  结论: 自然数.fib (n + 1) - ψ * 自然数.fib n = φ ^ n
  证明: by
  grind [goldenRatio_mul_fib_succ_add_fib]

Depends on / 依赖: goldenRatio_mul_fib_succ_add_fib
-/
theorem fib_succ_sub_goldenConj_mul_fib (n : Nat) : Nat.fib (n + 1) - ψ * Nat.fib n = φ ^ n := by
  grind [goldenRatio_mul_fib_succ_add_fib]

end Real
