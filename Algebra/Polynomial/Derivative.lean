/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# The derivative map on polynomials

## Main definitions
* `Polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.
* `Polynomial.derivativeFinsupp`: Iterated derivatives as a finite support function.

-/

@[expose] public section


noncomputable section

open Finset

open Polynomial

open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : Nat}

section Derivative

section Semiring

variable [Semiring R] {p : R[X]}

/--
Definition of `derivative` / `derivative` 的定义

English:
definition derivative
  signature: : R[X] ->ₗ[R] R[X] where
  body: p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_z

中文:
定义 derivative
  签名: : R[X] ->ₗ[R] R[X] where
  定义体: p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_z

Depends on / 依赖: p.sum
-/
def derivative : R[X] ->ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_zero, sum]

/--
theorem `derivative_apply` / 定理 `derivative_apply`

English:
theorem derivative_apply
  given: (p : R[X])
  statement: derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1)
  proof: rfl

中文:
定理 derivative_apply
  条件: (p : R[X])
  结论: derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1)
  证明: rfl
-/
theorem derivative_apply (p : R[X]) : derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1) :=
  rfl

/--
theorem `coeff_derivative` / 定理 `coeff_derivative`

English:
theorem coeff_derivative
  given: (p : R[X]) (n : Nat)
  proof: by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum]; rw [Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero]; rw [mul_zero]; rw [zero_mul]
    · int

中文:
定理 coeff_derivative
  条件: (p : R[X]) (n : 自然数)
  证明: by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum]; rw [Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero]; rw [mul_zero]; rw [zero_mul]
    · int

Depends on / 依赖: Finset, Finset.sum_eq_single, H.symm, Nat.add_one_sub_one, Nat.add_succ_sub_one, Nat.cast_zero, Nat.succ, add_one_sub_one, add_succ_sub_one, add_zero, cast_zero, coeff_C_mul, coeff_X_pow, coeff_sum, congr_arg, derivative_apply, if_neg, if_true, intros, mul_one
-/
theorem coeff_derivative (p : R[X]) (n : Nat) :
    coeff (derivative p) n = coeff p (n + 1) * (n + 1) := by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum]; rw [Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero]; rw [mul_zero]; rw [zero_mul]
    · intro _ H
      rw [Nat.add_one_sub_one]; rw [if_neg (mt (congr_arg Nat.succ) H.symm)]; rw [mul_zero]
  · simp_all

@[simp]
/--
theorem `derivative_zero` / 定理 `derivative_zero`

English:
theorem derivative_zero
  statement: derivative (0 : R[X]) = 0
  proof: derivative.map_zero

中文:
定理 derivative_zero
  结论: derivative (0 : R[X]) = 0
  证明: derivative.map_zero

Depends on / 依赖: derivative, derivative.map_zero, map_zero
-/
theorem derivative_zero : derivative (0 : R[X]) = 0 :=
  derivative.map_zero

/--
theorem `iterate_derivative_zero` / 定理 `iterate_derivative_zero`

English:
theorem iterate_derivative_zero
  given: {k : Nat}
  statement: derivative^[k] (0 : R[X]) = 0
  proof: iterate_map_zero derivative k

中文:
定理 iterate_derivative_zero
  条件: {k : 自然数}
  结论: derivative^[k] (0 : R[X]) = 0
  证明: iterate_map_zero derivative k

Depends on / 依赖: derivative, iterate_map_zero
-/
theorem iterate_derivative_zero {k : Nat} : derivative^[k] (0 : R[X]) = 0 :=
  iterate_map_zero derivative k

/--
theorem `derivative_monomial` / 定理 `derivative_monomial`

English:
theorem derivative_monomial
  given: (a : R) (n : Nat)
  proof: by
  rw [derivative_apply]; rw [sum_monomial_index]; rw [C_mul_X_pow_eq_monomial]
  simp

@[simp]

中文:
定理 derivative_monomial
  条件: (a : R) (n : 自然数)
  证明: by
  rw [derivative_apply]; rw [sum_monomial_index]; rw [C_mul_X_pow_eq_monomial]
  simp

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, derivative_apply, sum_monomial_index
-/
theorem derivative_monomial (a : R) (n : Nat) :
    derivative (monomial n a) = monomial (n - 1) (a * n) := by
  rw [derivative_apply]; rw [sum_monomial_index]; rw [C_mul_X_pow_eq_monomial]
  simp

@[simp]
/--
theorem `derivative_monomial_succ` / 定理 `derivative_monomial_succ`

English:
theorem derivative_monomial_succ
  given: (a : R) (n : Nat)
  proof: by
  rw [derivative_monomial]; rw [add_tsub_cancel_right]; rw [Nat.cast_add]; rw [Nat.cast_one]

中文:
定理 derivative_monomial_succ
  条件: (a : R) (n : 自然数)
  证明: by
  rw [derivative_monomial]; rw [add_tsub_cancel_right]; rw [Nat.cast_add]; rw [Nat.cast_one]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, cast_add, cast_one, derivative_monomial
-/
theorem derivative_monomial_succ (a : R) (n : Nat) :
    derivative (monomial (n + 1) a) = monomial n (a * (n + 1)) := by
  rw [derivative_monomial]; rw [add_tsub_cancel_right]; rw [Nat.cast_add]; rw [Nat.cast_one]

/--
theorem `derivative_C_mul_X` / 定理 `derivative_C_mul_X`

English:
theorem derivative_C_mul_X
  given: (a : R)
  statement: derivative (C a * X) = C a
  proof: by
  simp [C_mul_X_eq_monomial, mul_one]

中文:
定理 derivative_C_mul_X
  条件: (a : R)
  结论: derivative (C a * X) = C a
  证明: by
  simp [C_mul_X_eq_monomial, mul_one]

Depends on / 依赖: C_mul_X_eq_monomial, mul_one
-/
theorem derivative_C_mul_X (a : R) : derivative (C a * X) = C a := by
  simp [C_mul_X_eq_monomial, mul_one]

/--
theorem `derivative_C_mul_X_pow` / 定理 `derivative_C_mul_X_pow`

English:
theorem derivative_C_mul_X_pow
  given: (a : R) (n : Nat)
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [C_mul_X_pow_eq_monomial]; rw [derivative_monomial]

中文:
定理 derivative_C_mul_X_pow
  条件: (a : R) (n : 自然数)
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [C_mul_X_pow_eq_monomial]; rw [derivative_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, derivative_monomial
-/
theorem derivative_C_mul_X_pow (a : R) (n : Nat) :
    derivative (C a * X ^ n) = C (a * n) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial]; rw [C_mul_X_pow_eq_monomial]; rw [derivative_monomial]

/--
theorem `derivative_C_mul_X_sq` / 定理 `derivative_C_mul_X_sq`

English:
theorem derivative_C_mul_X_sq
  given: (a : R)
  statement: derivative (C a * X ^ 2) = C (a * 2) * X
  proof: by
  rw [derivative_C_mul_X_pow]; rw [Nat.cast_two]; rw [pow_one]

中文:
定理 derivative_C_mul_X_sq
  条件: (a : R)
  结论: derivative (C a * X ^ 2) = C (a * 2) * X
  证明: by
  rw [derivative_C_mul_X_pow]; rw [Nat.cast_two]; rw [pow_one]

Depends on / 依赖: Nat.cast_two, cast_two, derivative_C_mul_X_pow, pow_one
-/
theorem derivative_C_mul_X_sq (a : R) : derivative (C a * X ^ 2) = C (a * 2) * X := by
  rw [derivative_C_mul_X_pow]; rw [Nat.cast_two]; rw [pow_one]

/--
theorem `derivative_X_pow` / 定理 `derivative_X_pow`

English:
theorem derivative_X_pow
  given: (n : Nat)
  statement: derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1)
  proof: by
  convert! derivative_C_mul_X_pow (1 : R) n <;> simp

@[simp]

中文:
定理 derivative_X_pow
  条件: (n : 自然数)
  结论: derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1)
  证明: by
  convert! derivative_C_mul_X_pow (1 : R) n <;> simp

@[simp]

Depends on / 依赖: convert, derivative_C_mul_X_pow
-/
theorem derivative_X_pow (n : Nat) : derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1) := by
  convert! derivative_C_mul_X_pow (1 : R) n <;> simp

@[simp]
/--
theorem `derivative_X_pow_succ` / 定理 `derivative_X_pow_succ`

English:
theorem derivative_X_pow_succ
  given: (n : Nat)
  proof: by
  simp [derivative_X_pow]

中文:
定理 derivative_X_pow_succ
  条件: (n : 自然数)
  证明: by
  simp [derivative_X_pow]

Depends on / 依赖: derivative_X_pow
-/
theorem derivative_X_pow_succ (n : Nat) :
    derivative (X ^ (n + 1) : R[X]) = C (n + 1 : R) * X ^ n := by
  simp [derivative_X_pow]

/--
theorem `derivative_X_sq` / 定理 `derivative_X_sq`

English:
theorem derivative_X_sq
  statement: derivative (X ^ 2 : R[X]) = C 2 * X
  proof: by
  rw [derivative_X_pow]; rw [Nat.cast_two]; rw [pow_one]

@[simp]

中文:
定理 derivative_X_sq
  结论: derivative (X ^ 2 : R[X]) = C 2 * X
  证明: by
  rw [derivative_X_pow]; rw [Nat.cast_two]; rw [pow_one]

@[simp]

Depends on / 依赖: Nat.cast_two, cast_two, derivative_X_pow, pow_one
-/
theorem derivative_X_sq : derivative (X ^ 2 : R[X]) = C 2 * X := by
  rw [derivative_X_pow]; rw [Nat.cast_two]; rw [pow_one]

@[simp]
/--
theorem `derivative_C` / 定理 `derivative_C`

English:
theorem derivative_C
  given: {a : R}
  statement: derivative (C a) = 0
  proof: by simp [derivative_apply]

中文:
定理 derivative_C
  条件: {a : R}
  结论: derivative (C a) = 0
  证明: by simp [derivative_apply]

Depends on / 依赖: derivative_apply
-/
theorem derivative_C {a : R} : derivative (C a) = 0 := by simp [derivative_apply]

/--
theorem `derivative_of_natDegree_zero` / 定理 `derivative_of_natDegree_zero`

English:
theorem derivative_of_natDegree_zero
  given: {p : R[X]} (hp : p.natDegree = 0)
  statement: derivative p = 0
  proof: by
  rw [eq_C_of_natDegree_eq_zero hp]; rw [derivative_C]

@[simp]

中文:
定理 derivative_of_natDegree_zero
  条件: {p : R[X]} (hp : p.natDegree = 0)
  结论: derivative p = 0
  证明: by
  rw [eq_C_of_natDegree_eq_zero hp]; rw [derivative_C]

@[simp]

Depends on / 依赖: derivative_C, eq_C_of_natDegree_eq_zero
-/
theorem derivative_of_natDegree_zero {p : R[X]} (hp : p.natDegree = 0) : derivative p = 0 := by
  rw [eq_C_of_natDegree_eq_zero hp]; rw [derivative_C]

@[simp]
/--
theorem `derivative_X` / 定理 `derivative_X`

English:
theorem derivative_X
  statement: derivative (X : R[X]) = 1
  proof: (derivative_monomial _ _).trans by simp

@[simp]

中文:
定理 derivative_X
  结论: derivative (X : R[X]) = 1
  证明: (derivative_monomial _ _).trans by simp

@[simp]

Depends on / 依赖: derivative_monomial
-/
theorem derivative_X : derivative (X : R[X]) = 1 :=
(derivative_monomial _ _).trans by simp

@[simp]
/--
theorem `derivative_one` / 定理 `derivative_one`

English:
theorem derivative_one
  statement: derivative (1 : R[X]) = 0
  proof: derivative_C

@[simp]

中文:
定理 derivative_one
  结论: derivative (1 : R[X]) = 0
  证明: derivative_C

@[simp]

Depends on / 依赖: derivative_C
-/
theorem derivative_one : derivative (1 : R[X]) = 0 :=
  derivative_C

@[simp]
/--
theorem `derivative_add` / 定理 `derivative_add`

English:
theorem derivative_add
  given: {f g : R[X]}
  statement: derivative (f + g) = derivative f + derivative g
  proof: derivative.map_add f g

中文:
定理 derivative_add
  条件: {f g : R[X]}
  结论: derivative (f + g) = derivative f + derivative g
  证明: derivative.map_add f g

Depends on / 依赖: derivative, derivative.map_add, map_add
-/
theorem derivative_add {f g : R[X]} : derivative (f + g) = derivative f + derivative g :=
  derivative.map_add f g

/--
theorem `derivative_X_add_C` / 定理 `derivative_X_add_C`

English:
theorem derivative_X_add_C
  given: (c : R)
  statement: derivative (X + C c) = 1
  proof: by
  rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]

中文:
定理 derivative_X_add_C
  条件: (c : R)
  结论: derivative (X + C c) = 1
  证明: by
  rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]

Depends on / 依赖: add_zero, derivative_C, derivative_X, derivative_add
-/
theorem derivative_X_add_C (c : R) : derivative (X + C c) = 1 := by
  rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]

/--
theorem `derivative_sum` / 定理 `derivative_sum`

English:
theorem derivative_sum
  given: {s : Finset ι} {f : ι -> R[X]}
  proof: map_sum ..

中文:
定理 derivative_sum
  条件: {s : Finset ι} {f : ι -> R[X]}
  证明: map_sum ..

Depends on / 依赖: map_sum
-/
theorem derivative_sum {s : Finset ι} {f : ι -> R[X]} :
    derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
  map_sum ..

/--
theorem `iterate_derivative_sum` / 定理 `iterate_derivative_sum`

English:
theorem iterate_derivative_sum
  given: (k : Nat) (s : Finset ι) (f : ι -> R[X])
  proof: by
  simp_rw [← Module.End.pow_apply, map_sum]

中文:
定理 iterate_derivative_sum
  条件: (k : 自然数) (s : Finset ι) (f : ι -> R[X])
  证明: by
  simp_rw [← Module.End.pow_apply, map_sum]

Depends on / 依赖: Module, Module.End.pow_apply, map_sum, pow_apply, simp_rw
-/
theorem iterate_derivative_sum (k : Nat) (s : Finset ι) (f : ι -> R[X]) :
    derivative^[k] (∑ b in s, f b) = ∑ b in s, derivative^[k] (f b) := by
  simp_rw [← Module.End.pow_apply, map_sum]

/--
theorem `derivative_smul` / 定理 `derivative_smul`

English:
theorem derivative_smul
  statement: {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] (s : S)
  proof: derivative.map_smul_of_tower s p

@[simp]

中文:
定理 derivative_smul
  结论: {S : 类型} [SMulZeroClass S R] [IsScalarTower S R R] (s : S)
  证明: derivative.map_smul_of_tower s p

@[simp]

Depends on / 依赖: derivative, derivative.map_smul_of_tower, map_smul_of_tower
-/
theorem derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] (s : S)
    (p : R[X]) : derivative (s • p) = s • derivative p :=
  derivative.map_smul_of_tower s p

@[simp]
/--
theorem `iterate_derivative_smul` / 定理 `iterate_derivative_smul`

English:
theorem iterate_derivative_smul
  statement: {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R]
  proof: by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih]

@[simp]

中文:
定理 iterate_derivative_smul
  结论: {S : 类型} [SMulZeroClass S R] [IsScalarTower S R R]
  证明: by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih]

@[simp]

Depends on / 依赖: generalizing
-/
theorem iterate_derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R]
    (s : S) (p : R[X]) (k : Nat) : derivative^[k] (s • p) = s • derivative^[k] p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih]

@[simp]
/--
theorem `iterate_derivative_C_mul` / 定理 `iterate_derivative_C_mul`

English:
theorem iterate_derivative_C_mul
  given: (a : R) (p : R[X]) (k : Nat)
  proof: by
  simp_rw [← smul_eq_C_mul, iterate_derivative_smul]

中文:
定理 iterate_derivative_C_mul
  条件: (a : R) (p : R[X]) (k : 自然数)
  证明: by
  simp_rw [← smul_eq_C_mul, iterate_derivative_smul]

Depends on / 依赖: iterate_derivative_smul, simp_rw, smul_eq_C_mul
-/
theorem iterate_derivative_C_mul (a : R) (p : R[X]) (k : Nat) :
    derivative^[k] (C a * p) = C a * derivative^[k] p := by
  simp_rw [← smul_eq_C_mul, iterate_derivative_smul]

/--
theorem `derivative_C_mul` / 定理 `derivative_C_mul`

English:
theorem derivative_C_mul
  given: (a : R) (p : R[X])
  proof: iterate_derivative_C_mul _ _ 1

中文:
定理 derivative_C_mul
  条件: (a : R) (p : R[X])
  证明: iterate_derivative_C_mul _ _ 1

Depends on / 依赖: iterate_derivative_C_mul
-/
theorem derivative_C_mul (a : R) (p : R[X]) :
    derivative (C a * p) = C a * derivative p := iterate_derivative_C_mul _ _ 1

/--
theorem `of_mem_support_derivative` / 定理 `of_mem_support_derivative`

English:
theorem of_mem_support_derivative
  given: {p : R[X]} {n : Nat} (h : n in p.derivative.support)
  proof: mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
mem_support_iff.1 h show p.derivative.coeff n = 0 by rw [coeff_derivative, h1, zero_mul]

中文:
定理 of_mem_support_derivative
  条件: {p : R[X]} {n : 自然数} (h : n in p.derivative.support)
  证明: mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
mem_support_iff.1 h show p.derivative.coeff n = 0 by rw [coeff_derivative, h1, zero_mul]

Depends on / 依赖: coeff_derivative, derivative, mem_support_iff, p.coeff, p.derivative.coeff, zero_mul
-/
theorem of_mem_support_derivative {p : R[X]} {n : Nat} (h : n in p.derivative.support) :
    n + 1 in p.support :=
  mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
mem_support_iff.1 h show p.derivative.coeff n = 0 by rw [coeff_derivative, h1, zero_mul]

/--
theorem `degree_derivative_lt` / 定理 `degree_derivative_lt`

English:
theorem degree_derivative_lt
  given: {p : R[X]} (hp : p != 0)
  statement: p.derivative.degree < p.degree
  proof: (Finset.sup_lt_iff <| bot_lt_iff_ne_bot.2 <| mt degree_eq_bot.1 hp).2 fun n hp =>
lt_of_lt_of_le (WithBot.coe_lt_coe.2 n.lt_succ_self)
Finset.le_sup of_mem_support_derivative hp

中文:
定理 degree_derivative_lt
  条件: {p : R[X]} (hp : p != 0)
  结论: p.derivative.degree < p.degree
  证明: (Finset.sup_lt_iff <| bot_lt_iff_ne_bot.2 <| mt degree_eq_bot.1 hp).2 fun n hp =>
lt_of_lt_of_le (WithBot.coe_lt_coe.2 n.lt_succ_self)
Finset.le_sup of_mem_support_derivative hp

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_lt_iff, WithBot, WithBot.coe_lt_coe, bot_lt_iff_ne_bot, coe_lt_coe, degree_eq_bot, le_sup, lt_of_lt_of_le, lt_succ_self, n.lt_succ_self, of_mem_support_derivative, sup_lt_iff
-/
theorem degree_derivative_lt {p : R[X]} (hp : p != 0) : p.derivative.degree < p.degree :=
  (Finset.sup_lt_iff <| bot_lt_iff_ne_bot.2 <| mt degree_eq_bot.1 hp).2 fun n hp =>
lt_of_lt_of_le (WithBot.coe_lt_coe.2 n.lt_succ_self)
Finset.le_sup of_mem_support_derivative hp

/--
theorem `degree_derivative_le` / 定理 `degree_derivative_le`

English:
theorem degree_derivative_le
  given: {p : R[X]}
  statement: p.derivative.degree <= p.degree
  proof: letI := Classical.decEq R
if H : p = 0 then le_of_eq by rw [H, derivative_zero] else (degree_derivative_lt H).le

中文:
定理 degree_derivative_le
  条件: {p : R[X]}
  结论: p.derivative.degree <= p.degree
  证明: letI := Classical.decEq R
if H : p = 0 then le_of_eq by rw [H, derivative_zero] else (degree_derivative_lt H).le

Depends on / 依赖: Classical, Classical.decEq, degree_derivative_lt, derivative_zero, le_of_eq
-/
theorem degree_derivative_le {p : R[X]} : p.derivative.degree <= p.degree :=
  letI := Classical.decEq R
if H : p = 0 then le_of_eq by rw [H, derivative_zero] else (degree_derivative_lt H).le

/--
theorem `natDegree_derivative_lt` / 定理 `natDegree_derivative_lt`

English:
theorem natDegree_derivative_lt
  given: {p : R[X]} (hp : p.natDegree != 0)
  proof: by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [hp', Polynomial.natDegree_zero]
    exact hp.bot_lt
  · rw [natDegree_lt_natDegree_iff hp']
    exact degree_derivative_lt fun h => hp (h.symm ▸ natDegree_zero)

中文:
定理 natDegree_derivative_lt
  条件: {p : R[X]} (hp : p.natDegree != 0)
  证明: by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [hp', Polynomial.natDegree_zero]
    exact hp.bot_lt
  · rw [natDegree_lt_natDegree_iff hp']
    exact degree_derivative_lt fun h => hp (h.symm ▸ natDegree_zero)

Depends on / 依赖: Polynomial, Polynomial.natDegree_zero, bot_lt, degree_derivative_lt, derivative, eq_or_ne, h.symm, hp.bot_lt, natDegree_lt_natDegree_iff, natDegree_zero
-/
theorem natDegree_derivative_lt {p : R[X]} (hp : p.natDegree != 0) :
    p.derivative.natDegree < p.natDegree := by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [hp', Polynomial.natDegree_zero]
    exact hp.bot_lt
  · rw [natDegree_lt_natDegree_iff hp']
    exact degree_derivative_lt fun h => hp (h.symm ▸ natDegree_zero)

/--
theorem `natDegree_derivative_le` / 定理 `natDegree_derivative_le`

English:
theorem natDegree_derivative_le
  given: (p : R[X])
  statement: p.derivative.natDegree <= p.natDegree - 1
  proof: by
  by_cases p0 : p.natDegree = 0
  · simp [p0, derivative_of_natDegree_zero]
  · exact Nat.le_sub_one_of_lt (natDegree_derivative_lt p0)

中文:
定理 natDegree_derivative_le
  条件: (p : R[X])
  结论: p.derivative.natDegree <= p.natDegree - 1
  证明: by
  by_cases p0 : p.natDegree = 0
  · simp [p0, derivative_of_natDegree_zero]
  · exact Nat.le_sub_one_of_lt (natDegree_derivative_lt p0)

Depends on / 依赖: Nat.le_sub_one_of_lt, NonUnitalRingHomClass, NonUnitalRingHomClass.toNonUnitalRingHom, derivative_of_natDegree_zero, le_sub_one_of_lt, natDegree, natDegree_derivative_lt, p.natDegree, toNonUnitalRingHom
-/
theorem natDegree_derivative_le (p : R[X]) : p.derivative.natDegree <= p.natDegree - 1 := by
  by_cases p0 : p.natDegree = 0
  · simp [p0, derivative_of_natDegree_zero]
  · exact Nat.le_sub_one_of_lt (natDegree_derivative_lt p0)

/--
theorem `natDegree_iterate_derivative` / 定理 `natDegree_iterate_derivative`

English:
theorem natDegree_iterate_derivative
  given: (p : R[X]) (k : Nat)
  proof: by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.sub_zero]
  | succ d hd =>
      rw [Function.iterate_succ_apply']; rw [Nat.sub_succ']
exact (natDegree_derivative_le _).trans Nat.sub_le_sub_right hd 1

@[simp]

中文:
定理 natDegree_iterate_derivative
  条件: (p : R[X]) (k : 自然数)
  证明: by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.sub_zero]
  | succ d hd =>
      rw [Function.iterate_succ_apply']; rw [Nat.sub_succ']
exact (natDegree_derivative_le _).trans Nat.sub_le_sub_right hd 1

@[simp]

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.sub_le_sub_right, Nat.sub_succ, Nat.sub_zero, iterate_succ_apply, iterate_zero_apply, natDegree_derivative_le, sub_le_sub_right, sub_succ, sub_zero
-/
theorem natDegree_iterate_derivative (p : R[X]) (k : Nat) :
    (derivative^[k] p).natDegree <= p.natDegree - k := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.sub_zero]
  | succ d hd =>
      rw [Function.iterate_succ_apply']; rw [Nat.sub_succ']
exact (natDegree_derivative_le _).trans Nat.sub_le_sub_right hd 1

@[simp]
/--
theorem `derivative_natCast` / 定理 `derivative_natCast`

English:
theorem derivative_natCast
  given: {n : Nat}
  statement: derivative (n : R[X]) = 0
  proof: by
  rw [← map_natCast C n]
  exact derivative_C

@[simp]

中文:
定理 derivative_natCast
  条件: {n : 自然数}
  结论: derivative (n : R[X]) = 0
  证明: by
  rw [← map_natCast C n]
  exact derivative_C

@[simp]

Depends on / 依赖: derivative_C, map_natCast
-/
theorem derivative_natCast {n : Nat} : derivative (n : R[X]) = 0 := by
  rw [← map_natCast C n]
  exact derivative_C

@[simp]
/--
theorem `derivative_ofNat` / 定理 `derivative_ofNat`

English:
theorem derivative_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: derivative_natCast

中文:
定理 derivative_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: derivative_natCast

Depends on / 依赖: derivative_natCast
-/
theorem derivative_ofNat (n : Nat) [n.AtLeastTwo] :
    derivative (ofNat(n) : R[X]) = 0 :=
  derivative_natCast

/--
theorem `iterate_derivative_eq_zero` / 定理 `iterate_derivative_eq_zero`

English:
theorem iterate_derivative_eq_zero
  given: {p : R[X]} {x : Nat} (hx : p.natDegree < x)
  proof: by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with | _ _ ih
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, iterate_derivative_z

中文:
定理 iterate_derivative_eq_zero
  条件: {p : R[X]} {x : 自然数} (hx : p.natDegree < x)
  证明: by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with | _ _ ih
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, iterate_derivative_z

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.exists_eq_succ_of_ne_zero, Nat.le_of_lt_succ, Nat.strong_induction_on, derivative_of_natDegree_zero, exists_eq_succ_of_ne_zero, generalizing, iterate_derivative_zero, iterate_succ_apply, le_of_lt_succ, natDegree, natDegree_derivative_lt, p.natDegree, pos_of_gt, strong_induction_on, this.trans_le, trans_le
-/
theorem iterate_derivative_eq_zero {p : R[X]} {x : Nat} (hx : p.natDegree < x) :
    Polynomial.derivative^[x] p = 0 := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with | _ _ ih
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, iterate_derivative_zero]
  have := natDegree_derivative_lt hp
  exact ih _ this (this.trans_le <| Nat.le_of_lt_succ hx) rfl

@[simp]
/--
theorem `iterate_derivative_C` / 定理 `iterate_derivative_C`

English:
theorem iterate_derivative_C
  given: {k} (h : 0 < k)
  statement: derivative^[k] (C a : R[X]) = 0
  proof: iterate_derivative_eq_zero (natDegree_C _).trans_lt h

@[simp]

中文:
定理 iterate_derivative_C
  条件: {k} (h : 0 < k)
  结论: derivative^[k] (C a : R[X]) = 0
  证明: iterate_derivative_eq_zero (natDegree_C _).trans_lt h

@[simp]

Depends on / 依赖: iterate_derivative_eq_zero, natDegree_C, trans_lt
-/
theorem iterate_derivative_C {k} (h : 0 < k) : derivative^[k] (C a : R[X]) = 0 :=
iterate_derivative_eq_zero (natDegree_C _).trans_lt h

@[simp]
/--
theorem `iterate_derivative_one` / 定理 `iterate_derivative_one`

English:
theorem iterate_derivative_one
  given: {k} (h : 0 < k)
  statement: derivative^[k] (1 : R[X]) = 0
  proof: iterate_derivative_C h

@[simp]

中文:
定理 iterate_derivative_one
  条件: {k} (h : 0 < k)
  结论: derivative^[k] (1 : R[X]) = 0
  证明: iterate_derivative_C h

@[simp]

Depends on / 依赖: iterate_derivative_C
-/
theorem iterate_derivative_one {k} (h : 0 < k) : derivative^[k] (1 : R[X]) = 0 :=
  iterate_derivative_C h

@[simp]
/--
theorem `iterate_derivative_X` / 定理 `iterate_derivative_X`

English:
theorem iterate_derivative_X
  given: {k} (h : 1 < k)
  statement: derivative^[k] (X : R[X]) = 0
  proof: iterate_derivative_eq_zero natDegree_X_le.trans_lt h

@[simp]

中文:
定理 iterate_derivative_X
  条件: {k} (h : 1 < k)
  结论: derivative^[k] (X : R[X]) = 0
  证明: iterate_derivative_eq_zero natDegree_X_le.trans_lt h

@[simp]

Depends on / 依赖: iterate_derivative_eq_zero, natDegree_X_le, natDegree_X_le.trans_lt, trans_lt
-/
theorem iterate_derivative_X {k} (h : 1 < k) : derivative^[k] (X : R[X]) = 0 :=
iterate_derivative_eq_zero natDegree_X_le.trans_lt h

@[simp]
/--
theorem `derivative_mul` / 定理 `derivative_mul`

English:
theorem derivative_mul
  given: {f g : R[X]}
  statement: derivative (f * g) = derivative f * g + f * derivative g
  proof: by
  induction f using Polynomial.induction_on' with
  | add => simp only [add_mul, map_add, add_assoc, add_left_comm, *]
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add => simp only [mul_add, map_add, add_assoc, add_left_comm, *]
  | monomial n b => ?_
  simp only [

中文:
定理 derivative_mul
  条件: {f g : R[X]}
  结论: derivative (f * g) = derivative f * g + f * derivative g
  证明: by
  induction f using Polynomial.induction_on' with
  | add => simp only [add_mul, map_add, add_assoc, add_left_comm, *]
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add => simp only [mul_add, map_add, add_assoc, add_left_comm, *]
  | monomial n b => ?_
  simp only [

Depends on / 依赖: Nat.cast_add, Nat.cast_commute, Nat.cast_zero, Polynomial, Polynomial.induction_on, add_assoc, add_left_comm, add_mul, cast_add, cast_commute, cast_zero, derivative_monomial, induction_on, map_add, map_zero, monomial, monomial_mul_monomial, mul_add, mul_assoc, mul_zero
-/
theorem derivative_mul {f g : R[X]} : derivative (f * g) = derivative f * g + f * derivative g := by
  induction f using Polynomial.induction_on' with
  | add => simp only [add_mul, map_add, add_assoc, add_left_comm, *]
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add => simp only [mul_add, map_add, add_assoc, add_left_comm, *]
  | monomial n b => ?_
  simp only [monomial_mul_monomial, derivative_monomial]
  simp only [mul_assoc, (Nat.cast_commute _ _).eq, Nat.cast_add, mul_add, map_add]
  cases m with
  | zero => simp only [zero_add, Nat.cast_zero, mul_zero, map_zero]
  | succ m =>
  cases n with
  | zero => simp only [add_zero, Nat.cast_zero, mul_zero, map_zero]
  | succ n => grind

/--
theorem `derivative_eval` / 定理 `derivative_eval`

English:
theorem derivative_eval
  given: (p : R[X]) (x : R)
  proof: by
  simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]

@[simp]

中文:
定理 derivative_eval
  条件: (p : R[X]) (x : R)
  证明: by
  simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]

@[simp]

Depends on / 依赖: derivative_apply, eval_C, eval_mul_X_pow, eval_sum, simp_rw
-/
theorem derivative_eval (p : R[X]) (x : R) :
    p.derivative.eval x = p.sum fun n a => a * n * x ^ (n - 1) := by
  simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]

@[simp]
/--
theorem `derivative_map` / 定理 `derivative_map`

English:
theorem derivative_map
  given: [Semiring S] (p : R[X]) (f : R ->+* S)
  proof: by
  let n := max p.natDegree (map f p).natDegree
  rw [derivative_apply]; rw [derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  on_goal 1 => rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  · simp only [Polynomial.map_s

中文:
定理 derivative_map
  条件: [Semiring S] (p : R[X]) (f : R ->+* S)
  证明: by
  let n := max p.natDegree (map f p).natDegree
  rw [derivative_apply]; rw [derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  on_goal 1 => rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  · simp only [Polynomial.map_s

Depends on / 依赖: Polynomial, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow, Polynomial.map_sum, all_goals, coeff_map, derivative_apply, le_max_left, le_max_right, lt_add_one, map_C, map_X, map_mul, map_natCast, map_pow, map_sum, natDegree, on_goal
-/
theorem derivative_map [Semiring S] (p : R[X]) (f : R ->+* S) :
    derivative (p.map f) = p.derivative.map f := by
  let n := max p.natDegree (map f p).natDegree
  rw [derivative_apply]; rw [derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  on_goal 1 => rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  · simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, coeff_map,
      map_natCast, Polynomial.map_natCast, Polynomial.map_pow, map_X]
  all_goals intro n; rw [zero_mul, C_0, zero_mul]

@[simp]
/--
theorem `iterate_derivative_map` / 定理 `iterate_derivative_map`

English:
theorem iterate_derivative_map
  given: [Semiring S] (p : R[X]) (f : R ->+* S) (k : Nat)
  proof: by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [ih, Function.iterate_succ, Polynomial.derivative_map, Function.comp_apply]

中文:
定理 iterate_derivative_map
  条件: [Semiring S] (p : R[X]) (f : R ->+* S) (k : 自然数)
  证明: by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [ih, Function.iterate_succ, Polynomial.derivative_map, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Polynomial, Polynomial.derivative_map, comp_apply, derivative_map, generalizing, iterate_succ
-/
theorem iterate_derivative_map [Semiring S] (p : R[X]) (f : R ->+* S) (k : Nat) :
    Polynomial.derivative^[k] (p.map f) = (Polynomial.derivative^[k] p).map f := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [ih, Function.iterate_succ, Polynomial.derivative_map, Function.comp_apply]

/--
theorem `derivative_natCast_mul` / 定理 `derivative_natCast_mul`

English:
theorem derivative_natCast_mul
  given: {n : Nat} {f : R[X]}
  proof: by
  simp

@[simp]

中文:
定理 derivative_natCast_mul
  条件: {n : 自然数} {f : R[X]}
  证明: by
  simp

@[simp]
-/
theorem derivative_natCast_mul {n : Nat} {f : R[X]} :
    derivative ((n : R[X]) * f) = n * derivative f := by
  simp

@[simp]
/--
theorem `iterate_derivative_natCast_mul` / 定理 `iterate_derivative_natCast_mul`

English:
theorem iterate_derivative_natCast_mul
  given: {n k : Nat} {f : R[X]}
  proof: by
  induction k generalizing f <;> simp [*]

中文:
定理 iterate_derivative_natCast_mul
  条件: {n k : 自然数} {f : R[X]}
  证明: by
  induction k generalizing f <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem iterate_derivative_natCast_mul {n k : Nat} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction k generalizing f <;> simp [*]

/--
theorem `coeff_iterate_derivative` / 定理 `coeff_iterate_derivative`

English:
theorem coeff_iterate_derivative
  given: {k} (p : R[X]) (m : Nat)
  proof: by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih m.succ]; rw [N

中文:
定理 coeff_iterate_derivative
  条件: {k} (p : R[X]) (m : 自然数)
  证明: by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih m.succ]; rw [N

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.add_succ, Nat.cast_add_one, Nat.descFactorial, Nat.succ, Nat.succ_add, add_succ, cast_add_one, coeff_derivative, derivative, descFactorial, generalizing, iterate_succ_apply, k.succ, m.succ, nsmul_eq_mul, p.coeff, smul_smul, succ_add
-/
theorem coeff_iterate_derivative {k} (p : R[X]) (m : Nat) :
    (derivative^[k] p).coeff m = (m + k).descFactorial k • p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply']; rw [coeff_derivative]; rw [ih m.succ]; rw [Nat.succ_add]; rw [Nat.add_succ]
        _ = ((m + 1) * Nat.descFactorial (Nat.succ (m + k)) k) • p.coeff (m + k.succ) := by
          rw [← Nat.cast_add_one]; rw [← nsmul_eq_mul']; rw [smul_smul]
        _ = Nat.descFactorial (m.succ + k) k.succ • p.coeff (m + k.succ) := by
          rw [← Nat.succ_add]; rw [Nat.descFactorial_succ]; rw [add_tsub_cancel_right]
        _ = Nat.descFactorial (m + k.succ) k.succ • p.coeff (m + k.succ) := by
          rw [Nat.succ_add_eq_add_succ]

/--
theorem `iterate_derivative_eq_sum` / 定理 `iterate_derivative_eq_sum`

English:
theorem iterate_derivative_eq_sum
  given: (p : R[X]) (k : Nat)
  proof: by
  conv_lhs => rw [(derivative^[k] p).as_sum_support_C_mul_X_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_iterate_derivative]; rw [Nat.descFactorial_eq_factorial_mul_choose]

中文:
定理 iterate_derivative_eq_sum
  条件: (p : R[X]) (k : 自然数)
  证明: by
  conv_lhs => rw [(derivative^[k] p).as_sum_support_C_mul_X_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_iterate_derivative]; rw [Nat.descFactorial_eq_factorial_mul_choose]

Depends on / 依赖: Nat.descFactorial_eq_factorial_mul_choose, as_sum_support_C_mul_X_pow, coeff_iterate_derivative, conv_lhs, derivative, descFactorial_eq_factorial_mul_choose, sum_congr
-/
theorem iterate_derivative_eq_sum (p : R[X]) (k : Nat) :
    derivative^[k] p =
      ∑ x in (derivative^[k] p).support, C ((x + k).descFactorial k • p.coeff (x + k)) * X ^ x := by
  conv_lhs => rw [(derivative^[k] p).as_sum_support_C_mul_X_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_iterate_derivative]; rw [Nat.descFactorial_eq_factorial_mul_choose]

/--
theorem `iterate_derivative_eq_factorial_smul_sum` / 定理 `iterate_derivative_eq_factorial_smul_sum`

English:
theorem iterate_derivative_eq_factorial_smul_sum
  given: (p : R[X]) (k : Nat)
  proof: by
  conv_lhs => rw [iterate_derivative_eq_sum]
  rw [smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_mul_assoc]; rw [smul_C]; rw [smul_smul]; rw [Nat.descFactorial_eq_factorial_mul_choose]

中文:
定理 iterate_derivative_eq_factorial_smul_sum
  条件: (p : R[X]) (k : 自然数)
  证明: by
  conv_lhs => rw [iterate_derivative_eq_sum]
  rw [smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_mul_assoc]; rw [smul_C]; rw [smul_smul]; rw [Nat.descFactorial_eq_factorial_mul_choose]

Depends on / 依赖: Nat.descFactorial_eq_factorial_mul_choose, conv_lhs, descFactorial_eq_factorial_mul_choose, iterate_derivative_eq_sum, smul_C, smul_mul_assoc, smul_smul, smul_sum, sum_congr
-/
theorem iterate_derivative_eq_factorial_smul_sum (p : R[X]) (k : Nat) :
    derivative^[k] p = k ! •
      ∑ x in (derivative^[k] p).support, C ((x + k).choose k • p.coeff (x + k)) * X ^ x := by
  conv_lhs => rw [iterate_derivative_eq_sum]
  rw [smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_mul_assoc]; rw [smul_C]; rw [smul_smul]; rw [Nat.descFactorial_eq_factorial_mul_choose]

/--
theorem `iterate_derivative_mul` / 定理 `iterate_derivative_mul`

English:
theorem iterate_derivative_mul
  given: {n} (p q : R[X])
  proof: by
  induction n with
  | zero =>
    simp [Finset.range]
  | succ n IH =>
    calc
      derivative^[n + 1] (p * q) =
          derivative (∑ k in range n.succ,
              n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
        rw [Function.iterate_succ_apply']; rw [IH]
      _ = (

中文:
定理 iterate_derivative_mul
  条件: {n} (p q : R[X])
  证明: by
  induction n with
  | zero =>
    simp [Finset.range]
  | succ n IH =>
    calc
      derivative^[n + 1] (p * q) =
          derivative (∑ k in range n.succ,
              n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
        rw [Function.iterate_succ_apply']; rw [IH]
      _ = (

Depends on / 依赖: Finset, Finset.range, Function, Function.iterate_succ_apply, Nat.succ_eq_add_one, derivative, derivative_mul, derivative_natCast, iterate_succ_apply, n.choose, n.succ, nsmul_eq_mul, succ_eq_add_one, zero_mu
-/
theorem iterate_derivative_mul {n} (p q : R[X]) :
    derivative^[n] (p * q) =
      ∑ k in range n.succ, (n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
  induction n with
  | zero =>
    simp [Finset.range]
  | succ n IH =>
    calc
      derivative^[n + 1] (p * q) =
          derivative (∑ k in range n.succ,
              n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
        rw [Function.iterate_succ_apply']; rw [IH]
      _ = (∑ k in range n.succ,
            n.choose k • (derivative^[n - k + 1] p * derivative^[k] q)) +
          ∑ k in range n.succ,
            n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) := by
        simp only [Nat.succ_eq_add_one, nsmul_eq_mul, derivative_mul, derivative_natCast, zero_mul,
          derivative_sum, zero_add, Function.iterate_succ', Function.comp_apply]
        simp_rw [mul_add, sum_add_distrib]
      _ = (∑ k in range n.succ,
                n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
              1 • (derivative^[n + 1] p * derivative^[0] q) +
            ∑ k in range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) :=
        ?_
      _ = ((∑ k in range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q)) +
              ∑ k in range n.succ,
                n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
            1 • (derivative^[n + 1] p * derivative^[0] q) := by
        rw [add_comm]; rw [add_assoc]
      _ = (∑ i in range n.succ,
              (n + 1).choose (i + 1) • (derivative^[n + 1 - (i + 1)] p * derivative^[i + 1] q)) +
            1 • (derivative^[n + 1] p * derivative^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k in range n.succ.succ,
            n.succ.choose k • (derivative^[n.succ - k] p * derivative^[k] q) := by
        rw [sum_range_succ' _ n.succ]; rw [Nat.choose_zero_right]; rw [tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      lia
    · rw [Nat.choose_zero_right, tsub_zero]

/--
Iterated derivatives as a finite support function.
-/
@[simps! apply_apply]
/--
Definition of `derivativeFinsupp` / `derivativeFinsupp` 的定义

English:
definition derivativeFinsupp
  signature: : R[X] ->ₗ[R] Nat ->₀ R[X] where
  body: .onFinset (range (p.natDegree + 1)) (derivative^[·] p) fun i => by
    contrapose; simp_all [iterate_derivative_eq_zero]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

中文:
定义 derivativeFinsupp
  签名: : R[X] ->ₗ[R] 自然数 ->₀ R[X] where
  定义体: .onFinset (range (p.natDegree + 1)) (derivative^[·] p) fun i => by
    contrapose; simp_all [iterate_derivative_eq_zero]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: contrapose, derivative, iterate_derivative_eq_zero, map_add, map_smul, natDegree, onFinset, p.natDegree
-/
noncomputable def derivativeFinsupp : R[X] ->ₗ[R] Nat ->₀ R[X] where
  toFun p := .onFinset (range (p.natDegree + 1)) (derivative^[·] p) fun i => by
    contrapose; simp_all [iterate_derivative_eq_zero]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/--
theorem `support_derivativeFinsupp_subset_range` / 定理 `support_derivativeFinsupp_subset_range`

English:
theorem support_derivativeFinsupp_subset_range
  given: {p : R[X]} {n : Nat} (h : p.natDegree < n)
  proof: by
  dsimp [derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset_range.mpr h)

@[simp]

中文:
定理 support_derivativeFinsupp_subset_range
  条件: {p : R[X]} {n : 自然数} (h : p.natDegree < n)
  证明: by
  dsimp [derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset_range.mpr h)

@[simp]

Depends on / 依赖: Finset, Finset.range_subset_range.mpr, Finsupp, Finsupp.support_onFinset_subset.trans, derivativeFinsupp, range_subset_range, support_onFinset_subset
-/
theorem support_derivativeFinsupp_subset_range {p : R[X]} {n : Nat} (h : p.natDegree < n) :
    (derivativeFinsupp p).support subseteq range n := by
  dsimp [derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset_range.mpr h)

@[simp]
/--
theorem `derivativeFinsupp_C` / 定理 `derivativeFinsupp_C`

English:
theorem derivativeFinsupp_C
  given: (r : R)
  statement: derivativeFinsupp (C r : R[X]) = .single 0 (C r)
  proof: by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

@[simp]

中文:
定理 derivativeFinsupp_C
  条件: (r : R)
  结论: derivativeFinsupp (C r : R[X]) = .single 0 (C r)
  证明: by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

@[simp]
-/
theorem derivativeFinsupp_C (r : R) : derivativeFinsupp (C r : R[X]) = .single 0 (C r) := by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

@[simp]
/--
theorem `derivativeFinsupp_one` / 定理 `derivativeFinsupp_one`

English:
theorem derivativeFinsupp_one
  statement: derivativeFinsupp (1 : R[X]) = .single 0 1
  proof: by
  simpa using derivativeFinsupp_C (1 : R)

@[simp]

中文:
定理 derivativeFinsupp_one
  结论: derivativeFinsupp (1 : R[X]) = .single 0 1
  证明: by
  simpa using derivativeFinsupp_C (1 : R)

@[simp]

Depends on / 依赖: derivativeFinsupp_C
-/
theorem derivativeFinsupp_one : derivativeFinsupp (1 : R[X]) = .single 0 1 := by
  simpa using derivativeFinsupp_C (1 : R)

@[simp]
/--
theorem `derivativeFinsupp_X` / 定理 `derivativeFinsupp_X`

English:
theorem derivativeFinsupp_X
  statement: derivativeFinsupp (X : R[X]) = .single 0 X + .single 1 1
  proof: by
  ext i : 1
  match i with
  | 0 => simp
  | 1 => simp
  | (n + 2) => simp

中文:
定理 derivativeFinsupp_X
  结论: derivativeFinsupp (X : R[X]) = .single 0 X + .single 1 1
  证明: by
  ext i : 1
  match i with
  | 0 => simp
  | 1 => simp
  | (n + 2) => simp
-/
theorem derivativeFinsupp_X : derivativeFinsupp (X : R[X]) = .single 0 X + .single 1 1 := by
  ext i : 1
  match i with
  | 0 => simp
  | 1 => simp
  | (n + 2) => simp

/--
theorem `derivativeFinsupp_map` / 定理 `derivativeFinsupp_map`

English:
theorem derivativeFinsupp_map
  given: [Semiring S] (p : R[X]) (f : R ->+* S)
  proof: by
  ext i : 1
  simp

中文:
定理 derivativeFinsupp_map
  条件: [Semiring S] (p : R[X]) (f : R ->+* S)
  证明: by
  ext i : 1
  simp
-/
theorem derivativeFinsupp_map [Semiring S] (p : R[X]) (f : R ->+* S) :
    derivativeFinsupp (p.map f) = (derivativeFinsupp p).mapRange (·.map f) (by simp) := by
  ext i : 1
  simp

/--
theorem `derivativeFinsupp_derivative` / 定理 `derivativeFinsupp_derivative`

English:
theorem derivativeFinsupp_derivative
  given: (p : R[X])
  proof: by
  ext i : 1
  simp

中文:
定理 derivativeFinsupp_derivative
  条件: (p : R[X])
  证明: by
  ext i : 1
  simp
-/
theorem derivativeFinsupp_derivative (p : R[X]) :
    derivativeFinsupp (derivative p) =
      (derivativeFinsupp p).comapDomain Nat.succ Nat.succ_injective.injOn := by
  ext i : 1
  simp

section IsAddTorsionFree
variable [IsAddTorsionFree R]

/--
lemma `mem_support_derivative` / 引理 `mem_support_derivative`

English:
lemma mem_support_derivative
  statement: n in (derivative p).support ↔ n + 1 in p.support
  proof: by
  suffices ¬p.coeff (n + 1) * (n + 1 : Nat) = 0 ↔ coeff p (n + 1) != 0 by
    simpa only [mem_support_iff, coeff_derivative, Ne, Nat.cast_succ]
  rw [← nsmul_eq_mul']; rw [smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or]

@[simp]

中文:
引理 mem_support_derivative
  结论: n in (derivative p).support ↔ n + 1 in p.support
  证明: by
  suffices ¬p.coeff (n + 1) * (n + 1 : Nat) = 0 ↔ coeff p (n + 1) != 0 by
    simpa only [mem_support_iff, coeff_derivative, Ne, Nat.cast_succ]
  rw [← nsmul_eq_mul']; rw [smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or]

@[simp]

Depends on / 依赖: Nat.cast_succ, Nat.succ_ne_zero, cast_succ, coeff_derivative, false_or, mem_support_iff, nsmul_eq_mul, p.coeff, smul_eq_zero, succ_ne_zero
-/
lemma mem_support_derivative : n in (derivative p).support ↔ n + 1 in p.support := by
  suffices ¬p.coeff (n + 1) * (n + 1 : Nat) = 0 ↔ coeff p (n + 1) != 0 by
    simpa only [mem_support_iff, coeff_derivative, Ne, Nat.cast_succ]
  rw [← nsmul_eq_mul']; rw [smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or]

@[simp]
/--
lemma `degree_derivative` / 引理 `degree_derivative`

English:
lemma degree_derivative
  given: (hp : p.natDegree != 0)
  statement: degree (derivative p) = ↑(natDegree p - 1)
  proof: by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [mem_support_der

中文:
引理 degree_derivative
  条件: (hp : p.natDegree != 0)
  结论: degree (derivative p) = ↑(natDegree p - 1)
  证明: by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [mem_support_der

Depends on / 依赖: Finset, Finset.sup_le, WithBot, WithBot.coe_le_coe, coe_le_coe, coeff_natDegree, degree_C_mul_X_pow_le, degree_sum_le, derivative_apply, le_antisymm, le_natDegree_of_mem_supp, le_sup, le_trans, leadingCoeff_ne_zero, mem_support_derivative, mem_support_iff, sup_le, tsub_add_cancel_of_le, tsub_le_tsub_right
-/
lemma degree_derivative (hp : p.natDegree != 0) : degree (derivative p) = ↑(natDegree p - 1) := by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [mem_support_derivative]; rw [tsub_add_cancel_of_le (by lia)]; rw [mem_support_iff]; rw [coeff_natDegree]; rw [leadingCoeff_ne_zero]
    rintro rfl
    simp at hp

@[simp]
/--
lemma `natDegree_derivative` / 引理 `natDegree_derivative`

English:
lemma natDegree_derivative
  given: (p : R[X])
  statement: p.derivative.natDegree = p.natDegree - 1
  proof: by
  by_cases hp : p.natDegree = 0
  · grind [natDegree_derivative_le]
  · simp [natDegree, degree_derivative hp]

中文:
引理 natDegree_derivative
  条件: (p : R[X])
  结论: p.derivative.natDegree = p.natDegree - 1
  证明: by
  by_cases hp : p.natDegree = 0
  · grind [natDegree_derivative_le]
  · simp [natDegree, degree_derivative hp]

Depends on / 依赖: degree_derivative, natDegree, natDegree_derivative_le, p.natDegree
-/
lemma natDegree_derivative (p : R[X]) : p.derivative.natDegree = p.natDegree - 1 := by
  by_cases hp : p.natDegree = 0
  · grind [natDegree_derivative_le]
  · simp [natDegree, degree_derivative hp]

/--
lemma `derivative_eq_zero` / 引理 `derivative_eq_zero`

English:
lemma derivative_eq_zero
  statement: p.derivative = 0 ↔ p.natDegree = 0 where
  proof: by
    obtain rfl | hp' := eq_or_ne p 0
    · exact natDegree_zero
    rw [natDegree_eq_zero_iff_degree_le_zero]
    by_contra! f_nat_degree_pos
    rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
    let m := p.natDegree - 1
    have hm : m + 1 = p.natDegree := tsub_add_cancel_of_le (by lia

中文:
引理 derivative_eq_zero
  结论: p.derivative = 0 ↔ p.natDegree = 0 where
  证明: by
    obtain rfl | hp' := eq_or_ne p 0
    · exact natDegree_zero
    rw [natDegree_eq_zero_iff_degree_le_zero]
    by_contra! f_nat_degree_pos
    rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
    let m := p.natDegree - 1
    have hm : m + 1 = p.natDegree := tsub_add_cancel_of_le (by lia
-/
@[simp] lemma derivative_eq_zero : p.derivative = 0 ↔ p.natDegree = 0 where
  mp hp := by
    obtain rfl | hp' := eq_or_ne p 0
    · exact natDegree_zero
    rw [natDegree_eq_zero_iff_degree_le_zero]
    by_contra! f_nat_degree_pos
    rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
    let m := p.natDegree - 1
    have hm : m + 1 = p.natDegree := tsub_add_cancel_of_le (by lia)
    have h2 := coeff_derivative p m
    rw [Polynomial.ext_iff] at hp
    rw [hp m]; rw [coeff_zero]; rw [← Nat.cast_add_one]; rw [← nsmul_eq_mul']; rw [eq_comm]; rw [smul_eq_zero] at h2
    replace h2 := h2.resolve_left m.succ_ne_zero
    rw [hm]; rw [← leadingCoeff]; rw [leadingCoeff_eq_zero] at h2
    exact hp' h2
  mpr hp := by rw [eq_C_of_natDegree_eq_zero hp, derivative_C]

/--
lemma `derivative_ne_zero` / 引理 `derivative_ne_zero`

English:
lemma derivative_ne_zero
  statement: p.derivative != 0 ↔ p.natDegree != 0
  proof: derivative_eq_zero.ne

中文:
引理 derivative_ne_zero
  结论: p.derivative != 0 ↔ p.natDegree != 0
  证明: derivative_eq_zero.ne

Depends on / 依赖: derivative_eq_zero, derivative_eq_zero.ne
-/
lemma derivative_ne_zero : p.derivative != 0 ↔ p.natDegree != 0 := derivative_eq_zero.ne

/--
lemma `leadingCoeff_derivative` / 引理 `leadingCoeff_derivative`

English:
lemma leadingCoeff_derivative
  given: (p : R[X])
  proof: by
  by_cases hp : p.natDegree = 0
  · simp [hp]
  rw [leadingCoeff]; rw [leadingCoeff]; rw [coeff_derivative]; rw [natDegree_derivative]
  norm_cast
  congr <;> lia

@[deprecated (since := "2026-06-03")]
alias ⟨natDegree_eq_zero_of_derivative_eq_zero, _⟩ := derivative_eq_zero

中文:
引理 leadingCoeff_derivative
  条件: (p : R[X])
  证明: by
  by_cases hp : p.natDegree = 0
  · simp [hp]
  rw [leadingCoeff]; rw [leadingCoeff]; rw [coeff_derivative]; rw [natDegree_derivative]
  norm_cast
  congr <;> lia

@[deprecated (since := "2026-06-03")]
alias ⟨natDegree_eq_zero_of_derivative_eq_zero, _⟩ := derivative_eq_zero
-/
@[simp] lemma leadingCoeff_derivative (p : R[X]) :
    leadingCoeff (derivative p) = leadingCoeff p * p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [hp]
  rw [leadingCoeff]; rw [leadingCoeff]; rw [coeff_derivative]; rw [natDegree_derivative]
  norm_cast
  congr <;> lia

@[deprecated (since := "2026-06-03")]
alias ⟨natDegree_eq_zero_of_derivative_eq_zero, _⟩ := derivative_eq_zero

/--
lemma `eq_C_of_derivative_eq_zero` / 引理 `eq_C_of_derivative_eq_zero`

English:
lemma eq_C_of_derivative_eq_zero
  given: (h : derivative p = 0)
  statement: p = C (p.coeff 0)
  proof: eq_C_of_natDegree_eq_zero derivative_eq_zero.1 h

@[deprecated degree_derivative (since := "2026-06-03")]

中文:
引理 eq_C_of_derivative_eq_zero
  条件: (h : derivative p = 0)
  结论: p = C (p.coeff 0)
  证明: eq_C_of_natDegree_eq_zero derivative_eq_zero.1 h

@[deprecated degree_derivative (since := "2026-06-03")]

Depends on / 依赖: derivative_eq_zero, eq_C_of_natDegree_eq_zero
-/
lemma eq_C_of_derivative_eq_zero (h : derivative p = 0) : p = C (p.coeff 0) :=
eq_C_of_natDegree_eq_zero derivative_eq_zero.1 h

@[deprecated degree_derivative (since := "2026-06-03")]
/--
lemma `degree_derivative_eq` / 引理 `degree_derivative_eq`

English:
lemma degree_derivative_eq
  given: (p : R[X]) (hp : 0 < natDegree p)
  proof: degree_derivative (by lia)

中文:
引理 degree_derivative_eq
  条件: (p : R[X]) (hp : 0 < natDegree p)
  证明: degree_derivative (by lia)

Depends on / 依赖: degree_derivative
-/
lemma degree_derivative_eq (p : R[X]) (hp : 0 < natDegree p) :
    degree (derivative p) = (natDegree p - 1 : Nat) :=
  degree_derivative (by lia)

end IsAddTorsionFree
end Semiring

section CommSemiring

variable [CommSemiring R]

/--
theorem `derivative_pow_succ` / 定理 `derivative_pow_succ`

English:
theorem derivative_pow_succ
  given: (p : R[X]) (n : Nat)
  proof: Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ]; rw [derivative_mul]; rw [ih]; rw [Nat.add_one]; rw [mul_right_comm]; rw [C_add]; rw [add_mul]; rw [add_mul]; rw [pow_succ]; rw [← mul_assoc]; rw [C_1]; rw [one_mul]; simp [add_mul]

中文:
定理 derivative_pow_succ
  条件: (p : R[X]) (n : 自然数)
  证明: Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ]; rw [derivative_mul]; rw [ih]; rw [Nat.add_one]; rw [mul_right_comm]; rw [C_add]; rw [add_mul]; rw [add_mul]; rw [pow_succ]; rw [← mul_assoc]; rw [C_1]; rw [one_mul]; simp [add_mul]

Depends on / 依赖: C_add, Nat.add_one, Nat.recOn, add_mul, add_one, derivative_mul, mul_assoc, mul_right_comm, one_mul, pow_succ
-/
theorem derivative_pow_succ (p : R[X]) (n : Nat) :
    derivative (p ^ (n + 1)) = C (n + 1 : R) * p ^ n * derivative p :=
  Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ]; rw [derivative_mul]; rw [ih]; rw [Nat.add_one]; rw [mul_right_comm]; rw [C_add]; rw [add_mul]; rw [add_mul]; rw [pow_succ]; rw [← mul_assoc]; rw [C_1]; rw [one_mul]; simp [add_mul]

/--
theorem `derivative_pow` / 定理 `derivative_pow`

English:
theorem derivative_pow
  given: (p : R[X]) (n : Nat)
  proof: Nat.casesOn n (by simp) fun n =>
    by rw [p.derivative_pow_succ n, Nat.add_one_sub_one, n.cast_succ]

中文:
定理 derivative_pow
  条件: (p : R[X]) (n : 自然数)
  证明: Nat.casesOn n (by simp) fun n =>
    by rw [p.derivative_pow_succ n, Nat.add_one_sub_one, n.cast_succ]

Depends on / 依赖: Nat.add_one_sub_one, Nat.casesOn, add_one_sub_one, casesOn, cast_succ, derivative_pow_succ, n.cast_succ, p.derivative_pow_succ
-/
theorem derivative_pow (p : R[X]) (n : Nat) :
    derivative (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p :=
  Nat.casesOn n (by simp) fun n =>
    by rw [p.derivative_pow_succ n, Nat.add_one_sub_one, n.cast_succ]

/--
theorem `derivative_sq` / 定理 `derivative_sq`

English:
theorem derivative_sq
  given: (p : R[X])
  statement: derivative (p ^ 2) = C 2 * p * derivative p
  proof: by
  rw [derivative_pow_succ]; rw [Nat.cast_one]; rw [one_add_one_eq_two]; rw [pow_one]

中文:
定理 derivative_sq
  条件: (p : R[X])
  结论: derivative (p ^ 2) = C 2 * p * derivative p
  证明: by
  rw [derivative_pow_succ]; rw [Nat.cast_one]; rw [one_add_one_eq_two]; rw [pow_one]

Depends on / 依赖: Nat.cast_one, cast_one, derivative_pow_succ, one_add_one_eq_two, pow_one
-/
theorem derivative_sq (p : R[X]) : derivative (p ^ 2) = C 2 * p * derivative p := by
  rw [derivative_pow_succ]; rw [Nat.cast_one]; rw [one_add_one_eq_two]; rw [pow_one]

/--
theorem `pow_sub_one_dvd_derivative_of_pow_dvd` / 定理 `pow_sub_one_dvd_derivative_of_pow_dvd`

English:
theorem pow_sub_one_dvd_derivative_of_pow_dvd
  statement: {p q : R[X]} {n : Nat}
  proof: by
  obtain ⟨r, rfl⟩ := dvd
  rw [derivative_mul]; rw [derivative_pow]
  exact (((dvd_mul_left _ _).mul_right _).mul_right _).add ((pow_dvd_pow q n.pred_le).mul_right _)

中文:
定理 pow_sub_one_dvd_derivative_of_pow_dvd
  结论: {p q : R[X]} {n : 自然数}
  证明: by
  obtain ⟨r, rfl⟩ := dvd
  rw [derivative_mul]; rw [derivative_pow]
  exact (((dvd_mul_left _ _).mul_right _).mul_right _).add ((pow_dvd_pow q n.pred_le).mul_right _)

Depends on / 依赖: derivative_mul, derivative_pow, dvd_mul_left, mul_right, n.pred_le, pow_dvd_pow, pred_le
-/
theorem pow_sub_one_dvd_derivative_of_pow_dvd {p q : R[X]} {n : Nat}
    (dvd : q ^ n ∣ p) : q ^ (n - 1) ∣ derivative p := by
  obtain ⟨r, rfl⟩ := dvd
  rw [derivative_mul]; rw [derivative_pow]
  exact (((dvd_mul_left _ _).mul_right _).mul_right _).add ((pow_dvd_pow q n.pred_le).mul_right _)

/--
theorem `pow_sub_dvd_iterate_derivative_of_pow_dvd` / 定理 `pow_sub_dvd_iterate_derivative_of_pow_dvd`

English:
theorem pow_sub_dvd_iterate_derivative_of_pow_dvd
  statement: {p q : R[X]} {n : Nat} (m : Nat)
  proof: by
  induction m generalizing p with
  | zero => simpa
  | succ m ih =>
    rw [Nat.sub_succ]; rw [Function.iterate_succ']
    exact pow_sub_one_dvd_derivative_of_pow_dvd (ih dvd)

中文:
定理 pow_sub_dvd_iterate_derivative_of_pow_dvd
  结论: {p q : R[X]} {n : 自然数} (m : 自然数)
  证明: by
  induction m generalizing p with
  | zero => simpa
  | succ m ih =>
    rw [Nat.sub_succ]; rw [Function.iterate_succ']
    exact pow_sub_one_dvd_derivative_of_pow_dvd (ih dvd)

Depends on / 依赖: Function, Function.iterate_succ, Nat.sub_succ, generalizing, iterate_succ, pow_sub_one_dvd_derivative_of_pow_dvd, sub_succ
-/
theorem pow_sub_dvd_iterate_derivative_of_pow_dvd {p q : R[X]} {n : Nat} (m : Nat)
    (dvd : q ^ n ∣ p) : q ^ (n - m) ∣ derivative^[m] p := by
  induction m generalizing p with
  | zero => simpa
  | succ m ih =>
    rw [Nat.sub_succ]; rw [Function.iterate_succ']
    exact pow_sub_one_dvd_derivative_of_pow_dvd (ih dvd)

/--
theorem `pow_sub_dvd_iterate_derivative_pow` / 定理 `pow_sub_dvd_iterate_derivative_pow`

English:
theorem pow_sub_dvd_iterate_derivative_pow
  given: (p : R[X]) (n m : Nat)
  proof: pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

中文:
定理 pow_sub_dvd_iterate_derivative_pow
  条件: (p : R[X]) (n m : 自然数)
  证明: pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

Depends on / 依赖: RingHomClass, RingHomClass.toRingHom, dvd_rfl, pow_sub_dvd_iterate_derivative_of_pow_dvd, toRingHom
-/
theorem pow_sub_dvd_iterate_derivative_pow (p : R[X]) (n m : Nat) :
    p ^ (n - m) ∣ derivative^[m] (p ^ n) := pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

/--
theorem `dvd_iterate_derivative_pow` / 定理 `dvd_iterate_derivative_pow`

English:
theorem dvd_iterate_derivative_pow
  given: (f : R[X]) (n : Nat) {m : Nat} (c : R) (hm : m != 0)
  proof: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply]; rw [derivative_pow]; rw [mul_assoc]; rw [C_eq_natCast]; rw [iterate_derivative_natCast_mul]; rw [eval_mul]; rw [eval_natCast]
  exact dvd_mul_right _ _

中文:
定理 dvd_iterate_derivative_pow
  条件: (f : R[X]) (n : 自然数) {m : 自然数} (c : R) (hm : m != 0)
  证明: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply]; rw [derivative_pow]; rw [mul_assoc]; rw [C_eq_natCast]; rw [iterate_derivative_natCast_mul]; rw [eval_mul]; rw [eval_natCast]
  exact dvd_mul_right _ _

Depends on / 依赖: C_eq_natCast, Function, Function.iterate_succ_apply, Nat.exists_eq_succ_of_ne_zero, NonUnitalRingHomClass, RingHomClass, RingHomClass.toNonUnitalRingHomClass, derivative_pow, dvd_mul_right, eval_mul, eval_natCast, exists_eq_succ_of_ne_zero, iterate_derivative_natCast_mul, iterate_succ_apply, mul_assoc, toNonUnitalRingHomClass
-/
theorem dvd_iterate_derivative_pow (f : R[X]) (n : Nat) {m : Nat} (c : R) (hm : m != 0) :
    (n : R) ∣ eval c (derivative^[m] (f ^ n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply]; rw [derivative_pow]; rw [mul_assoc]; rw [C_eq_natCast]; rw [iterate_derivative_natCast_mul]; rw [eval_mul]; rw [eval_natCast]
  exact dvd_mul_right _ _

/--
theorem `iterate_derivative_X_pow_eq_natCast_mul` / 定理 `iterate_derivative_X_pow_eq_natCast_mul`

English:
theorem iterate_derivative_X_pow_eq_natCast_mul
  given: (n k : Nat)
  proof: by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [tsub_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply']; rw [ih]; rw [derivative_natCast_mul]; rw [derivative_X_pow]; rw [C_eq_natCast]; rw [Nat.descFac

中文:
定理 iterate_derivative_X_pow_eq_natCast_mul
  条件: (n k : 自然数)
  证明: by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [tsub_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply']; rw [ih]; rw [derivative_natCast_mul]; rw [derivative_X_pow]; rw [C_eq_natCast]; rw [Nat.descFac

Depends on / 依赖: C_eq_natCast, Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.cast_mul, Nat.cast_one, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_sub, cast_mul, cast_one, derivative_X_pow, derivative_natCast_mul, descFactorial_succ, descFactorial_zero, iterate_succ_apply, iterate_zero_apply, mul_assoc, mul_left_comm, one_mul
-/
theorem iterate_derivative_X_pow_eq_natCast_mul (n k : Nat) :
    derivative^[k] (X ^ n : R[X]) = ↑(Nat.descFactorial n k : R[X]) * X ^ (n - k) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [tsub_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply']; rw [ih]; rw [derivative_natCast_mul]; rw [derivative_X_pow]; rw [C_eq_natCast]; rw [Nat.descFactorial_succ]; rw [Nat.sub_sub]; rw [Nat.cast_mul]
    simp [mul_assoc, mul_left_comm]

/--
theorem `iterate_derivative_X_pow_eq_C_mul` / 定理 `iterate_derivative_X_pow_eq_C_mul`

English:
theorem iterate_derivative_X_pow_eq_C_mul
  given: (n k : Nat)
  proof: by
  rw [iterate_derivative_X_pow_eq_natCast_mul n k]; rw [C_eq_natCast]

中文:
定理 iterate_derivative_X_pow_eq_C_mul
  条件: (n k : 自然数)
  证明: by
  rw [iterate_derivative_X_pow_eq_natCast_mul n k]; rw [C_eq_natCast]

Depends on / 依赖: C_eq_natCast, iterate_derivative_X_pow_eq_natCast_mul
-/
theorem iterate_derivative_X_pow_eq_C_mul (n k : Nat) :
    derivative^[k] (X ^ n : R[X]) = C (Nat.descFactorial n k : R) * X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_natCast_mul n k]; rw [C_eq_natCast]

/--
theorem `iterate_derivative_X_pow_eq_smul` / 定理 `iterate_derivative_X_pow_eq_smul`

English:
theorem iterate_derivative_X_pow_eq_smul
  given: (n : Nat) (k : Nat)
  proof: by
  rw [iterate_derivative_X_pow_eq_C_mul n k]; rw [smul_eq_C_mul]

中文:
定理 iterate_derivative_X_pow_eq_smul
  条件: (n : 自然数) (k : 自然数)
  证明: by
  rw [iterate_derivative_X_pow_eq_C_mul n k]; rw [smul_eq_C_mul]

Depends on / 依赖: iterate_derivative_X_pow_eq_C_mul, smul_eq_C_mul
-/
theorem iterate_derivative_X_pow_eq_smul (n : Nat) (k : Nat) :
    derivative^[k] (X ^ n : R[X]) = (Nat.descFactorial n k : R) • X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_C_mul n k]; rw [smul_eq_C_mul]

/--
theorem `derivative_X_add_C_pow` / 定理 `derivative_X_add_C_pow`

English:
theorem derivative_X_add_C_pow
  given: (c : R) (m : Nat)
  proof: by
  rw [derivative_pow]; rw [derivative_X_add_C]; rw [mul_one]

中文:
定理 derivative_X_add_C_pow
  条件: (c : R) (m : 自然数)
  证明: by
  rw [derivative_pow]; rw [derivative_X_add_C]; rw [mul_one]

Depends on / 依赖: derivative_X_add_C, derivative_pow, mul_one
-/
theorem derivative_X_add_C_pow (c : R) (m : Nat) :
    derivative ((X + C c) ^ m) = C (m : R) * (X + C c) ^ (m - 1) := by
  rw [derivative_pow]; rw [derivative_X_add_C]; rw [mul_one]

/--
theorem `derivative_X_add_C_sq` / 定理 `derivative_X_add_C_sq`

English:
theorem derivative_X_add_C_sq
  given: (c : R)
  statement: derivative ((X + C c) ^ 2) = C 2 * (X + C c)
  proof: by
  rw [derivative_sq]; rw [derivative_X_add_C]; rw [mul_one]

中文:
定理 derivative_X_add_C_sq
  条件: (c : R)
  结论: derivative ((X + C c) ^ 2) = C 2 * (X + C c)
  证明: by
  rw [derivative_sq]; rw [derivative_X_add_C]; rw [mul_one]

Depends on / 依赖: derivative_X_add_C, derivative_sq, mul_one
-/
theorem derivative_X_add_C_sq (c : R) : derivative ((X + C c) ^ 2) = C 2 * (X + C c) := by
  rw [derivative_sq]; rw [derivative_X_add_C]; rw [mul_one]

/--
theorem `iterate_derivative_X_add_pow` / 定理 `iterate_derivative_X_add_pow`

English:
theorem iterate_derivative_X_add_pow
  given: (n k : Nat) (c : R)
  proof: by
  induction k with
  | zero => simp
  | succ k IH =>
      simp [Nat.sub_succ', Function.iterate_succ_apply', IH, derivative_X_add_C_pow]
      ring

中文:
定理 iterate_derivative_X_add_pow
  条件: (n k : 自然数) (c : R)
  证明: by
  induction k with
  | zero => simp
  | succ k IH =>
      simp [Nat.sub_succ', Function.iterate_succ_apply', IH, derivative_X_add_C_pow]
      ring

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.sub_succ, derivative_X_add_C_pow, iterate_succ_apply, sub_succ
-/
theorem iterate_derivative_X_add_pow (n k : Nat) (c : R) :
    derivative^[k] ((X + C c) ^ n) = Nat.descFactorial n k • (X + C c) ^ (n - k) := by
  induction k with
  | zero => simp
  | succ k IH =>
      simp [Nat.sub_succ', Function.iterate_succ_apply', IH, derivative_X_add_C_pow]
      ring

/--
theorem `iterate_derivative_mul_X_pow` / 定理 `iterate_derivative_mul_X_pow`

English:
theorem iterate_derivative_mul_X_pow
  given: (n m : Nat) (p : R[X])
  proof: by
  have hsum : derivative^[n] (p * X ^ m) =
      ∑ k in range n.succ,
        (n.choose k * m.descFactorial k) • (derivative^[n - k] p * X ^ (m - k)) := by
    simp_rw [iterate_derivative_mul, iterate_derivative_X_pow_eq_smul, mul_smul]
    congr! 2 with k hk
    norm_cast
    ring
  rw [hsum]
  

中文:
定理 iterate_derivative_mul_X_pow
  条件: (n m : 自然数) (p : R[X])
  证明: by
  have hsum : derivative^[n] (p * X ^ m) =
      ∑ k in range n.succ,
        (n.choose k * m.descFactorial k) • (derivative^[n - k] p * X ^ (m - k)) := by
    simp_rw [iterate_derivative_mul, iterate_derivative_X_pow_eq_smul, mul_smul]
    congr! 2 with k hk
    norm_cast
    ring
  rw [hsum]
  

Depends on / 依赖: Nat.choose_eq_zero_of_lt, Nat.descFactorial_eq_zero_iff_, choose_eq_zero_of_lt, derivative, descFactorial, descFactorial_eq_zero_iff_, iterate_derivative_X_pow_eq_smul, iterate_derivative_mul, le_or_gt, m.descFactorial, mul_smul, n.choose, n.succ, replace, simp_rw, sum_congr_of_eq_on_inter
-/
theorem iterate_derivative_mul_X_pow (n m : Nat) (p : R[X]) :
    derivative^[n] (p * X ^ m) =
      ∑ k in range (min m n).succ,
        (n.choose k * m.descFactorial k) • (derivative^[n - k] p * X ^ (m - k)) := by
  have hsum : derivative^[n] (p * X ^ m) =
      ∑ k in range n.succ,
        (n.choose k * m.descFactorial k) • (derivative^[n - k] p * X ^ (m - k)) := by
    simp_rw [iterate_derivative_mul, iterate_derivative_X_pow_eq_smul, mul_smul]
    congr! 2 with k hk
    norm_cast
    ring
  rw [hsum]
  refine sum_congr_of_eq_on_inter (fun k hk hk' => ?_) (by simp_all) (by simp)
  rcases le_or_gt k m with hkm | hkm
  · replace hk' : n < k := by simpa [hkm] using hk'
    simp [Nat.choose_eq_zero_of_lt hk']
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkm]

/--
theorem `iterate_derivative_mul_X` / 定理 `iterate_derivative_mul_X`

English:
theorem iterate_derivative_mul_X
  given: {n : Nat} (p : R[X])
  proof: by
  convert! p.iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

中文:
定理 iterate_derivative_mul_X
  条件: {n : 自然数} (p : R[X])
  证明: by
  convert! p.iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

Depends on / 依赖: convert, iterate_derivative_mul_X_pow, p.iterate_derivative_mul_X_pow, sum_range_succ
-/
theorem iterate_derivative_mul_X {n : Nat} (p : R[X]) :
    derivative^[n] (p * X) = (derivative^[n] p) * X + n • derivative^[n - 1] p := by
  convert! p.iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

/--
theorem `iterate_derivative_derivative_mul_X` / 定理 `iterate_derivative_derivative_mul_X`

English:
theorem iterate_derivative_derivative_mul_X
  given: {n : Nat} (p : R[X])
  proof: by
  convert! (derivative p).iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

中文:
定理 iterate_derivative_derivative_mul_X
  条件: {n : 自然数} (p : R[X])
  证明: by
  convert! (derivative p).iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

Depends on / 依赖: convert, derivative, iterate_derivative_mul_X_pow, sum_range_succ
-/
theorem iterate_derivative_derivative_mul_X {n : Nat} (p : R[X]) :
    derivative^[n] (derivative p * X) = (derivative^[n + 1] p) * X + n • derivative^[n] p := by
  convert! (derivative p).iterate_derivative_mul_X_pow n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

/--
theorem `iterate_derivative_derivative_mul_X_sq` / 定理 `iterate_derivative_derivative_mul_X_sq`

English:
theorem iterate_derivative_derivative_mul_X_sq
  given: {n : Nat} (p : R[X])
  proof: by
  convert! (derivative^[2] p).iterate_derivative_mul_X_pow n 2
  rcases n with rfl | n; · simp
  rcases n with rfl | n; · simp [sum_range_succ, ← mul_assoc]
  suffices ((n + 1 + 1) * (n + 1) / 2) * 2 = (n + 1 + 1) * (n + 1) by
    simp -implicitDefEqProofs [this, -nsmul_eq_mul, sum_range_succ, Na

中文:
定理 iterate_derivative_derivative_mul_X_sq
  条件: {n : 自然数} (p : R[X])
  证明: by
  convert! (derivative^[2] p).iterate_derivative_mul_X_pow n 2
  rcases n with rfl | n; · simp
  rcases n with rfl | n; · simp [sum_range_succ, ← mul_assoc]
  suffices ((n + 1 + 1) * (n + 1) / 2) * 2 = (n + 1 + 1) * (n + 1) by
    simp -implicitDefEqProofs [this, -nsmul_eq_mul, sum_range_succ, Na

Depends on / 依赖: Nat.choose_two_right, Nat.div_mul_cancel, Nat.two_dvd_mul_add_one, choose_two_right, convert, derivative, div_mul_cancel, implicitDefEqProofs, iterate_derivative_mul_X_pow, mul_assoc, mul_comm, nsmul_eq_mul, sum_range_succ, two_dvd_mul_add_one
-/
theorem iterate_derivative_derivative_mul_X_sq {n : Nat} (p : R[X]) :
    derivative^[n] (derivative^[2] p * X ^ 2) =
      (derivative^[n + 2] p) * X ^ 2 + (2 * n) • (derivative^[n + 1] p) * X +
        (n * (n - 1)) • derivative^[n] p := by
  convert! (derivative^[2] p).iterate_derivative_mul_X_pow n 2
  rcases n with rfl | n; · simp
  rcases n with rfl | n; · simp [sum_range_succ, ← mul_assoc]
  suffices ((n + 1 + 1) * (n + 1) / 2) * 2 = (n + 1 + 1) * (n + 1) by
    simp -implicitDefEqProofs [this, -nsmul_eq_mul, sum_range_succ, Nat.choose_two_right]
    ring
  rw [mul_comm (n + 1 + 1)]
  exact Nat.div_mul_cancel (Nat.two_dvd_mul_add_one _)

/--
theorem `derivative_comp` / 定理 `derivative_comp`

English:
theorem derivative_comp
  given: (p q : R[X])
  proof: by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_natCast, zero_add, map_mul]
    ring

中文:
定理 derivative_comp
  条件: (p q : R[X])
  证明: by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_natCast, zero_add, map_mul]
    ring

Depends on / 依赖: C_eq_natCast, Polynomial, Polynomial.induction_on, derivative_C, derivative_monomial, derivative_mul, derivative_pow, induction_on, map_mul, monomial_comp, mul_add, zero_add, zero_mul
-/
theorem derivative_comp (p q : R[X]) :
    derivative (p.comp q) = derivative q * p.derivative.comp q := by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_natCast, zero_add, map_mul]
    ring

/--
theorem `derivative_eval₂_C` / 定理 `derivative_eval₂_C`

English:
theorem derivative_eval₂_C
  given: (p q : R[X])
  proof: Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add]; rw [derivative_add]; rw [ih₁]; rw [ih₂]; rw [derivative_add]; rw [eval₂_add]; rw [add_mul])
    fun n r ih => by
    rw [pow_succ]; rw [← mul_assoc]; rw [eval₂_

中文:
定理 derivative_eval₂_C
  条件: (p q : R[X])
  证明: Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add]; rw [derivative_add]; rw [ih₁]; rw [ih₂]; rw [derivative_add]; rw [eval₂_add]; rw [add_mul])
    fun n r ih => by
    rw [pow_succ]; rw [← mul_assoc]; rw [eval₂_

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_mul, derivative_C, derivative_X, derivative_add, derivative_mul, induction_on, mul_assoc, mul_one, mul_right_comm, pow_succ, zero_mul
-/
theorem derivative_eval₂_C (p q : R[X]) :
    derivative (p.eval₂ C q) = p.derivative.eval₂ C q * derivative q :=
  Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add]; rw [derivative_add]; rw [ih₁]; rw [ih₂]; rw [derivative_add]; rw [eval₂_add]; rw [add_mul])
    fun n r ih => by
    rw [pow_succ]; rw [← mul_assoc]; rw [eval₂_mul]; rw [eval₂_X]; rw [derivative_mul]; rw [ih]; rw [@derivative_mul _ _ _ X]; rw [derivative_X]; rw [mul_one]; rw [eval₂_add]; rw [@eval₂_mul _ _ _ _ X]; rw [eval₂_X]; rw [add_mul]; rw [mul_right_comm]

/--
theorem `derivative_prod` / 定理 `derivative_prod`

English:
theorem derivative_prod
  given: [DecidableEq ι] {s : Multiset ι} {f : ι -> R[X]}
  proof: by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [derivative_mul]; rw [Multiset.map_cons _ i s]; rw [Multiset.sum_cons]; rw [Multiset.erase_cons_head]; rw [mul_comm (derivative (f i))]
  congr
  rw [h]; rw [← AddMonoidHom.coe_mulLeft

中文:
定理 derivative_prod
  条件: [DecidableEq ι] {s : Multiset ι} {f : ι -> R[X]}
  证明: by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [derivative_mul]; rw [Multiset.map_cons _ i s]; rw [Multiset.sum_cons]; rw [Multiset.erase_cons_head]; rw [mul_comm (derivative (f i))]
  congr
  rw [h]; rw [← AddMonoidHom.coe_mulLeft

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_mulLeft, AddMonoidHom.mulLeft, Function, Function.comp_apply, Multiset, Multiset.erase_cons_head, Multiset.induction_on, Multiset.map_congr, Multiset.map_cons, Multiset.map_map, Multiset.prod_cons, Multiset.sum_cons, coe_mulLeft, comp_apply, congr_arg, derivative, derivative_mul, erase_cons_head, induction_on
-/
theorem derivative_prod [DecidableEq ι] {s : Multiset ι} {f : ι -> R[X]} :
    derivative (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * derivative (f i)) s).sum := by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [derivative_mul]; rw [Multiset.map_cons _ i s]; rw [Multiset.sum_cons]; rw [Multiset.erase_cons_head]; rw [mul_comm (derivative (f i))]
  congr
  rw [h]; rw [← AddMonoidHom.coe_mulLeft]; rw [(AddMonoidHom.mulLeft (f i)).map_multiset_sum _]; rw [AddMonoidHom.coe_mulLeft]
  simp only [Function.comp_apply, Multiset.map_map]
  refine congr_arg _ (Multiset.map_congr rfl fun j hj => ?_)
  rw [← mul_assoc]; rw [← Multiset.prod_cons]; rw [← Multiset.map_cons]
  by_cases hij : i = j
  · simp [hij, Multiset.cons_erase hj]
  · simp [hij]

/--
theorem `derivative_prod_finset` / 定理 `derivative_prod_finset`

English:
theorem derivative_prod_finset
  given: [DecidableEq ι] {s : Finset ι} {f : ι -> R[X]}
  proof: by
  simpa using! derivative_prod

中文:
定理 derivative_prod_finset
  条件: [DecidableEq ι] {s : Finset ι} {f : ι -> R[X]}
  证明: by
  simpa using! derivative_prod

Depends on / 依赖: derivative_prod
-/
theorem derivative_prod_finset [DecidableEq ι] {s : Finset ι} {f : ι -> R[X]} :
    derivative (∏ b in s, f b) =
      ∑ a in s, (∏ b in s.erase a, f b) * derivative (f a) := by
  simpa using! derivative_prod

end CommSemiring

section Ring

variable [Ring R]

@[simp]
/--
theorem `derivative_neg` / 定理 `derivative_neg`

English:
theorem derivative_neg
  given: (f : R[X])
  statement: derivative (-f) = -derivative f
  proof: map_neg derivative f

中文:
定理 derivative_neg
  条件: (f : R[X])
  结论: derivative (-f) = -derivative f
  证明: map_neg derivative f

Depends on / 依赖: derivative, map_neg
-/
theorem derivative_neg (f : R[X]) : derivative (-f) = -derivative f :=
  map_neg derivative f

/--
theorem `iterate_derivative_neg` / 定理 `iterate_derivative_neg`

English:
theorem iterate_derivative_neg
  given: {f : R[X]} {k : Nat}
  statement: derivative^[k] (-f) = -derivative^[k] f
  proof: iterate_map_neg derivative k f

@[simp]

中文:
定理 iterate_derivative_neg
  条件: {f : R[X]} {k : 自然数}
  结论: derivative^[k] (-f) = -derivative^[k] f
  证明: iterate_map_neg derivative k f

@[simp]

Depends on / 依赖: derivative, iterate_map_neg
-/
theorem iterate_derivative_neg {f : R[X]} {k : Nat} : derivative^[k] (-f) = -derivative^[k] f :=
  iterate_map_neg derivative k f

@[simp]
/--
theorem `derivative_sub` / 定理 `derivative_sub`

English:
theorem derivative_sub
  given: {f g : R[X]}
  statement: derivative (f - g) = derivative f - derivative g
  proof: map_sub derivative f g

中文:
定理 derivative_sub
  条件: {f g : R[X]}
  结论: derivative (f - g) = derivative f - derivative g
  证明: map_sub derivative f g

Depends on / 依赖: derivative, map_sub
-/
theorem derivative_sub {f g : R[X]} : derivative (f - g) = derivative f - derivative g :=
  map_sub derivative f g

/--
theorem `derivative_X_sub_C` / 定理 `derivative_X_sub_C`

English:
theorem derivative_X_sub_C
  given: (c : R)
  statement: derivative (X - C c) = 1
  proof: by
  rw [derivative_sub]; rw [derivative_X]; rw [derivative_C]; rw [sub_zero]

中文:
定理 derivative_X_sub_C
  条件: (c : R)
  结论: derivative (X - C c) = 1
  证明: by
  rw [derivative_sub]; rw [derivative_X]; rw [derivative_C]; rw [sub_zero]

Depends on / 依赖: derivative_C, derivative_X, derivative_sub, sub_zero
-/
theorem derivative_X_sub_C (c : R) : derivative (X - C c) = 1 := by
  rw [derivative_sub]; rw [derivative_X]; rw [derivative_C]; rw [sub_zero]

/--
theorem `iterate_derivative_sub` / 定理 `iterate_derivative_sub`

English:
theorem iterate_derivative_sub
  given: {k : Nat} {f g : R[X]}
  proof: iterate_map_sub derivative k f g

@[simp]

中文:
定理 iterate_derivative_sub
  条件: {k : 自然数} {f g : R[X]}
  证明: iterate_map_sub derivative k f g

@[simp]

Depends on / 依赖: derivative, iterate_map_sub
-/
theorem iterate_derivative_sub {k : Nat} {f g : R[X]} :
    derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g :=
  iterate_map_sub derivative k f g

@[simp]
/--
theorem `derivative_intCast` / 定理 `derivative_intCast`

English:
theorem derivative_intCast
  given: {n : Int}
  statement: derivative (n : R[X]) = 0
  proof: by
  rw [← C_eq_intCast n]
  exact derivative_C

中文:
定理 derivative_intCast
  条件: {n : 整数}
  结论: derivative (n : R[X]) = 0
  证明: by
  rw [← C_eq_intCast n]
  exact derivative_C

Depends on / 依赖: C_eq_intCast, derivative_C
-/
theorem derivative_intCast {n : Int} : derivative (n : R[X]) = 0 := by
  rw [← C_eq_intCast n]
  exact derivative_C

/--
theorem `derivative_intCast_mul` / 定理 `derivative_intCast_mul`

English:
theorem derivative_intCast_mul
  given: {n : Int} {f : R[X]}
  statement: derivative ((n : R[X]) * f) =
  proof: by
  simp

@[simp]

中文:
定理 derivative_intCast_mul
  条件: {n : 整数} {f : R[X]}
  结论: derivative ((n : R[X]) * f) =
  证明: by
  simp

@[simp]
-/
theorem derivative_intCast_mul {n : Int} {f : R[X]} : derivative ((n : R[X]) * f) =
    n * derivative f := by
  simp

@[simp]
/--
theorem `iterate_derivative_intCast_mul` / 定理 `iterate_derivative_intCast_mul`

English:
theorem iterate_derivative_intCast_mul
  given: {n : Int} {k : Nat} {f : R[X]}
  proof: by
  induction k generalizing f <;> simp [*]

中文:
定理 iterate_derivative_intCast_mul
  条件: {n : 整数} {k : 自然数} {f : R[X]}
  证明: by
  induction k generalizing f <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem iterate_derivative_intCast_mul {n : Int} {k : Nat} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction k generalizing f <;> simp [*]

end Ring

section CommRing

variable [CommRing R]

/--
theorem `derivative_comp_one_sub_X` / 定理 `derivative_comp_one_sub_X`

English:
theorem derivative_comp_one_sub_X
  given: (p : R[X])
  proof: by simp [derivative_comp]

@[simp]

中文:
定理 derivative_comp_one_sub_X
  条件: (p : R[X])
  证明: by simp [derivative_comp]

@[simp]

Depends on / 依赖: derivative_comp
-/
theorem derivative_comp_one_sub_X (p : R[X]) :
    derivative (p.comp (1 - X)) = -p.derivative.comp (1 - X) := by simp [derivative_comp]

@[simp]
/--
theorem `iterate_derivative_comp_one_sub_X` / 定理 `iterate_derivative_comp_one_sub_X`

English:
theorem iterate_derivative_comp_one_sub_X
  given: (p : R[X]) (k : Nat)
  proof: by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

中文:
定理 iterate_derivative_comp_one_sub_X
  条件: (p : R[X]) (k : 自然数)
  证明: by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

Depends on / 依赖: derivative, derivative_comp, generalizing, pow_succ
-/
theorem iterate_derivative_comp_one_sub_X (p : R[X]) (k : Nat) :
    derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (derivative^[k] p).comp (1 - X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

/--
theorem `eval_multiset_prod_X_sub_C_derivative` / 定理 `eval_multiset_prod_X_sub_C_derivative`

English:
theorem eval_multiset_prod_X_sub_C_derivative
  statement: [DecidableEq R]
  proof: by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))
  simpa using this

中文:
定理 eval_multiset_prod_X_sub_C_derivative
  结论: [DecidableEq R]
  证明: by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))
  simpa using this

Depends on / 依赖: Multiset, Multiset.cons_erase, Multiset.map, S.erase, cons_erase, evalRingHom, map_multiset_prod, nth_rw
-/
theorem eval_multiset_prod_X_sub_C_derivative [DecidableEq R]
    {S : Multiset R} {r : R} (hr : r in S) :
    eval r (derivative (Multiset.map (fun a => X - C a) S).prod) =
      (Multiset.map (fun a => r - a) (S.erase r)).prod := by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))
  simpa using this

/--
theorem `derivative_X_sub_C_pow` / 定理 `derivative_X_sub_C_pow`

English:
theorem derivative_X_sub_C_pow
  given: (c : R) (m : Nat)
  proof: by
  rw [derivative_pow]; rw [derivative_X_sub_C]; rw [mul_one]

中文:
定理 derivative_X_sub_C_pow
  条件: (c : R) (m : 自然数)
  证明: by
  rw [derivative_pow]; rw [derivative_X_sub_C]; rw [mul_one]

Depends on / 依赖: derivative_X_sub_C, derivative_pow, mul_one
-/
theorem derivative_X_sub_C_pow (c : R) (m : Nat) :
    derivative ((X - C c) ^ m) = C (m : R) * (X - C c) ^ (m - 1) := by
  rw [derivative_pow]; rw [derivative_X_sub_C]; rw [mul_one]

/--
theorem `derivative_X_sub_C_sq` / 定理 `derivative_X_sub_C_sq`

English:
theorem derivative_X_sub_C_sq
  given: (c : R)
  statement: derivative ((X - C c) ^ 2) = C 2 * (X - C c)
  proof: by
  rw [derivative_sq]; rw [derivative_X_sub_C]; rw [mul_one]

中文:
定理 derivative_X_sub_C_sq
  条件: (c : R)
  结论: derivative ((X - C c) ^ 2) = C 2 * (X - C c)
  证明: by
  rw [derivative_sq]; rw [derivative_X_sub_C]; rw [mul_one]

Depends on / 依赖: derivative_X_sub_C, derivative_sq, mul_one
-/
theorem derivative_X_sub_C_sq (c : R) : derivative ((X - C c) ^ 2) = C 2 * (X - C c) := by
  rw [derivative_sq]; rw [derivative_X_sub_C]; rw [mul_one]

/--
theorem `iterate_derivative_X_sub_pow` / 定理 `iterate_derivative_X_sub_pow`

English:
theorem iterate_derivative_X_sub_pow
  given: (n k : Nat) (c : R)
  proof: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [iterate_derivative_X_add_pow]

中文:
定理 iterate_derivative_X_sub_pow
  条件: (n k : 自然数) (c : R)
  证明: by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [iterate_derivative_X_add_pow]

Depends on / 依赖: C_neg, iterate_derivative_X_add_pow, sub_eq_add_neg
-/
theorem iterate_derivative_X_sub_pow (n k : Nat) (c : R) :
    derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C c) ^ (n - k) := by
  rw [sub_eq_add_neg]; rw [← C_neg]; rw [iterate_derivative_X_add_pow]

/--
theorem `iterate_derivative_X_sub_pow_self` / 定理 `iterate_derivative_X_sub_pow_self`

English:
theorem iterate_derivative_X_sub_pow_self
  given: (n : Nat) (c : R)
  proof: by
  rw [iterate_derivative_X_sub_pow]; rw [n.sub_self]; rw [pow_zero]; rw [nsmul_one]; rw [n.descFactorial_self]

中文:
定理 iterate_derivative_X_sub_pow_self
  条件: (n : 自然数) (c : R)
  证明: by
  rw [iterate_derivative_X_sub_pow]; rw [n.sub_self]; rw [pow_zero]; rw [nsmul_one]; rw [n.descFactorial_self]

Depends on / 依赖: descFactorial_self, iterate_derivative_X_sub_pow, n.descFactorial_self, n.sub_self, nsmul_one, pow_zero, sub_self
-/
theorem iterate_derivative_X_sub_pow_self (n : Nat) (c : R) :
    derivative^[n] ((X - C c) ^ n) = n.factorial := by
  rw [iterate_derivative_X_sub_pow]; rw [n.sub_self]; rw [pow_zero]; rw [nsmul_one]; rw [n.descFactorial_self]

/--
theorem `iterate_derivative_eq_zero_of_degree_lt` / 定理 `iterate_derivative_eq_zero_of_degree_lt`

English:
theorem iterate_derivative_eq_zero_of_degree_lt
  given: {k : Nat} {P : R[X]} (h : P.degree < k)
  proof: by
  induction k generalizing P
case zero => exact degree_eq_bot.mp WithBot.lt_coe_bot.mp h
  case succ k ind =>
    by_cases P = 0
    case pos hP => simp [hP]
    case neg hP =>
      rw [Function.iterate_add_apply]; rw [Function.iterate_one]
      by_cases derivative P = 0
      case pos hP' => s

中文:
定理 iterate_derivative_eq_zero_of_degree_lt
  条件: {k : 自然数} {P : R[X]} (h : P.degree < k)
  证明: by
  induction k generalizing P
case zero => exact degree_eq_bot.mp WithBot.lt_coe_bot.mp h
  case succ k ind =>
    by_cases P = 0
    case pos hP => simp [hP]
    case neg hP =>
      rw [Function.iterate_add_apply]; rw [Function.iterate_one]
      by_cases derivative P = 0
      case pos hP' => s

Depends on / 依赖: Function, Function.iterate_add_apply, Function.iterate_one, P.natDegree, WithBot, WithBot.lt_coe_bot.mp, contrapose, degree_eq_bot, degree_eq_bot.mp, derivative, derivative_of_natDegree_zero, generalizing, iterate_add_apply, iterate_one, lt_coe_bot, natDegree, natDegree_derivative, natDegree_lt_iff_degree_lt
-/
theorem iterate_derivative_eq_zero_of_degree_lt {k : Nat} {P : R[X]} (h : P.degree < k) :
    derivative^[k] P = 0 := by
  induction k generalizing P
case zero => exact degree_eq_bot.mp WithBot.lt_coe_bot.mp h
  case succ k ind =>
    by_cases P = 0
    case pos hP => simp [hP]
    case neg hP =>
      rw [Function.iterate_add_apply]; rw [Function.iterate_one]
      by_cases derivative P = 0
      case pos hP' => simp [hP']
      case neg hP' =>
        have hP'' : P.natDegree != 0 := by
          contrapose hP'
          exact derivative_of_natDegree_zero hP'
refine ind (natDegree_lt_iff_degree_lt hP').mp ?_
        linarith [(natDegree_lt_iff_degree_lt hP).mpr h, natDegree_derivative_lt hP'']

/--
theorem `iterate_derivative_prod_X_sub_C` / 定理 `iterate_derivative_prod_X_sub_C`

English:
theorem iterate_derivative_prod_X_sub_C
  given: {k : Nat} {S : Finset R} (hk : k <= #S)
  proof: by
  classical
  induction k
  case zero => simp
  case succ k ind =>
    specialize ind (Nat.le_of_succ_le hk)
    nth_rewrite 1 [add_comm]
    rw [Function.iterate_add_apply]; rw [Function.iterate_one]; rw [ind]; rw [← nsmul_eq_mul]; rw [derivative_smul]; rw [nsmul_eq_mul]; rw [derivative_sum]; rw

中文:
定理 iterate_derivative_prod_X_sub_C
  条件: {k : 自然数} {S : Finset R} (hk : k <= #S)
  证明: by
  classical
  induction k
  case zero => simp
  case succ k ind =>
    specialize ind (Nat.le_of_succ_le hk)
    nth_rewrite 1 [add_comm]
    rw [Function.iterate_add_apply]; rw [Function.iterate_one]; rw [ind]; rw [← nsmul_eq_mul]; rw [derivative_smul]; rw [nsmul_eq_mul]; rw [derivative_sum]; rw

Depends on / 依赖: Function, Function.iterate_add_apply, Function.iterate_one, Nat.cast_mul, Nat.factorial_succ, Nat.le_of_succ_le, S.powersetCard, T.erase, add_comm, cast_mul, classical, derivative, derivative_smul, derivative_sum, factorial_succ, iterate_add_apply, iterate_one, le_of_succ_le, mul_assoc, mul_comm
-/
theorem iterate_derivative_prod_X_sub_C {k : Nat} {S : Finset R} (hk : k <= #S) :
    derivative^[k] (∏ a in S, (X - C a)) =
    k.factorial * ∑ T in S.powersetCard (#S - k), ∏ a in T, (X - C a) := by
  classical
  induction k
  case zero => simp
  case succ k ind =>
    specialize ind (Nat.le_of_succ_le hk)
    nth_rewrite 1 [add_comm]
    rw [Function.iterate_add_apply]; rw [Function.iterate_one]; rw [ind]; rw [← nsmul_eq_mul]; rw [derivative_smul]; rw [nsmul_eq_mul]; rw [derivative_sum]; rw [Nat.factorial_succ]; rw [mul_comm (k + 1)]; rw [Nat.cast_mul]; rw [mul_assoc]
    congr 1
    calc
      ∑ T in S.powersetCard (#S - k), derivative (∏ a in T, (X - C a)) =
      ∑ T in S.powersetCard (#S - k), ∑ i in T, ∏ a in T.erase i, (X - C a) := by
        congr! with T hT
        simp_rw [derivative_prod_finset, derivative_X_sub_C, mul_one]
      _ = ∑ (T in S.powersetCard (#S - k)) (i in S) with i in T, ∏ a in T.erase i, (X - C a) := by
        rw [← sum_finset_product']
        grind
      _ = ∑ (T in S.powersetCard (#S - (k + 1))) (i in S) with i ∉ T, ∏ a in T, (X - C a) := by
        apply sum_bij' (fun ⟨T, i⟩ _ => ⟨T.erase i, i⟩) (fun ⟨T, i⟩ _ => ⟨insert i T, i⟩)
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        all_goals grind
      _ = ∑ T in S.powersetCard (#S - (k + 1)), ∑ i in S \ T, ∏ a in T, (X - C a) := by
        rw [← sum_finset_product']
        grind
      _ = (k + 1) * ∑ T in S.powersetCard (#S - (k + 1)), ∏ a in T, (X - C a) := by
        rw [mul_sum]
        congr! 1 with T hT
        simp [sum_const, show #(S \ T) = k + 1 by grind]
      _ = _ := by grind

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

@[simp]
/--
theorem `dvd_derivative_iff` / 定理 `dvd_derivative_iff`

English:
theorem dvd_derivative_iff
  given: {P : R[X]}
  statement: P ∣ derivative P ↔ derivative P = 0 where
  proof: by
    by_cases hP : P = 0
    · simp only [hP, derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hP)
  mpr h := by simp [h]

中文:
定理 dvd_derivative_iff
  条件: {P : R[X]}
  结论: P ∣ derivative P ↔ derivative P = 0 where
  证明: by
    by_cases hP : P = 0
    · simp only [hP, derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hP)
  mpr h := by simp [h]

Depends on / 依赖: degree_derivative_lt, derivative_zero, eq_zero_of_dvd_of_degree_lt
-/
theorem dvd_derivative_iff {P : R[X]} : P ∣ derivative P ↔ derivative P = 0 where
  mp h := by
    by_cases hP : P = 0
    · simp only [hP, derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hP)
  mpr h := by simp [h]

end NoZeroDivisors

section CommSemiringNoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R]

/--
theorem `derivative_pow_eq_zero` / 定理 `derivative_pow_eq_zero`

English:
theorem derivative_pow_eq_zero
  given: {n : Nat} (chn : (n : R) != 0) {a : R[X]}
  proof: by
  nontriviality R
  rw [← C_ne_zero]; rw [C_eq_natCast] at chn
  simp +contextual [derivative_pow, chn]

中文:
定理 derivative_pow_eq_zero
  条件: {n : 自然数} (chn : (n : R) != 0) {a : R[X]}
  证明: by
  nontriviality R
  rw [← C_ne_zero]; rw [C_eq_natCast] at chn
  simp +contextual [derivative_pow, chn]

Depends on / 依赖: C_eq_natCast, C_ne_zero, contextual, derivative_pow, nontriviality
-/
theorem derivative_pow_eq_zero {n : Nat} (chn : (n : R) != 0) {a : R[X]} :
    derivative (a ^ n) = 0 ↔ derivative a = 0 := by
  nontriviality R
  rw [← C_ne_zero]; rw [C_eq_natCast] at chn
  simp +contextual [derivative_pow, chn]

end CommSemiringNoZeroDivisors

end Derivative

end Polynomial
