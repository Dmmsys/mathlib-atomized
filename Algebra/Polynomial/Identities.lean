/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Theory of univariate polynomials

The main def is `Polynomial.binomExpansion`.
-/

@[expose] public section


noncomputable section

namespace Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R}
  {m n : ℕ}

section Identities

/- @TODO: `powAddExpansion` and `powSubPowFactor` are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

  Maybe use `Data.Nat.Choose` to prove it.
-/
/-- `(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in the ring.
-/
/-
**Polynomial.powAddExpansion** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：powAddExpansion {R : Type*} [CommSemiring R] (x y : R) : forall n : Nat, {
 k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 } | 0 => ⟨0, by simp
⟩ | 1 => ⟨0, by simp⟩ | n + 2 => by obtain ⟨z, hz⟩
参数：x y : R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in th
e ring.
-/
def powAddExpansion {R : Type*} [CommSemiring R] (x y : R) :
    ∀ n : ℕ, { k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | n + 2 => by
    obtain ⟨z, hz⟩ := (powAddExpansion x y (n + 1))
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z + (n + 1) * x ^ n + z * y) * y ^ 2 := by
        push_cast
        ring!

variable [CommRing R]

set_option backward.privateInPublic true in
/-
**Polynomial.polyBinomAux1** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def polyBinomAux1 (x y : R) (e : ℕ) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } := by
  exists (powAddExpansion x y e).val
  congr
  apply (powAddExpansion _ _ _).property
/-
**Polynomial.poly_binom_aux2** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      f.sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) := by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  apply (polyBinomAux1 x y _ _).property

set_option backward.privateInPublic true in
/-
**Polynomial.poly_binom_aux3** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.sum fun e a => a * x ^ e) + f.sum fun e a => a * e * x ^ (e - 1) * y) +
        f.sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 := by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
/-
**Polynomial.binomExpansion** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：binomExpansion (f : R[X]) (x y : R) : { k : R // f.eval (x + y) = f.eval x
 + f.derivative.eval x * y + k * y ^ 2 }
参数：f : R[X]；x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` 
at `x`,
plus some element `k : R` times `y^2`.
-/
def binomExpansion (f : R[X]) (x y : R) :
    { k : R // f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 } := by
  exists f.sum fun e a => a * (polyBinomAux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
  · rw [derivative_eval]
    exact (Finset.sum_mul ..).symm
  · exact (Finset.sum_mul ..).symm

/-- `x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
/-
**Polynomial.powSubPowFactor** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：powSubPowFactor (x y : R) : forall i : Nat, { z : R // x ^ i - y ^ i = z *
 (x - y) } | 0 => ⟨0, by simp⟩ | 1 => ⟨1, by simp⟩ | k + 2 => by obtain ⟨z, hz⟩
参数：x y : R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def powSubPowFactor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨1, by simp⟩
  | k + 2 => by
    obtain ⟨z, hz⟩ := @powSubPowFactor x y (k + 1)
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz

/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
/-
**Polynomial.evalSubFactor** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * 
(x - y) }
参数：f : R[X]；x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } := by
  refine ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc, ← (powSubPowFactor x y _).prop, mul_sub]

end Identities

end Polynomial

