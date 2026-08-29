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
  {m n : Nat}

section Identities

/- @TODO: `powAddExpansion` and `powSubPowFactor` are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

  Maybe use `Data.Nat.Choose` to prove it.
-/
/--
Definition of `powAddExpansion` / `powAddExpansion` 的定义

English:
definition powAddExpansion
  signature: {R : Type*} [CommSemiring R] (x y : R)
  body: (powAddExpansion x y (n + 1))
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z 

中文:
定义 powAddExpansion
  签名: {R : 类型} [交换半环 R] (x y : R)
  定义体: (powAddExpansion x y (n + 1))
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z 

Depends on / 依赖: NonAssocSemiring, fast_instance, powAddExpansion, toNonAssocSemiring
-/
def powAddExpansion {R : Type*} [CommSemiring R] (x y : R) :
    forall n : Nat, { k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 }
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
/--
Definition of `polyBinomAux1` / `polyBinomAux1` 的定义

English:
definition polyBinomAux1
  signature: (x y : R) (e : Nat) (a : R)
  body: by
  exists (powAddExpansion x y e).val
  congr
  apply (powAddExpansion _ _ _).property

中文:
定义 polyBinomAux1
  签名: (x y : R) (e : 自然数) (a : R)
  定义体: by
  exists (powAddExpansion x y e).val
  congr
  apply (powAddExpansion _ _ _).property

Depends on / 依赖: NonAssocCommSemiring, SetLike, toNonAssocCommSemiring
-/
private def polyBinomAux1 (x y : R) (e : Nat) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } := by
  exists (powAddExpansion x y e).val
  congr
  apply (powAddExpansion _ _ _).property

/--
theorem `poly_binom_aux2` / 定理 `poly_binom_aux2`

English:
theorem poly_binom_aux2
  given: (f : R[X]) (x y : R)
  proof: by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  apply (polyBinomAux1 x y _ _).property

中文:
定理 poly_binom_aux2
  条件: (f : R[X]) (x y : R)
  证明: by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  apply (polyBinomAux1 x y _ _).property
-/
private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      f.sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) := by
  unfold eval; rw [eval₂_eq_sum]; congr with (n z)
  apply (polyBinomAux1 x y _ _).property

set_option backward.privateInPublic true in
/--
theorem `poly_binom_aux3` / 定理 `poly_binom_aux3`

English:
theorem poly_binom_aux3
  given: (f : R[X]) (x y : R)
  proof: by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]

中文:
定理 poly_binom_aux3
  条件: (f : R[X]) (x y : R)
  证明: by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]
-/
private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.sum fun e a => a * x ^ e) + f.sum fun e a => a * e * x ^ (e - 1) * y) +
        f.sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 := by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `binomExpansion` / `binomExpansion` 的定义

English:
definition binomExpansion
  signature: (f : R[X]) (x y : R)
  body: by
  exists f.sum fun e a => a * (polyBinomAux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
  · rw [derivative_eval]
    exact (Finset.sum_mul ..).symm
  · exact (Finset.sum_mul ..).symm

中文:
定义 binomExpansion
  签名: (f : R[X]) (x y : R)
  定义体: by
  exists f.sum fun e a => a * (polyBinomAux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
  · rw [derivative_eval]
    exact (Finset.sum_mul ..).symm
  · exact (Finset.sum_mul ..).symm

Depends on / 依赖: Finset, Finset.sum_mul, derivative_eval, eval_eq_sum, f.sum, polyBinomAux1, poly_binom_aux3, sum_mul
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

/--
Definition of `powSubPowFactor` / `powSubPowFactor` 的定义

English:
definition powSubPowFactor
  signature: (x y : R)
  body: @powSubPowFactor x y (k + 1)
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz

中文:
定义 powSubPowFactor
  签名: (x y : R)
  定义体: @powSubPowFactor x y (k + 1)
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz

Depends on / 依赖: powSubPowFactor
-/
def powSubPowFactor (x y : R) : forall i : Nat, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨1, by simp⟩
  | k + 2 => by
    obtain ⟨z, hz⟩ := @powSubPowFactor x y (k + 1)
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz

/--
Definition of `evalSubFactor` / `evalSubFactor` 的定义

English:
definition evalSubFactor
  signature: (f : R[X]) (x y : R)
  body: by
  refine ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc]; rw [← (powSubPowFactor x y _).prop]; rw [mul_sub]

中文:
定义 evalSubFactor
  签名: (f : R[X]) (x y : R)
  定义体: by
  refine ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc]; rw [← (powSubPowFactor x y _).prop]; rw [mul_sub]

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sum_sub_distrib, f.sum, mul_assoc, mul_sub, powSubPowFactor, sum_mul, sum_sub_distrib
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } := by
  refine ⟨f.sum fun i r => r * (powSubPowFactor x y i).val, ?_⟩
  delta eval; rw [eval₂_eq_sum, eval₂_eq_sum]
  simp only [sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i
  rw [mul_assoc]; rw [← (powSubPowFactor x y _).prop]; rw [mul_sub]

end Identities

end Polynomial
