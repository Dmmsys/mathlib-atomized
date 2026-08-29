/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Liouville Function

This file defines the Liouville function `λ(n)`.

## Main Definitions

* `ArithmeticFunction.liouville` is the Liouville function `λ(n)` defined to be `1` if `n` has an
  even number of prime factors (counting multiplicity) and `-1` otherwise.
-/

@[expose] public section

namespace ArithmeticFunction

/--
Definition of `liouville` / `liouville` 的定义

English:
definition liouville
  signature: : ArithmeticFunction Int where
  body: if n = 0 then 0 else (-1) ^ cardFactors n
  map_zero' := by simp

中文:
定义 liouville
  签名: : ArithmeticFunction 整数 where
  定义体: if n = 0 then 0 else (-1) ^ cardFactors n
  map_zero' := by simp

Depends on / 依赖: cardFactors
-/
def liouville : ArithmeticFunction Int where
  toFun n := if n = 0 then 0 else (-1) ^ cardFactors n
  map_zero' := by simp

/--
theorem `liouville_apply` / 定理 `liouville_apply`

English:
theorem liouville_apply
  given: {n : Nat} (h : n != 0)
  statement: liouville n = (-1) ^ cardFactors n
  proof: if_neg h

中文:
定理 liouville_apply
  条件: {n : 自然数} (h : n != 0)
  结论: liouville n = (-1) ^ cardFactors n
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem liouville_apply {n : Nat} (h : n != 0) : liouville n = (-1) ^ cardFactors n :=
  if_neg h

/--
theorem `liouville_ne_zero` / 定理 `liouville_ne_zero`

English:
theorem liouville_ne_zero
  given: {n : Nat} (h : n != 0)
  statement: liouville n != 0
  proof: by
  simp [liouville_apply h]

中文:
定理 liouville_ne_zero
  条件: {n : 自然数} (h : n != 0)
  结论: liouville n != 0
  证明: by
  simp [liouville_apply h]

Depends on / 依赖: liouville_apply
-/
theorem liouville_ne_zero {n : Nat} (h : n != 0) : liouville n != 0 := by
  simp [liouville_apply h]

/--
theorem `liouville_apply_one` / 定理 `liouville_apply_one`

English:
theorem liouville_apply_one
  statement: liouville 1 = 1
  proof: by
  simp [liouville_apply]

中文:
定理 liouville_apply_one
  结论: liouville 1 = 1
  证明: by
  simp [liouville_apply]

Depends on / 依赖: liouville_apply
-/
theorem liouville_apply_one : liouville 1 = 1 := by
  simp [liouville_apply]

/--
theorem `liouville_apply_mul` / 定理 `liouville_apply_mul`

English:
theorem liouville_apply_mul
  given: (m n : Nat)
  statement: liouville (m * n) = liouville m * liouville n
  proof: by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [liouville_apply, cardFactors_mul, hm, hn, pow_add]

中文:
定理 liouville_apply_mul
  条件: (m n : 自然数)
  结论: liouville (m * n) = liouville m * liouville n
  证明: by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [liouville_apply, cardFactors_mul, hm, hn, pow_add]

Depends on / 依赖: cardFactors_mul, liouville_apply, pow_add
-/
theorem liouville_apply_mul (m n : Nat) : liouville (m * n) = liouville m * liouville n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [liouville_apply, cardFactors_mul, hm, hn, pow_add]

/--
theorem `isMultiplicative_liouville` / 定理 `isMultiplicative_liouville`

English:
theorem isMultiplicative_liouville
  statement: IsMultiplicative liouville
  proof: ⟨liouville_apply_one, fun {m n} _ => liouville_apply_mul m n⟩

中文:
定理 isMultiplicative_liouville
  结论: 是Multiplicative liouville
  证明: ⟨liouville_apply_one, fun {m n} _ => liouville_apply_mul m n⟩

Depends on / 依赖: liouville_apply_mul, liouville_apply_one
-/
theorem isMultiplicative_liouville : IsMultiplicative liouville :=
  ⟨liouville_apply_one, fun {m n} _ => liouville_apply_mul m n⟩

end ArithmeticFunction
