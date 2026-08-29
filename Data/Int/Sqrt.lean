/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Common

/-!
# Square root of integers

This file defines the square root function on integers. `Int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `Int.sqrt z = 0`.
-/

@[expose] public section


namespace Int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot]
/--
Definition of `sqrt` / `sqrt` 的定义

English:
definition sqrt
  signature: (z : Int)
  body: Nat.sqrt Int.toNat z

中文:
定义 sqrt
  签名: (z : 整数)
  定义体: Nat.sqrt Int.toNat z

Depends on / 依赖: Int.toNat, Nat.sqrt
-/
def sqrt (z : Int) : Int :=
Nat.sqrt Int.toNat z

/--
theorem `sqrt_eq` / 定理 `sqrt_eq`

English:
theorem sqrt_eq
  given: (n : Int)
  statement: sqrt (n * n) = n.natAbs
  proof: by
  rw [sqrt]; rw [← natAbs_mul_self]; rw [toNat_natCast]; rw [Nat.sqrt_eq]

中文:
定理 sqrt_eq
  条件: (n : 整数)
  结论: sqrt (n * n) = n.natAbs
  证明: by
  rw [sqrt]; rw [← natAbs_mul_self]; rw [toNat_natCast]; rw [Nat.sqrt_eq]

Depends on / 依赖: Nat.sqrt_eq, natAbs_mul_self, sqrt_eq, toNat_natCast
-/
theorem sqrt_eq (n : Int) : sqrt (n * n) = n.natAbs := by
  rw [sqrt]; rw [← natAbs_mul_self]; rw [toNat_natCast]; rw [Nat.sqrt_eq]

/--
theorem `exists_mul_self` / 定理 `exists_mul_self`

English:
theorem exists_mul_self
  given: (x : Int)
  statement: (exists n, n * n = x) ↔ sqrt x * sqrt x = x
  proof: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.natCast_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩

中文:
定理 exists_mul_self
  条件: (x : 整数)
  结论: (存在 n, n * n = x) ↔ sqrt x * sqrt x = x
  证明: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.natCast_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩

Depends on / 依赖: Int.natCast_mul, natAbs_mul_self, natCast_mul, sqrt_eq
-/
theorem exists_mul_self (x : Int) : (exists n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.natCast_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩

/--
theorem `sqrt_nonneg` / 定理 `sqrt_nonneg`

English:
theorem sqrt_nonneg
  given: (n : Int)
  statement: 0 <= sqrt n
  proof: natCast_nonneg _

@[simp, norm_cast]

中文:
定理 sqrt_nonneg
  条件: (n : 整数)
  结论: 0 <= sqrt n
  证明: natCast_nonneg _

@[simp, norm_cast]

Depends on / 依赖: natCast_nonneg
-/
theorem sqrt_nonneg (n : Int) : 0 <= sqrt n :=
  natCast_nonneg _

@[simp, norm_cast]
/--
theorem `sqrt_natCast` / 定理 `sqrt_natCast`

English:
theorem sqrt_natCast
  given: (n : Nat)
  statement: Int.sqrt (n : Int) = Nat.sqrt n
  proof: by rw [sqrt, toNat_natCast]

@[simp]

中文:
定理 sqrt_natCast
  条件: (n : 自然数)
  结论: 整数.sqrt (n : 整数) = 自然数.sqrt n
  证明: by rw [sqrt, toNat_natCast]

@[simp]

Depends on / 依赖: toNat_natCast
-/
theorem sqrt_natCast (n : Nat) : Int.sqrt (n : Int) = Nat.sqrt n := by rw [sqrt, toNat_natCast]

@[simp]
/--
theorem `sqrt_ofNat` / 定理 `sqrt_ofNat`

English:
theorem sqrt_ofNat
  given: (n : Nat)
  statement: Int.sqrt ofNat(n) = Nat.sqrt ofNat(n)
  proof: sqrt_natCast _

中文:
定理 sqrt_ofNat
  条件: (n : 自然数)
  结论: 整数.sqrt of自然数(n) = 自然数.sqrt of自然数(n)
  证明: sqrt_natCast _

Depends on / 依赖: sqrt_natCast
-/
theorem sqrt_ofNat (n : Nat) : Int.sqrt ofNat(n) = Nat.sqrt ofNat(n) :=
  sqrt_natCast _

end Int
