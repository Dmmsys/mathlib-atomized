/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.PNat.Basic

/-!
# Equivalence between `ℕ+` and `nonZeroDivisors ℕ`
-/

@[expose] public section

/-- `ℕ+` is equivalent to `nonZeroDivisors ℕ` in terms of order and multiplication. -/
@[simps]
/--
Definition of `PNat.equivNonZeroDivisorsNat` / `PNat.equivNonZeroDivisorsNat` 的定义

English:
definition PNat.equivNonZeroDivisorsNat
  signature: : Nat+ ≃*o nonZeroDivisors Nat where
  body: ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simp [Nat.pos_iff_ne_zero]⟩
  map_mul' := by simp
  map_le_map_iff' := by simp

中文:
定义 PNat.equivNonZeroDivisorsNat
  签名: : 自然数+ ≃*o nonZeroDivisors 自然数 where
  定义体: ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simp [Nat.pos_iff_ne_zero]⟩
  map_mul' := by simp
  map_le_map_iff' := by simp

Depends on / 依赖: x.val
-/
def PNat.equivNonZeroDivisorsNat : Nat+ ≃*o nonZeroDivisors Nat where
  toFun x := ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simp [Nat.pos_iff_ne_zero]⟩
  map_mul' := by simp
  map_le_map_iff' := by simp
