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
/-
**PNat.equivNonZeroDivisorsNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PNat.equivNonZeroDivisorsNat : Nat+ ≃*o nonZeroDivisors Nat where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℕ+` is equivalent to `nonZeroDivisors ℕ` in terms of order and multiplication.
-/
def PNat.equivNonZeroDivisorsNat : ℕ+ ≃*o nonZeroDivisors ℕ where
  toFun x := ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simp [Nat.pos_iff_ne_zero]⟩
  map_mul' := by simp
  map_le_map_iff' := by simp
