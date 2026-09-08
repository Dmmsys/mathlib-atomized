/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Jeremy Tan
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Lemmas about `Int.natAbs`

This file contains some results on `Int.natAbs`, the absolute value of an integer as a
natural number.

## Main results

* `Int.natAbsHom`: `Int.natAbs` bundled as a `MonoidWithZeroHom`.
-/

@[expose] public section

namespace Int

/-- `Int.natAbs` as a bundled `MonoidWithZeroHom`. -/
@[simps]
/-
**Int.natAbsHom** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：natAbsHom : Int ->*₀ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_zero`：Int.natAbs 0 = 0
· 使用定理 `Int.natAbs_one`：Int.natAbs 1 = 1
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs

--- 原说明 ---
`Int.natAbs` as a bundled `MonoidWithZeroHom`.
-/
def natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero
/-
**Int.natAbs_natCast_sub_natCast_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_natCast_sub_natCast_of_ge {a b : Nat} (h : b <= a) : Int.natAbs (↑a
 - ↑b) = a - b
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natAbs_natCast_sub_natCast_of_ge {a b : ℕ} (h : b ≤ a) : Int.natAbs (↑a - ↑b) = a - b := by
  lia
/-
**Int.natAbs_natCast_sub_natCast_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_natCast_sub_natCast_of_le {a b : Nat} (h : a <= b) : Int.natAbs (↑a
 - ↑b) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natAbs_natCast_sub_natCast_of_le {a b : ℕ} (h : a ≤ b) : Int.natAbs (↑a - ↑b) = b - a := by
  lia

end Int

