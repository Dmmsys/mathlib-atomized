/-
Copyright (c) 2025 Javier Burroni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier Burroni
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.PNat.Basic

/-!
# Order related instances for `ℕ+`
-/

public section

namespace PNat
open Nat

/-
**PNat.instSuccOrder** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instSuccOrder : SuccOrder Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSuccOrder : SuccOrder ℕ+ :=
  .ofSuccLeIff (· + 1) Iff.rfl
/-
**PNat.instSuccAddOrder** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instSuccAddOrder : SuccAddOrder Nat+ where succ_eq_add_one _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSuccAddOrder : SuccAddOrder ℕ+ where
  succ_eq_add_one _ := rfl
/-
**PNat.instNoMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instNoMaxOrder : NoMaxOrder Nat+ where exists_gt n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.lt_succ_self`：lt_succ_self (a : Nat+) : a < succPNat a
-/
instance instNoMaxOrder : NoMaxOrder ℕ+ where
  exists_gt n := ⟨n + 1, lt_succ_self n⟩

@[simp]
/-
**PNat.succ_eq_add_one** 是 Mathlib 中的一个引理，位于命名空间 `PNat`。
形式化陈述：succ_eq_add_one (n : Nat+) : Order.succ n = n + 1
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma succ_eq_add_one (n : ℕ+) : Order.succ n = n + 1 := rfl

end PNat

