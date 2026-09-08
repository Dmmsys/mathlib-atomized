/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Nat.Cast.Prod

/-!
# The product of two `AddGroupWithOne`s.
-/

public section


namespace Prod

variable {α β : Type*} [AddGroupWithOne α] [AddGroupWithOne β]

/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroupWithOne (α × β) :=
  { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by ext <;> simp
    intCast_negSucc := fun _ => by ext <;> simp }

@[simp]
/-
**Prod.fst_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_intCast (n : Int) : (n : α × β).fst = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl

@[simp]
/-
**Prod.snd_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_intCast (n : Int) : (n : α × β).snd = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl

end Prod

