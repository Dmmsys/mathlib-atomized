/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Init

/-!
# Basic facts about `Thunk`.
-/

@[expose] public section

namespace Thunk

/-
**Thunk.get_pure** 是 Mathlib 中的一个定理，位于命名空间 `Thunk`。
形式化陈述：∀ {α : Type u_1} (x : α), (Thunk.pure x).get = x
参数：x : α；Thunk.pure x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem get_pure {α} (x : α) : (Thunk.pure x).get = x := rfl
/-
**Thunk.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `Thunk`。
形式化陈述：∀ {α : Type u_1} (f : Unit → α), { fn := f }.get = f ()
参数：f : Unit → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem get_mk {α} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

universe u v
variable {α : Type u} {β : Type v}
/-
**Thunk.** 是 Mathlib 中的一个实例，位于命名空间 `Thunk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

/-- The Cartesian product of two thunks. -/
/-
**Thunk.prod** 是 Mathlib 中的一个定义，位于命名空间 `Thunk`。
形式化陈述：prod (a : Thunk α) (b : Thunk β) : Thunk (α × β)
参数：a : Thunk α；b : Thunk β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two thunks.
-/
def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)
/-
**Thunk.prod_get_fst** 是 Mathlib 中的一个定理，位于命名空间 `Thunk`。
形式化陈述：∀ {α : Type u} {β : Type v} {a : Thunk α} {b : Thunk β}, (a.prod b).get.1 
= a.get
参数：a.prod b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_get_fst {a : Thunk α} {b : Thunk β} : (prod a b).get.1 = a.get := rfl
/-
**Thunk.prod_get_snd** 是 Mathlib 中的一个定理，位于命名空间 `Thunk`。
形式化陈述：∀ {α : Type u} {β : Type v} {a : Thunk α} {b : Thunk β}, (a.prod b).get.2 
= b.get
参数：a.prod b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_get_snd {a : Thunk α} {b : Thunk β} : (prod a b).get.2 = b.get := rfl

/-- The sum of two thunks. -/
/-
**Thunk.add** 是 Mathlib 中的一个定义，位于命名空间 `Thunk`。
形式化陈述：add [Add α] (a b : Thunk α) : Thunk α
参数：a b : Thunk α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two thunks.
-/
def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get
/-
**Thunk.** 是 Mathlib 中的一个实例，位于命名空间 `Thunk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] : Add (Thunk α) := ⟨add⟩
/-
**Thunk.add_get** 是 Mathlib 中的一个定理，位于命名空间 `Thunk`。
形式化陈述：∀ {α : Type u} [inst : Add α] {a b : Thunk α}, (a + b).get = a.get + b.get
参数：a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem add_get [Add α] {a b : Thunk α} : (a + b).get = a.get + b.get := rfl

end Thunk

