/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib/Data/Option/`.
Other basic operations on `Option` are defined in the core library.
-/

@[expose] public section

namespace Option

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
/-
**Option.traverse.** 是 Mathlib 中的一个定义，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Traverse an object of `Option α` with a function `f : α → F β` for an applicativ
e `F`.
-/
protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β) := Option.mapA f

variable {α : Type*} {β : Type*}

/-- An elimination principle for `Option`. It is a nondependent version of `Option.rec`. -/
/-
**Option.elim'** 是 Mathlib 中的一个引理，位于命名空间 `Option`。
形式化陈述：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : β) (g : α -> β) 
(a : α) (x : β) : Option.elim' f (update g a x) = update (Option.elim' f g) (som
e a) x
参数：f : β；g : α -> β；a : α；x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elimination principle for `Option`. It is a nondependent version of `Option.r
ec`.
-/
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

@[simp]
/-
**Option.elim'_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (b : β) (f : α → β), Option.elim' b f none
 = b
参数：b : β；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
theorem elim'_none (b : β) (f : α → β) : Option.elim' b f none = b := rfl

@[simp]
/-
**Option.elim'_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {a : α} (b : β) (f : α → β), Option.elim' 
b f (some a) = f a
参数：b : β；f : α → β；some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
theorem elim'_some {a : α} (b : β) (f : α → β) : Option.elim' b f (some a) = f a := rfl

@[simp]
/-
**Option.elim'_none_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : Option α → β), Option.elim' (f none) 
(f ∘ some) = f
参数：f : Option α → β；f none；f ∘ some。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim'_none_some (f : Option α → β) : (Option.elim' (f none) (f ∘ some)) = f :=
  funext fun o ↦ by cases o <;> rfl
/-
**Option.elim'_eq_elim** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (b : β) (f : α → β) (a : Option α), Option
.elim' b f a = a.elim b f
参数：b : β；f : α → β；a : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma elim'_eq_elim {α β : Type*} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[deprecated "Use `Option.get!` (which will panic on `none`) or \
    `Option.getD` (which takes an explicit default value)." (since := "2026-01-05")]
/-
**Option.iget** 是 Mathlib 中的一个定义，位于命名空间 `Option`。
形式化陈述：{α : Type u_1} → [Inhabited α] → Option α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

@[deprecated "Use `Option.getD`." (since := "2026-01-05")]
/-
**Option.iget_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：iget_some [Inhabited α] {a : α} : (some a).iget = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

end Option

