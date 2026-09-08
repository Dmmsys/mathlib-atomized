/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Init

/-!
# Helper definitions and instances for `Ordering`
-/

@[expose] public section

universe u

namespace Ordering

variable {α : Type*}

/-- `Compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
/-
**Ordering.Compares** 是 Mathlib 中的一个定义，位于命名空间 `Ordering`。
形式化陈述：{α : Type u_1} → [LT α] → Ordering → α → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Compares o a b` means that `a` and `b` have the ordering relation `o` between t
hem, assuming
that the relation `a < b` is defined.
-/
def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b
/-
**Ordering.compares_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a b : α), Ordering.lt.Compares a b = (a < 
b)
参数：a b : α；a < b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl
/-
**Ordering.compares_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a b : α), Ordering.eq.Compares a b = (a = 
b)
参数：a b : α；a = b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl
/-
**Ordering.compares_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a b : α), Ordering.gt.Compares a b = (a > 
b)
参数：a b : α；a > b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

/-- `o₁.dthen fun h => o₂(h)` is like `o₁.then o₂` but `o₂` is allowed to depend on
`h : o₁ = .eq`. -/
/-
**Ordering.dthen** 是 Mathlib 中的一个定义，位于命名空间 `Ordering`。
形式化陈述：(o : Ordering) → (o = Ordering.eq → Ordering) → Ordering
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`o₁.dthen fun h => o₂(h)` is like `o₁.then o₂` but `o₂` is allowed to depend on
`h : o₁ = .eq`.
-/
@[macro_inline] def dthen :
    (o : Ordering) → (o = .eq → Ordering) → Ordering
  | .eq, f => f rfl
  | o, _ => o

end Ordering

/--
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
/-
**cmpUsing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cmpUsing {α : Type u} (lt : α -> α -> Prop) [DecidableRel lt] (a b : α) : 
Ordering
参数：lt : α -> α -> Prop；a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

/--
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
/-
**cmp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cmp {α : Type u} [LT α] [DecidableLT α] (a b : α) : Ordering
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmp {α : Type u} [LT α] [DecidableLT α] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b
