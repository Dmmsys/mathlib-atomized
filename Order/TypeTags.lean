/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Order.Notation

/-!
# Order-related type synonyms

In this file we define `WithBot` and `WithTop`.
-/

@[expose] public section

variable {α : Type*}

/-- Attach `⊥` to a type. -/
@[to_dual /-- Attach `⊤` to a type. -/]
/-
**WithBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WithBot (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attach `⊥` to a type.
-/
def WithBot (α : Type*) := Option α
/-
**WithBot.instRepr** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithBot.instRepr [Repr α] : Repr (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
/-
**WithTop.instRepr** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithTop.instRepr [Repr α] : Repr (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

namespace WithBot

/-- The canonical map from `α` into `WithBot α` -/
@[to_dual (attr := coe, match_pattern) /-- The canonical map from `α` into `WithTop α` -/]
/-
**WithBot.some** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：some : α -> WithBot α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `α` into `WithBot α`
-/
def some : α → WithBot α :=
  Option.some

@[to_dual]
/-
**WithBot.coe** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：coe : Coe α (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
/-
**WithBot.bot** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：bot : Bot (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[to_dual]
/-
**WithBot.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：inhabited : Inhabited (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[to_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/]
/-
**WithBot.recBotCoe** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → {C : WithBot α → Sort u_2} → C ⊥ → ((a : α) → C ↑a) → (n 
: WithBot α) → C n
参数：(a : α) → C ↑a；n : WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[to_dual (attr := simp)]
/-
**WithBot.recBotCoe_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：recBotCoe_bot {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a) :
 @recBotCoe _ C d f ⊥ = d
参数：d : C ⊥；f : forall a : α, C a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
/-
**WithBot.recBotCoe_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：recBotCoe_coe {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a) (
x : α) : @recBotCoe _ C d f ↑x = f x
参数：d : C ⊥；f : forall a : α, C a；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot

