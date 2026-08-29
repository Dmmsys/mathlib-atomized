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
/--
Definition of `WithBot` / `WithBot` 的定义

English:
definition WithBot
  signature: (α : Type*)
  body: Option α

中文:
定义 WithBot
  签名: (α : 类型)
  定义体: Option α
-/
def WithBot (α : Type*) := Option α

/--
Instance `WithBot.instRepr` / 实例 `WithBot.instRepr`

English:
instance WithBot.instRepr
  signature: [Repr α]
  body: ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]

中文:
实例 WithBot.instRepr
  签名: [Repr α]
  定义体: ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
-/
instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
/--
Instance `WithTop.instRepr` / 实例 `WithTop.instRepr`

English:
instance WithTop.instRepr
  signature: [Repr α]
  body: ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

中文:
实例 WithTop.instRepr
  签名: [Repr α]
  定义体: ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩
-/
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

namespace WithBot

/-- The canonical map from `α` into `WithBot α` -/
@[to_dual (attr := coe, match_pattern) /-- The canonical map from `α` into `WithTop α` -/]
/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: : α -> WithBot α
  body: Option.some

@[to_dual]

中文:
定义 some
  签名: : α -> WithBot α
  定义体: Option.some

@[to_dual]

Depends on / 依赖: Option.some
-/
def some : α -> WithBot α :=
  Option.some

@[to_dual]
/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : Coe α (WithBot α)
  body: ⟨some⟩

@[to_dual]

中文:
实例 coe
  签名: : Coe α (WithBot α)
  定义体: ⟨some⟩

@[to_dual]
-/
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : Bot (WithBot α)
  body: ⟨none⟩

@[to_dual]

中文:
实例 bot
  签名: : 底元素 (WithBot α)
  定义体: ⟨none⟩

@[to_dual]
-/
instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[to_dual]
/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (WithBot α)
  body: ⟨⊥⟩

中文:
实例 inhabited
  签名: : 可居 (WithBot α)
  定义体: ⟨⊥⟩
-/
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[to_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/]
/--
Definition of `recBotCoe` / `recBotCoe` 的定义

English:
definition recBotCoe
  signature: {C : WithBot α -> Sort*} (bot : C ⊥) (coe : forall a : α, C a)

中文:
定义 recBotCoe
  签名: {C : WithBot α -> 类型层*} (bot : C ⊥) (coe : 对任意 a : α, C a)
-/
def recBotCoe {C : WithBot α -> Sort*} (bot : C ⊥) (coe : forall a : α, C a) : forall n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[to_dual (attr := simp)]
/--
theorem `recBotCoe_bot` / 定理 `recBotCoe_bot`

English:
theorem recBotCoe_bot
  given: {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 recBotCoe_bot
  条件: {C : WithBot α -> 类型层*} (d : C ⊥) (f : 对任意 a : α, C a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem recBotCoe_bot {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `recBotCoe_coe` / 定理 `recBotCoe_coe`

English:
theorem recBotCoe_coe
  given: {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a) (x : α)
  proof: rfl

中文:
定理 recBotCoe_coe
  条件: {C : WithBot α -> 类型层*} (d : C ⊥) (f : 对任意 a : α, C a) (x : α)
  证明: rfl
-/
theorem recBotCoe_coe {C : WithBot α -> Sort*} (d : C ⊥) (f : forall a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot
