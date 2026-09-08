/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.Order.CollectFacts
public meta import Mathlib.Util.AtomM

/-!
# Facts preprocessing for the `order` tactic

In this file we implement the preprocessing procedure for the `order` tactic.
See `Mathlib/Tactic/Order.lean` for details of preprocessing.
-/

public meta section

namespace Mathlib.Tactic.Order

universe u

open Lean Expr Meta

section Lemmas

/-
**Mathlib.Tactic.Order.not_lt_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tacti
c.Order`。
形式化陈述：not_lt_of_not_le {α : Type u} [Preorder α] {x y : α} (h : ¬(x <= y)) : ¬(x
 < y)
参数：h : ¬(x <= y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma not_lt_of_not_le {α : Type u} [Preorder α] {x y : α} (h : ¬(x ≤ y)) : ¬(x < y) :=
  (h ·.le)
/-
**Mathlib.Tactic.Order.le_of_not_lt_le** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic
.Order`。
形式化陈述：le_of_not_lt_le {α : Type u} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : 
x <= y) : y <= x
参数：h1 : ¬(x < y)；h2 : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `not_lt_iff_le_imp_ge`：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a
)
-/
lemma le_of_not_lt_le {α : Type u} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x ≤ y) :
    y ≤ x :=
  not_lt_iff_le_imp_ge.mp h1 h2

end Lemmas

/-- Supported order types: linear, partial, and preorder. -/
/-
**Mathlib.Tactic.Order.OrderType** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Ord
er`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Supported order types: linear, partial, and preorder.
-/
inductive OrderType
| lin | part | pre
deriving BEq
/-
**Mathlib.Tactic.Order.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString OrderType where
  toString
  | .lin => "linear order"
  | .part => "partial order"
  | .pre => "preorder"

/-- Find the "best" instance of an order on a given type. A linear order is preferred over a partial
order, and a partial order is preferred over a preorder. -/
/-
**Mathlib.Tactic.Order.findBestOrderInstance** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.Order`。
形式化陈述：findBestOrderInstance (type : Expr) : MetaM Option OrderType
参数：type : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find the "best" instance of an order on a given type. A linear order is preferre
d over a partial
order, and a partial order is preferred over a preorder.
-/
def findBestOrderInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none

/-- Replaces facts of the form `x = ⊤` with `y ≤ x` for all `y`, and similarly for `x = ⊥`. -/
/-
**Mathlib.Tactic.Order.replaceBotTop** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.O
rder`。
形式化陈述：replaceBotTop (facts : Array AtomicFact) : AtomM Array AtomicFact
参数：facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replaces facts of the form `x = ⊤` with `y ≤ x` for all `y`, and similarly for `
x = ⊥`.
-/
def replaceBotTop (facts : Array AtomicFact) :
    AtomM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .isBot idx =>
      -- `atoms` contains atoms for all types we are working on, so here we need to filter only
      -- those with the same type as `atoms[idx]`
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
          res := res.push <| .le idx i (← mkAppOptM ``bot_le #[none, none, none, atom])
    | .isTop idx =>
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
          res := res.push <| .le i idx (← mkAppOptM ``le_top #[none, none, none, atom])
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for preorders. Replaces `x < y` with two equivalent facts: `x ≤ y` and
`¬ (y ≤ x)`. Replaces `x = y` with `x ≤ y`, `y ≤ x` and removes `x ≠ y`. -/
/-
**Mathlib.Tactic.Order.preprocessFactsPreorder** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.Order`。
形式化陈述：preprocessFactsPreorder (facts : Array AtomicFact) : MetaM Array AtomicFac
t
参数：facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preprocesses facts for preorders. Replaces `x < y` with two equivalent facts: `x
 ≤ y` and
`¬ (y ≤ x)`. Replaces `x = y` with `x ≤ y`, `y ≤ x` and removes `x ≠ y`.
-/
def preprocessFactsPreorder (facts : Array AtomicFact) : MetaM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
      res := res.push <| .nle rhs lhs (← mkAppM ``not_le_of_gt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for partial orders. Replaces `x < y`, `¬ (x ≤ y)`, and `x = y` with
equivalent facts involving only `≤`, `≠`, and `≮`. For each fact `x = y ⊔ z` adds `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`. -/
/-
**Mathlib.Tactic.Order.preprocessFactsPartial** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Tactic.Order`。
形式化陈述：preprocessFactsPartial (facts : Array AtomicFact) : AtomM Array AtomicFact
参数：facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preprocesses facts for partial orders. Replaces `x < y`, `¬ (x ≤ y)`, and `x = y
` with
equivalent facts involving only `≤`, `≠`, and `≮`. For each fact `x = y ⊔ z` add
s `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`.
-/
def preprocessFactsPartial (facts : Array AtomicFact) :
    AtomM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
      res := res.push <| .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push <| .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
      res := res.push <| .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push <| .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for linear orders. Replaces `x < y`, `¬ (x ≤ y)`, `¬ (x < y)`, and `x = y`
with equivalent facts involving only `≤` and `≠`. For each fact `x = y ⊔ z` adds `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`. -/
/-
**Mathlib.Tactic.Order.preprocessFactsLinear** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.Order`。
形式化陈述：preprocessFactsLinear (facts : Array AtomicFact) : AtomM Array AtomicFact
参数：facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preprocesses facts for linear orders. Replaces `x < y`, `¬ (x ≤ y)`, `¬ (x < y)`
, and `x = y`
with equivalent facts involving only `≤` and `≠`. For each fact `x = y ⊔ z` adds
 `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`.
-/
def preprocessFactsLinear (facts : Array AtomicFact) :
    AtomM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_ge #[proof])
    | .nlt lhs rhs proof =>
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_gt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
      res := res.push <| .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push <| .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
      res := res.push <| .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push <| .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for order of `orderType` using either `preprocessFactsPreorder` or
`preprocessFactsPartial` or `preprocessFactsLinear`. -/
/-
**Mathlib.Tactic.Order.preprocessFacts** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Order`。
形式化陈述：preprocessFacts (facts : Array AtomicFact) (orderType : OrderType) : AtomM
 (Array AtomicFact)
参数：facts : Array AtomicFact；orderType : OrderType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preprocesses facts for order of `orderType` using either `preprocessFactsPreorde
r` or
`preprocessFactsPartial` or `preprocessFactsLinear`.
-/
def preprocessFacts (facts : Array AtomicFact) (orderType : OrderType) : AtomM (Array AtomicFact) :=
  match orderType with
  | .pre => preprocessFactsPreorder facts
  | .part => preprocessFactsPartial facts
  | .lin => preprocessFactsLinear facts

end Mathlib.Tactic.Order

