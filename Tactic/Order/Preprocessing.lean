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

/--
lemma `not_lt_of_not_le` / 引理 `not_lt_of_not_le`

English:
lemma not_lt_of_not_le
  given: {α : Type u} [Preorder α] {x y : α} (h : ¬(x <= y))
  statement: ¬(x < y)
  proof: (h ·.le)

中文:
引理 not_lt_of_not_le
  条件: {α : 类型u} [预序 α] {x y : α} (h : ¬(x <= y))
  结论: ¬(x < y)
  证明: (h ·.le)
-/
lemma not_lt_of_not_le {α : Type u} [Preorder α] {x y : α} (h : ¬(x <= y)) : ¬(x < y) :=
  (h ·.le)

/--
lemma `le_of_not_lt_le` / 引理 `le_of_not_lt_le`

English:
lemma le_of_not_lt_le
  given: {α : Type u} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x <= y)
  proof: not_lt_iff_le_imp_ge.mp h1 h2

中文:
引理 le_of_not_lt_le
  条件: {α : 类型u} [预序 α] {x y : α} (h1 : ¬(x < y)) (h2 : x <= y)
  证明: not_lt_iff_le_imp_ge.mp h1 h2

Depends on / 依赖: not_lt_iff_le_imp_ge, not_lt_iff_le_imp_ge.mp
-/
lemma le_of_not_lt_le {α : Type u} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x <= y) :
    y <= x :=
  not_lt_iff_le_imp_ge.mp h1 h2

end Lemmas

/--
Inductive type `OrderType` / 归纳类型 `OrderType`

English:
inductive OrderType
  constructors (1):
    - lin: | part | pre

中文:
归纳类型 序型
  构造子 (1 个):
    - lin: | part | pre
-/
inductive OrderType
| lin | part | pre
deriving BEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString OrderType

中文:
实例 :
  签名: ToString 序型
-/
instance : ToString OrderType where
  toString
  | .lin => "linear order"
  | .part => "partial order"
  | .pre => "preorder"

/--
Definition of `findBestOrderInstance` / `findBestOrderInstance` 的定义

English:
definition findBestOrderInstance
  signature: (type : Expr)
  body: do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none

中文:
定义 findBestOrderInstance
  签名: (type : Expr)
  定义体: do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none
-/
def findBestOrderInstance (type : Expr) : MetaM Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none

/--
Definition of `replaceBotTop` / `replaceBotTop` 的定义

English:
definition replaceBotTop
  signature: (facts : Array AtomicFact)
  body: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .isBot idx =>
      -- `atoms` contains atoms for all types we are working on, so here we need to filter only
      -- those with the same type as `atoms[idx]`
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le idx i (← mkAppOptM ``bot_le #[none, none, none, atom])
    | .isTop idx =>
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le i idx (← mkAppOptM ``le_top #[none, none, none, atom])
    | _ =>
      res := res.push fact
  return res

中文:
定义 replaceBotTop
  签名: (facts : 数组 AtomicFact)
  定义体: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .isBot idx =>
      -- `atoms` contains atoms for all types we are working on, so here we need to filter only
      -- those with the same type as `atoms[idx]`
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le idx i (← mkAppOptM ``bot_le #[none, none, none, atom])
    | .isTop idx =>
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le i idx (← mkAppOptM ``le_top #[none, none, none, atom])
    | _ =>
      res := res.push fact
  return res

Depends on / 依赖: K.isCompact, isCompact, isCompact_iff_compactSpace
-/
def replaceBotTop (facts : Array AtomicFact) :
AtomM Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .isBot idx =>
      -- `atoms` contains atoms for all types we are working on, so here we need to filter only
      -- those with the same type as `atoms[idx]`
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le idx i (← mkAppOptM ``bot_le #[none, none, none, atom])
    | .isTop idx =>
      let type ← inferType (← get).atoms[idx]!
      for (atom, i) in (← get).atoms.zipIdx do
        if (← withReducible <| isDefEq type (← inferType atom)) && i != idx then
res := res.push .le i idx (← mkAppOptM ``le_top #[none, none, none, atom])
    | _ =>
      res := res.push fact
  return res

/--
Definition of `preprocessFactsPreorder` / `preprocessFactsPreorder` 的定义

English:
definition preprocessFactsPreorder
  signature: (facts : Array AtomicFact)
  body: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
res := res.push .nle rhs lhs (← mkAppM ``not_le_of_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res

中文:
定义 preprocessFactsPreorder
  签名: (facts : 数组 AtomicFact)
  定义体: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
res := res.push .nle rhs lhs (← mkAppM ``not_le_of_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res
-/
def preprocessFactsPreorder (facts : Array AtomicFact) : MetaM Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
res := res.push .nle rhs lhs (← mkAppM ``not_le_of_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res

/--
Definition of `preprocessFactsPartial` / `preprocessFactsPartial` 的定义

English:
definition preprocessFactsPartial
  signature: (facts : Array AtomicFact)
  body: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

中文:
定义 preprocessFactsPartial
  签名: (facts : 数组 AtomicFact)
  定义体: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res
-/
def preprocessFactsPartial (facts : Array AtomicFact) :
AtomM Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/--
Definition of `preprocessFactsLinear` / `preprocessFactsLinear` 的定义

English:
definition preprocessFactsLinear
  signature: (facts : Array AtomicFact)
  body: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .le rhs lhs (← mkAppM ``le_of_not_ge #[proof])
    | .nlt lhs rhs proof =>
res := res.push .le rhs lhs (← mkAppM ``le_of_not_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

中文:
定义 preprocessFactsLinear
  签名: (facts : 数组 AtomicFact)
  定义体: do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .le rhs lhs (← mkAppM ``le_of_not_ge #[proof])
    | .nlt lhs rhs proof =>
res := res.push .le rhs lhs (← mkAppM ``le_of_not_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res
-/
def preprocessFactsLinear (facts : Array AtomicFact) :
AtomM Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
res := res.push .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
res := res.push .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
res := res.push .le rhs lhs (← mkAppM ``le_of_not_ge #[proof])
    | .nlt lhs rhs proof =>
res := res.push .le rhs lhs (← mkAppM ``le_of_not_gt #[proof])
    | .eq lhs rhs proof =>
res := res.push .le lhs rhs (← mkAppM ``le_of_eq #[proof])
res := res.push .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
res := res.push .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | .isInf lhs rhs inf =>
res := res.push .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
res := res.push .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, (← get).atoms[lhs]!, (← get).atoms[rhs]!])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/--
Definition of `preprocessFacts` / `preprocessFacts` 的定义

English:
definition preprocessFacts
  signature: (facts : Array AtomicFact) (orderType : OrderType)
  body: match orderType with
  | .pre => preprocessFactsPreorder facts
  | .part => preprocessFactsPartial facts
  | .lin => preprocessFactsLinear facts

中文:
定义 preprocessFacts
  签名: (facts : 数组 AtomicFact) (orderType : 序型)
  定义体: match orderType with
  | .pre => preprocessFactsPreorder facts
  | .part => preprocessFactsPartial facts
  | .lin => preprocessFactsLinear facts

Depends on / 依赖: orderType, preprocessFactsLinear, preprocessFactsPartial, preprocessFactsPreorder
-/
def preprocessFacts (facts : Array AtomicFact) (orderType : OrderType) : AtomM (Array AtomicFact) :=
  match orderType with
  | .pre => preprocessFactsPreorder facts
  | .part => preprocessFactsPartial facts
  | .lin => preprocessFactsLinear facts

end Mathlib.Tactic.Order
