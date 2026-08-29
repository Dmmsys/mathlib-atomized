/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public meta import Qq
public import Mathlib.Order.BoundedOrder.Basic -- shake: keep (Qq dependency)
public import Mathlib.Order.Lattice -- shake: keep (Qq dependency)
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Util.AtomM

/-!
# Facts collection for the `order` Tactic

This file implements the collection of facts for the `order` tactic.
-/

public meta section

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/--
Inductive type `AtomicFact` / 归纳类型 `AtomicFact`

English:
inductive AtomicFact
  constructors (10):
    - eq: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - ne: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - le: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - nle: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - lt: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - nlt: (lhs : Nat) (rhs : Nat) (proof : Expr)
    - isTop: (idx : Nat)
    - isBot: (idx : Nat)
    - isInf: (lhs : Nat) (rhs : Nat) (res : Nat)
    - isSup: (lhs : Nat) (rhs : Nat) (res : Nat)

中文:
归纳类型 AtomicFact
  构造子 (10 个):
    - eq: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - ne: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - le: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - nle: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - lt: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - nlt: (lhs : 自然数) (rhs : 自然数) (proof : Expr)
    - isTop: (idx : 自然数)
    - isBot: (idx : 自然数)
    - isInf: (lhs : 自然数) (rhs : 自然数) (res : 自然数)
    - isSup: (lhs : 自然数) (rhs : 自然数) (res : 自然数)
-/
inductive AtomicFact
| eq (lhs : Nat) (rhs : Nat) (proof : Expr)
| ne (lhs : Nat) (rhs : Nat) (proof : Expr)
| le (lhs : Nat) (rhs : Nat) (proof : Expr)
| nle (lhs : Nat) (rhs : Nat) (proof : Expr)
| lt (lhs : Nat) (rhs : Nat) (proof : Expr)
| nlt (lhs : Nat) (rhs : Nat) (proof : Expr)
| isTop (idx : Nat)
| isBot (idx : Nat)
| isInf (lhs : Nat) (rhs : Nat) (res : Nat)
| isSup (lhs : Nat) (rhs : Nat) (res : Nat)
deriving Inhabited, BEq

-- For debugging purposes.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString AtomicFact
  body: match fa with
  | .eq lhs rhs _ => s!"#{lhs} = #{rhs}"
  | .ne lhs rhs _ => s!"#{lhs} != #{rhs}"
  | .le lhs rhs _ => s!"#{lhs} <= #{rhs}"
  | .nle lhs rhs _ => s!"¬ #{lhs} <= #{rhs}"
  | .lt lhs rhs _ => s!"#{lhs} < #{rhs}"
  | .nlt lhs rhs _ => s!"¬ #{lhs} < #{rhs}"
  | .isTop idx => s!"#{idx} := 

中文:
实例 :
  签名: ToString AtomicFact
  定义体: match fa with
  | .eq lhs rhs _ => s!"#{lhs} = #{rhs}"
  | .ne lhs rhs _ => s!"#{lhs} != #{rhs}"
  | .le lhs rhs _ => s!"#{lhs} <= #{rhs}"
  | .nle lhs rhs _ => s!"¬ #{lhs} <= #{rhs}"
  | .lt lhs rhs _ => s!"#{lhs} < #{rhs}"
  | .nlt lhs rhs _ => s!"¬ #{lhs} < #{rhs}"
  | .isTop idx => s!"#{idx} := 
-/
instance : ToString AtomicFact where
  toString fa := match fa with
  | .eq lhs rhs _ => s!"#{lhs} = #{rhs}"
  | .ne lhs rhs _ => s!"#{lhs} != #{rhs}"
  | .le lhs rhs _ => s!"#{lhs} <= #{rhs}"
  | .nle lhs rhs _ => s!"¬ #{lhs} <= #{rhs}"
  | .lt lhs rhs _ => s!"#{lhs} < #{rhs}"
  | .nlt lhs rhs _ => s!"¬ #{lhs} < #{rhs}"
  | .isTop idx => s!"#{idx} := ⊤"
  | .isBot idx => s!"#{idx} := ⊥"
  | .isInf lhs rhs res => s!"#{res} := #{lhs} ⊓ #{rhs}"
  | .isSup lhs rhs res => s!"#{res} := #{lhs} ⊔ #{rhs}"

/--
Definition of `CollectFactsState` / `CollectFactsState` 的定义

English:
abbreviation CollectFactsState
  body: Std.HashMap Expr Array AtomicFact

中文:
缩写 CollectFactsState
  定义体: Std.HashMap Expr Array AtomicFact

Depends on / 依赖: AtomicFact, HashMap, Std.HashMap
-/
abbrev CollectFactsState := Std.HashMap Expr Array AtomicFact

/--
Definition of `CollectFactsM` / `CollectFactsM` 的定义

English:
abbreviation CollectFactsM
  body: StateT CollectFactsState AtomM

中文:
缩写 CollectFactsM
  定义体: StateT CollectFactsState AtomM

Depends on / 依赖: CollectFactsState, StateT
-/
abbrev CollectFactsM := StateT CollectFactsState AtomM

/--
Definition of `addType` / `addType` 的定义

English:
definition addType
  signature: {u : Level} (type : Q(Type u))
  body: do
  match ← (← get).keys.findM? (withReducibleAndInstances <| isDefEq type ·) with
  | none =>
    modify fun res => res.insert type #[]
    pure type
  | some t => pure t

中文:
定义 addType
  签名: {u : Level} (type : Q(类型u))
  定义体: do
  match ← (← get).keys.findM? (withReducibleAndInstances <| isDefEq type ·) with
  | none =>
    modify fun res => res.insert type #[]
    pure type
  | some t => pure t
-/
def addType {u : Level} (type : Q(Type u)) : CollectFactsM Q(Type u) := do
  match ← (← get).keys.findM? (withReducibleAndInstances <| isDefEq type ·) with
  | none =>
    modify fun res => res.insert type #[]
    pure type
  | some t => pure t

/--
Definition of `addFact` / `addFact` 的定义

English:
definition addFact
  signature: (type : Expr) (fact : AtomicFact)
  body: modify fun res => res.modify type fun facts => facts.push fact

中文:
定义 addFact
  签名: (type : Expr) (阶乘 : AtomicFact)
  定义体: modify fun res => res.modify type fun facts => facts.push fact

Depends on / 依赖: facts.push, modify, res.modify
-/
def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit :=
  modify fun res => res.modify type fun facts => facts.push fact

/--
Definition of `addAtom` / `addAtom` 的定义

English:
definition addAtom
  signature: {u : Level} (type : Q(Type u)) (x : Q($type))
  body: do
  match ← AtomM.containsThenAddQ x with
  | (true, idx, _) => return idx
  | (false, idx, ⟨x', _⟩) =>
    match x' with
    | ~q((@OrderTop.toTop _ $instLE $instTop).top) =>
      addFact type (.isTop idx)
    | ~q((@OrderBot.toBot _ $instLE $instBot).bot) =>
      addFact type (.isBot idx)
    |

中文:
定义 addAtom
  签名: {u : Level} (type : Q(类型u)) (x : Q($type))
  定义体: do
  match ← AtomM.containsThenAddQ x with
  | (true, idx, _) => return idx
  | (false, idx, ⟨x', _⟩) =>
    match x' with
    | ~q((@OrderTop.toTop _ $instLE $instTop).top) =>
      addFact type (.isTop idx)
    | ~q((@OrderBot.toBot _ $instLE $instBot).bot) =>
      addFact type (.isBot idx)
    |
-/
partial def addAtom {u : Level} (type : Q(Type u)) (x : Q($type)) : CollectFactsM Nat := do
  match ← AtomM.containsThenAddQ x with
  | (true, idx, _) => return idx
  | (false, idx, ⟨x', _⟩) =>
    match x' with
    | ~q((@OrderTop.toTop _ $instLE $instTop).top) =>
      addFact type (.isTop idx)
    | ~q((@OrderBot.toBot _ $instLE $instBot).bot) =>
      addFact type (.isBot idx)
    | ~q((@SemilatticeSup.toMax _ $inst).max $a $b) =>
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      addFact type (.isSup aIdx bIdx idx)
    | ~q((@SemilatticeInf.toMin _ $inst).min $a $b) =>
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      addFact type (.isInf aIdx bIdx idx)
    | _ => pure ()
    return idx

-- TODO: The linter claims `u` is unused, but it used on the next line.
set_option linter.unusedVariables false in
/--
Definition of `collectFactsImp` / `collectFactsImp` 的定义

English:
definition collectFactsImp
  signature: (only? : Bool) (hyps : Array Expr) (negGoal : Expr)
  body: do
  let ctx ← getLCtx
  for expr in hyps do
    processExpr expr
  processExpr negGoal
  if !only? then
    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let e := ldecl.toExpr
      if e == negGoal then
        continue
      processExpr e

中文:
定义 collectFactsImp
  签名: (only? : 布尔值) (hyps : 数组 Expr) (negGoal : Expr)
  定义体: do
  let ctx ← getLCtx
  for expr in hyps do
    processExpr expr
  processExpr negGoal
  if !only? then
    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let e := ldecl.toExpr
      if e == negGoal then
        continue
      processExpr e
-/
partial def collectFactsImp (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
    CollectFactsM Unit := do
  let ctx ← getLCtx
  for expr in hyps do
    processExpr expr
  processExpr negGoal
  if !only? then
    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let e := ldecl.toExpr
      if e == negGoal then
        continue
      processExpr e
where
  /-- Extracts facts and atoms from the expression. -/
  processExpr (expr : Expr) : CollectFactsM Unit := do
    let type ← inferType expr
    if !(← isProp type) then
      return
    let ⟨u, type, expr⟩ ← inferTypeQ expr
    let _ : u =QL 0 := ⟨⟩
    match type with
    | ~q(@Eq ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
addFact α .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
addFact α .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
addFact α .lt xIdx yIdx expr
    | ~q(@Ne ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
addFact α .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
addFact α .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
addFact α .nlt xIdx yIdx expr
      | _ => return
    | ~q($p ∧ $q) =>
      processExpr q(And.left $expr)
      processExpr q(And.right $expr)
    | ~q(Exists $P) =>
      processExpr q(Exists.choose_spec $expr)
    | _ => return

/--
Definition of `collectFacts` / `collectFacts` 的定义

English:
definition collectFacts
  signature: (only? : Bool) (hyps : Array Expr) (negGoal : Expr)
  body: do
  return (← (collectFactsImp only? hyps negGoal).run ∅).snd

中文:
定义 collectFacts
  签名: (only? : 布尔值) (hyps : 数组 Expr) (negGoal : Expr)
  定义体: do
  return (← (collectFactsImp only? hyps negGoal).run ∅).snd
-/
def collectFacts (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
AtomM Std.HashMap Expr Array AtomicFact := do
  return (← (collectFactsImp only? hyps negGoal).run ∅).snd

end Mathlib.Tactic.Order
