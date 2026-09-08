/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public meta import Qq
public import Mathlib.Order.BoundedOrder.Basic  -- shake: keep (Qq dependency)
public import Mathlib.Order.Lattice  -- shake: keep (Qq dependency)
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Util.AtomM

/-!
# Facts collection for the `order` Tactic

This file implements the collection of facts for the `order` tactic.
-/

public meta section

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/-- A structure for storing facts about variables. -/
/-
**Mathlib.Tactic.Order.AtomicFact** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Or
der`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure for storing facts about variables.
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
/-
**Mathlib.Tactic.Order.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString AtomicFact where
  toString fa := match fa with
  | .eq lhs rhs _ => s!"#{lhs} = #{rhs}"
  | .ne lhs rhs _ => s!"#{lhs} ≠ #{rhs}"
  | .le lhs rhs _ => s!"#{lhs} ≤ #{rhs}"
  | .nle lhs rhs _ => s!"¬ #{lhs} ≤ #{rhs}"
  | .lt lhs rhs _ => s!"#{lhs} < #{rhs}"
  | .nlt lhs rhs _ => s!"¬ #{lhs} < #{rhs}"
  | .isTop idx => s!"#{idx} := ⊤"
  | .isBot idx => s!"#{idx} := ⊥"
  | .isInf lhs rhs res => s!"#{res} := #{lhs} ⊓ #{rhs}"
  | .isSup lhs rhs res => s!"#{res} := #{lhs} ⊔ #{rhs}"

/-- State for `CollectFactsM`. It contains a map that maps a type to atomic facts collected for
this type. -/
/-
**Mathlib.Tactic.Order.CollectFactsState** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Ta
ctic.Order`。
形式化陈述：CollectFactsState
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
State for `CollectFactsM`. It contains a map that maps a type to atomic facts co
llected for
this type.
-/
abbrev CollectFactsState := Std.HashMap Expr <| Array AtomicFact

/-- Monad for the fact collection procedure. -/
/-
**Mathlib.Tactic.Order.CollectFactsM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic
.Order`。
形式化陈述：CollectFactsM
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monad for the fact collection procedure.
-/
abbrev CollectFactsM := StateT CollectFactsState AtomM

/-- Adds `type` to the state. It checks if the type has already been added up to
`reducible_and_instances` transparency. Returns the type that is added to the state and
definitionally equal (but may be not syntactically equal) to `type`. -/
/-
**Mathlib.Tactic.Order.addType** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Order`。
形式化陈述：addType {u : Level} (type : Q(Type u)) : CollectFactsM Q(Type u)
参数：type : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds `type` to the state. It checks if the type has already been added up to
`reducible_and_instances` transparency. Returns the type that is added to the st
ate and
definitionally equal (but may be not syntactically equal) to `type`.
-/
def addType {u : Level} (type : Q(Type u)) : CollectFactsM Q(Type u) := do
  match ← (← get).keys.findM? (withReducibleAndInstances <| isDefEq type ·) with
  | none =>
    modify fun res => res.insert type #[]
    pure type
  | some t => pure t

/-- Adds `fact` to the state. Assumes that `type` is already added by `addType`. -/
/-
**Mathlib.Tactic.Order.addFact** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Order`。
形式化陈述：addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit
参数：type : Expr；fact : AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds `fact` to the state. Assumes that `type` is already added by `addType`.
-/
def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit :=
  modify fun res => res.modify type fun facts => facts.push fact

/-- Updates the state with the atom `x`. If `x` is `⊤` or `⊥`, adds the corresponding fact. If `x`
is `y ⊔ z`, adds a fact about it, then recursively calls `addAtom` on `y` and `z`.
Similarly for `⊓`. Assumes that `type` is already added by `addType`. -/
/-
**Mathlib.Tactic.Order.addAtom** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.Orde
r`。
形式化陈述：{u : Level} → (type : Q(Type u)) → Q(«$type») → Mathlib.Tactic.Order.Colle
ctFactsM ℕ
参数：type : Q(Type u)；«$type»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Updates the state with the atom `x`. If `x` is `⊤` or `⊥`, adds the correspondin
g fact. If `x`
is `y ⊔ z`, adds a fact about it, then recursively calls `addAtom` on `y` and `z
`.
Similarly for `⊓`. Assumes that `type` is already added by `addType`.
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
/-- Implementation for `collectFacts` in `CollectFactsM` monad. -/
/-
**Mathlib.Tactic.Order.collectFactsImp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Order`。
形式化陈述：Bool → Array Expr → Expr → Mathlib.Tactic.Order.CollectFactsM Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation for `collectFacts` in `CollectFactsM` monad.
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
        addFact α <| .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .lt xIdx yIdx expr
    | ~q(@Ne ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .nlt xIdx yIdx expr
      | _ => return
    | ~q($p ∧ $q) =>
      processExpr q(And.left $expr)
      processExpr q(And.right $expr)
    | ~q(Exists $P) =>
      processExpr q(Exists.choose_spec $expr)
    | _ => return

/-- Collects facts from the local context. `negGoal` is the negated goal, `hyps` is the expressions
passed to the tactic using square brackets. If `only?` is true, we collect facts only from `hyps`
and `negGoal`, otherwise we also use the local context.

For each occurring type `α`, the returned map contains an array containing all collected
`AtomicFact`s about atoms of type `α`. -/
/-
**Mathlib.Tactic.Order.collectFacts** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Or
der`。
形式化陈述：collectFacts (only? : Bool) (hyps : Array Expr) (negGoal : Expr) : AtomM S
td.HashMap Expr Array AtomicFact
参数：only? : Bool；hyps : Array Expr；negGoal : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collects facts from the local context. `negGoal` is the negated goal, `hyps` is 
the expressions
passed to the tactic using square brackets. If `only?` is true, we collect facts
 only from `hyps`
and `negGoal`, otherwise we also use the local context.

For each occurring type `α`, the returned map contains an array containing all c
ollected
`AtomicFact`s about atoms of type `α`.
-/
def collectFacts (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
    AtomM <| Std.HashMap Expr <| Array AtomicFact := do
  return (← (collectFactsImp only? hyps negGoal).run ∅).snd

end Mathlib.Tactic.Order

