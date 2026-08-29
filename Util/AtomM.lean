/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.Simp.Types
public import Qq
public import Qq.Typ

/-!
# A monad for tracking and deduplicating atoms

This monad is used by tactics like `ring` and `abel` to keep uninterpreted atoms in a consistent
order, and also to allow unifying atoms up to a specified transparency mode.

Note: this can become very expensive because it is using `isDefEq`.
For performance reasons, consider whether `Lean.Meta.Canonicalizer.canon` can be used instead.
After canonicalizing, a `HashMap Expr Nat` suffices to keep track of previously seen atoms,
and is much faster as it uses `Expr` equality rather than `isDefEq`.
-/

public meta section

namespace Mathlib.Tactic
open Lean Meta

/--
Definition of `AtomM.Context` / `AtomM.Context` 的定义

English:
structure AtomM.Context
  parameters: where
  axioms and operations (2):
    - red : TransparencyMode
    - evalAtom : Expr -> MetaM Simp.Result  [default: fun e => pure { expr := e }]

中文:
结构 AtomM.余ntext
  参数: where
  公理与运算 (2 个):
    - red : TransparencyMode
    - evalAtom : Expr -> MetaM Simp.Result  [默认: fun e => pure { expr := e }]
-/
structure AtomM.Context where
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr -> MetaM Simp.Result := fun e => pure { expr := e }
  deriving Inhabited

/--
Definition of `AtomM.State` / `AtomM.State` 的定义

English:
structure AtomM.State
  parameters: where
  axioms and operations (1):
    - atoms : Array Expr  [default: #[]]

中文:
结构 AtomM.State
  参数: where
  公理与运算 (1 个):
    - atoms : 数组 Expr  [默认: #[]]
-/
structure AtomM.State where
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Array Expr := #[]

/--
Definition of `AtomM` / `AtomM` 的定义

English:
abbreviation AtomM
  body: ReaderT AtomM.Context StateRefT AtomM.State MetaM

中文:
缩写 AtomM
  定义体: ReaderT AtomM.Context StateRefT AtomM.State MetaM

Depends on / 依赖: AtomM.Context, AtomM.State, Context, ReaderT, StateRefT
-/
abbrev AtomM := ReaderT AtomM.Context StateRefT AtomM.State MetaM

/--
Definition of `AtomM.run` / `AtomM.run` 的定义

English:
definition AtomM.run
  signature: {α : Type} (red : TransparencyMode) (m : AtomM α)
  body: (m { red, evalAtom }).run' {}

中文:
定义 AtomM.run
  签名: {α : 类型} (red : TransparencyMode) (m : AtomM α)
  定义体: (m { red, evalAtom }).run' {}
-/
def AtomM.run {α : Type} (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr -> MetaM Simp.Result := fun e => pure { expr := e }) :
    MetaM α :=
  (m { red, evalAtom }).run' {}

/--
Definition of `isDefEqSafe` / `isDefEqSafe` 的定义

English:
definition isDefEqSafe
  signature: (a b : Expr)
  body: try isDefEq a b catch _ => pure false

中文:
定义 isDefEqSafe
  签名: (a b : Expr)
  定义体: try isDefEq a b catch _ => pure false

Depends on / 依赖: isDefEq
-/
def isDefEqSafe (a b : Expr) : MetaM Bool :=
  try isDefEq a b catch _ => pure false

/--
Definition of `AtomM.containsThenAdd` / `AtomM.containsThenAdd` 的定义

English:
definition AtomM.containsThenAdd
  signature: (e : Expr)
  body: do
  let c ← get
  for h : i in [:c.atoms.size] do
if ← withTransparency (← read).red isDefEqSafe e c.atoms[i] then
      return (true, i, c.atoms[i])
  modifyGet fun c => ((false, c.atoms.size, e), { c with atoms := c.atoms.push e })

中文:
定义 AtomM.containsThenAdd
  签名: (e : Expr)
  定义体: do
  let c ← get
  for h : i in [:c.atoms.size] do
if ← withTransparency (← read).red isDefEqSafe e c.atoms[i] then
      return (true, i, c.atoms[i])
  modifyGet fun c => ((false, c.atoms.size, e), { c with atoms := c.atoms.push e })
-/
def AtomM.containsThenAdd (e : Expr) : AtomM (Bool × Nat × Expr) := do
  let c ← get
  for h : i in [:c.atoms.size] do
if ← withTransparency (← read).red isDefEqSafe e c.atoms[i] then
      return (true, i, c.atoms[i])
  modifyGet fun c => ((false, c.atoms.size, e), { c with atoms := c.atoms.push e })

open Qq in
/--
Definition of `AtomM.containsThenAddQ` / `AtomM.containsThenAddQ` 的定义

English:
definition AtomM.containsThenAddQ
  signature: {u : Level} {α : Q(Type u)} (e : Q($α))
  body: do
  let (b, n, e') ← AtomM.containsThenAdd e
  return (b, n, ⟨e', ⟨⟩⟩)

中文:
定义 AtomM.containsThenAddQ
  签名: {u : Level} {α : Q(类型u)} (e : Q($α))
  定义体: do
  let (b, n, e') ← AtomM.containsThenAdd e
  return (b, n, ⟨e', ⟨⟩⟩)
-/
def AtomM.containsThenAddQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Bool × Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (b, n, e') ← AtomM.containsThenAdd e
  return (b, n, ⟨e', ⟨⟩⟩)

/--
Definition of `AtomM.addAtom` / `AtomM.addAtom` 的定义

English:
definition AtomM.addAtom
  signature: (e : Expr)
  body: Prod.snd < > AtomM.containsThenAdd e

中文:
定义 AtomM.addAtom
  签名: (e : Expr)
  定义体: Prod.snd < > AtomM.containsThenAdd e

Depends on / 依赖: AtomM.containsThenAdd, Prod.snd, containsThenAdd
-/
def AtomM.addAtom (e : Expr) : AtomM (Nat × Expr) :=
Prod.snd < > AtomM.containsThenAdd e

open Qq in
/--
Definition of `AtomM.addAtomQ` / `AtomM.addAtomQ` 的定义

English:
definition AtomM.addAtomQ
  signature: {u : Level} {α : Q(Type u)} (e : Q($α))
  body: do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

中文:
定义 AtomM.addAtomQ
  签名: {u : Level} {α : Q(类型u)} (e : Q($α))
  定义体: do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)
-/
def AtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic
