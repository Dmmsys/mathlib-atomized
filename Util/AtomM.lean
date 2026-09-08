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

/-- The context (read-only state) of the `AtomM` monad. -/
/-
**Mathlib.Tactic.AtomM.Context** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.AtomM
`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The context (read-only state) of the `AtomM` monad.
-/
structure AtomM.Context where
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

/-- The mutable state of the `AtomM` monad. -/
/-
**Mathlib.Tactic.AtomM.State** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.AtomM`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mutable state of the `AtomM` monad.
-/
structure AtomM.State where
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Array Expr := #[]

/-- The monad that `ring` works in. This is only used for collecting atoms. -/
/-
**Mathlib.Tactic.AtomM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：AtomM
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad that `ring` works in. This is only used for collecting atoms.
-/
abbrev AtomM := ReaderT AtomM.Context <| StateRefT AtomM.State MetaM

/-- Run a computation in the `AtomM` monad. -/
/-
**Mathlib.Tactic.AtomM.run** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.AtomM`。
形式化陈述：{α : Type} →   Meta.TransparencyMode →     Mathlib.Tactic.AtomM α → (optPa
ram (Expr → MetaM Meta.Simp.Result) fun e => pure { expr := e }) → MetaM α
参数：optParam (Expr → MetaM Meta.Simp.Result) fun e => pure { expr := e }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run a computation in the `AtomM` monad.
-/
def AtomM.run {α : Type} (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  (m { red, evalAtom }).run' {}

/-- A safe version of `isDefEq` that doesn't throw errors. We use it to avoid
"unknown free variable `_fvar.102937`" errors when there may be out-of-scope free variables.

TODO: don't catch any other errors
-/
/-
**Mathlib.Tactic.isDefEqSafe** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：isDefEqSafe (a b : Expr) : MetaM Bool
参数：a b : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A safe version of `isDefEq` that doesn't throw errors. We use it to avoid
"unknown free variable `_fvar.102937`" errors when there may be out-of-scope fre
e variables.

TODO: don't catch any other errors
-/
def isDefEqSafe (a b : Expr) : MetaM Bool :=
  try isDefEq a b catch _ => pure false

/-- If an atomic expression has already been encountered, return `true`, the index and the stored
form of the atom (which will be defeq at the specified transparency, but not necessarily
syntactically equal). If the atomic expression has *not* already been encountered, store it in the
list of atoms, and return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `containsThenAdd` should be considered
the normal form.
-/
/-
**Mathlib.Tactic.AtomM.containsThenAdd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.AtomM`。
形式化陈述：Expr → Mathlib.Tactic.AtomM (Bool × ℕ × Expr)
参数：Bool × ℕ × Expr。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
If an atomic expression has already been encountered, return `true`, the index a
nd the stored
form of the atom (which will be defeq at the specified transparency, but not nec
essarily
syntactically equal). If the atomic expression has *not* already been encountere
d, store it in the
list of atoms, and return the new index (and the stored form of the atom, which 
will be itself).

In a normalizing tactic, the expression returned by `containsThenAdd` should be 
considered
the normal form.
-/
def AtomM.containsThenAdd (e : Expr) : AtomM (Bool × Nat × Expr) := do
  let c ← get
  for h : i in [:c.atoms.size] do
    if ← withTransparency (← read).red <| isDefEqSafe e c.atoms[i] then
      return (true, i, c.atoms[i])
  modifyGet fun c ↦ ((false, c.atoms.size, e), { c with atoms := c.atoms.push e })

open Qq in
/-- If an atomic expression has already been encountered, return `true`, the index and the stored
form of the atom (which will be defeq at the specified transparency, but not necessarily
syntactically equal). If the atomic expression has *not* already been encountered, store it in the
list of atoms, and return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `AtomM.containsThenAddQ` should be considered
the normal form.

This is a strongly-typed version of `AtomM.containsThenAdd` for code using `Qq`.
-/
/-
**Mathlib.Tactic.AtomM.containsThenAddQ** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.AtomM`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (e : Q(«$α»)) → Mathlib.Tactic.AtomM (Bool
 × ℕ × { e' // «$e» =Q «$e'» })
参数：Type u；e : Q(«$α»)；Bool × ℕ × { e' // «$e» =Q «$e'» }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an atomic expression has already been encountered, return `true`, the index a
nd the stored
form of the atom (which will be defeq at the specified transparency, but not nec
essarily
syntactically equal). If the atomic expression has *not* already been encountere
d, store it in the
list of atoms, and return the new index (and the stored form of the atom, which 
will be itself).

In a normalizing tactic, the expression returned by `AtomM.containsThenAddQ` sho
uld be considered
the normal form.

This is a strongly-typed version of `AtomM.containsThenAdd` for code using `Qq`.
-/
def AtomM.containsThenAddQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Bool × Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (b, n, e') ← AtomM.containsThenAdd e
  return (b, n, ⟨e', ⟨⟩⟩)

/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtom` should be considered the normal form.
-/
/-
**Mathlib.Tactic.AtomM.addAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.AtomM`。
形式化陈述：Expr → Mathlib.Tactic.AtomM (ℕ × Expr)
参数：ℕ × Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an atomic expression has already been encountered, get the index and the stor
ed form of the
atom (which will be defeq at the specified transparency, but not necessarily syn
tactically equal).
If the atomic expression has *not* already been encountered, store it in the lis
t of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtom` should be consider
ed the normal form.
-/
def AtomM.addAtom (e : Expr) : AtomM (Nat × Expr) :=
  Prod.snd <$> AtomM.containsThenAdd e

open Qq in
/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtomQ` should be considered the normal form.

This is a strongly-typed version of `AtomM.addAtom` for code using `Qq`.
-/
/-
**Mathlib.Tactic.AtomM.addAtomQ** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.AtomM`
。
形式化陈述：{u : Level} → {α : Q(Type u)} → (e : Q(«$α»)) → Mathlib.Tactic.AtomM (ℕ × 
{ e' // «$e» =Q «$e'» })
参数：Type u；e : Q(«$α»)；ℕ × { e' // «$e» =Q «$e'» }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an atomic expression has already been encountered, get the index and the stor
ed form of the
atom (which will be defeq at the specified transparency, but not necessarily syn
tactically equal).
If the atomic expression has *not* already been encountered, store it in the lis
t of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtomQ` should be conside
red the normal form.

This is a strongly-typed version of `AtomM.addAtom` for code using `Qq`.
-/
def AtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic

