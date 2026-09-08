/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Patrick Massot
-/
module

public meta import Lean.Elab.Tactic.Location
public meta import Mathlib.Lean.Expr.Basic
public import Mathlib.Util.Tactic

/-!
# The `rename_bvar` tactic

This file defines the `rename_bvar` tactic, for renaming bound variables.
-/

public meta section

namespace Mathlib.Tactic

open Lean Parser Elab Tactic

/-- Renames a bound variable in a hypothesis. -/
/-
**Mathlib.Tactic.renameBVarHyp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：renameBVarHyp (mvarId : MVarId) (fvarId : FVarId) (old new : Name) : MetaM
 Unit
参数：mvarId : MVarId；fvarId : FVarId；old new : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Renames a bound variable in a hypothesis.
-/
def renameBVarHyp (mvarId : MVarId) (fvarId : FVarId) (old new : Name) :
    MetaM Unit :=
  modifyLocalDecl mvarId fvarId fun ldecl ↦
    ldecl.setType <| ldecl.type.renameBVar old new

/-- Renames a bound variable in the target. -/
/-
**Mathlib.Tactic.renameBVarTarget** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：renameBVarTarget (mvarId : MVarId) (old new : Name) : MetaM Unit
参数：mvarId : MVarId；old new : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Renames a bound variable in the target.
-/
def renameBVarTarget (mvarId : MVarId) (old new : Name) : MetaM Unit :=
  modifyTarget mvarId fun e ↦ e.renameBVar old new

/--
* `rename_bvar old → new` renames all bound variables named `old` to `new` in the target.
* `rename_bvar old → new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m := by
  rename_bvar n → q at h -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_bvar m → n -- target is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
```
Note: name clashes are resolved automatically.
-/
elab "rename_bvar " old:ident " → " new:ident loc?:(location)? : tactic => do
  let mvarId ← getMainGoal
  instantiateMVarDeclMVars mvarId
  match loc? with
  | none => renameBVarTarget mvarId old.getId new.getId
  | some loc =>
    withLocation (expandLocation loc)
      (fun fvarId ↦ renameBVarHyp mvarId fvarId old.getId new.getId)
      (renameBVarTarget mvarId old.getId new.getId)
      fun _ ↦ throwError "unexpected location syntax"

end Mathlib.Tactic

