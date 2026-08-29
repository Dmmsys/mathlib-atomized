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

/--
Definition of `renameBVarHyp` / `renameBVarHyp` 的定义

English:
definition renameBVarHyp
  signature: (mvarId : MVarId) (fvarId : FVarId) (old new : Name)
  body: modifyLocalDecl mvarId fvarId fun ldecl =>
ldecl.setType ldecl.type.renameBVar old new

中文:
定义 renameBVarHyp
  签名: (mvarId : MVarId) (fvarId : FVarId) (old new : Name)
  定义体: modifyLocalDecl mvarId fvarId fun ldecl =>
ldecl.setType ldecl.type.renameBVar old new

Depends on / 依赖: fvarId, ldecl.setType, ldecl.type.renameBVar, modifyLocalDecl, mvarId, renameBVar, setType
-/
def renameBVarHyp (mvarId : MVarId) (fvarId : FVarId) (old new : Name) :
    MetaM Unit :=
  modifyLocalDecl mvarId fvarId fun ldecl =>
ldecl.setType ldecl.type.renameBVar old new

/--
Definition of `renameBVarTarget` / `renameBVarTarget` 的定义

English:
definition renameBVarTarget
  signature: (mvarId : MVarId) (old new : Name)
  body: modifyTarget mvarId fun e => e.renameBVar old new

中文:
定义 renameBVarTarget
  签名: (mvarId : MVarId) (old new : Name)
  定义体: modifyTarget mvarId fun e => e.renameBVar old new

Depends on / 依赖: e.renameBVar, modifyTarget, mvarId, renameBVar
-/
def renameBVarTarget (mvarId : MVarId) (old new : Name) : MetaM Unit :=
  modifyTarget mvarId fun e => e.renameBVar old new

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
elab "rename_bvar " old:ident " -> " new:ident loc?:(location)? : tactic => do
  let mvarId ← getMainGoal
  instantiateMVarDeclMVars mvarId
  match loc? with
  | none => renameBVarTarget mvarId old.getId new.getId
  | some loc =>
    withLocation (expandLocation loc)
      (fun fvarId => renameBVarHyp mvarId fvarId old.getId new.getId)
      (renameBVarTarget mvarId old.getId new.getId)
      fun _ => throwError "unexpected location syntax"

end Mathlib.Tactic
