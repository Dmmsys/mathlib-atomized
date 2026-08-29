/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.SyntheticMVars
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# Additions to `Lean.Elab.Tactic.Meta`
-/

@[expose] public section

namespace Lean.Elab
open Term

/--
Definition of `runTactic'` / `runTactic'` 的定义

English:
definition runTactic'
  signature: (mvarId : MVarId) (tacticCode : Syntax) (ctx : Context := {}) (s : State := {})
  body: do
  instantiateMVarDeclMVars mvarId
  let go : TermElabM (List MVarId) :=
    withSynthesize do Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run' ctx s

中文:
定义 runTactic'
  签名: (mvarId : MVarId) (tacticCode : Syntax) (ctx : Context := {}) (s : State := {})
  定义体: do
  instantiateMVarDeclMVars mvarId
  let go : TermElabM (List MVarId) :=
    withSynthesize do Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run' ctx s
-/
def runTactic' (mvarId : MVarId) (tacticCode : Syntax) (ctx : Context := {}) (s : State := {}) :
    MetaM (List MVarId) := do
  instantiateMVarDeclMVars mvarId
  let go : TermElabM (List MVarId) :=
    withSynthesize do Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run' ctx s

end Lean.Elab
