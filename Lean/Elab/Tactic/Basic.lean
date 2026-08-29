/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jon Eugster
-/
module

public import Mathlib.Lean.Meta
/-!
# Additions to `Lean.Elab.Tactic.Basic`
-/

@[expose] public section

open Lean Elab Tactic

namespace Lean.Elab.Tactic

/--
Definition of `getMainTarget''` / `getMainTarget''` 的定义

English:
definition getMainTarget''
  signature: : TacticM Expr
  body: do
  (← getMainGoal).getType''

中文:
定义 getMainTarget''
  签名: : TacticM Expr
  定义体: do
  (← getMainGoal).getType''
-/
def getMainTarget'' : TacticM Expr := do
  (← getMainGoal).getType''

end Lean.Elab.Tactic
