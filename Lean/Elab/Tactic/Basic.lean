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

/-- Return expected type for the main goal, cleaning up annotations, using `Lean.MVarId.getType''`.
Remark: note that `MVarId.getType'` uses `whnf` instead of `cleanupAnnotations`, and
`MVarId.getType''` also uses `cleanupAnnotations` -/
/-
**Lean.Elab.Tactic.getMainTarget''** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：getMainTarget'' : TacticM Expr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return expected type for the main goal, cleaning up annotations, using `Lean.MVa
rId.getType''`.
Remark: note that `MVarId.getType'` uses `whnf` instead of `cleanupAnnotations`,
 and
`MVarId.getType''` also uses `cleanupAnnotations`
-/
def getMainTarget'' : TacticM Expr := do
  (← getMainGoal).getType''

end Lean.Elab.Tactic

