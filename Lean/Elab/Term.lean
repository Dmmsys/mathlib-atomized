/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
module

public import Mathlib.Init
public import Lean.Elab.Term

/-!
# Additions to `Lean.Elab.Term`
-/

public meta section

namespace Lean.Elab.Term

/-- Fully elaborates the term `patt`, allowing typeclass inference failure,
but while setting `errToSorry` to false.
Typeclass failures result in plain metavariables.
Instantiates all assigned metavariables. -/
/-
**Lean.Elab.Term.elabPattern** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Term`。
形式化陈述：elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr
参数：patt : Term；expectedType? : Option Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fully elaborates the term `patt`, allowing typeclass inference failure,
but while setting `errToSorry` to false.
Typeclass failures result in plain metavariables.
Instantiates all assigned metavariables.
-/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

end Lean.Elab.Term

