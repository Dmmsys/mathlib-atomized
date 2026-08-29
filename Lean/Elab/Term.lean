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

/--
Definition of `elabPattern` / `elabPattern` 的定义

English:
definition elabPattern
  signature: (patt : Term) (expectedType? : Option Expr)
  body: do
withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false })
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

中文:
定义 elabPattern
  签名: (patt : 项) (expectedType? : 选项类型 Expr)
  定义体: do
withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false })
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t
-/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false })
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

end Lean.Elab.Term
