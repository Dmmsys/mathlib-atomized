/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
`dsimp% […] t` runs `dsimp […]` on term `t`.
If `t` is a proof, then it runs `dsimp […]` on the type of `t` instead.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can do `rw [dsimp% foo]`.
-/

public meta section

namespace Mathlib.Tactic

open Lean Elab Term Meta Parser Tactic

/--
`dsimp% […] t` runs `dsimp […]` on term `t`.
If `t` is a proof, then it runs `dsimp […]` on the type of `t` instead.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can write `rw [dsimp% foo]`.
-/
syntax (name := dsimpPercent) "dsimp%" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? ppSpace term : term

@[term_elab dsimpPercent, inherit_doc dsimpPercent]
/--
Definition of `dsimpPercentElaborator` / `dsimpPercentElaborator` 的定义

English:
definition dsimpPercentElaborator
  signature: : TermElab
  body: fun stx expectedType => do
  let fresh ← mkFreshExprMVar default
  let go : TacticM Expr := do
    let e ← Term.elabTerm stx[5] expectedType
    -- `stx` has the same shape as a normal `dsimp` call, so we can pass it to `mkSimpContext`.
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let dsimp (e : Expr) : MetaM Expr := do
      -- Ensure that only instantiating metavariables isn't counted as progress.
      let e ← instantiateMVars e
      let (dsimpResult, _) ← Meta.dsimp e ctx simprocs
      if dsimpResult == e then
        throwError "`dsimp%` made no progress"
      return dsimpResult
    if ← isProof e then
      mkExpectedTypeHint e (← dsimp (← inferType e))
    else
      dsimp e
.run' { goals := [fresh.mvarId!] } go { elaborator := .anonymous }

中文:
定义 dsimpPercentElaborator
  签名: : TermElab
  定义体: fun stx expectedType => do
  let fresh ← mkFreshExprMVar default
  let go : TacticM Expr := do
    let e ← Term.elabTerm stx[5] expectedType
    -- `stx` has the same shape as a normal `dsimp` call, so we can pass it to `mkSimpContext`.
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let dsimp (e : Expr) : MetaM Expr := do
      -- Ensure that only instantiating metavariables isn't counted as progress.
      let e ← instantiateMVars e
      let (dsimpResult, _) ← Meta.dsimp e ctx simprocs
      if dsimpResult == e then
        throwError "`dsimp%` made no progress"
      return dsimpResult
    if ← isProof e then
      mkExpectedTypeHint e (← dsimp (← inferType e))
    else
      dsimp e
.run' { goals := [fresh.mvarId!] } go { elaborator := .anonymous }

Depends on / 依赖: expectedType
-/
def dsimpPercentElaborator : TermElab := fun stx expectedType => do
  let fresh ← mkFreshExprMVar default
  let go : TacticM Expr := do
    let e ← Term.elabTerm stx[5] expectedType
    -- `stx` has the same shape as a normal `dsimp` call, so we can pass it to `mkSimpContext`.
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let dsimp (e : Expr) : MetaM Expr := do
      -- Ensure that only instantiating metavariables isn't counted as progress.
      let e ← instantiateMVars e
      let (dsimpResult, _) ← Meta.dsimp e ctx simprocs
      if dsimpResult == e then
        throwError "`dsimp%` made no progress"
      return dsimpResult
    if ← isProof e then
      mkExpectedTypeHint e (← dsimp (← inferType e))
    else
      dsimp e
.run' { goals := [fresh.mvarId!] } go { elaborator := .anonymous }

end Mathlib.Tactic
