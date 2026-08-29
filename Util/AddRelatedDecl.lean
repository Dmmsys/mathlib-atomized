/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Init
public meta import Lean.Elab.DeclarationRange
public meta import Lean.Linter.TacticTypeCheck

/-!
# `addRelatedDecl`

-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic

/-- An `(attr := ...)` argument for applying the same attributes to multiple declarations. -/
syntax optAttrArg := atomic(" (" &"attr" " := " Parser.Term.attrInstance,* ")")?

/--
Definition of `elabOptAttrArg` / `elabOptAttrArg` 的定义

English:
definition elabOptAttrArg
  signature: : TSyntax ``optAttrArg -> TermElabM (Array Attribute)

中文:
定义 elabOptAttrArg
  签名: : TSyntax ``optAttrArg -> TermElabM (Array Attribute)

Depends on / 依赖: elabAttrs
-/
def elabOptAttrArg : TSyntax ``optAttrArg -> TermElabM (Array Attribute)
  | `(optAttrArg| (attr := $[$attrs],*)) => elabAttrs attrs
  | _ => pure #[]

/--
Definition of `checkImplicitTransparency` / `checkImplicitTransparency` 的定义

English:
definition checkImplicitTransparency
  signature: (declType : Expr)
  body: do
  let origDiag := (← get).diag
  let result : Option (List Name) ← withOptions (diagnostics.set · true) do
    try Meta.check declType .default catch _ => return none
    let counterDefault := (← get).diag.unfoldCounter
    modify ({ · with diag := origDiag })
    try
      Meta.check declType .i

中文:
定义 checkImplicitTransparency
  签名: (declType : Expr)
  定义体: do
  let origDiag := (← get).diag
  let result : Option (List Name) ← withOptions (diagnostics.set · true) do
    try Meta.check declType .default catch _ => return none
    let counterDefault := (← get).diag.unfoldCounter
    modify ({ · with diag := origDiag })
    try
      Meta.check declType .i
-/
private def checkImplicitTransparency (declType : Expr) : MetaM (Option (List Name)) := do
  let origDiag := (← get).diag
  let result : Option (List Name) ← withOptions (diagnostics.set · true) do
    try Meta.check declType .default catch _ => return none
    let counterDefault := (← get).diag.unfoldCounter
    modify ({ · with diag := origDiag })
    try
      Meta.check declType .implicit
      return none
    catch _ =>
      let counterInst := (← get).diag.unfoldCounter
      let diff := Meta.subCounters counterDefault counterInst
      let env ← getEnv
return some diff.toList.filterMap fun (n, count) => do
guard count > 0
guard getReducibilityStatusCore env n matches .semireducible
guard !Meta.isInstanceCore env n
        return n
  -- Always restore the original diagnostics snapshot, mirroring `tacticCheckInstances`.
  modify ({ · with diag := origDiag })
  return result

/--
Definition of `warnIfImplicitIllTyped` / `warnIfImplicitIllTyped` 的定义

English:
definition warnIfImplicitIllTyped
  signature: (ref : Syntax) (declName : Name) (declType : Expr)
  body: do
  let lintOpt : Lean.Option Bool :=
    { name := `linter.tacticCheckInstances, defValue := false }
  unless lintOpt.get (← getOptions) do return
  let some candidates ← checkImplicitTransparency declType | return
  if candidates.isEmpty then return
  let bullets := MessageData.joinSep (candidate

中文:
定义 warnIfImplicitIllTyped
  签名: (ref : Syntax) (declName : Name) (declType : Expr)
  定义体: do
  let lintOpt : Lean.Option Bool :=
    { name := `linter.tacticCheckInstances, defValue := false }
  unless lintOpt.get (← getOptions) do return
  let some candidates ← checkImplicitTransparency declType | return
  if candidates.isEmpty then return
  let bullets := MessageData.joinSep (candidate
-/
def warnIfImplicitIllTyped (ref : Syntax) (declName : Name) (declType : Expr) : MetaM Unit := do
  let lintOpt : Lean.Option Bool :=
    { name := `linter.tacticCheckInstances, defValue := false }
  unless lintOpt.get (← getOptions) do return
  let some candidates ← checkImplicitTransparency declType | return
  if candidates.isEmpty then return
  let bullets := MessageData.joinSep (candidates.map (m!"{MessageData.ofConstName ·}")) Format.line
  Lean.Linter.logLint lintOpt ref
    m!"generated lemma {MessageData.ofConstName declName} is not type-correct at \
      `.implicit` transparency; consider marking some of the following as \
      `@[implicit_reducible]`:{indentD bullets}"

/--
Definition of `addRelatedDecl` / `addRelatedDecl` 的定义

English:
definition addRelatedDecl
  signature: (src tgt : Name) (ref : Syntax)
  body: do
  -- If `tgt` already exists in an imported module, the `addDeclarationRangesFromSyntax` call
  -- below panics (and if it exists in the current module, `addDecl` would fail with a less
  -- helpful message), so we check for a pre-existing declaration up front.
  checkNotAlreadyDeclared tgt
  add

中文:
定义 addRelatedDecl
  签名: (src tgt : Name) (ref : Syntax)
  定义体: do
  -- If `tgt` already exists in an imported module, the `addDeclarationRangesFromSyntax` call
  -- below panics (and if it exists in the current module, `addDecl` would fail with a less
  -- helpful message), so we check for a pre-existing declaration up front.
  checkNotAlreadyDeclared tgt
  add
-/
def addRelatedDecl (src tgt : Name) (ref : Syntax)
    (attrs : TSyntax ``optAttrArg)
    (construct : Expr -> List Name -> MetaM (Expr × List Name))
    (docstringPrefix? : Option String := none)
    (hoverInfo : Bool := false) :
    MetaM Unit := do
  -- If `tgt` already exists in an imported module, the `addDeclarationRangesFromSyntax` call
  -- below panics (and if it exists in the current module, `addDecl` would fail with a less
  -- helpful message), so we check for a pre-existing declaration up front.
  checkNotAlreadyDeclared tgt
  addDeclarationRangesFromSyntax tgt (← getRef) ref
let info ← withoutExporting getConstInfo src
  let value := .const src (info.levelParams.map mkLevelParam)
  let (newValue, newLevels) ← construct value info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  unless ← isProp newType do throwError "Related declaration is not a proposition: {newType}"
  warnIfImplicitIllTyped ref tgt newType
addDecl ← mkThmOrUnsafeDef
    { levelParams := newLevels, type := newType, name := tgt, value := newValue }
  if isProtected (← getEnv) src then
setEnv addProtected (← getEnv) tgt
  match docstringPrefix?, ← findDocString? (← getEnv) src with
  | none, none => pure ()
  | some doc, none | none, some doc => addDocStringCore tgt doc
  | some docPre, some docPost => addDocStringCore tgt s!"{docPre}\n\n---\n\n{docPost}"
  inferDefEqAttr tgt
  Term.TermElabM.run' do
    let attrs ← elabOptAttrArg attrs
    Term.applyAttributes src attrs
    Term.applyAttributes tgt attrs
    if hoverInfo then
      Term.addTermInfo' ref (← mkConstWithLevelParams tgt) (isBinder := true)

end Mathlib.Tactic
