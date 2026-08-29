/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init
public import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Additions to the delaborator
-/

@[expose] public section

namespace Lean.PrettyPrinter.Delaborator

open Delaborator.SubExpr

/--
Definition of `withBindingBodyUnusedName'` / `withBindingBodyUnusedName'` 的定义

English:
definition withBindingBodyUnusedName'
  signature: {α} (d : Syntax -> Expr -> DelabM α)
  body: do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)

中文:
定义 withBindingBodyUnusedName'
  签名: {α} (d : Syntax -> Expr -> DelabM α)
  定义体: do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)
-/
def withBindingBodyUnusedName' {α} (d : Syntax -> Expr -> DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)

/--
Definition of `OptionsPerPos.setBool` / `OptionsPerPos.setBool` 的定义

English:
definition OptionsPerPos.setBool
  signature: (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool)
  body: .setBool n v let e := opts.getD p {}
  opts.insert p e

中文:
定义 OptionsPerPos.set布尔
  签名: (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : 布尔值)
  定义体: .setBool n v let e := opts.getD p {}
  opts.insert p e

Depends on / 依赖: insert, opts.getD, opts.insert, setBool
-/
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
.setBool n v let e := opts.getD p {}
  opts.insert p e

/--
Definition of `annotateGoToDef` / `annotateGoToDef` 的定义

English:
definition annotateGoToDef
  signature: (stx : Term) (target : Name)
  body: do
  let module := (← findModuleOf? target).getD (← getEnv).mainModule
  let some range ← findDeclarationRanges? target | return stx
  let stx ← annotateCurPos stx
  let location := { module, range := range.selectionRange }
  addDelabTermInfo (← getPos) stx (← getExpr) (location? := some location)
  return stx

中文:
定义 annotateGoToDef
  签名: (stx : 项) (target : Name)
  定义体: do
  let module := (← findModuleOf? target).getD (← getEnv).mainModule
  let some range ← findDeclarationRanges? target | return stx
  let stx ← annotateCurPos stx
  let location := { module, range := range.selectionRange }
  addDelabTermInfo (← getPos) stx (← getExpr) (location? := some location)
  return stx
-/
def annotateGoToDef (stx : Term) (target : Name) : DelabM Term := do
  let module := (← findModuleOf? target).getD (← getEnv).mainModule
  let some range ← findDeclarationRanges? target | return stx
  let stx ← annotateCurPos stx
  let location := { module, range := range.selectionRange }
  addDelabTermInfo (← getPos) stx (← getExpr) (location? := some location)
  return stx

/--
Definition of `annotateGoToSyntaxDef` / `annotateGoToSyntaxDef` 的定义

English:
definition annotateGoToSyntaxDef
  signature: (stx : Term)
  body: do
  annotateGoToDef stx stx.raw.getKind

中文:
定义 annotateGoToSyntaxDef
  签名: (stx : 项)
  定义体: do
  annotateGoToDef stx stx.raw.getKind
-/
def annotateGoToSyntaxDef (stx : Term) : DelabM Term := do
  annotateGoToDef stx stx.raw.getKind

end Lean.PrettyPrinter.Delaborator
