/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-!
# Attribute to pretty-print universe level parameters by default

This module contains the `pp_with_univ` attribute, which enables pretty-printing
of universe parameters for the associated declaration. This is helpful for definitions like
`Ordinal`, where the universe levels are both relevant and not deducible from the arguments.
-/

public meta section

namespace Mathlib.PPWithUniv

open Lean Parser PrettyPrinter Delaborator SubExpr Elab Command

/--
Definition of `delabWithUniv` / `delabWithUniv` 的定义

English:
definition delabWithUniv
  signature: : Delab
  body: whenPPOption (·.get pp.universes.name true)
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead delabApp

中文:
定义 delabWithUniv
  签名: : Delab
  定义体: whenPPOption (·.get pp.universes.name true)
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead delabApp

Depends on / 依赖: SubExpr, delabApp, enablePPUnivOnHead, expr.getAppArgs, expr.getAppFn.setOption, getAppArgs, getAppFn, mkAppN, pp.universes.name, setOption, subExpr, subExpr.expr, universes, whenPPOption, withTheReader
-/
def delabWithUniv : Delab :=
whenPPOption (·.get pp.universes.name true)
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead delabApp

/--
`attribute [pp_with_univ] Ordinal` instructs the pretty-printer to
print `Ordinal.{u}` with universe parameters by default
(unless `pp.universes` is explicitly set to `false`).
-/
syntax (name := ppWithUnivAttr) "pp_with_univ" : attr

initialize registerBuiltinAttribute {
  name := `ppWithUnivAttr
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| pp_with_univ) => do
liftCommandElabM withRef ref do
let attr ← Elab.elabAttr ← `(Term.attrInstance| delab $(mkIdent <| `app ++ src))
liftTermElabM Term.applyAttributes ``delabWithUniv #[{attr with kind}]
  | _ => throwUnsupportedSyntax }

end PPWithUniv

end Mathlib
