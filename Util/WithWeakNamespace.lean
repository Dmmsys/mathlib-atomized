/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam, Gabriel Ebner
-/
module

public import Mathlib.Init

/-!
# Defines `with_weak_namespace` command.

Changes the current namespace without causing scoped things to go out of scope.
-/

public meta section

namespace Lean.Elab.Command

/--
Definition of `resolveNamespace` / `resolveNamespace` 的定义

English:
definition resolveNamespace
  signature: (ns : Name)

中文:
定义 resolveNamespace
  签名: (ns : Name)
-/
def resolveNamespace (ns : Name) : Name -> Name
  | `_root_ => Name.anonymous
  | Name.str n s .. => Name.mkStr (resolveNamespace ns n) s
  | Name.num n i .. => Name.mkNum (resolveNamespace ns n) i
  | Name.anonymous => ns

/--
Definition of `withWeakNamespace` / `withWeakNamespace` 的定义

English:
definition withWeakNamespace
  signature: {α : Type} (ns : Name) (m : CommandElabM α)
  body: do
  let old ← getCurrNamespace
  let ns := resolveNamespace old ns
  modify fun s => { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

中文:
定义 withWeakNamespace
  签名: {α : 类型} (ns : Name) (m : CommandElabM α)
  定义体: do
  let old ← getCurrNamespace
  let ns := resolveNamespace old ns
  modify fun s => { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })
-/
def withWeakNamespace {α : Type} (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  let ns := resolveNamespace old ns
  modify fun s => { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

/-- Changes the current namespace without causing scoped things to go out of scope -/
elab "with_weak_namespace " ns:ident cmd:command : command =>
  withWeakNamespace ns.getId (elabCommand cmd)

end Lean.Elab.Command
