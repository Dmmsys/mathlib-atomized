/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Environment
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# Additional utilities for `Lean.Environment`
-/

namespace Lean.Environment

public section constKind

/- The following declarations account for the fact that the `ConstantKind` of a declaration is
accessible when getting its `ConstantVal`, but is not recorded in said `ConstantVal`. -/

/--
Definition of `findConstValWithKind?` / `findConstValWithKind?` 的定义

English:
definition findConstValWithKind?
  signature: (env : Environment) (decl : Name) (skipRealize := false)
  body: do
  let info ← env.findAsync? decl skipRealize
  return (info.toConstantVal, info.kind)

中文:
定义 findConstValWithKind?
  签名: (env : Environment) (decl : Name) (skip实数ize := false)
  定义体: do
  let info ← env.findAsync? decl skipRealize
  return (info.toConstantVal, info.kind)
-/
def findConstValWithKind? (env : Environment) (decl : Name) (skipRealize := false) :
    Option (ConstantVal × ConstantKind) := do
  let info ← env.findAsync? decl skipRealize
  return (info.toConstantVal, info.kind)

/--
Definition of `findConstValOfKind?` / `findConstValOfKind?` 的定义

English:
definition findConstValOfKind?
  signature: (env : Environment) (p : ConstantKind -> Bool) (decl : Name)
  body: do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

中文:
定义 findConstValOfKind?
  签名: (env : Environment) (p : ConstantKind -> 布尔值) (decl : Name)
  定义体: do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

Depends on / 依赖: ConstantVal
-/
def findConstValOfKind? (env : Environment) (p : ConstantKind -> Bool) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

/--
Definition of `findTheoremConstVal?` / `findTheoremConstVal?` 的定义

English:
definition findTheoremConstVal?
  signature: (env : Environment) (decl : Name)
  body: do
  env.findConstValOfKind? (· matches .thm) decl skipRealize

中文:
定义 findTheoremConstVal?
  签名: (env : Environment) (decl : Name)
  定义体: do
  env.findConstValOfKind? (· matches .thm) decl skipRealize

Depends on / 依赖: ConstantVal
-/
def findTheoremConstVal? (env : Environment) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  env.findConstValOfKind? (· matches .thm) decl skipRealize

end constKind

end Lean.Environment
