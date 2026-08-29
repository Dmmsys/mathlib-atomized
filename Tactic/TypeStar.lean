/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# Support for `Sort*` and `Type*`.

These elaborate as `Sort u` and `Type u` with a fresh implicit universe variable `u`.
-/

public meta section

namespace Lean.Elab.Term

/--
Definition of `mkFreshLevelName` / `mkFreshLevelName` 的定义

English:
definition mkFreshLevelName
  signature: (usedLevelNames : List Name) (namePrefix : Name := `u)
  body: go 1

中文:
定义 mkFreshLevelName
  签名: (usedLevelNames : 列表 Name) (namePrefix : Name := `u)
  定义体: go 1
-/
partial def mkFreshLevelName (usedLevelNames : List Name) (namePrefix : Name := `u) : Name :=
  go 1
where
  /-- Check if `namePrefix.appendIndexAfter n` is unused, else recurse with `n+1`. -/
  go n : Name :=
    let u := namePrefix.appendIndexAfter n
    if usedLevelNames.contains u then go (n+1) else u

/--
Definition of `mkFreshLevelParam` / `mkFreshLevelParam` 的定义

English:
definition mkFreshLevelParam
  signature: (namePrefix : Name := `u)
  body: do
  let levelNames ← getLevelNames
  let u := mkFreshLevelName levelNames namePrefix
setLevelNames insert levelNames u
  return mkLevelParam u

中文:
定义 mkFreshLevelParam
  签名: (namePrefix : Name := `u)
  定义体: do
  let levelNames ← getLevelNames
  let u := mkFreshLevelName levelNames namePrefix
setLevelNames insert levelNames u
  return mkLevelParam u
-/
def mkFreshLevelParam (namePrefix : Name := `u)
    (insert : List Name -> Name -> List Name := (·.cons)) : TermElabM Level := do
  let levelNames ← getLevelNames
  let u := mkFreshLevelName levelNames namePrefix
setLevelNames insert levelNames u
  return mkLevelParam u

/-- The syntax `variable (X Y ... Z : Sort*)` creates a new distinct implicit universe variable
for each variable in the sequence. -/
elab "Sort*" : term => return .sort ← mkFreshLevelParam

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => return .sort .succ ← mkFreshLevelParam

end Lean.Elab.Term
