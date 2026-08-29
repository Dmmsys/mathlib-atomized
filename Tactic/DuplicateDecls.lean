/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init
public import ImportGraph.Lean.Environment

/-!
# A tool for finding duplicate declarations

It is easy to accidentally create multiple instances of the same theorem or instance.
This file defines a tool to automatically detect such cases.
The order of hypotheses, and their binder info and binder names are ignored.
Universe parameters are also ignored.

For theorems, it is completely redundant to have multiple of the same type.
For instances, we typically also don't want to have multiple of the same type.

To use it, simply run the following command in a file that does not use the module system:
```
open Lean Mathlib.Tactic.DuplicateDecls
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"
run_meta do logInfo m!"{← lintDuplicateDeclarations .instances}"
run_meta do logInfo m!"{← lintDuplicateDeclarations .defs}"
```

## How does it work

The function `sortBinders` reorders the forall binders of a declaration type into a canonical form,
which lets us detect duplication even when the arguments are in a different order.
We also erase the binder kinds (e.g. implicit/explicit) in the type,
and we erase all universe levels, both of which help to find more duplicates.

To avoid flagging aliases as duplicate (which are most likely intentionally duplicated),
we filter out declarations that are defined as another declaration (see `isAlias`).

The results are sorted by module name.
-/

meta section

namespace Mathlib.Tactic.DuplicateDecls
open Lean Meta

-- Note: I tried using a cache in the implementation, but that seemed to only slow things down.
/--
Definition of `eraseUnivs` / `eraseUnivs` 的定义

English:
definition eraseUnivs
  signature: (e : Expr)
  body: match e with
  | .sort _ => .sort 0
  | .const declName _ => .const declName []
  | .app fn arg => e.updateApp! (eraseUnivs fn) (eraseUnivs arg)
  | .lam _ t b _ => e.updateLambdaE! (eraseUnivs t) (eraseUnivs b)
  | .forallE _ t b _ => e.updateForallE! (eraseUnivs t) (eraseUnivs b)
  | .letE _ t v b _ => e.updateLetE! (eraseUnivs t) (eraseUnivs v) (eraseUnivs b)
  | .mdata _ expr => e.updateMData! (eraseUnivs expr)
  | .proj _ _ s => e.updateProj! (eraseUnivs s)
  | e => e

中文:
定义 eraseUnivs
  签名: (e : Expr)
  定义体: match e with
  | .sort _ => .sort 0
  | .const declName _ => .const declName []
  | .app fn arg => e.updateApp! (eraseUnivs fn) (eraseUnivs arg)
  | .lam _ t b _ => e.updateLambdaE! (eraseUnivs t) (eraseUnivs b)
  | .forallE _ t b _ => e.updateForallE! (eraseUnivs t) (eraseUnivs b)
  | .letE _ t v b _ => e.updateLetE! (eraseUnivs t) (eraseUnivs v) (eraseUnivs b)
  | .mdata _ expr => e.updateMData! (eraseUnivs expr)
  | .proj _ _ s => e.updateProj! (eraseUnivs s)
  | e => e
-/
partial def eraseUnivs (e : Expr) : Expr :=
  match e with
  | .sort _ => .sort 0
  | .const declName _ => .const declName []
  | .app fn arg => e.updateApp! (eraseUnivs fn) (eraseUnivs arg)
  | .lam _ t b _ => e.updateLambdaE! (eraseUnivs t) (eraseUnivs b)
  | .forallE _ t b _ => e.updateForallE! (eraseUnivs t) (eraseUnivs b)
  | .letE _ t v b _ => e.updateLetE! (eraseUnivs t) (eraseUnivs v) (eraseUnivs b)
  | .mdata _ expr => e.updateMData! (eraseUnivs expr)
  | .proj _ _ s => e.updateProj! (eraseUnivs s)
  | e => e

/--
Definition of `sortBinders` / `sortBinders` 的定义

English:
definition sortBinders
  signature: (e : Expr)
  body: do
  (if e.isLambda then lambdaTelescope else forallTelescope) e fun fvars e => do
  let n := fvars.size
  let fvars : Vector Expr n := fvars.toVector
  let mut remainingTypes ← fvars.mapM (return some <| eraseUnivs <| ← inferType ·)
  let mut e := eraseUnivs e
  let mut sortedTypes := #[]
  for _ in *...n do
    let mut minType? : Option (Fin n × Expr) := none
    for h : i in 0...n do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if let some (minIdx, minType) := minType? then
            if type.quickLt minType then
              continue
          minType? := some (⟨i, by get_elem_tactic⟩, type)
    let some (minIdx, minType) := minType? |
      panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e => .forallE `_ type e .default

中文:
定义 sortBinders
  签名: (e : Expr)
  定义体: do
  (if e.isLambda then lambdaTelescope else forallTelescope) e fun fvars e => do
  let n := fvars.size
  let fvars : Vector Expr n := fvars.toVector
  let mut remainingTypes ← fvars.mapM (return some <| eraseUnivs <| ← inferType ·)
  let mut e := eraseUnivs e
  let mut sortedTypes := #[]
  for _ in *...n do
    let mut minType? : Option (Fin n × Expr) := none
    for h : i in 0...n do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if let some (minIdx, minType) := minType? then
            if type.quickLt minType then
              continue
          minType? := some (⟨i, by get_elem_tactic⟩, type)
    let some (minIdx, minType) := minType? |
      panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e => .forallE `_ type e .default
-/
def sortBinders (e : Expr) : MetaM Expr := do
  (if e.isLambda then lambdaTelescope else forallTelescope) e fun fvars e => do
  let n := fvars.size
  let fvars : Vector Expr n := fvars.toVector
  let mut remainingTypes ← fvars.mapM (return some <| eraseUnivs <| ← inferType ·)
  let mut e := eraseUnivs e
  let mut sortedTypes := #[]
  for _ in *...n do
    let mut minType? : Option (Fin n × Expr) := none
    for h : i in 0...n do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if let some (minIdx, minType) := minType? then
            if type.quickLt minType then
              continue
          minType? := some (⟨i, by get_elem_tactic⟩, type)
    let some (minIdx, minType) := minType? |
      panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e => .forallE `_ type e .default

/--
Definition of `isAlias` / `isAlias` 的定义

English:
definition isAlias
  signature: (cinfo : ConstantInfo)
  body: (cinfo.value? (allowOpaque := true)).any isConstBVarApp

中文:
定义 isAlias
  签名: (cinfo : ConstantInfo)
  定义体: (cinfo.value? (allowOpaque := true)).any isConstBVarApp

Depends on / 依赖: allowOpaque, cinfo.value, isConstBVarApp
-/
def isAlias (cinfo : ConstantInfo) : Bool :=
  (cinfo.value? (allowOpaque := true)).any isConstBVarApp
where
  isConstBVarApp : Expr -> Bool
  | .const .. => true
  | .app f (.bvar _) => isConstBVarApp f
  | .lam _ _ b _ => isConstBVarApp b
  | _ => false

/-- An inductive type for the kind of duplicate declarations to search for. -/
public inductive Target where
  /-- Search for duplicate theorems. -/
  | theorems
  /-- Search for duplicate instances that aren't theorems. -/
  | instances
  /-- Search for duplicate definitions that aren't instances or theorems,
  Also indexes on the value, not just the type. -/
  | defs

/--
Definition of `duplicateDeclarations` / `duplicateDeclarations` 的定义

English:
definition duplicateDeclarations
  signature: (cfg : Target)
  body: MetaM.run' do
  let env ← getEnv
  let mut visited : Std.HashMap Expr Name := {}
  let mut dups : Std.HashMap Expr (Array Name) := {}
  for (name, cinfo) in env.constants.map₁ do
    if name.isInternalDetail
      || name.isMetaprogramming
      || !allowCompletion env name
      || Linter.isDeprecated env name
      || isAlias cinfo then continue
    if ← isProp cinfo.type then
      unless cfg matches .theorems do continue
    else
      match cfg with
      | .theorems => continue
      | .instances => if (← isClass? cinfo.type).isNone then continue
      | .defs =>
        if (← isClass? cinfo.type).isNone then
          if let some value := cinfo.value? then
            let normValue ← sortBinders value
            let normType ← sortBinders cinfo.type
            let key := .app normValue normType
            if let some name' := visited[key]? then
              dups := dups.alter key (·.getD #[name'] |>.push name)
            else
              visited := visited.insert key name
        continue
    let normType ← sortBinders cinfo.type
    if let some name' := visited[normType]? then
      dups := dups.alter normType (·.getD #[name'] |>.push name)
    else
      visited := visited.insert normType name
  return dups.valuesArray

中文:
定义 duplicateDeclarations
  签名: (cfg : Target)
  定义体: MetaM.run' do
  let env ← getEnv
  let mut visited : Std.HashMap Expr Name := {}
  let mut dups : Std.HashMap Expr (Array Name) := {}
  for (name, cinfo) in env.constants.map₁ do
    if name.isInternalDetail
      || name.isMetaprogramming
      || !allowCompletion env name
      || Linter.isDeprecated env name
      || isAlias cinfo then continue
    if ← isProp cinfo.type then
      unless cfg matches .theorems do continue
    else
      match cfg with
      | .theorems => continue
      | .instances => if (← isClass? cinfo.type).isNone then continue
      | .defs =>
        if (← isClass? cinfo.type).isNone then
          if let some value := cinfo.value? then
            let normValue ← sortBinders value
            let normType ← sortBinders cinfo.type
            let key := .app normValue normType
            if let some name' := visited[key]? then
              dups := dups.alter key (·.getD #[name'] |>.push name)
            else
              visited := visited.insert key name
        continue
    let normType ← sortBinders cinfo.type
    if let some name' := visited[normType]? then
      dups := dups.alter normType (·.getD #[name'] |>.push name)
    else
      visited := visited.insert normType name
  return dups.valuesArray

Depends on / 依赖: MetaM.run
-/
def duplicateDeclarations (cfg : Target) : CoreM (Array (Array Name)) := MetaM.run' do
  let env ← getEnv
  let mut visited : Std.HashMap Expr Name := {}
  let mut dups : Std.HashMap Expr (Array Name) := {}
  for (name, cinfo) in env.constants.map₁ do
    if name.isInternalDetail
      || name.isMetaprogramming
      || !allowCompletion env name
      || Linter.isDeprecated env name
      || isAlias cinfo then continue
    if ← isProp cinfo.type then
      unless cfg matches .theorems do continue
    else
      match cfg with
      | .theorems => continue
      | .instances => if (← isClass? cinfo.type).isNone then continue
      | .defs =>
        if (← isClass? cinfo.type).isNone then
          if let some value := cinfo.value? then
            let normValue ← sortBinders value
            let normType ← sortBinders cinfo.type
            let key := .app normValue normType
            if let some name' := visited[key]? then
              dups := dups.alter key (·.getD #[name'] |>.push name)
            else
              visited := visited.insert key name
        continue
    let normType ← sortBinders cinfo.type
    if let some name' := visited[normType]? then
      dups := dups.alter normType (·.getD #[name'] |>.push name)
    else
      visited := visited.insert normType name
  return dups.valuesArray

/--
Definition of `libraryNumber` / `libraryNumber` 的定义

English:
definition libraryNumber
  signature: (module : Name)
  body: #[`Init, `Std, `Lean, `Batteries, `Mathlib].idxOf module.getRoot

中文:
定义 libraryNumber
  签名: (module : Name)
  定义体: #[`Init, `Std, `Lean, `Batteries, `Mathlib].idxOf module.getRoot

Depends on / 依赖: Batteries, Mathlib, getRoot, module, module.getRoot
-/
def libraryNumber (module : Name) : Nat :=
  #[`Init, `Std, `Lean, `Batteries, `Mathlib].idxOf module.getRoot

/--
Definition of `ModuleKey` / `ModuleKey` 的定义

English:
definition ModuleKey
  body: Nat × String
  deriving Inhabited

中文:
定义 ModuleKey
  定义体: Nat × String
  deriving Inhabited
-/
def ModuleKey := Nat × String
  deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord ModuleKey
  body: ⟨fun a b => (compare a.1 b.1).then (compare a.2 b.2)⟩

中文:
实例 :
  签名: 序 ModuleKey
  定义体: ⟨fun a b => (compare a.1 b.1).then (compare a.2 b.2)⟩

Depends on / 依赖: compare
-/
instance : Ord ModuleKey := ⟨fun a b => (compare a.1 b.1).then (compare a.2 b.2)⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT ModuleKey
  body: ltOfOrd

中文:
实例 :
  签名: LT ModuleKey
  定义体: ltOfOrd

Depends on / 依赖: ltOfOrd
-/
instance : LT ModuleKey := ltOfOrd
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE ModuleKey
  body: leOfOrd

中文:
实例 :
  签名: LE ModuleKey
  定义体: leOfOrd

Depends on / 依赖: leOfOrd
-/
instance : LE ModuleKey := leOfOrd
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max ModuleKey
  body: maxOfLe

中文:
实例 :
  签名: 最大值 ModuleKey
  定义体: maxOfLe

Depends on / 依赖: maxOfLe
-/
instance : Max ModuleKey := maxOfLe

/--
Definition of `mkModuleKey!` / `mkModuleKey!` 的定义

English:
definition mkModuleKey!
  signature: (name : Name) (env : Environment)
  body: let mod := (env.getModuleFor? name).get!
  (libraryNumber mod, mod.toString)

中文:
定义 mkModuleKey!
  签名: (name : Name) (env : Environment)
  定义体: let mod := (env.getModuleFor? name).get!
  (libraryNumber mod, mod.toString)

Depends on / 依赖: env.getModuleFor, getModuleFor, libraryNumber, mod.toString, toString
-/
def mkModuleKey! (name : Name) (env : Environment) : ModuleKey :=
  let mod := (env.getModuleFor? name).get!
  (libraryNumber mod, mod.toString)

/--
Definition of `sortedDuplicateDeclarations` / `sortedDuplicateDeclarations` 的定义

English:
definition sortedDuplicateDeclarations
  signature: (cfg : Target)
  body: do
  let env ← getEnv
  let dups ← duplicateDeclarations cfg
  let mut result : Std.TreeMap ModuleKey (Array (Array Name)) := {}
  for names in dups do
.max?.get! let moduleKey := names.map (mkModuleKey! · env)
    result := result.alter moduleKey (·.getD #[] |>.push (names.qsort Name.lt))
  return result.toArray.map fun (a, dups) => (a.2, dups)

中文:
定义 sortedDuplicateDeclarations
  签名: (cfg : Target)
  定义体: do
  let env ← getEnv
  let dups ← duplicateDeclarations cfg
  let mut result : Std.TreeMap ModuleKey (Array (Array Name)) := {}
  for names in dups do
.max?.get! let moduleKey := names.map (mkModuleKey! · env)
    result := result.alter moduleKey (·.getD #[] |>.push (names.qsort Name.lt))
  return result.toArray.map fun (a, dups) => (a.2, dups)
-/
def sortedDuplicateDeclarations (cfg : Target) :
    CoreM (Array (String × Array (Array Name))) := do
  let env ← getEnv
  let dups ← duplicateDeclarations cfg
  let mut result : Std.TreeMap ModuleKey (Array (Array Name)) := {}
  for names in dups do
.max?.get! let moduleKey := names.map (mkModuleKey! · env)
    result := result.alter moduleKey (·.getD #[] |>.push (names.qsort Name.lt))
  return result.toArray.map fun (a, dups) => (a.2, dups)

/-- The duplicate declarations linter. It tells you which duplicate declarations there are
in the current environment. -/
public def lintDuplicateDeclarations (tgt : Target) : CoreM MessageData := do
  if (← getEnv).header.isModule then
    throwError "In order to detect aliases, this function should be run in a non-module"
  let dups ← sortedDuplicateDeclarations tgt
  let mut msg := m!"Number of duplicates: {dups.foldl (init := 0) (· + ·.2.size)}"
  for (module, dups) in dups do
    msg := msg ++ s!"\n\n-- {module}"
    for names in dups do
      msg := msg ++ "\n"
      for name in names do
        msg := msg ++ m!"\n{.ofConstName name} : {(← getConstInfo name).type}"
  return msg

end Mathlib.Tactic.DuplicateDecls
