/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.DefView
public meta import Lean.Util.CollectAxioms
public meta import ImportGraph.Imports.Redundant
public meta import ImportGraph.Imports.RequiredModules
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Elab.DeclModifiers

/-! # `#min_imports in` a command to find minimal imports

`#min_imports in stx` scans the syntax `stx` to find a collection of minimal imports that should be
sufficient for `stx` to make sense.
If `stx` is a command, then it also elaborates `stx` and, in case it is a declaration, then
it also finds the imports implied by the declaration.

Unlike the related `#find_home`, this command takes into account notation and tactic information.

## Limitations

Parsing of `attribute`s is hard and the command makes minimal effort to support them.
Here is an example where the command fails to notice a dependency:
```lean
import Mathlib.Data.Sym.Sym2.Init -- the actual minimal import
import Aesop.Frontend.Attribute -- the import that `#min_imports in` suggests

import Mathlib.Tactic.MinImports

-- import Aesop.Frontend.Attribute
#min_imports in
@[aesop (rule_sets := [Sym2]) [safe [constructors, cases], norm]]
inductive Rel (α : Type) : α × α → α × α → Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)

-- `import Mathlib.Data.Sym.Sym2.Init` is not detected by `#min_imports in`.
```

## Todo

*Examples*
When parsing an `example`, `#min_imports in` retrieves all the information that it can from the
`Syntax` of the `example`, but, since the `example` is not added to the environment, it fails
to retrieve any `Expr` information about the proof term.
It would be desirable to make `#min_imports in example ...` inspect the resulting proof and
report imports, but this feature is missing for the moment.

*Using `InfoTrees`*
It may be more efficient (not necessarily in terms of speed, but of simplicity of code),
to inspect the `InfoTrees` for each command and retrieve information from there.
I have not looked into this yet.
-/

public meta section

open Lean Elab Command

namespace Mathlib.Command.MinImports

/--
Definition of `isInitImport` / `isInitImport` 的定义

English:
definition isInitImport
  signature: : Name -> Bool

中文:
定义 isInitImport
  签名: : Name -> 布尔值
-/
partial def isInitImport : Name -> Bool
  | `Init => true
  | .str p _ => isInitImport p
  | _ => false

/-- `getSyntaxNodeKinds stx` takes a `Syntax` input `stx` and returns the `NameSet` of all the
`SyntaxNodeKinds` and all the identifiers contained in `stx`. -/
partial
/--
Definition of `getSyntaxNodeKinds` / `getSyntaxNodeKinds` 的定义

English:
definition getSyntaxNodeKinds
  signature: : Syntax -> NameSet

中文:
定义 getSyntaxNodeKinds
  签名: : Syntax -> NameSet
-/
def getSyntaxNodeKinds : Syntax -> NameSet
  | .node _ kind args =>
    ((args.map getSyntaxNodeKinds).foldl (NameSet.append · ·) {}).insert kind
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/--
Definition of `getVisited` / `getVisited` 的定义

English:
definition getVisited
  signature: (decl : Name)
  body: do
  unless (← hasConst decl) do
    return {}
  -- without resetting the state, the "unused tactics" linter gets confused?
  let st ← get
  liftCoreM decl.transitivelyUsedConstants <* set st

中文:
定义 getVisited
  签名: (decl : Name)
  定义体: do
  unless (← hasConst decl) do
    return {}
  -- without resetting the state, the "unused tactics" linter gets confused?
  let st ← get
  liftCoreM decl.transitivelyUsedConstants <* set st
-/
def getVisited (decl : Name) : CommandElabM NameSet := do
  unless (← hasConst decl) do
    return {}
  -- without resetting the state, the "unused tactics" linter gets confused?
  let st ← get
  liftCoreM decl.transitivelyUsedConstants <* set st

/--
Definition of `getId` / `getId` 的定义

English:
definition getId
  signature: (stx : Syntax)
  body: do
  -- If the command contains a `declId`, we use the implied `ident`.
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      -- Otherwise, the command could be a nameless `instance`.
      match stx.find? (·.isOfKind ``Lean.Parser

中文:
定义 getId
  签名: (stx : Syntax)
  定义体: do
  -- If the command contains a `declId`, we use the implied `ident`.
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      -- Otherwise, the command could be a nameless `instance`.
      match stx.find? (·.isOfKind ``Lean.Parser
-/
def getId (stx : Syntax) : CommandElabM Syntax := do
  -- If the command contains a `declId`, we use the implied `ident`.
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      -- Otherwise, the command could be a nameless `instance`.
      match stx.find? (·.isOfKind ``Lean.Parser.Command.instance) with
        | none => return .missing
        | some stx => do
          -- if it is a nameless `instance`, we retrieve the autogenerated name
          let dv ← mkDefViewOfInstance {} stx
          return dv.declId[0]

/-- `getIds stx` extracts all identifiers, collecting them in a `NameSet`. -/
partial
/--
Definition of `getIds` / `getIds` 的定义

English:
definition getIds
  signature: : Syntax -> NameSet

中文:
定义 getIds
  签名: : Syntax -> NameSet
-/
def getIds : Syntax -> NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/--
Definition of `getAttrNames` / `getAttrNames` 的定义

English:
definition getAttrNames
  signature: (stx : Syntax)
  body: match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

中文:
定义 getAttrNames
  签名: (stx : Syntax)
  定义体: match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

Depends on / 依赖: Lean.Parser.Term.attributes, Parser, attributes, getIds, isOfKind, stx.find
-/
def getAttrNames (stx : Syntax) : NameSet :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

/--
Definition of `getAttrs` / `getAttrs` 的定义

English:
definition getAttrs
  signature: (env : Environment) (stx : Syntax)
  body: Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

中文:
定义 getAttrs
  签名: (env : Environment) (stx : Syntax)
  定义体: Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

Depends on / 依赖: Id.run, NameSet, attr.ref, getAttrNames, getAttributeImpl, insert, new.insert, return
-/
def getAttrs (env : Environment) (stx : Syntax) : NameSet :=
  Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

/--
Definition of `previousInstName` / `previousInstName` 的定义

English:
definition previousInstName
  signature: : Name -> Name
  body: tail.takeEndWhile (· != '_')
    let newTail := match last.toNat? with
                    | some (n + 2) => s!"_{n + 1}"
                    | _ => ""
    let newTailPrefix := tail.dropEndWhile (· != '_')
    if newTailPrefix.isEmpty then nm else
    let newTail :=
      (if newTailPrefix.back == '

中文:
定义 previousInstName
  签名: : Name -> Name
  定义体: tail.takeEndWhile (· != '_')
    let newTail := match last.toNat? with
                    | some (n + 2) => s!"_{n + 1}"
                    | _ => ""
    let newTailPrefix := tail.dropEndWhile (· != '_')
    if newTailPrefix.isEmpty then nm else
    let newTail :=
      (if newTailPrefix.back == '

Depends on / 依赖: tail.takeEndWhile, takeEndWhile
-/
def previousInstName : Name -> Name
  | nm@(.str init tail) =>
    let last := tail.takeEndWhile (· != '_')
    let newTail := match last.toNat? with
                    | some (n + 2) => s!"_{n + 1}"
                    | _ => ""
    let newTailPrefix := tail.dropEndWhile (· != '_')
    if newTailPrefix.isEmpty then nm else
    let newTail :=
      (if newTailPrefix.back == '_' then newTailPrefix.dropEnd 1 else newTailPrefix).copy ++ newTail
    .str init newTail
  | nm => nm

/--
Definition of `getDeclName` / `getDeclName` 的定义

English:
definition getDeclName
  signature: (cmd : Syntax)
  body: do
  let ns ← getCurrNamespace
  let id1 ← getId cmd
  let id2 := mkIdentFrom id1 (previousInstName id1.getId)
  let some declStx := cmd.find? (·.isOfKind ``Parser.Command.declaration) | pure default
  let some modifiersStx := declStx.find? (·.isOfKind ``Parser.Command.declModifiers) | pure default


中文:
定义 getDeclName
  签名: (cmd : Syntax)
  定义体: do
  let ns ← getCurrNamespace
  let id1 ← getId cmd
  let id2 := mkIdentFrom id1 (previousInstName id1.getId)
  let some declStx := cmd.find? (·.isOfKind ``Parser.Command.declaration) | pure default
  let some modifiersStx := declStx.find? (·.isOfKind ``Parser.Command.declModifiers) | pure default

-/
def getDeclName (cmd : Syntax) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let id1 ← getId cmd
  let id2 := mkIdentFrom id1 (previousInstName id1.getId)
  let some declStx := cmd.find? (·.isOfKind ``Parser.Command.declaration) | pure default
  let some modifiersStx := declStx.find? (·.isOfKind ``Parser.Command.declModifiers) | pure default
  let modifiers : TSyntax ``Parser.Command.declModifiers := ⟨modifiersStx⟩
  -- the `get`/`set` state catches issues with elaboration of, for instance, `scoped` attributes
  let s ← get
  let modifiers ← elabModifiers modifiers
  set s
  liftCoreM do (
    -- Try applying the algorithm in `Lean.mkDeclName` to attach a namespace to the name.
    -- Unfortunately calling `Lean.mkDeclName` directly won't work: it will complain that there is
    -- already a declaration with this name.
    (do
      let shortName := id1.getId
      let view := extractMacroScopes shortName
      let name := view.name
      let isRootName := (`_root_).isPrefixOf name
      let mut fullName := if isRootName then
        { view with name := name.replacePrefix `_root_ Name.anonymous }.review
      else
        ns ++ shortName
      -- Apply name visibility rules: private names get mangled.
      match modifiers.visibility with
      | .private => return mkPrivateName (← getEnv) fullName
      | _ => return fullName) <|>
    -- try the visible name or the current "nameless" `instance` name
realizeGlobalConstNoOverload id1 >
    -- otherwise, guess what the previous "nameless" `instance` name was
realizeGlobalConstNoOverload id2 >
    -- failing everything, use the current namespace followed by the visible name
    return ns ++ id1.getId)

/--
Definition of `getAllDependencies` / `getAllDependencies` 的定义

English:
definition getAllDependencies
  signature: (cmd id : Syntax)
  body: do
  let env ← getEnv
  let nm ← getDeclName cmd
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  return (← getVisited nm)
.append (← getVisited id.getId)
.append (getSyntaxNodeKinds cmd)
.append (getAttrs env cmd)

中文:
定义 getAllDependencies
  签名: (cmd id : Syntax)
  定义体: do
  let env ← getEnv
  let nm ← getDeclName cmd
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  return (← getVisited nm)
.append (← getVisited id.getId)
.append (getSyntaxNodeKinds cmd)
.append (getAttrs env cmd)
-/
def getAllDependencies (cmd id : Syntax) :
    CommandElabM NameSet := do
  let env ← getEnv
  let nm ← getDeclName cmd
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  return (← getVisited nm)
.append (← getVisited id.getId)
.append (getSyntaxNodeKinds cmd)
.append (getAttrs env cmd)

/--
Definition of `getAllImports` / `getAllImports` 的定义

English:
definition getAllImports
  signature: (cmd id : Syntax) (dbg? : Bool := false)
  body: do
  let env ← getEnv
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  let ts ← getAllDependencies cmd id
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : Std.HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.inse

中文:
定义 getAllImports
  签名: (cmd id : Syntax) (dbg? : 布尔值 := false)
  定义体: do
  let env ← getEnv
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  let ts ← getAllDependencies cmd id
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : Std.HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.inse
-/
def getAllImports (cmd id : Syntax) (dbg? : Bool := false) :
    CommandElabM NameSet := do
  let env ← getEnv
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  let ts ← getAllDependencies cmd id
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : Std.HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.insert ((env.getModuleIdx? imp).getD default) imp
  let mut fins : NameSet := {}
  for t in ts do
    let new := match env.getModuleIdxFor? t with
      | some t => (hm.get? t).get!
      | none => .anonymous -- instead of `getMainModule`, we omit the current module
    if !fins.contains new then fins := fins.insert new
  return fins.erase .anonymous

/--
Definition of `getIrredundantImports` / `getIrredundantImports` 的定义

English:
definition getIrredundantImports
  signature: (env : Environment) (importNames : NameSet)
  body: importNames \ (env.findRedundantImports importNames.toArray)

中文:
定义 getIrredundantImports
  签名: (env : Environment) (importNames : NameSet)
  定义体: importNames \ (env.findRedundantImports importNames.toArray)

Depends on / 依赖: env.findRedundantImports, findRedundantImports, importNames, importNames.toArray, toArray
-/
def getIrredundantImports (env : Environment) (importNames : NameSet) : NameSet :=
  importNames \ (env.findRedundantImports importNames.toArray)

/--
Definition of `minImpsCore` / `minImpsCore` 的定义

English:
definition minImpsCore
  signature: (stx id : Syntax)
  body: do
    let tot := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let fileNames := (tot.toArray.filter (!isInitImport ·)).qsort Name.lt
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"public import {·}")).toList}"

中文:
定义 minImpsCore
  签名: (stx id : Syntax)
  定义体: do
    let tot := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let fileNames := (tot.toArray.filter (!isInitImport ·)).qsort Name.lt
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"public import {·}")).toList}"
-/
def minImpsCore (stx id : Syntax) : CommandElabM Unit := do
    let tot := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let fileNames := (tot.toArray.filter (!isInitImport ·)).qsort Name.lt
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"public import {·}")).toList}"

/-- `#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work. -/
syntax (name := minImpsStx) "#min_imports" " in " command : command

@[inherit_doc minImpsStx]
syntax "#min_imports" " in " term : command

elab_rules : command
  | `(#min_imports in $cmd:command) => do
    -- In case `cmd` is a "nameless" `instance`, we produce its name.
    -- It is important that this is collected *before* adding the declaration to the environment,
    -- since `getId` probes the name-generator using the current environment: if the declaration
    -- were already present, `getId` would return a new name that does not clash with it!
    let id ← getId cmd
Elab.Command.elabCommand cmd > pure ()
    minImpsCore cmd id
  | `(#min_imports in $cmd:term) => minImpsCore cmd cmd

end Mathlib.Command.MinImports
