/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

public import Mathlib.Init

/-!
Defines a command wrapper that prints the changes the command makes to the
environment.

```
#whats_new in
theorem foo : 42 = 6 * 7 := rfl
```
-/

public meta section

open Lean Elab Command

namespace Mathlib.WhatsNew

/--
Definition of `throwUnknownId` / `throwUnknownId` 的定义

English:
definition throwUnknownId
  signature: (id : Name)
  body: throwError "unknown identifier '{mkConst id}'"

中文:
定义 throwUnknownId
  签名: (id : Name)
  定义体: throwError "unknown identifier '{mkConst id}'"
-/
private def throwUnknownId (id : Name) : CommandElabM Unit :=
  throwError "unknown identifier '{mkConst id}'"

/--
Definition of `levelParamsToMessageData` / `levelParamsToMessageData` 的定义

English:
definition levelParamsToMessageData
  signature: (levelParams : List Name)
  body: match levelParams with
  | [] => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

中文:
定义 levelParamsToMessageData
  签名: (levelParams : 列表 Name)
  定义体: match levelParams with
  | [] => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"
-/
private def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | [] => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

/--
Definition of `mkHeader` / `mkHeader` 的定义

English:
definition mkHeader
  signature: (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
  body: do
  let m : MessageData :=
    match safety with
    | DefinitionSafety.unsafe => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m
  let (m, id) := match privateToUserName? id with
    | so

中文:
定义 mkHeader
  签名: (kind : String) (id : Name) (levelParams : 列表 Name) (type : Expr)
  定义体: do
  let m : MessageData :=
    match safety with
    | DefinitionSafety.unsafe => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m
  let (m, id) := match privateToUserName? id with
    | so
-/
private def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (safety : DefinitionSafety) : CoreM MessageData := do
  let m : MessageData :=
    match safety with
    | DefinitionSafety.unsafe => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m
  let (m, id) := match privateToUserName? id with
    | some id => (m ++ "private ", id)
    | none => (m, id)
  let m := m ++ kind ++ " " ++ id ++ levelParamsToMessageData levelParams ++ " : " ++ type
  pure m

/--
Definition of `mkHeader'` / `mkHeader'` 的定义

English:
definition mkHeader'
  signature: (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
  body: mkHeader kind id levelParams type
    (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe)

中文:
定义 mkHeader'
  签名: (kind : String) (id : Name) (levelParams : 列表 Name) (type : Expr)
  定义体: mkHeader kind id levelParams type
    (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe)
-/
private def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (isUnsafe : Bool) : CoreM MessageData :=
  mkHeader kind id levelParams type
    (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe)

/--
Definition of `printDefLike` / `printDefLike` 的定义

English:
definition printDefLike
  signature: (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
  body: return (← mkHeader kind id levelParams type safety) ++ " :=" ++ Format.line ++ value

中文:
定义 printDefLike
  签名: (kind : String) (id : Name) (levelParams : 列表 Name) (type : Expr)
  定义体: return (← mkHeader kind id levelParams type safety) ++ " :=" ++ Format.line ++ value
-/
private def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (value : Expr) (safety := DefinitionSafety.safe) : CoreM MessageData :=
  return (← mkHeader kind id levelParams type safety) ++ " :=" ++ Format.line ++ value

/--
Definition of `printInduct` / `printInduct` 的定义

English:
definition printInduct
  signature: (id : Name) (levelParams : List Name) (_numParams : Nat) (_numIndices : Nat)
  body: do
  let mut m ← mkHeader' "inductive" id levelParams type isUnsafe
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  pure m

中文:
定义 printInduct
  签名: (id : Name) (levelParams : 列表 Name) (_numParams : 自然数) (_numIndices : 自然数)
  定义体: do
  let mut m ← mkHeader' "inductive" id levelParams type isUnsafe
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  pure m
-/
private def printInduct (id : Name) (levelParams : List Name) (_numParams : Nat) (_numIndices : Nat)
    (type : Expr) (ctors : List Name) (isUnsafe : Bool) : CoreM MessageData := do
  let mut m ← mkHeader' "inductive" id levelParams type isUnsafe
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  pure m

/--
Definition of `printIdCore` / `printIdCore` 的定义

English:
definition printIdCore
  signature: (id : Name)

中文:
定义 printIdCore
  签名: (id : Name)
-/
private def printIdCore (id : Name) : ConstantInfo -> CoreM MessageData
  | ConstantInfo.axiomInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "axiom" id us t u
  | ConstantInfo.defnInfo { levelParams := us, type := t, value := v, safety := s, .. } =>
    printDefLike "def" id us t v s
  | ConstantInfo.thmInfo { levelParams := us, type := t, value := v, .. } =>
    printDefLike "theorem" id us t v
  | ConstantInfo.opaqueInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "constant" id us t u
  | ConstantInfo.quotInfo { levelParams := us, type := t, .. } =>
    mkHeader' "Quotient primitive" id us t false
  | ConstantInfo.ctorInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "constructor" id us t u
  | ConstantInfo.recInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    mkHeader' "recursor" id us t u
  | ConstantInfo.inductInfo
      { levelParams := us, numParams, numIndices, type := t, ctors, isUnsafe := u, .. } =>
    printInduct id us numParams numIndices t ctors u

/--
Definition of `diffExtension` / `diffExtension` 的定义

English:
definition diffExtension
  signature: (old new : Environment)
  body: unsafe do
  let mut asyncMode := ext.toEnvExtension.asyncMode
  if asyncMode matches .async .. then
    -- allow for diffing async extensions by bumping mode to sync
    asyncMode := .sync
  let oldSt := ext.toEnvExtension.getState (asyncMode := asyncMode) old
  let newSt := ext.toEnvExtension.getSt

中文:
定义 diffExtension
  签名: (old new : Environment)
  定义体: unsafe do
  let mut asyncMode := ext.toEnvExtension.asyncMode
  if asyncMode matches .async .. then
    -- allow for diffing async extensions by bumping mode to sync
    asyncMode := .sync
  let oldSt := ext.toEnvExtension.getState (asyncMode := asyncMode) old
  let newSt := ext.toEnvExtension.getSt

Depends on / 依赖: unsafe
-/
def diffExtension (old new : Environment)
    (ext : PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) :
    CoreM (Option MessageData) := unsafe do
  let mut asyncMode := ext.toEnvExtension.asyncMode
  if asyncMode matches .async .. then
    -- allow for diffing async extensions by bumping mode to sync
    asyncMode := .sync
  let oldSt := ext.toEnvExtension.getState (asyncMode := asyncMode) old
  let newSt := ext.toEnvExtension.getState (asyncMode := asyncMode) new
  if ptrAddrUnsafe oldSt == ptrAddrUnsafe newSt then return none
  let oldEntries := (ext.exportEntriesFn (← getEnv) oldSt.state).private
  let newEntries := (ext.exportEntriesFn (← getEnv) newSt.state).private
  pure m!"-- {ext.name} extension: {(newEntries.size - oldEntries.size : Int)} new entries"

/--
Definition of `whatsNew` / `whatsNew` 的定义

English:
definition whatsNew
  signature: (old new : Environment)
  body: do
  let mut diffs := #[]

  for (c, i) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push (← printIdCore c i)

  for ext in ← persistentEnvExtensionsRef.get do
    if let some diff ← diffExtension old new ext then
      diffs := diffs.push diff

  

中文:
定义 whatsNew
  签名: (old new : Environment)
  定义体: do
  let mut diffs := #[]

  for (c, i) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push (← printIdCore c i)

  for ext in ← persistentEnvExtensionsRef.get do
    if let some diff ← diffExtension old new ext then
      diffs := diffs.push diff

  
-/
def whatsNew (old new : Environment) : CoreM MessageData := do
  let mut diffs := #[]

  for (c, i) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push (← printIdCore c i)

  for ext in ← persistentEnvExtensionsRef.get do
    if let some diff ← diffExtension old new ext then
      diffs := diffs.push diff

  if diffs.isEmpty then return "no new constants"

pure MessageData.joinSep diffs.toList "\n\n"

/-- `#whats_new in` executes the following command and then prints the
declarations that were added to the environment. -/
elab "#whats_new " "in" ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    logInfo (← liftCoreM <| whatsNew oldEnv newEnv)

/-- `#whats_new in` executes the following command and then prints the
declarations that were added to the environment. -/
macro (name := oldStx) "whatsnew " "in" ppLine cmd:command : command =>
  `(command| #whats_new in $cmd)

deprecated_syntax oldStx "use `#whats_new` instead of `whatsnew`" (since := "2026-08-07")

end Mathlib.WhatsNew
