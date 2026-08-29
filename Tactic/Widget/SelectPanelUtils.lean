/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public meta import Lean.Meta.ExprLens
public meta import Mathlib.Tactic.Widget.SelectInsertParamsClass
public import Mathlib.Tactic.Widget.SelectInsertParamsClass
public import ProofWidgets.Component.MakeEditLink
public import ProofWidgets.Data.Html

/-! # Selection panel utilities

The main declaration is `mkSelectionPanelRPC` which helps creating rpc methods for widgets
generating tactic calls based on selected sub-expressions in the main goal.

There are also some minor helper functions.
-/

public meta section

open Lean Meta Server

open Lean.SubExpr in
/--
Definition of `getGoalLocations` / `getGoalLocations` 的定义

English:
definition getGoalLocations
  signature: (locations : Array GoalsLocation)
  body: Id.run do
  let mut res := #[]
  for location in locations do
    if let .target pos := location.loc then
      res := res.push pos
  return res

中文:
定义 getGoalLocations
  签名: (locations : 数组 GoalsLocation)
  定义体: Id.run do
  let mut res := #[]
  for location in locations do
    if let .target pos := location.loc then
      res := res.push pos
  return res

Depends on / 依赖: Id.run
-/
def getGoalLocations (locations : Array GoalsLocation) : Array SubExpr.Pos := Id.run do
  let mut res := #[]
  for location in locations do
    if let .target pos := location.loc then
      res := res.push pos
  return res

/--
Definition of `insertMetaVar` / `insertMetaVar` 的定义

English:
definition insertMetaVar
  signature: (e : Expr) (pos : SubExpr.Pos)
  body: replaceSubexpr (fun _ => do mkFreshExprMVar none .synthetic) pos e

中文:
定义 insertMetaVar
  签名: (e : Expr) (pos : SubExpr.Pos)
  定义体: replaceSubexpr (fun _ => do mkFreshExprMVar none .synthetic) pos e

Depends on / 依赖: mkFreshExprMVar, replaceSubexpr, synthetic
-/
def insertMetaVar (e : Expr) (pos : SubExpr.Pos) : MetaM Expr :=
  replaceSubexpr (fun _ => do mkFreshExprMVar none .synthetic) pos e

/--
Definition of `String.renameMetaVar` / `String.renameMetaVar` 的定义

English:
definition String.renameMetaVar
  signature: (s : String)
  body: match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++
      "?_".toSlice.intercalate (tail.map fun s => s.dropWhile Char.isDigit)

中文:
定义 String.renameMetaVar
  签名: (s : String)
  定义体: match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++
      "?_".toSlice.intercalate (tail.map fun s => s.dropWhile Char.isDigit)

Depends on / 依赖: Char.isDigit, dropWhile, intercalate, isDigit, s.dropWhile, s.splitOn, splitOn, tail.map, toSlice, toSlice.intercalate
-/
def String.renameMetaVar (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++
      "?_".toSlice.intercalate (tail.map fun s => s.dropWhile Char.isDigit)

open ProofWidgets

/--
Definition of `SelectInsertParams` / `SelectInsertParams` 的定义

English:
structure SelectInsertParams
  parameters: where
  axioms and operations (4):
    - pos : Lsp.Position
    - goals : Array Widget.InteractiveGoal
    - selectedLocations : Array SubExpr.GoalsLocation
    - replaceRange : Lsp.Range

中文:
结构 SelectInsertParams
  参数: where
  公理与运算 (4 个):
    - pos : Lsp.Position
    - goals : 数组 Widget.整数eractiveGoal
    - selectedLocations : 数组 SubExpr.GoalsLocation
    - replaceRange : Lsp.值域
-/
structure SelectInsertParams where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  /-- The range in the source document where the command will be inserted. -/
  replaceRange : Lsp.Range
  deriving SelectInsertParamsClass, RpcEncodable

open scoped Jsx in open SelectInsertParamsClass Lean.SubExpr in
/--
Definition of `mkSelectionPanelRPC` / `mkSelectionPanelRPC` 的定义

English:
definition mkSelectionPanelRPC
  signature: {Params : Type} [SelectInsertParamsClass Params]
  body: fun params => RequestM.asTask do
  let doc ← RequestM.readDoc
  if h : 0 < (goals params).size then
    let mainGoal := (goals params)[0]
    let mainGoalName := mainGoal.mvarId.name
    let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
    let be_where := 

中文:
定义 mkSelectionPanelRPC
  签名: {Params : 类型} [SelectInsertParams类 Params]
  定义体: fun params => RequestM.asTask do
  let doc ← RequestM.readDoc
  if h : 0 < (goals params).size then
    let mainGoal := (goals params)[0]
    let mainGoalName := mainGoal.mvarId.name
    let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
    let be_where := 

Depends on / 依赖: onlyOne
-/
def mkSelectionPanelRPC {Params : Type} [SelectInsertParamsClass Params]
    (mkCmdStr : (pos : Array GoalsLocation) -> (goalType : Expr) -> Params ->
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)))
    (helpMsg : String) (title : String) (onlyGoal := true) (onlyOne := false) :
    (params : Params) -> RequestM (RequestTask Html) :=
  fun params => RequestM.asTask do
  let doc ← RequestM.readDoc
  if h : 0 < (goals params).size then
    let mainGoal := (goals params)[0]
    let mainGoalName := mainGoal.mvarId.name
    let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
    let be_where := if onlyGoal then "in the main goal." else "in the main goal or its context."
    let errorMsg := s!"{all} should be {be_where}"
    let inner : Html ← (do
      if onlyOne && (selectedLocations params).size > 1 then
        return <span>{.text "You should select only one sub-expression"}</span>
      for selectedLocation in selectedLocations params do
        if selectedLocation.mvarId.name != mainGoalName then
          return <span>{.text errorMsg}</span>
        else if onlyGoal then
          if !(selectedLocation.loc matches (.target _)) then
            return <span>{.text errorMsg}</span>
      if (selectedLocations params).isEmpty then
        return <span>{.text helpMsg}</span>
      mainGoal.ctx.val.runMetaM {} do
        let md ← mainGoal.mvarId.getDecl
.sanitizeNames.run' {options := (← getOptions)} let lctx := md.lctx
        Meta.withLCtx lctx md.localInstances do
          let (linkText, newCode, range?) ← mkCmdStr (selectedLocations params) md.type.consumeMData
            params
          return .ofComponent
            MakeEditLink
            (.ofReplaceRange doc.meta (replaceRange params) newCode range?)
            #[ .text linkText ])
    return <details «open»={true}>
        <summary className="mv2 pointer">{.text title}</summary>
        <div className="ml1">{inner}</div>
      </details>
  else
    return <span>{.text "There is no goal to solve!"}</span> -- This shouldn't happen.
