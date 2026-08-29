/-
Copyright (c) 2025 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga, Thomas R. Murrills
-/
module

public import Mathlib.Lean.Environment
public import Lean.Server.InfoUtils
public import Lean.Meta.TryThis
public import Batteries.Tactic.Lint.Misc
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header -- shake: keep
public import Batteries.Tactic.Lint.Basic
import Lean.Elab.Term.TermElabM

/-!
# Additions to `Lean.Elab.InfoTree.Main`
-/

@[expose] public section

namespace Lean.Elab

open Lean.Meta
open Lean.Meta.Tactic.TryThis

/--
Definition of `collectTryThisSuggestions` / `collectTryThisSuggestions` 的定义

English:
definition collectTryThisSuggestions
  signature: (trees : PersistentArray InfoTree)
  body: trees.foldl (init := #[]) fun acc tree => go acc tree

中文:
定义 collectTryThisSuggestions
  签名: (trees : PersistentArray InfoTree)
  定义体: trees.foldl (init := #[]) fun acc tree => go acc tree
-/
partial def collectTryThisSuggestions (trees : PersistentArray InfoTree) : Array Suggestion :=
  trees.foldl (init := #[]) fun acc tree => go acc tree
where
  /-- Traverses an `InfoTree` to collect `TryThisInfo` suggestions. -/
  go (acc : Array Suggestion) : InfoTree -> Array Suggestion
    | .context _ t => go acc t
    | .node i children =>
      let acc := match i with
        | .ofCustomInfo ci =>
          match ci.value.get? TryThisInfo with
          | some tti => acc.push tti.suggestion
          | none => acc
        | _ => acc
      children.foldl (init := acc) fun acc tree => go acc tree
    | .hole _ => acc

namespace InfoTree

/--
Definition of `findSomeM?` / `findSomeM?` 的定义

English:
definition findSomeM?
  signature: {m : Type -> Type} [Monad m] {α}
  body: go ctx? t

中文:
定义 findSomeM?
  签名: {m : 类型 -> 类型} [单子 m] {α}
  定义体: go ctx? t
-/
partial def findSomeM? {m : Type -> Type} [Monad m] {α}
    (f : ContextInfo -> Info -> PersistentArray InfoTree -> m (Option α))
    (t : InfoTree) (ctx? : Option ContextInfo := none) : m (Option α) :=
  go ctx? t
where
  /-- Accumulates contexts and visits nodes if `ctx?` is not `none`. -/
  go ctx?
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | node i ts => do
    let a ← match ctx? with
      | none => pure none
      | some ctx => f ctx i ts
    match a with
    | some a => pure a
    | none => ts.findSomeM? (go <| i.updateContext? ctx?)
  | hole _ => pure none

/--
Definition of `findSome?` / `findSome?` 的定义

English:
definition findSome?
  signature: {α} (f : ContextInfo -> Info -> PersistentArray InfoTree -> Option α)
  body: Id.run t.findSomeM? f ctx?

中文:
定义 findSome?
  签名: {α} (f : ContextInfo -> Info -> PersistentArray InfoTree -> 选项类型 α)
  定义体: Id.run t.findSomeM? f ctx?
-/
def findSome? {α} (f : ContextInfo -> Info -> PersistentArray InfoTree -> Option α)
    (t : InfoTree) (ctx? : Option ContextInfo := none) : Option α :=
Id.run t.findSomeM? f ctx?

/--
Definition of `onHighestNode?` / `onHighestNode?` 的定义

English:
definition onHighestNode?
  signature: {α} (t : InfoTree) (ctx? : Option ContextInfo)
  body: t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

中文:
定义 onHighestNode?
  签名: {α} (t : InfoTree) (ctx? : 选项类型 ContextInfo)
  定义体: t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

Depends on / 依赖: findSome, t.findSome
-/
def onHighestNode? {α} (t : InfoTree) (ctx? : Option ContextInfo)
    (f : ContextInfo -> Info -> PersistentArray InfoTree -> α) : Option α :=
  t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

/--
Definition of `getHighestInfo?` / `getHighestInfo?` 的定义

English:
definition getHighestInfo?
  signature: (t : InfoTree) (ctx? : Option ContextInfo)
  body: t.onHighestNode? ctx? fun ctx i _ => (ctx, i)

中文:
定义 getHighestInfo?
  签名: (t : InfoTree) (ctx? : 选项类型 ContextInfo)
  定义体: t.onHighestNode? ctx? fun ctx i _ => (ctx, i)

Depends on / 依赖: onHighestNode, t.onHighestNode
-/
def getHighestInfo? (t : InfoTree) (ctx? : Option ContextInfo) : Option (ContextInfo × Info) :=
  t.onHighestNode? ctx? fun ctx i _ => (ctx, i)

/--
Definition of `getDeclsByBody` / `getDeclsByBody` 的定义

English:
definition getDeclsByBody
  signature: (t : InfoTree)
  body: t.collectNodesBottomUp fun ctx i _ decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if let some decl := ctx.parentDecl? then
          decl :: decls
        else decls
      else decls
    | _ => decls

中文:
定义 getDeclsByBody
  签名: (t : InfoTree)
  定义体: t.collectNodesBottomUp fun ctx i _ decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if let some decl := ctx.parentDecl? then
          decl :: decls
        else decls
      else decls
    | _ => decls

Depends on / 依赖: BodyInfo, Lean.Elab.Term.BodyInfo, collectNodesBottomUp, ctx.parentDecl, i.value.typeName, ofCustomInfo, parentDecl, t.collectNodesBottomUp, typeName
-/
def getDeclsByBody (t : InfoTree) : List Name :=
  t.collectNodesBottomUp fun ctx i _ decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if let some decl := ctx.parentDecl? then
          decl :: decls
        else decls
      else decls
    | _ => decls

/--
Definition of `getDeclBodyInfos` / `getDeclBodyInfos` 的定义

English:
definition getDeclBodyInfos
  signature: (t : InfoTree)
  body: t.foldInfoTree (init := []) fun ctx t acc =>
    match t with
    | .node (.ofCustomInfo i) body => Id.run do
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if h : 0 < body.size then
          -- See through `.context`s instead of just matching on `.node`:
          let result? := body[0].getHighestInfo? ctx
          if let some result := result? then
            return (i.stx, result) :: acc
      return acc
    | _ => acc

中文:
定义 getDeclBodyInfos
  签名: (t : InfoTree)
  定义体: t.foldInfoTree (init := []) fun ctx t acc =>
    match t with
    | .node (.ofCustomInfo i) body => Id.run do
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if h : 0 < body.size then
          -- See through `.context`s instead of just matching on `.node`:
          let result? := body[0].getHighestInfo? ctx
          if let some result := result? then
            return (i.stx, result) :: acc
      return acc
    | _ => acc

Depends on / 依赖: BodyInfo, Id.run, Lean.Elab.Term.BodyInfo, body.size, foldInfoTree, i.value.typeName, ofCustomInfo, t.foldInfoTree, typeName
-/
def getDeclBodyInfos (t : InfoTree) : List (Syntax × ContextInfo × Info) :=
  t.foldInfoTree (init := []) fun ctx t acc =>
    match t with
    | .node (.ofCustomInfo i) body => Id.run do
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if h : 0 < body.size then
          -- See through `.context`s instead of just matching on `.node`:
          let result? := body[0].getHighestInfo? ctx
          if let some result := result? then
            return (i.stx, result) :: acc
      return acc
    | _ => acc

/--
Definition of `getTheorems` / `getTheorems` 的定义

English:
definition getTheorems
  signature: (t : InfoTree) (env : Environment)
  body: t.getDeclsByBody.filterMap env.findTheoremConstVal?

中文:
定义 getTheorems
  签名: (t : InfoTree) (env : Environment)
  定义体: t.getDeclsByBody.filterMap env.findTheoremConstVal?

Depends on / 依赖: env.findTheoremConstVal, filterMap, findTheoremConstVal, getDeclsByBody, t.getDeclsByBody.filterMap
-/
def getTheorems (t : InfoTree) (env : Environment) : List ConstantVal :=
  t.getDeclsByBody.filterMap env.findTheoremConstVal?

end InfoTree

namespace Info

/--
Definition of `getLCtx?` / `getLCtx?` 的定义

English:
definition getLCtx?
  signature: : Info -> Option (LocalContext × Option Expr)

中文:
定义 getLCtx?
  签名: : Info -> 选项类型 (LocalContext × 选项类型 Expr)
-/
def getLCtx? : Info -> Option (LocalContext × Option Expr)
  | .ofTacticInfo i => do
    let g ← i.goalsBefore.head?
    let decl ← i.mctxBefore.findDecl? g
    some (decl.lctx, decl.type)
  | .ofTermInfo i
  | .ofPartialTermInfo i => some (i.lctx, i.expectedType?)
  | _ => none

end Lean.Elab.Info
