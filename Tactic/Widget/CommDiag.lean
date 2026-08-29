/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
module

public import Aesop
public import Mathlib.CategoryTheory.Category.Basic
public meta import Mathlib.Tactic.ToDual
public import ProofWidgets.Component.PenroseDiagram
public import ProofWidgets.Presentation.Expr

/-! This module defines tactic/meta infrastructure for displaying commutative diagrams in the
infoview. -/

public meta section

open Lean in
/--
Definition of `_root_.Lean.Expr.app7?` / `_root_.Lean.Expr.app7?` 的定义

English:
definition _root_.Lean.Expr.app7?
  signature: (e : Expr) (fName : Name)
  body: if e.isAppOfArity fName 7 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.a

中文:
定义 _root_.Lean.Expr.app7?
  签名: (e : Expr) (fName : Name)
  定义体: if e.isAppOfArity fName 7 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.a
-/
@[inline] def _root_.Lean.Expr.app7? (e : Expr) (fName : Name) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 7 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.appArg!
    )
  else
    none

namespace Mathlib.Tactic.Widget
open Lean Meta
open ProofWidgets
open CategoryTheory

/-! ## Metaprogramming utilities for breaking down category theory expressions -/

/--
Definition of `homType?` / `homType?` 的定义

English:
definition homType?
  signature: (e : Expr)
  body: do
  let some (_, _, A, B) := e.app4? ``Quiver.Hom | none
  return (A, B)

中文:
定义 homType?
  签名: (e : Expr)
  定义体: do
  let some (_, _, A, B) := e.app4? ``Quiver.Hom | none
  return (A, B)
-/
def homType? (e : Expr) : Option (Expr × Expr) := do
  let some (_, _, A, B) := e.app4? ``Quiver.Hom | none
  return (A, B)

/--
Definition of `homComp?` / `homComp?` 的定义

English:
definition homComp?
  signature: (f : Expr)
  body: do
  let some (_, _, _, _, _, f, g) := f.app7? ``CategoryStruct.comp | none
  return (f, g)

中文:
定义 homComp?
  签名: (f : Expr)
  定义体: do
  let some (_, _, _, _, _, f, g) := f.app7? ``CategoryStruct.comp | none
  return (f, g)
-/
def homComp? (f : Expr) : Option (Expr × Expr) := do
  let some (_, _, _, _, _, f, g) := f.app7? ``CategoryStruct.comp | none
  return (f, g)

/--
Definition of `ExprEmbeds` / `ExprEmbeds` 的定义

English:
abbreviation ExprEmbeds
  body: Array (String × Expr)

中文:
缩写 ExprEmbeds
  定义体: Array (String × Expr)
-/
abbrev ExprEmbeds := Array (String × Expr)

/-! ## Widget for general commutative diagrams -/

open scoped Jsx in
/--
Definition of `mkCommDiag` / `mkCommDiag` 的定义

English:
definition mkCommDiag
  signature: (sub : String) (embeds : ExprEmbeds)
  body: do
  let embeds ← embeds.mapM fun (s, h) =>
      return (s, <InteractiveCode fmt={← Widget.ppExprTagged h} />)
  return (
    <PenroseDiagram
      embeds={embeds}
      dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutative.dsl"}
      sty={include_str ".."/".."/".."/"widget"/"src"/

中文:
定义 mkCommDiag
  签名: (sub : String) (embeds : ExprEmbeds)
  定义体: do
  let embeds ← embeds.mapM fun (s, h) =>
      return (s, <InteractiveCode fmt={← Widget.ppExprTagged h} />)
  return (
    <PenroseDiagram
      embeds={embeds}
      dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutative.dsl"}
      sty={include_str ".."/".."/".."/"widget"/"src"/
-/
def mkCommDiag (sub : String) (embeds : ExprEmbeds) : MetaM Html := do
  let embeds ← embeds.mapM fun (s, h) =>
      return (s, <InteractiveCode fmt={← Widget.ppExprTagged h} />)
  return (
    <PenroseDiagram
      embeds={embeds}
      dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutative.dsl"}
      sty={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutative.sty"}
      sub={sub} />)

/-! ## Commutative triangles -/

/--
Definition of `subTriangle` / `subTriangle` 的定义

English:
definition subTriangle
  body: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"triangle.sub"

中文:
定义 subTriangle
  定义体: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"triangle.sub"

Depends on / 依赖: include_str, penrose, triangle, triangle.sub, widget
-/
def subTriangle := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"triangle.sub"

/--
Definition of `commTriangleM?` / `commTriangleM?` 的定义

English:
definition commTriangleM?
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  if let some (f, g) := homComp? lhs then
    let some (A, C) := homType? (← inferType rhs) | return none
    let some (_, B) := homType? (← inferType f) | return none
return some ← mkCommDiag subTriangle
      #[("A", A

中文:
定义 commTriangleM?
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  if let some (f, g) := homComp? lhs then
    let some (A, C) := homType? (← inferType rhs) | return none
    let some (_, B) := homType? (← inferType f) | return none
return some ← mkCommDiag subTriangle
      #[("A", A
-/
def commTriangleM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  if let some (f, g) := homComp? lhs then
    let some (A, C) := homType? (← inferType rhs) | return none
    let some (_, B) := homType? (← inferType f) | return none
return some ← mkCommDiag subTriangle
      #[("A", A), ("B", B), ("C", C),
        ("f", f), ("g", g), ("h", rhs)]
  let some (f, g) := homComp? rhs | return none
  let some (A, C) := homType? (← inferType lhs) | return none
  let some (_, B) := homType? (← inferType f) | return none
return some ← mkCommDiag subTriangle
    #[("A", A), ("B", B), ("C", C),
      ("f", f), ("g", g), ("h", lhs)]

/-- Presenter for a commutative triangle -/
@[expr_presenter]
/--
Definition of `commutativeTrianglePresenter` / `commutativeTrianglePresenter` 的定义

English:
definition commutativeTrianglePresenter
  signature: : ExprPresenter where
  body: "Commutative triangle"
  layoutKind := .block
  present type := do
    if let some d ← commTriangleM? type then
      return d
    throwError "Couldn't find a commutative triangle."

中文:
定义 commutativeTrianglePresenter
  签名: : ExprPresenter where
  定义体: "Commutative triangle"
  layoutKind := .block
  present type := do
    if let some d ← commTriangleM? type then
      return d
    throwError "Couldn't find a commutative triangle."

Depends on / 依赖: Commutative, triangle
-/
def commutativeTrianglePresenter : ExprPresenter where
  userName := "Commutative triangle"
  layoutKind := .block
  present type := do
    if let some d ← commTriangleM? type then
      return d
    throwError "Couldn't find a commutative triangle."

/-! ## Commutative squares -/

/--
Definition of `subSquare` / `subSquare` 的定义

English:
definition subSquare
  body: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"square.sub"

中文:
定义 subSquare
  定义体: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"square.sub"

Depends on / 依赖: include_str, penrose, square, square.sub, widget
-/
def subSquare := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"square.sub"

/--
Definition of `commSquareM?` / `commSquareM?` 的定义

English:
definition commSquareM?
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some (f, g) := homComp? lhs | return none
  let some (i, h) := homComp? rhs | return none
  let some (A, B) := homType? (← inferType f) | return none
  let some (D, C) := homType? (← inferType h) | return none
some

中文:
定义 commSquareM?
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some (f, g) := homComp? lhs | return none
  let some (i, h) := homComp? rhs | return none
  let some (A, B) := homType? (← inferType f) | return none
  let some (D, C) := homType? (← inferType h) | return none
some
-/
def commSquareM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some (f, g) := homComp? lhs | return none
  let some (i, h) := homComp? rhs | return none
  let some (A, B) := homType? (← inferType f) | return none
  let some (D, C) := homType? (← inferType h) | return none
some < > mkCommDiag subSquare
    #[("A", A), ("B", B), ("C", C), ("D", D),
      ("f", f), ("g", g), ("h", h), ("i", i)]

/-- Presenter for a commutative square -/
@[expr_presenter]
/--
Definition of `commutativeSquarePresenter` / `commutativeSquarePresenter` 的定义

English:
definition commutativeSquarePresenter
  signature: : ExprPresenter where
  body: "Commutative square"
  layoutKind := .block
  present type := do
    if let some d ← commSquareM? type then
      return d
    throwError "Couldn't find a commutative square."

中文:
定义 commutativeSquarePresenter
  签名: : ExprPresenter where
  定义体: "Commutative square"
  layoutKind := .block
  present type := do
    if let some d ← commSquareM? type then
      return d
    throwError "Couldn't find a commutative square."

Depends on / 依赖: Commutative, Functor, Functor.isContinuous_comp, Opens.grothendieckTopology, grothendieckTopology, isContinuous_comp, square
-/
def commutativeSquarePresenter : ExprPresenter where
  userName := "Commutative square"
  layoutKind := .block
  present type := do
    if let some d ← commSquareM? type then
      return d
    throwError "Couldn't find a commutative square."

end Widget

end Mathlib.Tactic
