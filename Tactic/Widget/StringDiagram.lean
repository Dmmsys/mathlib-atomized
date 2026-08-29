/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import ProofWidgets.Component.PenroseDiagram
public meta import ProofWidgets.Component.Panel.Basic
public meta import Mathlib.Data.List.Defs
public import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize
public meta import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public import Mathlib.Tactic.CategoryTheory.Monoidal.Normalize
public import ProofWidgets.Component.HtmlDisplay
public import ProofWidgets.Component.Panel.Basic
public import ProofWidgets.Component.PenroseDiagram
public import ProofWidgets.Presentation.Expr

/-!
# String Diagram Widget

This file provides meta infrastructure for displaying string diagrams for morphisms in monoidal
categories in the infoview. To enable the string diagram widget, you need to import this file and
inserting `with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]` at the beginning of the
proof. Alternatively, you can also write
```lean
open Mathlib.Tactic.Widget
show_panel_widgets [local StringDiagram]
```
to enable the string diagram widget in the current section.

We also have the `#string_diagram` command. For example,
```lean
#string_diagram MonoidalCategory.whisker_exchange
```
displays the string diagram for the exchange law of the left and right whiskerings.

String diagrams are graphical representations of morphisms in monoidal categories, which are
useful for rewriting computations. More precisely, objects in a monoidal category is represented
by strings, and morphisms between two objects is represented by nodes connecting two strings
associated with the objects. The tensor product `X ⊗ Y` corresponds to putting strings associated
with `X` and `Y` horizontally (from left to right), and the composition of morphisms `f : X ⟶ Y`
and `g : Y ⟶ Z` corresponds to connecting two nodes associated with `f` and `g` vertically (from
top to bottom) by strings associated with `Y`.

Currently, the string diagram widget provided in this file deals with equalities of morphisms
in monoidal categories. It displays string diagrams corresponding to the morphisms for the
left-hand and right-hand sides of the equality.

Some examples can be found in `MathlibTest/StringDiagram.lean`.

When drawing string diagrams, it is common to ignore associators and unitors. We follow this
convention. To do this, we need to extract non-structural morphisms that are not associators
and unitors from lean expressions. This operation is performed using the `Tactic.Monoidal.eval`
function.

A monoidal category can be viewed as a bicategory with a single object. The program in this
file can also be used to display the string diagram for general bicategories. With this in mind we
will sometimes refer to objects and morphisms in monoidal categories as 1-morphisms and 2-morphisms
respectively, borrowing the terminology of bicategories. Note that the relation between monoidal
categories and bicategories is formalized in `Mathlib/CategoryTheory/Bicategory/SingleObj.lean`,
although the string diagram widget does not use it directly.

-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab
open CategoryTheory

open BicategoryLike

namespace Widget.StringDiagram

initialize registerTraceClass `string_diagram

/-! ## Objects in string diagrams -/

/--
Definition of `AtomNode` / `AtomNode` 的定义

English:
structure AtomNode
  parameters: : Type where
  axioms and operations (4):
    - vPos : Nat
    - hPosSrc : Nat
    - hPosTar : Nat
    - atom : Atom

中文:
结构 AtomNode
  参数: : Type where
  公理与运算 (4 个):
    - vPos : 自然数
    - hPosSrc : 自然数
    - hPosTar : 自然数
    - atom : Atom
-/
structure AtomNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : Nat
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : Nat
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : Nat
  /-- The underlying expression of the node. -/
  atom : Atom

/--
Definition of `IdNode` / `IdNode` 的定义

English:
structure IdNode
  parameters: : Type where
  axioms and operations (4):
    - vPos : Nat
    - hPosSrc : Nat
    - hPosTar : Nat
    - id : Atom₁

中文:
结构 IdNode
  参数: : Type where
  公理与运算 (4 个):
    - vPos : 自然数
    - hPosSrc : 自然数
    - hPosTar : 自然数
    - id : Atom₁
-/
structure IdNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : Nat
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : Nat
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : Nat
  /-- The underlying expression of the node. -/
  id : Atom₁

/--
Inductive type `Node` / 归纳类型 `Node`

English:
inductive Node
  parameters: : Type
  constructors (2):
    - atom: AtomNode -> Node
    - id: IdNode -> Node

中文:
归纳类型 Node
  参数: : Type
  构造子 (2 个):
    - atom: AtomNode -> Node
    - id: IdNode -> Node
-/
inductive Node : Type
  | atom : AtomNode -> Node
  | id : IdNode -> Node

/--
Definition of `Node.e` / `Node.e` 的定义

English:
definition Node.e
  signature: : Node -> Expr

中文:
定义 Node.e
  签名: : Node -> Expr
-/
def Node.e : Node -> Expr
  | Node.atom n => n.atom.e
  | Node.id n => n.id.e

/--
Definition of `Node.srcList` / `Node.srcList` 的定义

English:
definition Node.srcList
  signature: : Node -> List (Node × Atom₁)

中文:
定义 Node.srcList
  签名: : Node -> List (Node × Atom₁)
-/
def Node.srcList : Node -> List (Node × Atom₁)
  | Node.atom n => n.atom.src.toList.map (fun f => (.atom n, f))
  | Node.id n => [(.id n, n.id)]

/--
Definition of `Node.tarList` / `Node.tarList` 的定义

English:
definition Node.tarList
  signature: : Node -> List (Node × Atom₁)

中文:
定义 Node.tarList
  签名: : Node -> List (Node × Atom₁)
-/
def Node.tarList : Node -> List (Node × Atom₁)
  | Node.atom n => n.atom.tgt.toList.map (fun f => (.atom n, f))
  | Node.id n => [(.id n, n.id)]

/--
Definition of `Node.vPos` / `Node.vPos` 的定义

English:
definition Node.vPos
  signature: : Node -> Nat

中文:
定义 Node.vPos
  签名: : Node -> 自然数
-/
def Node.vPos : Node -> Nat
  | Node.atom n => n.vPos
  | Node.id n => n.vPos

/--
Definition of `Node.hPosSrc` / `Node.hPosSrc` 的定义

English:
definition Node.hPosSrc
  signature: : Node -> Nat

中文:
定义 Node.hPosSrc
  签名: : Node -> 自然数
-/
def Node.hPosSrc : Node -> Nat
  | Node.atom n => n.hPosSrc
  | Node.id n => n.hPosSrc

/--
Definition of `Node.hPosTar` / `Node.hPosTar` 的定义

English:
definition Node.hPosTar
  signature: : Node -> Nat

中文:
定义 Node.hPosTar
  签名: : Node -> 自然数

Depends on / 依赖: NoetherianSpace, PrespectralSpace
-/
def Node.hPosTar : Node -> Nat
  | Node.atom n => n.hPosTar
  | Node.id n => n.hPosTar

/--
Definition of `Strand` / `Strand` 的定义

English:
structure Strand
  parameters: : Type where
  axioms and operations (4):
    - hPos : Nat
    - startPoint : Node
    - endPoint : Node
    - atom₁ : Atom₁

中文:
结构 Strand
  参数: : Type where
  公理与运算 (4 个):
    - hPos : 自然数
    - startPoint : Node
    - endPoint : Node
    - atom₁ : Atom₁

Depends on / 依赖: LocallyCompactSpace, PrespectralSpace
-/
structure Strand : Type where
  /-- The horizontal position of the strand in the string diagram. -/
  hPos : Nat
  /-- The start point of the strand in the string diagram. -/
  startPoint : Node
  /-- The end point of the strand in the string diagram. -/
  endPoint : Node
  /-- The underlying expression of the strand. -/
  atom₁ : Atom₁

/--
Definition of `Strand.vPos` / `Strand.vPos` 的定义

English:
definition Strand.vPos
  signature: (s : Strand)
  body: s.startPoint.vPos

中文:
定义 Strand.vPos
  签名: (s : Strand)
  定义体: s.startPoint.vPos

Depends on / 依赖: PrespectralSpace, T2Space, TotallySeparatedSpace, s.startPoint.vPos, startPoint
-/
def Strand.vPos (s : Strand) : Nat :=
  s.startPoint.vPos

end Widget.StringDiagram

namespace BicategoryLike

open Widget.StringDiagram

/--
Definition of `WhiskerRight.nodes` / `WhiskerRight.nodes` 的定义

English:
definition WhiskerRight.nodes
  signature: (v h₁ h₂ : Nat)
  body: η.nodes v h₁ h₂
    let k₁ := (ηs.map (fun n => n.srcList)).flatten.length
    let k₂ := (ηs.map (fun n => n.tarList)).flatten.length
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    ηs ++ [s]

中文:
定义 WhiskerRight.nodes
  签名: (v h₁ h₂ : 自然数)
  定义体: η.nodes v h₁ h₂
    let k₁ := (ηs.map (fun n => n.srcList)).flatten.length
    let k₂ := (ηs.map (fun n => n.tarList)).flatten.length
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    ηs ++ [s]
-/
def WhiskerRight.nodes (v h₁ h₂ : Nat) : WhiskerRight -> List Node
  | WhiskerRight.of η => [.atom ⟨v, h₁, h₂, η⟩]
  | WhiskerRight.whisker _ η f =>
    let ηs := η.nodes v h₁ h₂
    let k₁ := (ηs.map (fun n => n.srcList)).flatten.length
    let k₂ := (ηs.map (fun n => n.tarList)).flatten.length
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    ηs ++ [s]

/--
Definition of `HorizontalComp.nodes` / `HorizontalComp.nodes` 的定义

English:
definition HorizontalComp.nodes
  signature: (v h₁ h₂ : Nat)
  body: η.nodes v h₁ h₂
    let k₁ := (s₁.map (fun n => n.srcList)).flatten.length
    let k₂ := (s₁.map (fun n => n.tarList)).flatten.length
    let s₂ := ηs.nodes v (h₁ + k₁) (h₂ + k₂)
    s₁ ++ s₂

中文:
定义 HorizontalComp.nodes
  签名: (v h₁ h₂ : 自然数)
  定义体: η.nodes v h₁ h₂
    let k₁ := (s₁.map (fun n => n.srcList)).flatten.length
    let k₂ := (s₁.map (fun n => n.tarList)).flatten.length
    let s₂ := ηs.nodes v (h₁ + k₁) (h₂ + k₂)
    s₁ ++ s₂
-/
def HorizontalComp.nodes (v h₁ h₂ : Nat) : HorizontalComp -> List Node
  | HorizontalComp.of η => η.nodes v h₁ h₂
  | HorizontalComp.cons _ η ηs =>
    let s₁ := η.nodes v h₁ h₂
    let k₁ := (s₁.map (fun n => n.srcList)).flatten.length
    let k₂ := (s₁.map (fun n => n.tarList)).flatten.length
    let s₂ := ηs.nodes v (h₁ + k₁) (h₂ + k₂)
    s₁ ++ s₂

/--
Definition of `WhiskerLeft.nodes` / `WhiskerLeft.nodes` 的定义

English:
definition WhiskerLeft.nodes
  signature: (v h₁ h₂ : Nat)
  body: .id ⟨v, h₁, h₂, f⟩
    let ss := η.nodes v (h₁ + 1) (h₂ + 1)
    s :: ss

中文:
定义 WhiskerLeft.nodes
  签名: (v h₁ h₂ : 自然数)
  定义体: .id ⟨v, h₁, h₂, f⟩
    let ss := η.nodes v (h₁ + 1) (h₂ + 1)
    s :: ss
-/
def WhiskerLeft.nodes (v h₁ h₂ : Nat) : WhiskerLeft -> List Node
  | WhiskerLeft.of η => η.nodes v h₁ h₂
  | WhiskerLeft.whisker _ f η =>
    let s : Node := .id ⟨v, h₁, h₂, f⟩
    let ss := η.nodes v (h₁ + 1) (h₂ + 1)
    s :: ss

variable {ρ : Type} [MonadMor₁ (CoherenceM ρ)]

/--
Definition of `topNodes` / `topNodes` 的定义

English:
definition topNodes
  signature: (η : WhiskerLeft)
  body: do
  return (← η.srcM).toList.mapIdx fun i f => .id ⟨0, i, i, f⟩

中文:
定义 topNodes
  签名: (η : WhiskerLeft)
  定义体: do
  return (← η.srcM).toList.mapIdx fun i f => .id ⟨0, i, i, f⟩
-/
def topNodes (η : WhiskerLeft) : CoherenceM ρ (List Node) := do
  return (← η.srcM).toList.mapIdx fun i f => .id ⟨0, i, i, f⟩

/--
Definition of `NormalExpr.nodesAux` / `NormalExpr.nodesAux` 的定义

English:
definition NormalExpr.nodesAux
  signature: (v : Nat)
  body: η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂

中文:
定义 NormalExpr.nodesAux
  签名: (v : 自然数)
  定义体: η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂
-/
def NormalExpr.nodesAux (v : Nat) : NormalExpr -> CoherenceM ρ (List (List Node))
  | NormalExpr.nil _ α => return [(← α.srcM).toList.mapIdx fun i f => .id ⟨v, i, i, f⟩]
  | NormalExpr.cons _ _ η ηs => do
    let s₁ := η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂

/--
Definition of `NormalExpr.nodes` / `NormalExpr.nodes` 的定义

English:
definition NormalExpr.nodes
  signature: (e : NormalExpr)
  body: match e with
  | NormalExpr.nil _ _ => return []
  | NormalExpr.cons _ _ η _ => return (← topNodes η) :: (← e.nodesAux 1)

@[deprecated (since := "2026-02-26")] meta alias pairs := List.consecutivePairs

中文:
定义 NormalExpr.nodes
  签名: (e : NormalExpr)
  定义体: match e with
  | NormalExpr.nil _ _ => return []
  | NormalExpr.cons _ _ η _ => return (← topNodes η) :: (← e.nodesAux 1)

@[deprecated (since := "2026-02-26")] meta alias pairs := List.consecutivePairs

Depends on / 依赖: NormalExpr, NormalExpr.cons, NormalExpr.nil, e.nodesAux, nodesAux, return, topNodes
-/
def NormalExpr.nodes (e : NormalExpr) : CoherenceM ρ (List (List Node)) :=
  match e with
  | NormalExpr.nil _ _ => return []
  | NormalExpr.cons _ _ η _ => return (← topNodes η) :: (← e.nodesAux 1)

@[deprecated (since := "2026-02-26")] meta alias pairs := List.consecutivePairs

/--
Definition of `NormalExpr.strands` / `NormalExpr.strands` 的定义

English:
definition NormalExpr.strands
  signature: (e : NormalExpr)
  body: do
  let l ← e.nodes
  (l.consecutivePairs).mapM fun (x, y) => do
    let xs := (x.map (fun n => n.tarList)).flatten
    let ys := (y.map (fun n => n.srcList)).flatten
    -- sanity check
    if xs.length != ys.length then
      throwError "The number of the start and end points of a string does not

中文:
定义 NormalExpr.strands
  签名: (e : NormalExpr)
  定义体: do
  let l ← e.nodes
  (l.consecutivePairs).mapM fun (x, y) => do
    let xs := (x.map (fun n => n.tarList)).flatten
    let ys := (y.map (fun n => n.srcList)).flatten
    -- sanity check
    if xs.length != ys.length then
      throwError "The number of the start and end points of a string does not
-/
def NormalExpr.strands (e : NormalExpr) : CoherenceM ρ (List (List Strand)) := do
  let l ← e.nodes
  (l.consecutivePairs).mapM fun (x, y) => do
    let xs := (x.map (fun n => n.tarList)).flatten
    let ys := (y.map (fun n => n.srcList)).flatten
    -- sanity check
    if xs.length != ys.length then
      throwError "The number of the start and end points of a string does not match."
    (xs.zip ys).mapIdxM fun k ((n₁, f₁), (n₂, _)) => do
      return ⟨n₁.hPosTar + k, n₁, n₂, f₁⟩

end BicategoryLike

namespace Widget.StringDiagram

/--
Definition of `PenroseVar` / `PenroseVar` 的定义

English:
structure PenroseVar
  parameters: : Type where
  axioms and operations (3):
    - ident : String
    - indices : List Nat
    - e : Expr

中文:
结构 PenroseVar
  参数: : Type where
  公理与运算 (3 个):
    - ident : String
    - indices : List 自然数
    - e : Expr
-/
structure PenroseVar : Type where
  /-- The identifier of the variable. -/
  ident : String
  /-- The indices of the variable. -/
  indices : List Nat
  /-- The underlying expression of the variable. -/
  e : Expr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString PenroseVar
  body: ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

中文:
实例 :
  签名: ToString PenroseVar
  定义体: ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

Depends on / 依赖: indices, v.ident, v.indices.foldl
-/
instance : ToString PenroseVar :=
  ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

/--
Definition of `Node.toPenroseVar` / `Node.toPenroseVar` 的定义

English:
definition Node.toPenroseVar
  signature: (n : Node)
  body: ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

中文:
定义 Node.toPenroseVar
  签名: (n : Node)
  定义体: ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

Depends on / 依赖: hPosSrc, hPosTar, n.hPosSrc, n.hPosTar, n.vPos
-/
def Node.toPenroseVar (n : Node) : PenroseVar :=
  ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

/--
Definition of `Strand.toPenroseVar` / `Strand.toPenroseVar` 的定义

English:
definition Strand.toPenroseVar
  signature: (s : Strand)
  body: ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

中文:
定义 Strand.toPenroseVar
  签名: (s : Strand)
  定义体: ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

Depends on / 依赖: s.atom, s.hPos, s.vPos
-/
def Strand.toPenroseVar (s : Strand) : PenroseVar :=
  ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

/-! ## Widget for general string diagrams -/

open ProofWidgets Penrose DiagramBuilderM Lean.Server

open scoped Jsx in
/--
Definition of `addPenroseVar` / `addPenroseVar` 的定义

English:
definition addPenroseVar
  signature: (tp : String) (v : PenroseVar)
  body: do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

中文:
定义 addPenroseVar
  签名: (tp : String) (v : PenroseVar)
  定义体: do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h
-/
def addPenroseVar (tp : String) (v : PenroseVar) :
    DiagramBuilderM Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

/--
Definition of `addConstructor` / `addConstructor` 的定义

English:
definition addConstructor
  signature: (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar)
  body: do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

中文:
定义 addConstructor
  签名: (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar)
  定义体: do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"
-/
def addConstructor (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

open scoped Jsx in
/--
Definition of `mkStringDiagram` / `mkStringDiagram` 的定义

English:
definition mkStringDiagram
  signature: (nodes : List (List Node)) (strands : List (List Strand))
  body: do
  /- Add 2-morphisms. -/
  for x in nodes.flatten do
    match x with
    | .atom _ => do addPenroseVar "Atom" x.toPenroseVar
    | .id _ => do addPenroseVar "Id" x.toPenroseVar
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in l.consecutivePairs do
      addInstruction s!"Left({x₁

中文:
定义 mkStringDiagram
  签名: (nodes : List (List Node)) (strands : List (List Strand))
  定义体: do
  /- Add 2-morphisms. -/
  for x in nodes.flatten do
    match x with
    | .atom _ => do addPenroseVar "Atom" x.toPenroseVar
    | .id _ => do addPenroseVar "Id" x.toPenroseVar
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in l.consecutivePairs do
      addInstruction s!"Left({x₁
-/
def mkStringDiagram (nodes : List (List Node)) (strands : List (List Strand)) :
    DiagramBuilderM PUnit := do
  /- Add 2-morphisms. -/
  for x in nodes.flatten do
    match x with
    | .atom _ => do addPenroseVar "Atom" x.toPenroseVar
    | .id _ => do addPenroseVar "Id" x.toPenroseVar
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in l.consecutivePairs do
      addInstruction s!"Left({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add constraints. -/
  for (l₁, l₂) in nodes.consecutivePairs do
    if let some x₁ := l₁.head? then
      if let some x₂ := l₂.head? then
        addInstruction s!"Above({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add 1-morphisms as strings. -/
  for l in strands do
    for s in l do
      addConstructor "Mor1" s.toPenroseVar
        "MakeString" [s.startPoint.toPenroseVar, s.endPoint.toPenroseVar]

/--
Definition of `dsl` / `dsl` 的定义

English:
definition dsl
  body: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"

中文:
定义 dsl
  定义体: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"

Depends on / 依赖: include_str, monoidal, monoidal.dsl, penrose, widget
-/
def dsl :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"

/--
Definition of `sty` / `sty` 的定义

English:
definition sty
  body: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"

中文:
定义 sty
  定义体: include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"

Depends on / 依赖: include_str, monoidal, monoidal.sty, penrose, widget
-/
def sty :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"

/--
Inductive type `Kind` / 归纳类型 `Kind`

English:
inductive Kind
  parameters: where
  constructors (3):
    - monoidal: Kind
    - bicategory: Kind
    - none: Kind

中文:
归纳类型 Kind
  参数: where
  构造子 (3 个):
    - monoidal: Kind
    - bicategory: Kind
    - none: Kind
-/
inductive Kind where
  | monoidal : Kind
  | bicategory : Kind
  | none : Kind

/--
Definition of `Kind.name` / `Kind.name` 的定义

English:
definition Kind.name
  signature: : Kind -> Name

中文:
定义 Kind.name
  签名: : Kind -> Name
-/
def Kind.name : Kind -> Name
  | Kind.monoidal => `monoidal
  | Kind.bicategory => `bicategory
  | Kind.none => default

/--
Definition of `mkKind` / `mkKind` 的定义

English:
definition mkKind
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  let e ← (match (← whnfR e).eq? with
    | some (_, lhs, _) => return lhs
    | none => return e)
  let ctx? ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e
  match ctx? with
  | some _ => return .bicategory
  | none =>
    let ctx? ← BicategoryLike.mkContext

中文:
定义 mkKind
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  let e ← (match (← whnfR e).eq? with
    | some (_, lhs, _) => return lhs
    | none => return e)
  let ctx? ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e
  match ctx? with
  | some _ => return .bicategory
  | none =>
    let ctx? ← BicategoryLike.mkContext
-/
def mkKind (e : Expr) : MetaM Kind := do
  let e ← instantiateMVars e
  let e ← (match (← whnfR e).eq? with
    | some (_, lhs, _) => return lhs
    | none => return e)
  let ctx? ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e
  match ctx? with
  | some _ => return .bicategory
  | none =>
    let ctx? ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e
    match ctx? with
    | some _ => return .monoidal
    | none => return .none

open scoped Jsx in
/--
Definition of `stringM?` / `stringM?` 的定义

English:
definition stringM?
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  let k ← mkKind e
  let x : Option (List (List Node) × List (List Strand)) ← (match k with
    | .monoidal => do
      let some ctx ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e | return none
      CoherenceM.run (ctx := ctx) do
        let e' := (← Bicategor

中文:
定义 stringM?
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  let k ← mkKind e
  let x : Option (List (List Node) × List (List Strand)) ← (match k with
    | .monoidal => do
      let some ctx ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e | return none
      CoherenceM.run (ctx := ctx) do
        let e' := (← Bicategor
-/
def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let k ← mkKind e
  let x : Option (List (List Node) × List (List Strand)) ← (match k with
    | .monoidal => do
      let some ctx ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e | return none
      CoherenceM.run (ctx := ctx) do
        let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
        return some (← e'.nodes, ← e'.strands)
    | .bicategory => do
      let some ctx ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e | return none
      CoherenceM.run (ctx := ctx) do
        let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
        return some (← e'.nodes, ← e'.strands)
    | .none => return none)
  match x with
  | none => return none
  | some (nodes, strands) => do
    DiagramBuilderM.run do
      mkStringDiagram nodes strands
      trace[string_diagram] "Penrose substance: \n{(← get).sub}"
      match ← DiagramBuilderM.buildDiagram dsl sty with
      | some html => return html
      | none => return <span>No non-structural morphisms found.</span>

open scoped Jsx in
/--
Definition of `mkEqHtml` / `mkEqHtml` 的定义

English:
definition mkEqHtml
  signature: (lhs rhs : Html)
  body: <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram

中文:
定义 mkEqHtml
  签名: (lhs rhs : Html)
  定义体: <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram

Depends on / 依赖: className, details, diagram, pointer, summary
-/
def mkEqHtml (lhs rhs : Html) : Html :=
  <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for RHS</summary> {rhs}
      </details>
    </div>
  </div>

/--
Definition of `stringEqM?` / `stringEqM?` 的定义

English:
definition stringEqM?
  signature: (e : Expr)
  body: do
let e ← whnfR ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some lhs ← stringM? lhs | return none
  let some rhs ← stringM? rhs | return none
return some mkEqHtml lhs rhs

中文:
定义 stringEqM?
  签名: (e : Expr)
  定义体: do
let e ← whnfR ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some lhs ← stringM? lhs | return none
  let some rhs ← stringM? rhs | return none
return some mkEqHtml lhs rhs
-/
def stringEqM? (e : Expr) : MetaM (Option Html) := do
let e ← whnfR ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some lhs ← stringM? lhs | return none
  let some rhs ← stringM? rhs | return none
return some mkEqHtml lhs rhs

/--
Definition of `stringMorOrEqM?` / `stringMorOrEqM?` 的定义

English:
definition stringMorOrEqM?
  signature: (e : Expr)
  body: do
  forallTelescopeReducing (← whnfR <| ← inferType e) fun xs a => do
    if let some html ← stringM? (mkAppN e xs) then
      return some html
    else if let some html ← stringEqM? a then
      return some html
    else
      return none

中文:
定义 stringMorOrEqM?
  签名: (e : Expr)
  定义体: do
  forallTelescopeReducing (← whnfR <| ← inferType e) fun xs a => do
    if let some html ← stringM? (mkAppN e xs) then
      return some html
    else if let some html ← stringEqM? a then
      return some html
    else
      return none
-/
def stringMorOrEqM? (e : Expr) : MetaM (Option Html) := do
  forallTelescopeReducing (← whnfR <| ← inferType e) fun xs a => do
    if let some html ← stringM? (mkAppN e xs) then
      return some html
    else if let some html ← stringEqM? a then
      return some html
    else
      return none

/-- The `Expr` presenter for displaying string diagrams. -/
@[expr_presenter]
/--
Definition of `stringPresenter` / `stringPresenter` 的定义

English:
definition stringPresenter
  signature: : ExprPresenter where
  body: "String diagram"
  layoutKind := .block
  present type := do
    if let some html ← stringMorOrEqM? type then
      return html
    throwError "Couldn't find a 2-morphism to display a string diagram."

中文:
定义 stringPresenter
  签名: : ExprPresenter where
  定义体: "String diagram"
  layoutKind := .block
  present type := do
    if let some html ← stringMorOrEqM? type then
      return html
    throwError "Couldn't find a 2-morphism to display a string diagram."

Depends on / 依赖: diagram
-/
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some html ← stringMorOrEqM? type then
      return html
    throwError "Couldn't find a 2-morphism to display a string diagram."

open scoped Jsx in
/-- The RPC method for displaying string diagrams. -/
@[server_rpc_method]
/--
Definition of `rpc` / `rpc` 的定义

English:
definition rpc
  signature: (props : PanelWidgetProps)
  body: RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          stringEqM? type)
    match html 

中文:
定义 rpc
  签名: (props : PanelWidget命题s)
  定义体: RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          stringEqM? type)
    match html 

Depends on / 依赖: Diagram, RequestM, RequestM.asTask, asTask, g.ctx.val.runMetaM, g.mvarId.getType, g.mvarId.withContext, getType, isEmpty, mvarId, props.goals, props.goals.isEmpty, return, runMetaM, stringEqM, unreachable, withContext
-/
def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          stringEqM? type)
    match html with
    | none => return <span>No String Diagram.</span>
    | some inner => return inner

end StringDiagram

open ProofWidgets

/-- Display the string diagrams if the goal is an equality of morphisms in a monoidal category. -/
@[widget_module]
/--
Definition of `StringDiagram` / `StringDiagram` 的定义

English:
definition StringDiagram
  signature: : Component PanelWidgetProps
  body: mk_rpc_widget% StringDiagram.rpc

中文:
定义 StringDiagram
  签名: : Component PanelWidget命题s
  定义体: mk_rpc_widget% StringDiagram.rpc

Depends on / 依赖: StringDiagram, StringDiagram.rpc, mk_rpc_widget
-/
def StringDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% StringDiagram.rpc

open Command

/--
Display the string diagram for a given term.

Example usage:
```
/- String diagram for the equality theorem. -/
#string_diagram MonoidalCategory.whisker_exchange

/- String diagram for the morphism. -/
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y : C} (f : 𝟙_ C ⟶ X otimes Y) in
#string_diagram f
```
-/
syntax (name := stringDiagram) "#string_diagram " term : command

@[command_elab stringDiagram, inherit_doc stringDiagram]
/--
Definition of `elabStringDiagramCmd` / `elabStringDiagramCmd` 的定义

English:
definition elabStringDiagramCmd
  signature: : CommandElab
  body: fun
  | stx@`(#string_diagram $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← StringDiagram.stringMorOrE

中文:
定义 elabStringDiagramCmd
  签名: : CommandElab
  定义体: fun
  | stx@`(#string_diagram $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← StringDiagram.stringMorOrE
-/
def elabStringDiagramCmd : CommandElab := fun
  | stx@`(#string_diagram $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← StringDiagram.stringMorOrEqM? e with
      | some html => return html
      | none => throwError "could not find a morphism or equality: {e}"
liftCoreM Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

end Mathlib.Tactic.Widget
