/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus, Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.Util.Trace

/-!
# Explode command: datatypes

This file contains datatypes used by the `#explode` command and their associated methods.
-/

public meta section

open Lean

namespace Mathlib.Explode

initialize registerTraceClass `explode

/--
Inductive type `Status` / 归纳类型 `Status`

English:
inductive Status
  parameters: where
  constructors (5):
    - sintro: Status
    - intro: Status
    - cintro: Status
    - lam: Status
    - reg: Status

中文:
归纳类型 Status
  参数: where
  构造子 (5 个):
    - sintro: Status
    - intro: Status
    - cintro: Status
    - lam: Status
    - reg: Status
-/
inductive Status where
  /-- `├` Start intro (top-level) -/
  | sintro : Status
  /-- `Entry.depth` * `│` + `┌` Normal intro -/
  | intro : Status
  /-- `Entry.depth` * `│` + `├` Continuation intro -/
  | cintro : Status
  /-- `Entry.depth` * `│` -/
  | lam : Status
  /-- `Entry.depth` * `│` -/
  | reg : Status
  deriving Inhabited

/--
Definition of `Entry` / `Entry` 的定义

English:
structure Entry
  parameters: where
  axioms and operations (7):
    - type : MessageData
    - line : Option Nat  [default: none]
    - depth : Nat
    - status : Status
    - thm : MessageData
    - deps : List (Option Nat)
    - useAsDep : Bool

中文:
结构 Entry
  参数: where
  公理与运算 (7 个):
    - type : MessageData
    - line : 选项类型 自然数  [默认: none]
    - depth : 自然数
    - status : Status
    - thm : MessageData
    - deps : 列表 (选项类型 自然数)
    - useAsDep : 布尔值
-/
structure Entry where
  /-- A type of this expression as a `MessageData`. Make sure to use `addMessageContext`. -/
  type : MessageData
  /-- The row number, starting from `0`. This is set by `Entries.add`. -/
  line : Option Nat := none
  /-- How many `if`s (aka lambda-abstractions) this row is nested under. -/
  depth : Nat
  /-- What `Status` this entry has - this only affects how `│`s are displayed. -/
  status : Status
  /-- What to display in the "theorem applied" column.
  Make sure to use `addMessageContext` if needed. -/
  thm : MessageData
  /-- Which other lines (aka rows) this row depends on.
  `none` means that the dependency has been filtered out of the table. -/
  deps : List (Option Nat)
  /-- Whether or not to use this in future deps lists. Generally controlled by the `select` function
  passed to `explodeCore`. Exception: `∀I` may ignore this for introduced hypotheses. -/
  useAsDep : Bool

/--
Definition of `Entry.line!` / `Entry.line!` 的定义

English:
definition Entry.line!
  signature: (entry : Entry)
  body: entry.line.get!

中文:
定义 Entry.line!
  签名: (entry : Entry)
  定义体: entry.line.get!

Depends on / 依赖: entry.line.get
-/
def Entry.line! (entry : Entry) : Nat := entry.line.get!

/--
Definition of `Entries` / `Entries` 的定义

English:
structure Entries
  parameters: : Type where
  axioms and operations (2):
    - s : ExprMap Entry
    - l : List Entry

中文:
结构 Entries
  参数: : 类型 where
  公理与运算 (2 个):
    - s : ExprMap Entry
    - l : 列表 Entry
-/
structure Entries : Type where
  /-- Allows us to compare `Expr`s fast. -/
  s : ExprMap Entry
  /-- Simple list of `Expr`s. -/
  l : List Entry
  deriving Inhabited

/--
Definition of `Entries.find?` / `Entries.find?` 的定义

English:
definition Entries.find?
  signature: (es : Entries) (e : Expr)
  body: es.s[e]?

中文:
定义 Entries.find?
  签名: (es : Entries) (e : Expr)
  定义体: es.s[e]?

Depends on / 依赖: es.s
-/
def Entries.find? (es : Entries) (e : Expr) : Option Entry :=
  es.s[e]?

/--
Definition of `Entries.size` / `Entries.size` 的定义

English:
definition Entries.size
  signature: (es : Entries)
  body: es.s.size

中文:
定义 Entries.size
  签名: (es : Entries)
  定义体: es.s.size

Depends on / 依赖: es.s.size
-/
def Entries.size (es : Entries) : Nat :=
  es.s.size

/--
Definition of `Entries.add` / `Entries.add` 的定义

English:
definition Entries.add
  signature: (entries : Entries) (expr : Expr) (entry : Entry)
  body: if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)

中文:
定义 Entries.add
  签名: (entries : Entries) (expr : Expr) (entry : Entry)
  定义体: if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)

Depends on / 依赖: entries, entries.find, entries.l, entries.s.insert, entries.size, insert
-/
def Entries.add (entries : Entries) (expr : Expr) (entry : Entry) : Entry × Entries :=
  if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)

/--
Definition of `Entries.addSynonym` / `Entries.addSynonym` 的定义

English:
definition Entries.addSynonym
  signature: (entries : Entries) (expr : Expr) (entry : Entry)
  body: ⟨entries.s.insert expr entry, entries.l⟩

中文:
定义 Entries.addSynonym
  签名: (entries : Entries) (expr : Expr) (entry : Entry)
  定义体: ⟨entries.s.insert expr entry, entries.l⟩

Depends on / 依赖: entries, entries.l, entries.s.insert, insert
-/
def Entries.addSynonym (entries : Entries) (expr : Expr) (entry : Entry) : Entries :=
  ⟨entries.s.insert expr entry, entries.l⟩

end Explode

end Mathlib
