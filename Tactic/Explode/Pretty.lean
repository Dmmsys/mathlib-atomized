/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus, Kyle Miller
-/
module

public meta import Lean.Meta.Basic
public meta import Mathlib.Tactic.Explode.Datatypes
public import Mathlib.Tactic.Explode.Datatypes

/-!
# Explode command: pretty

This file contains UI code to render the Fitch table.
-/

public meta section

open Lean
namespace Mathlib.Explode

/--
Given a list of `MessageData`s, make them of equal length.
We need this in order to form columns in our Fitch table.

```lean
padRight ["hi", "hello"] = ["hi   ", "hello"]
```
-/
/-
**Mathlib.Explode.padRight** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Explode`。
形式化陈述：padRight (mds : List MessageData) : MetaM (List MessageData)
参数：mds : List MessageData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a list of `MessageData`s, make them of equal length.
We need this in order to form columns in our Fitch table.

```lean
padRight ["hi", "hello"] = ["hi   ", "hello"]
```
-/
def padRight (mds : List MessageData) : MetaM (List MessageData) := do
  -- 1. Find the max length of the word in a list
  let mut maxLength := 0
  for md in mds do
    maxLength := max maxLength (← md.toString).length

  -- 2. Pad all words in a list with " "
  let pad (md : MessageData) : MetaM MessageData := do
    let padWidth : Nat := maxLength - (← md.toString).length
    return md ++ "".pushn ' ' padWidth

  mds.mapM pad

/-- Render a particular row of the Fitch table. -/
/-
**Mathlib.Explode.rowToMessageData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Explode`。
形式化陈述：rowToMessageData : List MessageData -> List MessageData -> List MessageDat
a -> List Entry -> MetaM MessageData | line :: lines, dep :: deps, thm :: thms, 
en :: es => do let pipes
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Render a particular row of the Fitch table.
-/
def rowToMessageData :
    List MessageData → List MessageData → List MessageData → List Entry → MetaM MessageData
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let pipes := String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => s!"├ "
      | Status.intro  => s!"│ {pipes}┌ "
      | Status.cintro => s!"│ {pipes}├ "
      | Status.lam    => s!"│ {pipes}"
      | Status.reg    => s!"│ {pipes}"

    let row := m!"{line}│{dep}│ {thm} {pipes}{en.type}\n"
    return (← rowToMessageData lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil

/-- Given all `Entries`, return the entire Fitch table. -/
/-
**Mathlib.Explode.entriesToMessageData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Explod
e`。
形式化陈述：entriesToMessageData (entries : Entries) : MetaM MessageData
参数：entries : Entries。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given all `Entries`, return the entire Fitch table.
-/
def entriesToMessageData (entries : Entries) : MetaM MessageData := do
  -- ['1', '2', '3']
  let paddedLines ← padRight <| entries.l.map fun entry => m!"{entry.line!}"
  -- ['   ', '1,2', '1  ']
  let paddedDeps ← padRight <| entries.l.map fun entry =>
    String.intercalate "," <| entry.deps.map (fun dep => (dep.map toString).getD "_")
  -- ['p  ', 'hP ', '∀I ']
  let paddedThms ← padRight <| entries.l.map (·.thm)

  rowToMessageData paddedLines paddedDeps paddedThms entries.l

end Explode

end Mathlib

