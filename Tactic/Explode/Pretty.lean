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
Definition of `padRight` / `padRight` 的定义

English:
definition padRight
  signature: (mds : List MessageData)
  body: do
  -- 1. Find the max length of the word in a list
  let mut maxLength := 0
  for md in mds do
    maxLength := max maxLength (← md.toString).length

  -- 2. Pad all words in a list with " "
  let pad (md : MessageData) : MetaM MessageData := do
    let padWidth : Nat := maxLength - (← md.toString).length
    return md ++ "".pushn ' ' padWidth

  mds.mapM pad

中文:
定义 padRight
  签名: (mds : 列表 MessageData)
  定义体: do
  -- 1. Find the max length of the word in a list
  let mut maxLength := 0
  for md in mds do
    maxLength := max maxLength (← md.toString).length

  -- 2. Pad all words in a list with " "
  let pad (md : MessageData) : MetaM MessageData := do
    let padWidth : Nat := maxLength - (← md.toString).length
    return md ++ "".pushn ' ' padWidth

  mds.mapM pad
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

/--
Definition of `rowToMessageData` / `rowToMessageData` 的定义

English:
definition rowToMessageData
  signature: :
  body: String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => s!"├ "
      | Status.intro => s!"│ {pipes}┌ "
      | Status.cintro => s!"│ {pipes}├ "
      | Status.lam => s!"│ {pipes}"
      | Status.reg => s!"│ {pipes}"

    let row := m!"{line}│{dep}│ {thm} {pipes}{en.type}\n"
    return (← rowToMessageData lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil

中文:
定义 rowToMessageData
  签名: :
  定义体: String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => s!"├ "
      | Status.intro => s!"│ {pipes}┌ "
      | Status.cintro => s!"│ {pipes}├ "
      | Status.lam => s!"│ {pipes}"
      | Status.reg => s!"│ {pipes}"

    let row := m!"{line}│{dep}│ {thm} {pipes}{en.type}\n"
    return (← rowToMessageData lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil

Depends on / 依赖: List.replicate, String.join, en.depth, replicate
-/
def rowToMessageData :
    List MessageData -> List MessageData -> List MessageData -> List Entry -> MetaM MessageData
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let pipes := String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => s!"├ "
      | Status.intro => s!"│ {pipes}┌ "
      | Status.cintro => s!"│ {pipes}├ "
      | Status.lam => s!"│ {pipes}"
      | Status.reg => s!"│ {pipes}"

    let row := m!"{line}│{dep}│ {thm} {pipes}{en.type}\n"
    return (← rowToMessageData lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil

/--
Definition of `entriesToMessageData` / `entriesToMessageData` 的定义

English:
definition entriesToMessageData
  signature: (entries : Entries)
  body: do
  -- ['1', '2', '3']
let paddedLines ← padRight entries.l.map fun entry => m!"{entry.line!}"
  -- [' ', '1,2', '1 ']
let paddedDeps ← padRight entries.l.map fun entry =>
String.intercalate "," entry.deps.map (fun dep => (dep.map toString).getD "_")
  -- ['p ', 'hP ', '∀I ']
let paddedThms ← padRight entries.l.map (·.thm)

  rowToMessageData paddedLines paddedDeps paddedThms entries.l

中文:
定义 entriesToMessageData
  签名: (entries : Entries)
  定义体: do
  -- ['1', '2', '3']
let paddedLines ← padRight entries.l.map fun entry => m!"{entry.line!}"
  -- [' ', '1,2', '1 ']
let paddedDeps ← padRight entries.l.map fun entry =>
String.intercalate "," entry.deps.map (fun dep => (dep.map toString).getD "_")
  -- ['p ', 'hP ', '∀I ']
let paddedThms ← padRight entries.l.map (·.thm)

  rowToMessageData paddedLines paddedDeps paddedThms entries.l
-/
def entriesToMessageData (entries : Entries) : MetaM MessageData := do
  -- ['1', '2', '3']
let paddedLines ← padRight entries.l.map fun entry => m!"{entry.line!}"
  -- [' ', '1,2', '1 ']
let paddedDeps ← padRight entries.l.map fun entry =>
String.intercalate "," entry.deps.map (fun dep => (dep.map toString).getD "_")
  -- ['p ', 'hP ', '∀I ']
let paddedThms ← padRight entries.l.map (·.thm)

  rowToMessageData paddedLines paddedDeps paddedThms entries.l

end Explode

end Mathlib
