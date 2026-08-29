/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public meta import Mathlib.Data.String.Defs
public import Mathlib.Init

/-!
# Format Table

This file provides a simple function for formatting a two-dimensional array of `String`s
into a markdown-compliant table.
-/

public meta section

/--
Inductive type `Alignment` / 归纳类型 `Alignment`

English:
inductive Alignment
  parameters: where
  constructors (3):
    - left: 
    - right: 
    - center: 

中文:
归纳类型 Alignment
  参数: where
  构造子 (3 个):
    - left: 
    - right: 
    - center: 
-/
inductive Alignment where
  | left
  | right
  | center
deriving Inhabited, BEq

/--
Definition of `String.justify` / `String.justify` 的定义

English:
definition String.justify
  signature: (s : String) (a : Alignment) (width : Nat)
  body: match a with
  | Alignment.left => s.rightpad width
  | Alignment.right => s.leftpad width
  | Alignment.center =>
    let pad := (width - s.length) / 2
    String.replicate pad ' ' ++ s ++ String.replicate (width - s.length - pad) ' '

中文:
定义 String.justify
  签名: (s : String) (a : Alignment) (width : 自然数)
  定义体: match a with
  | Alignment.left => s.rightpad width
  | Alignment.right => s.leftpad width
  | Alignment.center =>
    let pad := (width - s.length) / 2
    String.replicate pad ' ' ++ s ++ String.replicate (width - s.length - pad) ' '

Depends on / 依赖: Alignment, Alignment.center, Alignment.left, Alignment.right, String.replicate, center, leftpad, length, replicate, rightpad, s.leftpad, s.length, s.rightpad
-/
def String.justify (s : String) (a : Alignment) (width : Nat) : String :=
  match a with
  | Alignment.left => s.rightpad width
  | Alignment.right => s.leftpad width
  | Alignment.center =>
    let pad := (width - s.length) / 2
    String.replicate pad ' ' ++ s ++ String.replicate (width - s.length - pad) ' '

/--
Definition of `formatTable` / `formatTable` 的定义

English:
definition formatTable
  signature: (headers : Array String) (table : Array (Array String))
  body: Id.run do
  -- If no alignments are provided, default to left alignment for all columns.
  let alignments := alignments.getD (Array.replicate headers.size Alignment.left)
  -- Escape all vertical bar characters inside a table cell,
  -- otherwise these could get interpreted as starting a new row or 

中文:
定义 formatTable
  签名: (headers : Array String) (table : Array (Array String))
  定义体: Id.run do
  -- If no alignments are provided, default to left alignment for all columns.
  let alignments := alignments.getD (Array.replicate headers.size Alignment.left)
  -- Escape all vertical bar characters inside a table cell,
  -- otherwise these could get interpreted as starting a new row or 
-/
def formatTable (headers : Array String) (table : Array (Array String))
    (alignments : Option (Array Alignment) := none) :
    String := Id.run do
  -- If no alignments are provided, default to left alignment for all columns.
  let alignments := alignments.getD (Array.replicate headers.size Alignment.left)
  -- Escape all vertical bar characters inside a table cell,
  -- otherwise these could get interpreted as starting a new row or column.
  let escapedHeaders := headers.map (fun header => header.replace "|" "\\|")
  let escapedTable := table.map (fun row => row.map (fun cell => cell.replace "|" "\\|"))
  -- Compute the maximum width of each column.
  let mut widths := escapedHeaders.map (·.length)
  for row in escapedTable do
    for i in [0:widths.size] do
      widths := widths.set! i (max widths[i]! ((row[i]?.map (·.length)).getD 0))
  -- Pad each cell with spaces to match the column width.
  let paddedHeaders := escapedHeaders.mapIdx fun i h => h.rightpad widths[i]!
  let paddedTable := escapedTable.map fun row => row.mapIdx fun i cell =>
    cell.justify alignments[i]! widths[i]!
  -- Construct the lines of the table
  let headerLine := "| " ++ String.intercalate " | " (paddedHeaders.toList) ++ " |"
  -- Construct the separator line, with colons to indicate alignment
  let separatorLine :=
    "| "
    ++ String.intercalate " | "
        (((widths.zip alignments).map fun ⟨w, a⟩ =>
              match w, a with
              | 0, _ => ""
              | 1, _ => "-"
              | _ + 2, Alignment.left => ":" ++ String.replicate (w-1) '-'
              | _ + 2, Alignment.right => String.replicate (w-1) '-' ++ ":"
              | _ + 2, Alignment.center => ":" ++ String.replicate (w-2) '-' ++ ":"
              ).toList)
    ++ " |"
  let rowLines := paddedTable.map (fun row => "| " ++ String.intercalate " | " (row.toList) ++ " |")
  -- Return the table
  return String.intercalate "\n" (headerLine :: separatorLine :: rowLines.toList)
