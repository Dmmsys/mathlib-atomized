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

/-- Possible alignment modes for each table item: left-aligned, right-aligned and centered. -/
/-
**Alignment** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Possible alignment modes for each table item: left-aligned, right-aligned and ce
ntered.
-/
inductive Alignment where
  | left
  | right
  | center
deriving Inhabited, BEq

/-- Align a `String` `s` to the left, right, or center within a field of width `width`. -/
/-
**String.justify** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：String.justify (s : String) (a : Alignment) (width : Nat) : String
参数：s : String；a : Alignment；width : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Align a `String` `s` to the left, right, or center within a field of width `widt
h`.
-/
def String.justify (s : String) (a : Alignment) (width : Nat) : String :=
  match a with
  | Alignment.left => s.rightpad width
  | Alignment.right => s.leftpad width
  | Alignment.center =>
    let pad := (width - s.length) / 2
    String.replicate pad ' ' ++ s ++ String.replicate (width - s.length - pad) ' '

/--
Render a two-dimensional array of `String`s into a markdown-compliant table.
`headers` is a list of column headers,
`table` is a 2D array of cell contents,
`alignments` describes how to align each table column (default: left-aligned). -/
/-
**formatTable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：formatTable (headers : Array String) (table : Array (Array String)) (align
ments : Option (Array Alignment)
参数：headers : Array String；table : Array (Array String)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Render a two-dimensional array of `String`s into a markdown-compliant table.
`headers` is a list of column headers,
`table` is a 2D array of cell contents,
`alignments` describes how to align each table column (default: left-aligned).
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
