/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Mathlib.Init
public import Lean.Message

/-!
# Utilities for analyzing `MessageData`

Utility functions for working with trace messages.

`withTraceNode` (in `Lean.Util.Trace`) stores a `TraceResult` in `TraceData.result?`
and prepends emoji to the rendered header:
- `✅️` (`checkEmoji`) for success
- `❌️` (`crossEmoji`) for failure
- `💥️` (`bombEmoji`) for exceptions

The `traceResultOf` function provides backward-compatible parsing of rendered headers.
-/

public section

namespace Lean.MessageData

/-- Determine the status of a trace node from its rendered header string.

`withTraceNode` prepends `checkEmoji`/`crossEmoji`/`bombEmoji`
(defined in `Lean.Util.Trace`) to trace headers to indicate outcomes.

The `TraceResult` will be recorded in trace messages directly in [lean4#12698](https://github.com/leanprover/lean4/pull/12698).
Once that PR is available, callers should prefer `td.result?` over calling this function. -/
@[deprecated Lean.TraceData.result? (since := "2026-03-23")]
/--
Definition of `traceResultOf` / `traceResultOf` 的定义

English:
definition traceResultOf
  signature: (headerStr : String)
  body: if headerStr.startsWith "✅️" then some .success
  else if headerStr.startsWith "❌️" then some .failure
  else if headerStr.startsWith "💥️" then some .error
  else none

中文:
定义 traceResultOf
  签名: (headerStr : String)
  定义体: if headerStr.startsWith "✅️" then some .success
  else if headerStr.startsWith "❌️" then some .failure
  else if headerStr.startsWith "💥️" then some .error
  else none

Depends on / 依赖: failure, headerStr, headerStr.startsWith, startsWith, success
-/
def traceResultOf (headerStr : String) : Option TraceResult :=
  if headerStr.startsWith "✅️" then some .success
  else if headerStr.startsWith "❌️" then some .failure
  else if headerStr.startsWith "💥️" then some .error
  else none

/-- Strip the leading status emoji and space from a trace header string,
leaving just the semantic content for comparison across trace runs.

Trace headers from `withTraceNode` have the form `"{emoji}[{VS16}] {content}"`.
This strips everything through the first space. Returns the string unchanged if
no recognized status prefix is present. -/
@[deprecated Lean.TraceData (since := "2026-03-23")]
/--
Definition of `stripTraceResultPrefix` / `stripTraceResultPrefix` 的定义

English:
definition stripTraceResultPrefix
  signature: (s : String)
  body: if (traceResultOf s).isNone then s else
.copy .dropPrefix ' ' s.toSlice.dropPrefix (!·.isWhitespace)

中文:
定义 stripTraceResultPrefix
  签名: (s : String)
  定义体: if (traceResultOf s).isNone then s else
.copy .dropPrefix ' ' s.toSlice.dropPrefix (!·.isWhitespace)

Depends on / 依赖: dropPrefix, isNone, isWhitespace, s.toSlice.dropPrefix, toSlice, traceResultOf
-/
def stripTraceResultPrefix (s : String) : String :=
  if (traceResultOf s).isNone then s else
.copy .dropPrefix ' ' s.toSlice.dropPrefix (!·.isWhitespace)

/--
Definition of `extractInstName` / `extractInstName` 的定义

English:
definition extractInstName
  signature: (s : String)
  body: match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

中文:
定义 extractInstName
  签名: (s : String)
  定义体: match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

Depends on / 依赖: name.trimAscii.toString, rest.splitOn, s.splitOn, splitOn, toString, trimAscii
-/
def extractInstName (s : String) : String :=
  match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

/--
Definition of `dedupByString` / `dedupByString` 的定义

English:
definition dedupByString
  signature: (msgs : Array MessageData)
  body: do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for msg in msgs do
    let s ← msg.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push msg
  return unique

中文:
定义 dedupByString
  签名: (msgs : Array MessageData)
  定义体: do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for msg in msgs do
    let s ← msg.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push msg
  return unique
-/
def dedupByString (msgs : Array MessageData) : BaseIO (Array MessageData) := do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for msg in msgs do
    let s ← msg.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push msg
  return unique

end Lean.MessageData

end
