/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# The "ppRoundtrip" linter

The "ppRoundtrip" linter emits a warning when the syntax of a command differs substantially
from the pretty-printed version of itself.
-/

meta section
open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The "ppRoundtrip" linter emits a warning when the syntax of a command differs substantially
from the pretty-printed version of itself.

The linter makes an effort to start the highlighting at the first difference.
However, it may not always be successful.
It also prints both the source code and the "expected code" in a 5-character radius from
the first difference.
-/
public register_option linter.ppRoundtrip : Bool := {
  defValue := false
  descr := "enable the ppRoundtrip linter"
}

/--
Definition of `polishPP` / `polishPP` 的定义

English:
definition polishPP
  signature: (s : String)
  body: let s := s.splitToList (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
.replace " /-!" "/-! "
    |>.replace "``` " "``` " -- avoid losing an existing space after the triple back-ticks
                              -- as a consequence of the following replacement
    |>.replace "`` " "`

中文:
定义 polishPP
  签名: (s : String)
  定义体: let s := s.splitToList (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
.replace " /-!" "/-! "
    |>.replace "``` " "``` " -- avoid losing an existing space after the triple back-ticks
                              -- as a consequence of the following replacement
    |>.replace "`` " "`

Depends on / 依赖: existing, filter, intercalate, isEmpty, isWhitespace, losing, replace, s.filter, s.splitToList, splitToList, triple
-/
def polishPP (s : String) : String :=
  let s := s.splitToList (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
.replace " /-!" "/-! "
    |>.replace "``` " "``` " -- avoid losing an existing space after the triple back-ticks
                              -- as a consequence of the following replacement
    |>.replace "`` " "``" -- weird pp ```#eval ``«Nat»``` pretty-prints as ```#eval `` «Nat»```
    |>.replace "notation3(" "notation3 ("
    |>.replace "notation3\"" "notation3 \""

/--
Definition of `polishSource` / `polishSource` 的定义

English:
definition polishSource
  signature: (s : String)
  body: let split := s.splitToList (· == '\n')
  let preWS := split.foldl (init := #[]) fun p q =>
    let txt := q.trimAsciiStart.copy.length
    (p.push (q.length - txt)).push txt
  let preWS := preWS.eraseIdxIfInBounds 0
  let s := (split.map String.trimAsciiStart).filter (· != "".toSlice)
  (" ".toSlice

中文:
定义 polishSource
  签名: (s : String)
  定义体: let split := s.splitToList (· == '\n')
  let preWS := split.foldl (init := #[]) fun p q =>
    let txt := q.trimAsciiStart.copy.length
    (p.push (q.length - txt)).push txt
  let preWS := preWS.eraseIdxIfInBounds 0
  let s := (split.map String.trimAsciiStart).filter (· != "".toSlice)
  (" ".toSlice

Depends on / 依赖: String.trimAsciiStart, eraseIdxIfInBounds, filter, intercalate, isEmpty, length, p.push, preWS.eraseIdxIfInBounds, q.length, q.trimAsciiStart.copy.length, s.filter, s.splitToList, split.foldl, split.map, splitToList, toSlice, toSlice.intercalate, trimAsciiStart
-/
def polishSource (s : String) : String × Array Nat :=
  let split := s.splitToList (· == '\n')
  let preWS := split.foldl (init := #[]) fun p q =>
    let txt := q.trimAsciiStart.copy.length
    (p.push (q.length - txt)).push txt
  let preWS := preWS.eraseIdxIfInBounds 0
  let s := (split.map String.trimAsciiStart).filter (· != "".toSlice)
  (" ".toSlice.intercalate (s.filter (!·.isEmpty)), preWS)

/--
Definition of `posToShiftedPos` / `posToShiftedPos` 的定义

English:
definition posToShiftedPos
  signature: (lths : Array Nat) (diff : Nat)
  body: Id.run do
  let mut (ws, noWS) := (diff, 0)
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws

中文:
定义 posToShiftedPos
  签名: (lths : Array 自然数) (diff : 自然数)
  定义体: Id.run do
  let mut (ws, noWS) := (diff, 0)
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws

Depends on / 依赖: Id.run
-/
def posToShiftedPos (lths : Array Nat) (diff : Nat) : Nat := Id.run do
  let mut (ws, noWS) := (diff, 0)
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws

/--
Definition of `zoomString` / `zoomString` 的定义

English:
definition zoomString
  signature: (str : String) (centre offset : Nat)
  body: { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }

中文:
定义 zoomString
  签名: (str : String) (centre offset : 自然数)
  定义体: { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }

Depends on / 依赖: centre, offset, startPos, stopPos
-/
def zoomString (str : String) (centre offset : Nat) : Substring.Raw :=
  { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }

/--
Definition of `capSourceInfo` / `capSourceInfo` 的定义

English:
definition capSourceInfo
  signature: (s : SourceInfo) (p : Nat)
  body: match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s

中文:
定义 capSourceInfo
  签名: (s : SourceInfo) (p : 自然数)
  定义体: match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s

Depends on / 依赖: canonical, endPos, leading, original, stopPos, synthetic, trailing
-/
def capSourceInfo (s : SourceInfo) (p : Nat) : SourceInfo :=
  match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s

/-- `capSyntax stx p` applies `capSourceInfo · s` to all `SourceInfo`s in all
`node`s, `atom`s and `ident`s contained in `stx`.

This is used to trim away all "fluff" that follows a command: comments and whitespace after
a command get removed with `capSyntax stx stx.getTailPos?.get!`.
-/
partial
/--
Definition of `capSyntax` / `capSyntax` 的定义

English:
definition capSyntax
  signature: (stx : Syntax) (p : Nat)
  body: match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p).copy
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s

中文:
定义 capSyntax
  签名: (stx : Syntax) (p : 自然数)
  定义体: match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p).copy
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s

Depends on / 依赖: args.map, capSourceInfo, capSyntax, r.stopPos, stopPos, val.take
-/
def capSyntax (stx : Syntax) (p : Nat) : Syntax :=
  match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p).copy
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s

namespace PPRoundtrip

@[inherit_doc Mathlib.Linter.linter.ppRoundtrip]
/--
Definition of `ppRoundtrip` / `ppRoundtrip` 的定义

English:
definition ppRoundtrip
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
    unless getLinterValue linter.ppRoundtrip (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let stx := capSyntax stx (stx.getTailPos?.getD default).1
    let origSubstring := stx.getSubstring?.getD default
    let

中文:
定义 ppRoundtrip
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
    unless getLinterValue linter.ppRoundtrip (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let stx := capSyntax stx (stx.getTailPos?.getD default).1
    let origSubstring := stx.getSubstring?.getD default
    let

Depends on / 依赖: withSetOptionIn
-/
def ppRoundtrip : Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.ppRoundtrip (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let stx := capSyntax stx (stx.getTailPos?.getD default).1
    let origSubstring := stx.getSubstring?.getD default
    let (real, lths) := polishSource origSubstring.toString
    let fmt ← (liftCoreM do PrettyPrinter.ppCategory `command stx <|> (do
      Linter.logLint linter.ppRoundtrip stx
        m!"The ppRoundtrip linter had some parsing issues: \
           feel free to silence it with `set_option linter.ppRoundtrip false in` \
           and report this error!"
      return real))
    let st := polishPP fmt.pretty
    if st != real then
      let diff := real.firstDiffPos st
      let pos := posToShiftedPos lths diff.1 + origSubstring.startPos.1
      let f := origSubstring.str.drop (pos)
      let extraLth := (f.takeWhile (· != diff.get st)).copy.length
      let srcCtxt := zoomString real diff.1 5
      let ppCtxt := zoomString st diff.1 5
      Linter.logLint linter.ppRoundtrip (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
        m!"source context\n'{srcCtxt}'\n'{ppCtxt}'\npretty-printed context"

initialize addLinter ppRoundtrip

end Mathlib.Linter.PPRoundtrip
