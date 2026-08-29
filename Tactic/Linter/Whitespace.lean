/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# The `whitespace` linter

The `whitespace` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The `whitespace` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

In practice, this makes sure that the spacing in a typical declaration looks like
```lean
example (a : Nat) {R : Type} [Add R] : <not linted part>
```
as opposed to
```lean
example (a: Nat) {R:Type} [Add R] : <not linted part>
```
-/
public register_option linter.style.whitespace : Bool := {
  defValue := false
  descr := "enable the whitespace linter"
}

/-- Deprecated in favour of `linter.style.whitespace` -/
public register_option linter.style.commandStart : Bool := {
  defValue := false
  descr := "deprecated: use the `linter.style.whitespace` option instead"
  deprecation? := some { since := "2026-01-07", text? := "use the `linter.style.whitespace` option instead" }
}

/-- If the `linter.style.whitespace.verbose` option is `true`, the `whitespace` linter
reports some helpful diagnostic information. -/
public register_option linter.style.whitespace.verbose : Bool := {
  defValue := false
  descr := "report diagnostic information for the `whitespace` linter"
}

/--
Definition of `CommandStart.endPos` / `CommandStart.endPos` 的定义

English:
definition CommandStart.endPos
  signature: (stx : Syntax)
  body: if let some cmd := stx.find? (#[``Parser.Command.declaration, `lemma].contains ·.getKind) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some sig => sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some s => s[0].getTailPos? -- `s[0]` is the `:` separating hypotheses and the type
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Parser.Command.variable || stx.isOfKind ``Parser.Command.omit then
    stx.getTailPos?
  else none

中文:
定义 CommandStart.endPos
  签名: (stx : Syntax)
  定义体: if let some cmd := stx.find? (#[``Parser.Command.declaration, `lemma].contains ·.getKind) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some sig => sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some s => s[0].getTailPos? -- `s[0]` is the `:` separating hypotheses and the type
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Parser.Command.variable || stx.isOfKind ``Parser.Command.omit then
    stx.getTailPos?
  else none

Depends on / 依赖: Command, Parser, Parser.Comm, Parser.Command.declaration, Parser.Command.inductive, Parser.Command.optDeclSig, Parser.Term.typeSpec, cmd.find, contains, dbg_trace, declaration, getKind, getTailPos, hypotheses, ind.find, inductive, isOfKind, optDeclSig, separating, sig.getTailPos
-/
def CommandStart.endPos (stx : Syntax) : Option String.Pos.Raw :=
  if let some cmd := stx.find? (#[``Parser.Command.declaration, `lemma].contains ·.getKind) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some sig => sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some s => s[0].getTailPos? -- `s[0]` is the `:` separating hypotheses and the type
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Parser.Command.variable || stx.isOfKind ``Parser.Command.omit then
    stx.getTailPos?
  else none

-- Some of the information contained in `FormatError` is redundant, however, it is useful to convert
-- between the `String.pos` and `String` length conveniently.
/--
Definition of `FormatError` / `FormatError` 的定义

English:
structure FormatError
  parameters: where
  axioms and operations (6):
    - srcNat : Nat
    - srcEndPos : String.Pos.Raw
    - fmtPos : Nat
    - msg : String
    - length : Nat
    - srcStartPos : String.Pos.Raw

中文:
结构 FormatError
  参数: where
  公理与运算 (6 个):
    - srcNat : 自然数
    - srcEndPos : String.Pos.Raw
    - fmtPos : 自然数
    - msg : String
    - length : 自然数
    - srcStartPos : String.Pos.Raw
-/
structure FormatError where
  /-- The distance to the end of the source string, as number of characters -/
  srcNat : Nat
  /-- The distance to the end of the source string, as number of string positions -/
  srcEndPos : String.Pos.Raw
  /-- The distance to the end of the formatted string, as number of characters -/
  fmtPos : Nat
  /-- The kind of formatting error. For example: `extra space`, `remove line break` or
  `missing space`.

  Strings starting with `Oh no` indicate an internal error.
  -/
  msg : String
  /-- The length of the mismatch, as number of characters. -/
  length : Nat
  /-- The starting position of the mismatch, as a `String.pos`. -/
  srcStartPos : String.Pos.Raw
  deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString FormatError
  body: s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

中文:
实例 :
  签名: ToString FormatError
  定义体: s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

Depends on / 依赖: f.fmtPos, f.length, f.msg, f.srcEndPos, f.srcNat, fmtPos, length, srcEndPos, srcNat, srcPos
-/
instance : ToString FormatError where
  toString f :=
    s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

/--
Definition of `mkFormatError` / `mkFormatError` 的定义

English:
definition mkFormatError
  signature: (ls ms : String) (msg : String) (length : Nat := 1)
  body: ls.length
  srcEndPos := ls.rawEndPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.rawEndPos

中文:
定义 mkFormatError
  签名: (ls ms : String) (msg : String) (length : 自然数 := 1)
  定义体: ls.length
  srcEndPos := ls.rawEndPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.rawEndPos

Depends on / 依赖: FormatError
-/
def mkFormatError (ls ms : String) (msg : String) (length : Nat := 1) : FormatError where
  srcNat := ls.length
  srcEndPos := ls.rawEndPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.rawEndPos

/--
Definition of `pushFormatError` / `pushFormatError` 的定义

English:
definition pushFormatError
  signature: (fs : Array FormatError) (f : FormatError)
  body: -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind than the new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

中文:
定义 pushFormatError
  签名: (fs : 数组 FormatError) (f : FormatError)
  定义体: -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind than the new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}
-/
def pushFormatError (fs : Array FormatError) (f : FormatError) : Array FormatError :=
  -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind than the new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

/--
Scan the two input strings `L` and `M`, assuming `M` is the pretty-printed version of `L`.
This almost means that `L` and `M` only differ in whitespace.

While scanning the two strings, accumulate any discrepancies --- with some heuristics to avoid
flagging some line-breaking changes.
(The pretty-printer does not always produce desirably formatted code.)
-/
partial
/--
Definition of `parallelScanAux` / `parallelScanAux` 的定义

English:
definition parallelScanAux
  signature: (as : Array FormatError) (L M : String.Slice)
  body: Id.run do
  if M.trimAscii.isEmpty then as else
  -- We try as hard as possible to scan the strings one character at a time.
  -- However, single line comments introduced with `--` pretty-print differently than `/--`.
  -- So, we first look ahead for `/--`: the linter will later ignore doc-strings, so it does not
  -- matter too much what we do here and we simply drop `/--` from the original string and the
  -- pretty-printed one, before continuing.
  -- Next, if we already dealt with `/--`, finding a `--` means that this is a single line comment
  -- (or possibly a comment embedded in a doc-string, which is ok, since we eventually discard
  -- doc-strings). In this case, we drop everything until the following line break in the
  -- original syntax, and for the same amount of characters in the pretty-printed one, since the
  -- pretty-printer *erases* the line break at the end of a single line comment.
  if let (some newL, some newM) := (L.dropPrefix? "/--", M.dropPrefix? "/--") then
    parallelScanAux as newL newM
  else if L.startsWith "--" then
    let (pos, diff) := Id.run do
      let mut diff := 0
      for ⟨pos, h⟩ in L.positions do
        if pos.get h == '\n' then
          return (pos, diff)
        diff := diff + 1
      return (L.endPos, diff)

    let newL := L.sliceFrom pos
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as newL.trimAsciiStart newM.trimAsciiStart
  else if let some newL := L.dropPrefix? "-/" then
    let newL := newL.trimAsciiStart
.trimAsciiStart let newM := M.drop 2
    parallelScanAux as newL newM
  else
    let ls := L.drop 1
    let ms := M.drop 1
    let m := M.front
    match L.front with
    | ' ' =>
      if m.isWhitespace then
        parallelScanAux as ls ms.trimAsciiStart
      else
        parallelScanAux (pushFormatError as (mkFormatError L.copy M.copy "extra space")) ls M
    | '\n' =>
      if m.isWhitespace then
        parallelScanAux as ls.trimAsciiStart ms.trimAsciiStart
      else
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "remove line break")) ls.trimAsciiStart M
    | l => -- `l` is not whitespace
      if l == m then
        parallelScanAux as ls ms
      else if m.isWhitespace then
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "missing space")) L ms.trimAsciiStart
      else
        -- If this code is reached, then `L` and `M` differ by something other than whitespace.
        -- This should not happen in practice.
        pushFormatError as (mkFormatError ls.copy ms.copy "Oh no! (Unreachable?)")

@[inherit_doc parallelScanAux]

中文:
定义 parallelScanAux
  签名: (as : 数组 FormatError) (L M : String.Slice)
  定义体: Id.run do
  if M.trimAscii.isEmpty then as else
  -- We try as hard as possible to scan the strings one character at a time.
  -- However, single line comments introduced with `--` pretty-print differently than `/--`.
  -- So, we first look ahead for `/--`: the linter will later ignore doc-strings, so it does not
  -- matter too much what we do here and we simply drop `/--` from the original string and the
  -- pretty-printed one, before continuing.
  -- Next, if we already dealt with `/--`, finding a `--` means that this is a single line comment
  -- (or possibly a comment embedded in a doc-string, which is ok, since we eventually discard
  -- doc-strings). In this case, we drop everything until the following line break in the
  -- original syntax, and for the same amount of characters in the pretty-printed one, since the
  -- pretty-printer *erases* the line break at the end of a single line comment.
  if let (some newL, some newM) := (L.dropPrefix? "/--", M.dropPrefix? "/--") then
    parallelScanAux as newL newM
  else if L.startsWith "--" then
    let (pos, diff) := Id.run do
      let mut diff := 0
      for ⟨pos, h⟩ in L.positions do
        if pos.get h == '\n' then
          return (pos, diff)
        diff := diff + 1
      return (L.endPos, diff)

    let newL := L.sliceFrom pos
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as newL.trimAsciiStart newM.trimAsciiStart
  else if let some newL := L.dropPrefix? "-/" then
    let newL := newL.trimAsciiStart
.trimAsciiStart let newM := M.drop 2
    parallelScanAux as newL newM
  else
    let ls := L.drop 1
    let ms := M.drop 1
    let m := M.front
    match L.front with
    | ' ' =>
      if m.isWhitespace then
        parallelScanAux as ls ms.trimAsciiStart
      else
        parallelScanAux (pushFormatError as (mkFormatError L.copy M.copy "extra space")) ls M
    | '\n' =>
      if m.isWhitespace then
        parallelScanAux as ls.trimAsciiStart ms.trimAsciiStart
      else
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "remove line break")) ls.trimAsciiStart M
    | l => -- `l` is not whitespace
      if l == m then
        parallelScanAux as ls ms
      else if m.isWhitespace then
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "missing space")) L ms.trimAsciiStart
      else
        -- If this code is reached, then `L` and `M` differ by something other than whitespace.
        -- This should not happen in practice.
        pushFormatError as (mkFormatError ls.copy ms.copy "Oh no! (Unreachable?)")

@[inherit_doc parallelScanAux]

Depends on / 依赖: Id.run
-/
def parallelScanAux (as : Array FormatError) (L M : String.Slice) : Array FormatError := Id.run do
  if M.trimAscii.isEmpty then as else
  -- We try as hard as possible to scan the strings one character at a time.
  -- However, single line comments introduced with `--` pretty-print differently than `/--`.
  -- So, we first look ahead for `/--`: the linter will later ignore doc-strings, so it does not
  -- matter too much what we do here and we simply drop `/--` from the original string and the
  -- pretty-printed one, before continuing.
  -- Next, if we already dealt with `/--`, finding a `--` means that this is a single line comment
  -- (or possibly a comment embedded in a doc-string, which is ok, since we eventually discard
  -- doc-strings). In this case, we drop everything until the following line break in the
  -- original syntax, and for the same amount of characters in the pretty-printed one, since the
  -- pretty-printer *erases* the line break at the end of a single line comment.
  if let (some newL, some newM) := (L.dropPrefix? "/--", M.dropPrefix? "/--") then
    parallelScanAux as newL newM
  else if L.startsWith "--" then
    let (pos, diff) := Id.run do
      let mut diff := 0
      for ⟨pos, h⟩ in L.positions do
        if pos.get h == '\n' then
          return (pos, diff)
        diff := diff + 1
      return (L.endPos, diff)

    let newL := L.sliceFrom pos
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as newL.trimAsciiStart newM.trimAsciiStart
  else if let some newL := L.dropPrefix? "-/" then
    let newL := newL.trimAsciiStart
.trimAsciiStart let newM := M.drop 2
    parallelScanAux as newL newM
  else
    let ls := L.drop 1
    let ms := M.drop 1
    let m := M.front
    match L.front with
    | ' ' =>
      if m.isWhitespace then
        parallelScanAux as ls ms.trimAsciiStart
      else
        parallelScanAux (pushFormatError as (mkFormatError L.copy M.copy "extra space")) ls M
    | '\n' =>
      if m.isWhitespace then
        parallelScanAux as ls.trimAsciiStart ms.trimAsciiStart
      else
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "remove line break")) ls.trimAsciiStart M
    | l => -- `l` is not whitespace
      if l == m then
        parallelScanAux as ls ms
      else if m.isWhitespace then
        parallelScanAux
          (pushFormatError as (mkFormatError L.copy M.copy "missing space")) L ms.trimAsciiStart
      else
        -- If this code is reached, then `L` and `M` differ by something other than whitespace.
        -- This should not happen in practice.
        pushFormatError as (mkFormatError ls.copy ms.copy "Oh no! (Unreachable?)")

@[inherit_doc parallelScanAux]
/--
Definition of `parallelScan` / `parallelScan` 的定义

English:
definition parallelScan
  signature: (src fmt : String)
  body: parallelScanAux ∅ src fmt

中文:
定义 parallelScan
  签名: (src fmt : String)
  定义体: parallelScanAux ∅ src fmt

Depends on / 依赖: parallelScanAux
-/
def parallelScan (src fmt : String) : Array FormatError :=
  parallelScanAux ∅ src fmt

namespace Style.Whitespace

/--
Definition of `unlintedNodes` / `unlintedNodes` 的定义

English:
abbreviation unlintedNodes
  body: #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- set builder notation, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- The pretty-printer adds a space between the backticks and the actual name.
  ``Parser.Term.doubleQuotedName,
  ]

中文:
缩写 unlintedNodes
  定义体: #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- set builder notation, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- The pretty-printer adds a space between the backticks and the actual name.
  ``Parser.Term.doubleQuotedName,
  ]
-/
abbrev unlintedNodes := #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- set builder notation, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- The pretty-printer adds a space between the backticks and the actual name.
  ``Parser.Term.doubleQuotedName,
  ]

/--
Definition of `getUnlintedRanges` / `getUnlintedRanges` 的定义

English:
definition getUnlintedRanges
  signature: (a : Array SyntaxNodeKind)
  body: args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      new.insert (s.getRange?.getD default)
    else
      new
  -- We special case `where` statements, since they may be followed by an indented doc-string.
  | curr, .atom info "where" =>
    if let some trail := info.getRangeWithTrailing? then
      curr.insert trail
    else
      curr
  | curr, _ => curr

中文:
定义 getUnlintedRanges
  签名: (a : 数组 SyntaxNodeKind)
  定义体: args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      new.insert (s.getRange?.getD default)
    else
      new
  -- We special case `where` statements, since they may be followed by an indented doc-string.
  | curr, .atom info "where" =>
    if let some trail := info.getRangeWithTrailing? then
      curr.insert trail
    else
      curr
  | curr, _ => curr

Depends on / 依赖: args.foldl, getUnlintedRanges
-/
def getUnlintedRanges (a : Array SyntaxNodeKind) :
    Std.HashSet Lean.Syntax.Range -> Syntax -> Std.HashSet Lean.Syntax.Range
  | curr, s@(.node _ kind args) =>
    let new := args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      new.insert (s.getRange?.getD default)
    else
      new
  -- We special case `where` statements, since they may be followed by an indented doc-string.
  | curr, .atom info "where" =>
    if let some trail := info.getRangeWithTrailing? then
      curr.insert trail
    else
      curr
  | curr, _ => curr

/--
Definition of `isOutside` / `isOutside` 的定义

English:
definition isOutside
  signature: (rgs : Std.HashSet Lean.Syntax.Range) (rg : Lean.Syntax.Range)
  body: rgs.all fun {start := a, stop := b} => !(a <= rg.start && rg.stop <= b)

中文:
定义 isOutside
  签名: (rgs : Std.HashSet Lean.Syntax.值域) (rg : Lean.Syntax.值域)
  定义体: rgs.all fun {start := a, stop := b} => !(a <= rg.start && rg.stop <= b)

Depends on / 依赖: rg.start, rg.stop, rgs.all
-/
def isOutside (rgs : Std.HashSet Lean.Syntax.Range) (rg : Lean.Syntax.Range) : Bool :=
  rgs.all fun {start := a, stop := b} => !(a <= rg.start && rg.stop <= b)

/-- `mkWindow orig start ctx` extracts from `orig` a string that starts at the first
non-whitespace character before `start`, then expands to cover `ctx` more characters
and continues still until the first non-whitespace character.

In essence, it extracts the substring of `orig` that begins at `start`, continues for `ctx`
characters plus expands left and right until it encounters the first whitespace character,
to avoid cutting into "words".

*Note*. `start` is the number of characters *from the right* where our focus is!
-/
public def mkWindow (orig : String) (start ctx : Nat) : String :=
  let head := orig.dropEnd (start + 1) -- `orig`, up to one character before the discrepancy
  let middle := orig.takeEnd (start + 1)
  let headCtx := head.takeEndWhile (!·.isWhitespace)
.takeWhile (!·.isWhitespace) let tail := middle.drop ctx
  s!"{headCtx}{middle.take ctx}{tail}"

@[inherit_doc Mathlib.Linter.linter.style.whitespace]
/--
Definition of `whitespaceLinter` / `whitespaceLinter` 的定义

English:
definition whitespaceLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.whitespace (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
.isSome then if stx.find? (·.isOfKind ``runCmd)
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart != 0 then
      Linter.logLint linter.style.whitespace stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
.isSome then if stx.find? (·.isOfKind `Lean.Parser.Command.macro_rules)
    return
  let some upTo := CommandStart.endPos stx | return

  let fmt : Option Format ←
      try
liftCoreM some < > PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.whitespace.verbose (stx.getHead?.getD stx)
          m!"The `whitespace` linter had some parsing issues: \
            feel free to silence it and report this error!"
        pure none
  if let some fmt := fmt then
    let st := fmt.pretty
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString

    let scan := parallelScan orig st

.getD default let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment)
.getD default let docStringEnd := docStringEnd.getTailPos?
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    for s in scan do
      let center := origSubstring.stopPos.unoffsetBy s.srcEndPos
      let rg : Lean.Syntax.Range :=
.increaseBy 1⟩ .unoffsetBy s.srcStartPos .offsetBy s.srcEndPos ⟨center, center
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      unless isOutside forbidden rg do
        continue
      unless rg.stop <= upTo do return
      unless docStringEnd <= rg.start do return

      let ctx := 4 -- the number of characters after the mismatch that linter prints
      let srcWindow := mkWindow orig s.srcNat (ctx + s.length)
      let expectedWindow := mkWindow st s.fmtPos (ctx + (1))
      Linter.logLint linter.style.whitespace (.ofRange rg)
        m!"{s.msg} in the source\n\n\
          This part of the code\n '{srcWindow}'\n\
          should be written as\n '{expectedWindow}'\n"
      Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"

中文:
定义 whitespaceLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.whitespace (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
.isSome then if stx.find? (·.isOfKind ``runCmd)
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart != 0 then
      Linter.logLint linter.style.whitespace stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
.isSome then if stx.find? (·.isOfKind `Lean.Parser.Command.macro_rules)
    return
  let some upTo := CommandStart.endPos stx | return

  let fmt : Option Format ←
      try
liftCoreM some < > PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.whitespace.verbose (stx.getHead?.getD stx)
          m!"The `whitespace` linter had some parsing issues: \
            feel free to silence it and report this error!"
        pure none
  if let some fmt := fmt then
    let st := fmt.pretty
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString

    let scan := parallelScan orig st

.getD default let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment)
.getD default let docStringEnd := docStringEnd.getTailPos?
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    for s in scan do
      let center := origSubstring.stopPos.unoffsetBy s.srcEndPos
      let rg : Lean.Syntax.Range :=
.increaseBy 1⟩ .unoffsetBy s.srcStartPos .offsetBy s.srcEndPos ⟨center, center
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      unless isOutside forbidden rg do
        continue
      unless rg.stop <= upTo do return
      unless docStringEnd <= rg.start do return

      let ctx := 4 -- the number of characters after the mismatch that linter prints
      let srcWindow := mkWindow orig s.srcNat (ctx + s.length)
      let expectedWindow := mkWindow st s.fmtPos (ctx + (1))
      Linter.logLint linter.style.whitespace (.ofRange rg)
        m!"{s.msg} in the source\n\n\
          This part of the code\n '{srcWindow}'\n\
          should be written as\n '{expectedWindow}'\n"
      Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"

Depends on / 依赖: withSetOptionIn
-/
def whitespaceLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.whitespace (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
.isSome then if stx.find? (·.isOfKind ``runCmd)
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart != 0 then
      Linter.logLint linter.style.whitespace stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
.isSome then if stx.find? (·.isOfKind `Lean.Parser.Command.macro_rules)
    return
  let some upTo := CommandStart.endPos stx | return

  let fmt : Option Format ←
      try
liftCoreM some < > PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.whitespace.verbose (stx.getHead?.getD stx)
          m!"The `whitespace` linter had some parsing issues: \
            feel free to silence it and report this error!"
        pure none
  if let some fmt := fmt then
    let st := fmt.pretty
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString

    let scan := parallelScan orig st

.getD default let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment)
.getD default let docStringEnd := docStringEnd.getTailPos?
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    for s in scan do
      let center := origSubstring.stopPos.unoffsetBy s.srcEndPos
      let rg : Lean.Syntax.Range :=
.increaseBy 1⟩ .unoffsetBy s.srcStartPos .offsetBy s.srcEndPos ⟨center, center
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      unless isOutside forbidden rg do
        continue
      unless rg.stop <= upTo do return
      unless docStringEnd <= rg.start do return

      let ctx := 4 -- the number of characters after the mismatch that linter prints
      let srcWindow := mkWindow orig s.srcNat (ctx + s.length)
      let expectedWindow := mkWindow st s.fmtPos (ctx + (1))
      Linter.logLint linter.style.whitespace (.ofRange rg)
        m!"{s.msg} in the source\n\n\
          This part of the code\n '{srcWindow}'\n\
          should be written as\n '{expectedWindow}'\n"
      Linter.logLintIf linter.style.whitespace.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"

initialize addLinter whitespaceLinter

end Style.Whitespace

end Mathlib.Linter
