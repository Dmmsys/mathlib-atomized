/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# A parser for superscripts and subscripts

This is intended for use in local notations. Basic usage is:
```
local syntax:arg term:max superscript(term) : term
local macro_rules | `($a:term $b:superscript) => `($a ^ $b)
```
where `superscript(term)` indicates that it will parse a superscript, and the `$b:superscript`
antiquotation binds the `term` argument of the superscript. Given a notation like this,
the expression `2⁶⁴` parses and expands to `2 ^ 64`.

The superscript body is considered to be the longest contiguous sequence of superscript tokens and
whitespace, so no additional bracketing is required (unless you want to separate two superscripts).
However, note that Unicode has a rather restricted character set for superscripts and subscripts
(see `Mapping.superscript` and `Mapping.subscript` in this file), so you should not use this
parser for complex expressions.
-/

public meta section

universe u

namespace Mathlib.Tactic

open Lean Parser PrettyPrinter Delaborator Std

namespace Superscript

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Hashable Char
  body: ⟨fun c => hash c.1⟩

中文:
实例 :
  签名: Hashable Char
  定义体: ⟨fun c => hash c.1⟩
-/
instance : Hashable Char := ⟨fun c => hash c.1⟩

/--
Definition of `Mapping` / `Mapping` 的定义

English:
structure Mapping
  parameters: where
  axioms and operations (2):
    - toNormal : Std.HashMap Char Char  [default: {}]
    - toSpecial : Std.HashMap Char Char  [default: {}]

中文:
结构 Mapping
  参数: where
  公理与运算 (2 个):
    - toNormal : Std.HashMap Char Char  [默认: {}]
    - toSpecial : Std.HashMap Char Char  [默认: {}]
-/
structure Mapping where
  /-- Map from "special" (e.g. superscript) characters to "normal" characters. -/
  toNormal : Std.HashMap Char Char := {}
  /-- Map from "normal" text to "special" (e.g. superscript) characters. -/
  toSpecial : Std.HashMap Char Char := {}
  deriving Inhabited

/--
Definition of `mkMapping` / `mkMapping` 的定义

English:
definition mkMapping
  signature: (s₁ s₂ : String)
  body: Id.run do
  let mut toNormal := {}
  let mut toSpecial := {}
  assert! s₁.length == s₂.length
  for sp in s₁.toRawSubstring, nm in s₂ do
    assert! !toNormal.contains sp
    assert! !toSpecial.contains nm
    toNormal := toNormal.insert sp nm
    toSpecial := toSpecial.insert nm sp
  pure { toNormal, toSpecial }

中文:
定义 mkMapping
  签名: (s₁ s₂ : String)
  定义体: Id.run do
  let mut toNormal := {}
  let mut toSpecial := {}
  assert! s₁.length == s₂.length
  for sp in s₁.toRawSubstring, nm in s₂ do
    assert! !toNormal.contains sp
    assert! !toSpecial.contains nm
    toNormal := toNormal.insert sp nm
    toSpecial := toSpecial.insert nm sp
  pure { toNormal, toSpecial }

Depends on / 依赖: Id.run
-/
def mkMapping (s₁ s₂ : String) : Mapping := Id.run do
  let mut toNormal := {}
  let mut toSpecial := {}
  assert! s₁.length == s₂.length
  for sp in s₁.toRawSubstring, nm in s₂ do
    assert! !toNormal.contains sp
    assert! !toSpecial.contains nm
    toNormal := toNormal.insert sp nm
    toSpecial := toSpecial.insert nm sp
  pure { toNormal, toSpecial }

/--
Definition of `Mapping.superscript` / `Mapping.superscript` 的定义

English:
definition Mapping.superscript
  body: mkMapping
  "⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾"
  "0123456789abcdefghijklmnopqrstuvwxyzABDEGHIJKLMNOPQRTUVWβγδεθιυφχ+-=()"

中文:
定义 Mapping.superscript
  定义体: mkMapping
  "⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾"
  "0123456789abcdefghijklmnopqrstuvwxyzABDEGHIJKLMNOPQRTUVWβγδεθιυφχ+-=()"

Depends on / 依赖: mkMapping
-/
def Mapping.superscript := mkMapping
  "⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾"
  "0123456789abcdefghijklmnopqrstuvwxyzABDEGHIJKLMNOPQRTUVWβγδεθιυφχ+-=()"

/--
Definition of `Mapping.subscript` / `Mapping.subscript` 的定义

English:
definition Mapping.subscript
  body: mkMapping
  "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎"
  "0123456789aehijklmnoprstuvxABCDEFGHIJKLMNOPQRSTUVWYZβγρφχ+-=()"

中文:
定义 Mapping.subscript
  定义体: mkMapping
  "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎"
  "0123456789aehijklmnoprstuvxABCDEFGHIJKLMNOPQRSTUVWYZβγρφχ+-=()"

Depends on / 依赖: mkMapping
-/
def Mapping.subscript := mkMapping
  "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎"
  "0123456789aehijklmnoprstuvxABCDEFGHIJKLMNOPQRSTUVWYZβγρφχ+-=()"

/--
Definition of `satisfyTokensFn` / `satisfyTokensFn` 的定义

English:
definition satisfyTokensFn
  signature: (p : Char -> Bool) (errorMsg : String) (many := true)
  body: fun c s =>
  let start := s.pos
  let s := takeWhile1Fn p errorMsg c s
  if s.hasError then s else
  let stop := s.pos
  let s := whitespace c s
  let toks := #[(start, stop, s.pos)]
  if many then
    let rec /-- Loop body of `satisfyTokensFn` -/
    loop (toks) (s : ParserState) : ParserState :=
      let start := s.pos
      let s := takeWhileFn p c s
      if s.pos == start then k toks s else
        let stop := s.pos
        let s := whitespace c s
        let toks := toks.push (start, stop, s.pos)
        loop toks s
    loop toks s
  else k toks s

中文:
定义 satisfyTokensFn
  签名: (p : Char -> 布尔值) (errorMsg : String) (many := true)
  定义体: fun c s =>
  let start := s.pos
  let s := takeWhile1Fn p errorMsg c s
  if s.hasError then s else
  let stop := s.pos
  let s := whitespace c s
  let toks := #[(start, stop, s.pos)]
  if many then
    let rec /-- Loop body of `satisfyTokensFn` -/
    loop (toks) (s : ParserState) : ParserState :=
      let start := s.pos
      let s := takeWhileFn p c s
      if s.pos == start then k toks s else
        let stop := s.pos
        let s := whitespace c s
        let toks := toks.push (start, stop, s.pos)
        loop toks s
    loop toks s
  else k toks s
-/
partial def satisfyTokensFn (p : Char -> Bool) (errorMsg : String) (many := true)
    (k : Array (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) -> ParserState -> ParserState) :
    ParserFn := fun c s =>
  let start := s.pos
  let s := takeWhile1Fn p errorMsg c s
  if s.hasError then s else
  let stop := s.pos
  let s := whitespace c s
  let toks := #[(start, stop, s.pos)]
  if many then
    let rec /-- Loop body of `satisfyTokensFn` -/
    loop (toks) (s : ParserState) : ParserState :=
      let start := s.pos
      let s := takeWhileFn p c s
      if s.pos == start then k toks s else
        let stop := s.pos
        let s := whitespace c s
        let toks := toks.push (start, stop, s.pos)
        loop toks s
    loop toks s
  else k toks s

variable {α : Type u} [Inhabited α] (as : Array α) (leftOfPartition : α -> Bool) in
/-- Given a predicate `leftOfPartition` which is true for indexes `< i` and false for `≥ i`,
returns `i`, by binary search. -/
@[specialize]
/--
Definition of `partitionPoint` / `partitionPoint` 的定义

English:
definition partitionPoint
  signature: (lo := 0) (hi := as.size)
  body: if lo < hi then
    let m := (lo + hi)/2
    let a := as[m]!
    if leftOfPartition a then
      partitionPoint (m+1) hi
    else
      partitionPoint lo m
  else lo

中文:
定义 partitionPoint
  签名: (lo := 0) (hi := as.size)
  定义体: if lo < hi then
    let m := (lo + hi)/2
    let a := as[m]!
    if leftOfPartition a then
      partitionPoint (m+1) hi
    else
      partitionPoint lo m
  else lo

Depends on / 依赖: as.size
-/
def partitionPoint (lo := 0) (hi := as.size) : Nat :=
  if lo < hi then
    let m := (lo + hi)/2
    let a := as[m]!
    if leftOfPartition a then
      partitionPoint (m+1) hi
    else
      partitionPoint lo m
  else lo

/--
Definition of `scriptFnNoAntiquot` / `scriptFnNoAntiquot` 的定义

English:
definition scriptFnNoAntiquot
  signature: (m : Mapping) (errorMsg : String) (p : ParserFn)
  body: fun c s =>
  let start := s.pos
  satisfyTokensFn m.toNormal.contains errorMsg many c s (k := fun toks s => Id.run do
    let mut newStr := ""
    -- This consists of a sorted array of `(from, to)` pairs, where indexes `from+i` in `newStr`
    -- such that `from+i < from'` for the next element of the array, are mapped to `to+i`.
    let mut aligns := #[((0 : String.Pos.Raw), start)]
    for (start, stopTk, stopWs) in toks do
      let mut pos := start
      while pos < stopTk do
        let ch := c.get pos
        let ch' := m.toNormal[ch]!
        newStr := newStr.push ch'
        pos := pos + ch
        if ch.utf8Size != ch'.utf8Size then
          aligns := aligns.push (newStr.rawEndPos, pos)
      newStr := newStr.push ' '
      if stopWs.1 - stopTk.1 != 1 then
        aligns := aligns.push (newStr.rawEndPos, stopWs)
    let ictx := mkInputContext newStr "<superscript>"
    let s' := p.run ictx c.toParserModuleContext c.tokens (mkParserState newStr)
    let rec /-- Applies the alignment mapping to a position. -/
    align (pos : String.Pos.Raw) :=
      let i := partitionPoint aligns (·.1 <= pos)
      let (a, b) := aligns[i - 1]!
.offsetBy b pos.unoffsetBy a
    let s := { s with pos := align s'.pos, errorMsg := s'.errorMsg }
    if s.hasError then return s
    let rec
    /-- Applies the alignment mapping to a `Substring`. -/
    alignSubstr : Substring.Raw -> Substring.Raw
      | ⟨_newStr, start, stop⟩ => c.substring (align start) (align stop),
    /-- Applies the alignment mapping to a `SourceInfo`. -/
    alignInfo : SourceInfo -> SourceInfo
      | .original leading pos trailing endPos =>
        -- Marking these as original breaks semantic highlighting,
        -- marking them as canonical breaks the unused variables linter. :(
        .original (alignSubstr leading) (align pos) (alignSubstr trailing) (align endPos)
      | .synthetic pos endPos canonical =>
        .synthetic (align pos) (align endPos) canonical
      | .none => .none,
     /-- Applies the alignment mapping to a `Syntax`. -/
     alignSyntax : Syntax -> Syntax
      | .missing => .missing
      | .node info kind args => .node (alignInfo info) kind (args.map alignSyntax)
      | .atom info val =>
        -- We have to preserve the unsubscripted `val` even though it breaks `Syntax.reprint`
        -- because basic parsers like `num` read the `val` directly
        .atom (alignInfo info) val
      | .ident info rawVal val preresolved =>
        .ident (alignInfo info) (alignSubstr rawVal) val preresolved
    s.pushSyntax (alignSyntax s'.stxStack.back)
  )

中文:
定义 scriptFnNoAntiquot
  签名: (m : Mapping) (errorMsg : String) (p : ParserFn)
  定义体: fun c s =>
  let start := s.pos
  satisfyTokensFn m.toNormal.contains errorMsg many c s (k := fun toks s => Id.run do
    let mut newStr := ""
    -- This consists of a sorted array of `(from, to)` pairs, where indexes `from+i` in `newStr`
    -- such that `from+i < from'` for the next element of the array, are mapped to `to+i`.
    let mut aligns := #[((0 : String.Pos.Raw), start)]
    for (start, stopTk, stopWs) in toks do
      let mut pos := start
      while pos < stopTk do
        let ch := c.get pos
        let ch' := m.toNormal[ch]!
        newStr := newStr.push ch'
        pos := pos + ch
        if ch.utf8Size != ch'.utf8Size then
          aligns := aligns.push (newStr.rawEndPos, pos)
      newStr := newStr.push ' '
      if stopWs.1 - stopTk.1 != 1 then
        aligns := aligns.push (newStr.rawEndPos, stopWs)
    let ictx := mkInputContext newStr "<superscript>"
    let s' := p.run ictx c.toParserModuleContext c.tokens (mkParserState newStr)
    let rec /-- Applies the alignment mapping to a position. -/
    align (pos : String.Pos.Raw) :=
      let i := partitionPoint aligns (·.1 <= pos)
      let (a, b) := aligns[i - 1]!
.offsetBy b pos.unoffsetBy a
    let s := { s with pos := align s'.pos, errorMsg := s'.errorMsg }
    if s.hasError then return s
    let rec
    /-- Applies the alignment mapping to a `Substring`. -/
    alignSubstr : Substring.Raw -> Substring.Raw
      | ⟨_newStr, start, stop⟩ => c.substring (align start) (align stop),
    /-- Applies the alignment mapping to a `SourceInfo`. -/
    alignInfo : SourceInfo -> SourceInfo
      | .original leading pos trailing endPos =>
        -- Marking these as original breaks semantic highlighting,
        -- marking them as canonical breaks the unused variables linter. :(
        .original (alignSubstr leading) (align pos) (alignSubstr trailing) (align endPos)
      | .synthetic pos endPos canonical =>
        .synthetic (align pos) (align endPos) canonical
      | .none => .none,
     /-- Applies the alignment mapping to a `Syntax`. -/
     alignSyntax : Syntax -> Syntax
      | .missing => .missing
      | .node info kind args => .node (alignInfo info) kind (args.map alignSyntax)
      | .atom info val =>
        -- We have to preserve the unsubscripted `val` even though it breaks `Syntax.reprint`
        -- because basic parsers like `num` read the `val` directly
        .atom (alignInfo info) val
      | .ident info rawVal val preresolved =>
        .ident (alignInfo info) (alignSubstr rawVal) val preresolved
    s.pushSyntax (alignSyntax s'.stxStack.back)
  )
-/
partial def scriptFnNoAntiquot (m : Mapping) (errorMsg : String) (p : ParserFn)
    (many := true) : ParserFn := fun c s =>
  let start := s.pos
  satisfyTokensFn m.toNormal.contains errorMsg many c s (k := fun toks s => Id.run do
    let mut newStr := ""
    -- This consists of a sorted array of `(from, to)` pairs, where indexes `from+i` in `newStr`
    -- such that `from+i < from'` for the next element of the array, are mapped to `to+i`.
    let mut aligns := #[((0 : String.Pos.Raw), start)]
    for (start, stopTk, stopWs) in toks do
      let mut pos := start
      while pos < stopTk do
        let ch := c.get pos
        let ch' := m.toNormal[ch]!
        newStr := newStr.push ch'
        pos := pos + ch
        if ch.utf8Size != ch'.utf8Size then
          aligns := aligns.push (newStr.rawEndPos, pos)
      newStr := newStr.push ' '
      if stopWs.1 - stopTk.1 != 1 then
        aligns := aligns.push (newStr.rawEndPos, stopWs)
    let ictx := mkInputContext newStr "<superscript>"
    let s' := p.run ictx c.toParserModuleContext c.tokens (mkParserState newStr)
    let rec /-- Applies the alignment mapping to a position. -/
    align (pos : String.Pos.Raw) :=
      let i := partitionPoint aligns (·.1 <= pos)
      let (a, b) := aligns[i - 1]!
.offsetBy b pos.unoffsetBy a
    let s := { s with pos := align s'.pos, errorMsg := s'.errorMsg }
    if s.hasError then return s
    let rec
    /-- Applies the alignment mapping to a `Substring`. -/
    alignSubstr : Substring.Raw -> Substring.Raw
      | ⟨_newStr, start, stop⟩ => c.substring (align start) (align stop),
    /-- Applies the alignment mapping to a `SourceInfo`. -/
    alignInfo : SourceInfo -> SourceInfo
      | .original leading pos trailing endPos =>
        -- Marking these as original breaks semantic highlighting,
        -- marking them as canonical breaks the unused variables linter. :(
        .original (alignSubstr leading) (align pos) (alignSubstr trailing) (align endPos)
      | .synthetic pos endPos canonical =>
        .synthetic (align pos) (align endPos) canonical
      | .none => .none,
     /-- Applies the alignment mapping to a `Syntax`. -/
     alignSyntax : Syntax -> Syntax
      | .missing => .missing
      | .node info kind args => .node (alignInfo info) kind (args.map alignSyntax)
      | .atom info val =>
        -- We have to preserve the unsubscripted `val` even though it breaks `Syntax.reprint`
        -- because basic parsers like `num` read the `val` directly
        .atom (alignInfo info) val
      | .ident info rawVal val preresolved =>
        .ident (alignInfo info) (alignSubstr rawVal) val preresolved
    s.pushSyntax (alignSyntax s'.stxStack.back)
  )

/--
Definition of `scriptParser` / `scriptParser` 的定义

English:
definition scriptParser
  signature: (m : Mapping) (antiquotName errorMsg : String) (p : Parser)
  body: let tokens := " " :: (m.toNormal.toArray.map (·.1.toString) |>.qsort (·<·)).toList
  let antiquotP := mkAntiquot antiquotName `term (isPseudoKind := true)
  let p := Superscript.scriptFnNoAntiquot m errorMsg p.fn many
  node kind {
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·)
    fn := withAntiquotFn antiquotP.fn p (isCatAntiquot := true)
  }

中文:
定义 scriptParser
  签名: (m : Mapping) (antiquotName errorMsg : String) (p : Parser)
  定义体: let tokens := " " :: (m.toNormal.toArray.map (·.1.toString) |>.qsort (·<·)).toList
  let antiquotP := mkAntiquot antiquotName `term (isPseudoKind := true)
  let p := Superscript.scriptFnNoAntiquot m errorMsg p.fn many
  node kind {
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·)
    fn := withAntiquotFn antiquotP.fn p (isCatAntiquot := true)
  }

Depends on / 依赖: Parser, SyntaxNodeKind, decl_name
-/
def scriptParser (m : Mapping) (antiquotName errorMsg : String) (p : Parser)
    (many := true) (kind : SyntaxNodeKind := by exact decl_name%) : Parser :=
let tokens := " " :: (m.toNormal.toArray.map (·.1.toString) |>.qsort (·<·)).toList
  let antiquotP := mkAntiquot antiquotName `term (isPseudoKind := true)
  let p := Superscript.scriptFnNoAntiquot m errorMsg p.fn many
  node kind {
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·)
    fn := withAntiquotFn antiquotP.fn p (isCatAntiquot := true)
  }

/--
Definition of `scriptParser.parenthesizer` / `scriptParser.parenthesizer` 的定义

English:
definition scriptParser.parenthesizer
  signature: (k : SyntaxNodeKind) (p : Parenthesizer)
  body: Parenthesizer.node.parenthesizer k p

中文:
定义 scriptParser.parenthesizer
  签名: (k : SyntaxNodeKind) (p : Parenthesizer)
  定义体: Parenthesizer.node.parenthesizer k p

Depends on / 依赖: Parenthesizer, Parenthesizer.node.parenthesizer, parenthesizer
-/
def scriptParser.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer :=
  Parenthesizer.node.parenthesizer k p

/--
Definition of `_root_.Std.Format.mapStringsM` / `_root_.Std.Format.mapStringsM` 的定义

English:
definition _root_.Std.Format.mapStringsM
  signature: {m} [Monad m] (f : Format) (f' : String -> m String)
  body: match f with
| .group f b => (.group · b) < > Std.Format.mapStringsM f f'
| .tag t g => .tag t < > Std.Format.mapStringsM g f'
| .append f g => .append < > Std.Format.mapStringsM f f' <*> Std.Format.mapStringsM g f'
| .nest n f => .nest n < > Std.Format.mapStringsM f f'
| .text s => .text < > f' s
  | .align _ | .line | .nil => pure f

中文:
定义 _root_.Std.Format.mapStringsM
  签名: {m} [单子 m] (f : Format) (f' : String -> m String)
  定义体: match f with
| .group f b => (.group · b) < > Std.Format.mapStringsM f f'
| .tag t g => .tag t < > Std.Format.mapStringsM g f'
| .append f g => .append < > Std.Format.mapStringsM f f' <*> Std.Format.mapStringsM g f'
| .nest n f => .nest n < > Std.Format.mapStringsM f f'
| .text s => .text < > f' s
  | .align _ | .line | .nil => pure f

Depends on / 依赖: Format, Std.Format.mapStringsM, append, mapStringsM
-/
def _root_.Std.Format.mapStringsM {m} [Monad m] (f : Format) (f' : String -> m String) : m Format :=
  match f with
| .group f b => (.group · b) < > Std.Format.mapStringsM f f'
| .tag t g => .tag t < > Std.Format.mapStringsM g f'
| .append f g => .append < > Std.Format.mapStringsM f f' <*> Std.Format.mapStringsM g f'
| .nest n f => .nest n < > Std.Format.mapStringsM f f'
| .text s => .text < > f' s
  | .align _ | .line | .nil => pure f

/--
Definition of `scriptParser.formatter` / `scriptParser.formatter` 的定义

English:
definition scriptParser.formatter
  signature: (name : String) (m : Mapping) (k : SyntaxNodeKind) (p : Formatter)
  body: do
  let stack ← modifyGet fun s => (s.stack, {s with stack := #[]})
  Formatter.node.formatter k p
  let st ← get
  let transformed : Except String _ := st.stack.mapM (·.mapStringsM fun s => do
    let some s := s.toList.mapM (m.toSpecial.insert ' ' ' ').get? | .error s
    .ok (String.ofList s))
  match transformed with
  | .error err =>
    -- TODO: this only appears if the caller explicitly calls the pretty-printer
    Lean.logErrorAt (← get).stxTrav.cur s!"Not a {name}: '{err}'"
    set { st with stack := stack ++ st.stack }
  | .ok newStack =>
    set { st with stack := stack ++ newStack }

中文:
定义 scriptParser.formatter
  签名: (name : String) (m : Mapping) (k : SyntaxNodeKind) (p : Formatter)
  定义体: do
  let stack ← modifyGet fun s => (s.stack, {s with stack := #[]})
  Formatter.node.formatter k p
  let st ← get
  let transformed : Except String _ := st.stack.mapM (·.mapStringsM fun s => do
    let some s := s.toList.mapM (m.toSpecial.insert ' ' ' ').get? | .error s
    .ok (String.ofList s))
  match transformed with
  | .error err =>
    -- TODO: this only appears if the caller explicitly calls the pretty-printer
    Lean.logErrorAt (← get).stxTrav.cur s!"Not a {name}: '{err}'"
    set { st with stack := stack ++ st.stack }
  | .ok newStack =>
    set { st with stack := stack ++ newStack }
-/
def scriptParser.formatter (name : String) (m : Mapping) (k : SyntaxNodeKind) (p : Formatter) :
    Formatter := do
  let stack ← modifyGet fun s => (s.stack, {s with stack := #[]})
  Formatter.node.formatter k p
  let st ← get
  let transformed : Except String _ := st.stack.mapM (·.mapStringsM fun s => do
    let some s := s.toList.mapM (m.toSpecial.insert ' ' ' ').get? | .error s
    .ok (String.ofList s))
  match transformed with
  | .error err =>
    -- TODO: this only appears if the caller explicitly calls the pretty-printer
    Lean.logErrorAt (← get).stxTrav.cur s!"Not a {name}: '{err}'"
    set { st with stack := stack ++ st.stack }
  | .ok newStack =>
    set { st with stack := stack ++ newStack }

end Superscript

/--
Definition of `superscript` / `superscript` 的定义

English:
definition superscript
  signature: (p : Parser)
  body: Superscript.scriptParser .superscript "superscript" "expected superscript character" p

中文:
定义 superscript
  签名: (p : Parser)
  定义体: Superscript.scriptParser .superscript "superscript" "expected superscript character" p

Depends on / 依赖: Superscript, Superscript.scriptParser, character, expected, scriptParser, superscript
-/
def superscript (p : Parser) : Parser :=
  Superscript.scriptParser .superscript "superscript" "expected superscript character" p
/-- Formatter for the superscript parser. -/
@[combinator_parenthesizer superscript]
/--
Definition of `superscript.parenthesizer` / `superscript.parenthesizer` 的定义

English:
definition superscript.parenthesizer
  body: Superscript.scriptParser.parenthesizer ``superscript

中文:
定义 superscript.parenthesizer
  定义体: Superscript.scriptParser.parenthesizer ``superscript

Depends on / 依赖: Superscript, Superscript.scriptParser.parenthesizer, parenthesizer, scriptParser, superscript
-/
def superscript.parenthesizer := Superscript.scriptParser.parenthesizer ``superscript
/-- Formatter for the superscript parser. -/
@[combinator_formatter superscript]
/--
Definition of `superscript.formatter` / `superscript.formatter` 的定义

English:
definition superscript.formatter
  body: Superscript.scriptParser.formatter "superscript" .superscript ``superscript

中文:
定义 superscript.formatter
  定义体: Superscript.scriptParser.formatter "superscript" .superscript ``superscript

Depends on / 依赖: Superscript, Superscript.scriptParser.formatter, formatter, scriptParser, superscript
-/
def superscript.formatter :=
  Superscript.scriptParser.formatter "superscript" .superscript ``superscript

/-- Shorthand for `superscript(term)`.

This is needed because the initializer below does not always run, and if it has not run then
downstream parsers using the combinators will crash.

See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Non-builtin.20parser.20aliases/near/365125476
for some context. -/
@[term_parser]
/--
Definition of `superscriptTerm` / `superscriptTerm` 的定义

English:
definition superscriptTerm
  body: leading_parser (withAnonymousAntiquot := false) superscript termParser

中文:
定义 superscriptTerm
  定义体: leading_parser (withAnonymousAntiquot := false) superscript termParser

Depends on / 依赖: leading_parser, superscript, termParser, withAnonymousAntiquot
-/
def superscriptTerm := leading_parser (withAnonymousAntiquot := false) superscript termParser

initialize register_parser_alias superscript

/--
Definition of `subscript` / `subscript` 的定义

English:
definition subscript
  signature: (p : Parser)
  body: Superscript.scriptParser .subscript "subscript" "expected subscript character" p

中文:
定义 subscript
  签名: (p : Parser)
  定义体: Superscript.scriptParser .subscript "subscript" "expected subscript character" p

Depends on / 依赖: Superscript, Superscript.scriptParser, character, expected, scriptParser, subscript
-/
def subscript (p : Parser) : Parser :=
  Superscript.scriptParser .subscript "subscript" "expected subscript character" p
/-- Formatter for the subscript parser. -/
@[combinator_parenthesizer subscript]
/--
Definition of `subscript.parenthesizer` / `subscript.parenthesizer` 的定义

English:
definition subscript.parenthesizer
  body: Superscript.scriptParser.parenthesizer ``subscript

中文:
定义 subscript.parenthesizer
  定义体: Superscript.scriptParser.parenthesizer ``subscript

Depends on / 依赖: Superscript, Superscript.scriptParser.parenthesizer, parenthesizer, scriptParser, subscript
-/
def subscript.parenthesizer := Superscript.scriptParser.parenthesizer ``subscript
/-- Formatter for the subscript parser. -/
@[combinator_formatter subscript]
/--
Definition of `subscript.formatter` / `subscript.formatter` 的定义

English:
definition subscript.formatter
  body: Superscript.scriptParser.formatter "subscript" .subscript ``subscript

中文:
定义 subscript.formatter
  定义体: Superscript.scriptParser.formatter "subscript" .subscript ``subscript

Depends on / 依赖: Superscript, Superscript.scriptParser.formatter, formatter, scriptParser, subscript
-/
def subscript.formatter := Superscript.scriptParser.formatter "subscript" .subscript ``subscript

/-- Shorthand for `subscript(term)`.

This is needed because the initializer below does not always run, and if it has not run then
downstream parsers using the combinators will crash.

See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Non-builtin.20parser.20aliases/near/365125476
for some context. -/
@[term_parser]
/--
Definition of `subscriptTerm` / `subscriptTerm` 的定义

English:
definition subscriptTerm
  body: leading_parser (withAnonymousAntiquot := false) subscript termParser

中文:
定义 subscriptTerm
  定义体: leading_parser (withAnonymousAntiquot := false) subscript termParser

Depends on / 依赖: leading_parser, subscript, termParser, withAnonymousAntiquot
-/
def subscriptTerm := leading_parser (withAnonymousAntiquot := false) subscript termParser

initialize register_parser_alias subscript

/--
Definition of `Superscript.isValid` / `Superscript.isValid` 的定义

English:
definition Superscript.isValid
  signature: (m : Mapping)

中文:
定义 Superscript.isValid
  签名: (m : Mapping)
-/
private partial def Superscript.isValid (m : Mapping) : Syntax -> Bool
  | .node _ kind args => kind == hygieneInfoKind || (!(scripted kind) && args.all (isValid m))
  | .atom _ s => valid s
  | .ident _ _ s _ => valid s.toString
  | _ => false
where
  valid (s : String) : Bool :=
    s.all ((m.toSpecial.insert ' ' ' ').contains ·)
  scripted : SyntaxNodeKind -> Bool :=
    #[``subscript, ``superscript].contains

/--
Definition of `delabSuperscript` / `delabSuperscript` 的定义

English:
definition delabSuperscript
  signature: : Delab
  body: do
  let stx ← delab
  if Superscript.isValid .superscript stx.raw then pure stx else failure

中文:
定义 delabSuperscript
  签名: : Delab
  定义体: do
  let stx ← delab
  if Superscript.isValid .superscript stx.raw then pure stx else failure
-/
def delabSuperscript : Delab := do
  let stx ← delab
  if Superscript.isValid .superscript stx.raw then pure stx else failure

/--
Definition of `delabSubscript` / `delabSubscript` 的定义

English:
definition delabSubscript
  signature: : Delab
  body: do
  let stx ← delab
  if Superscript.isValid .subscript stx.raw then pure stx else failure

中文:
定义 delabSubscript
  签名: : Delab
  定义体: do
  let stx ← delab
  if Superscript.isValid .subscript stx.raw then pure stx else failure
-/
def delabSubscript : Delab := do
  let stx ← delab
  if Superscript.isValid .subscript stx.raw then pure stx else failure

end Mathlib.Tactic
