/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# Cross-reference attributes

This file provides attributes for tagging Mathlib results with cross-references
to entries in external mathematical databases:

* `@[stacks TAG]` — [Stacks Project](https://stacks.math.columbia.edu/tags)
* `@[kerodon TAG]` — [Kerodon](https://kerodon.net/tag/)
* `@[wikidata QID]` — [Wikidata](https://www.wikidata.org)
* `@[lmfdb ID]` — [LMFDB](https://www.lmfdb.org)

Each attribute records the cross-reference in an environment extension and appends
a link to the declaration's docstring.

The shared infrastructure (`Database`, `Tag`, `tagExt`, `addCrossRefDoc`,
`traceCrossRefs`) is database-agnostic; per-database code defines a parser, the
attribute syntax, and the trace command.
-/

public meta section

open Lean Elab

namespace Mathlib.CrossRef

/-- The supported external databases -/
/-
**Mathlib.CrossRef.Database** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supported external databases
-/
inductive Database where
  | kerodon
  | lmfdb
  | stacks
  | wikidata
  deriving BEq, Hashable, Ord

namespace Database

/-- The base URL for an external database's tag pages. Always ends with `/`. -/
/-
**Mathlib.CrossRef.Database.url** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef.Data
base`。
形式化陈述：Mathlib.CrossRef.Database → String
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base URL for an external database's tag pages. Always ends with `/`.
-/
def url : Database → String
  | .kerodon => "https://kerodon.net/tag/"
  | .lmfdb => "https://www.lmfdb.org/knowledge/show/"
  | .stacks => "https://stacks.math.columbia.edu/tag/"
  | .wikidata => "https://www.wikidata.org/wiki/"

/-- The display label used in docstring links and trace output. -/
/-
**Mathlib.CrossRef.Database.label** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef.Da
tabase`。
形式化陈述：Mathlib.CrossRef.Database → String
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The display label used in docstring links and trace output.
-/
def label : Database → String
  | .kerodon => "Kerodon Tag"
  | .lmfdb => "LMFDB"
  | .stacks => "Stacks Tag"
  | .wikidata => "Wikidata"

/-- A lowercase short name for the given database. Useful when exporting to JSON. -/
/-
**Mathlib.CrossRef.Database.shortName** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRe
f.Database`。
形式化陈述：Mathlib.CrossRef.Database → String
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lowercase short name for the given database. Useful when exporting to JSON.
-/
def shortName : Database → String
  | .kerodon  => "kerodon"
  | .lmfdb    => "lmfdb"
  | .stacks   => "stacks"
  | .wikidata => "wikidata"

end Database

/-- A cross-reference from a Mathlib declaration to an entry in an external database. -/
/-
**Mathlib.CrossRef.Tag** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：Tag where /-- The name of the declaration carrying the cross-reference. -/
 declName : Name /-- The external database the entry belongs to. -/ database : D
atabase /-- The database identifier. -/ tag : String /-- An optional comment sup
plied with the attribute. -/ comment : String deriving BEq, Hashable  /-- The en
vironment extension storing all cross-references. `addImportedFn` is a constant 
function to avoid a performance overhead during initialization. -/ initialize ta
gExt : SimplePersistentEnv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cross-reference from a Mathlib declaration to an entry in an external database
.
-/
structure Tag where
  /-- The name of the declaration carrying the cross-reference. -/
  declName : Name
  /-- The external database the entry belongs to. -/
  database : Database
  /-- The database identifier. -/
  tag : String
  /-- An optional comment supplied with the attribute. -/
  comment : String
  deriving BEq, Hashable

/-- The environment extension storing all cross-references.
`addImportedFn` is a constant function to avoid a performance overhead during initialization. -/
initialize tagExt : SimplePersistentEnvExtension Tag (Array (Array Tag)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn tags := tags
    addEntryFn tags _ := tags
  }

/-- `addTagEntry declName db tag comment` records a cross-reference for `declName` in `tagExt`. -/
/-
**Mathlib.CrossRef.addTagEntry** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：addTagEntry {m : Type -> Type} [MonadEnv m] (declName : Name) (db : Databa
se) (tag comment : String) : m Unit
参数：declName : Name；db : Database；tag comment : String。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`addTagEntry declName db tag comment` records a cross-reference for `declName` i
n `tagExt`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (db : Database) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

/-- Append a cross-reference link to the docstring of `decl` and record it in `tagExt`.
This is the database-agnostic core of every cross-reference attribute's `add` handler. -/
/-
**Mathlib.CrossRef.addCrossRefDoc** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：addCrossRefDoc (db : Database) (decl : Name) (idStr comment : String) : Co
reM Unit
参数：db : Database；decl : Name；idStr comment : String。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a cross-reference link to the docstring of `decl` and record it in `tagEx
t`.
This is the database-agnostic core of every cross-reference attribute's `add` ha
ndler.
-/
def addCrossRefDoc (db : Database) (decl : Name) (idStr comment : String) : CoreM Unit := do
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  let commentInDoc := if comment.isEmpty then "" else s!" ({comment})"
  let link := s!"[{db.label} {idStr}]({db.url}{idStr}){commentInDoc}"
  addDocStringCore decl <| "\n\n".intercalate ([oldDoc, link].filter (· != ""))
  addTagEntry decl db idStr comment

open Parser

/-! ### Stacks (and Kerodon) parser -/

/-- `stacksTag` is the node kind of Stacks Project Tags: a sequence of digits and
uppercase letters. -/
/-
**Mathlib.CrossRef.stacksTagKind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：stacksTagKind : SyntaxNodeKind
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`stacksTag` is the node kind of Stacks Project Tags: a sequence of digits and
uppercase letters.
-/
abbrev stacksTagKind : SyntaxNodeKind := `stacksTag

/-- The main parser for Stacks Project Tags: it accepts any sequence of 4 digits or
uppercase letters. -/
/-
**Mathlib.CrossRef.stacksTagFn** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：stacksTagFn : ParserFn
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main parser for Stacks Project Tags: it accepts any sequence of 4 digits or
uppercase letters.
-/
def stacksTagFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "stacks tag"
  else
    let tag := c.extract i s.pos
    if !tag.all fun (c : Char) => c.isDigit || c.isUpper then
      ParserState.mkUnexpectedError s
        "Stacks tags must consist only of digits and uppercase letters."
    else if tag.length != 4 then
      ParserState.mkUnexpectedError s "Stacks tags must be exactly 4 characters"
    else
      mkNodeToken stacksTagKind i true c s

@[inherit_doc stacksTagFn]
/-
**Mathlib.CrossRef.stacksTagNoAntiquot** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossR
ef`。
形式化陈述：stacksTagNoAntiquot : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stacksTagNoAntiquot : Parser := {
  fn   := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
/-
**Mathlib.CrossRef.stacksTagParser** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：stacksTagParser : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stacksTagParser : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

/-! ### Wikidata parser -/

/-- `wikidataId` is the node kind of Wikidata identifiers: the letter `Q` followed by digits. -/
/-
**Mathlib.CrossRef.wikidataIdKind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.CrossRef`
。
形式化陈述：wikidataIdKind : SyntaxNodeKind
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`wikidataId` is the node kind of Wikidata identifiers: the letter `Q` followed b
y digits.
-/
abbrev wikidataIdKind : SyntaxNodeKind := `wikidataId

/-- The main parser for Wikidata identifiers: it accepts `Q` followed by one or more digits. -/
/-
**Mathlib.CrossRef.wikidataIdFn** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：wikidataIdFn : ParserFn
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main parser for Wikidata identifiers: it accepts `Q` followed by one or more
 digits.
-/
def wikidataIdFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "wikidata id"
  else
    let id := c.extract i s.pos
    match id.toList with
    | 'Q' :: rest@(_ :: _) =>
      if rest.all Char.isDigit then
        mkNodeToken wikidataIdKind i true c s
      else
        ParserState.mkUnexpectedError s
          "Wikidata ids must consist of the letter Q followed by digits."
    | _ =>
      ParserState.mkUnexpectedError s
        "Wikidata ids must start with the letter Q followed by one or more digits."

@[inherit_doc wikidataIdFn]
/-
**Mathlib.CrossRef.wikidataIdNoAntiquot** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Cross
Ref`。
形式化陈述：wikidataIdNoAntiquot : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def wikidataIdNoAntiquot : Parser := {
  fn   := wikidataIdFn
  info := mkAtomicInfo "wikidataId"
}

@[inherit_doc wikidataIdFn]
/-
**Mathlib.CrossRef.wikidataIdParser** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`
。
形式化陈述：wikidataIdParser : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def wikidataIdParser : Parser :=
  withAntiquot (mkAntiquot "wikidataId" wikidataIdKind) wikidataIdNoAntiquot

/-! # LMFDB parser -/

/-- `lmfdbId` is the node kind of LMFDB identifiers: lower case words with `.` in between.
The words can also contain underscores and digits. -/
/-
**Mathlib.CrossRef.lmfdbIdKind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：lmfdbIdKind : SyntaxNodeKind
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lmfdbId` is the node kind of LMFDB identifiers: lower case words with `.` in be
tween.
The words can also contain underscores and digits.
-/
abbrev lmfdbIdKind : SyntaxNodeKind := `lmfdbId

/-- The main parser for LMFDB identifiers: it accepts lower case words with `.` in between.
The words can also contain underscores and digits. -/
/-
**Mathlib.CrossRef.lmfdbIdFn** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：lmfdbIdFn : ParserFn
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main parser for LMFDB identifiers: it accepts lower case words with `.` in b
etween.
The words can also contain underscores and digits.
-/
def lmfdbIdFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum || c == '.' || c == '_') c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "lmfdb id"
  else
    if !(c.extract i s.pos).toList.all
      (fun c => c.isLower || c.isDigit || c == '.' || c == '_') then
      ParserState.mkUnexpectedError s
        "LMFDB ids must consist only of lowercase letters, digits, periods, and underscores."
    else
      mkNodeToken lmfdbIdKind i true c s

@[inherit_doc lmfdbIdFn]
/-
**Mathlib.CrossRef.lmfdbIdNoAntiquot** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef
`。
形式化陈述：lmfdbIdNoAntiquot : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lmfdbIdNoAntiquot : Parser := {
  fn   := lmfdbIdFn
  info := mkAtomicInfo "lmfdbId"
}

@[inherit_doc lmfdbIdFn]
/-
**Mathlib.CrossRef.lmfdbIdParser** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：lmfdbIdParser : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lmfdbIdParser : Parser :=
  withAntiquot (mkAntiquot "lmfdbId" lmfdbIdKind) lmfdbIdNoAntiquot

end Mathlib.CrossRef

open Mathlib.CrossRef

/-- Extract the underlying tag as a string from a `stacksTag` node. -/
/-
**Lean.TSyntax.getStacksTag** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lean.TSyntax.getStacksTag (stx : TSyntax stacksTagKind) : CoreM String
参数：stx : TSyntax stacksTagKind。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the underlying tag as a string from a `stacksTag` node.
-/
def Lean.TSyntax.getStacksTag (stx : TSyntax stacksTagKind) : CoreM String := do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val

/-- Extract the underlying identifier as a string from a `wikidataId` node. -/
/-
**Lean.TSyntax.getWikidataId** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lean.TSyntax.getWikidataId (stx : TSyntax wikidataIdKind) : CoreM String
参数：stx : TSyntax wikidataIdKind。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the underlying identifier as a string from a `wikidataId` node.
-/
def Lean.TSyntax.getWikidataId (stx : TSyntax wikidataIdKind) : CoreM String := do
  let some val := Syntax.isLit? wikidataIdKind stx | throwError "Malformed Wikidata id"
  return val

/-- Extract the underlying identifier as a string from a `lmfdbId` node. -/
/-
**Lean.TSyntax.getLmfdbId** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lean.TSyntax.getLmfdbId (stx : TSyntax lmfdbIdKind) : CoreM String
参数：stx : TSyntax lmfdbIdKind。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the underlying identifier as a string from a `lmfdbId` node.
-/
def Lean.TSyntax.getLmfdbId (stx : TSyntax lmfdbIdKind) : CoreM String := do
  let some val := Syntax.isLit? lmfdbIdKind stx | throwError "Malformed LMFDB id"
  return val

namespace Lean.PrettyPrinter

namespace Formatter

/-- The formatter for Stacks Project Tags syntax. -/
/-
**Lean.PrettyPrinter.Formatter.stacksTagNoAntiquot.formatter** 是 Mathlib 中的一个定义，
位于命名空间 `Lean.PrettyPrinter.Formatter.stacksTagNoAntiquot`。
形式化陈述：PrettyPrinter.Formatter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formatter for Stacks Project Tags syntax.
-/
@[combinator_formatter stacksTagNoAntiquot] def stacksTagNoAntiquot.formatter :=
  visitAtom stacksTagKind

/-- The formatter for Wikidata identifier syntax. -/
/-
**Lean.PrettyPrinter.Formatter.wikidataIdNoAntiquot.formatter** 是 Mathlib 中的一个定义
，位于命名空间 `Lean.PrettyPrinter.Formatter.wikidataIdNoAntiquot`。
形式化陈述：PrettyPrinter.Formatter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formatter for Wikidata identifier syntax.
-/
@[combinator_formatter wikidataIdNoAntiquot] def wikidataIdNoAntiquot.formatter :=
  visitAtom wikidataIdKind

/-- The formatter for LMFDB identifier syntax. -/
/-
**Lean.PrettyPrinter.Formatter.lmfdbIdNoAntiquot.formatter** 是 Mathlib 中的一个定义，位于
命名空间 `Lean.PrettyPrinter.Formatter.lmfdbIdNoAntiquot`。
形式化陈述：PrettyPrinter.Formatter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formatter for LMFDB identifier syntax.
-/
@[combinator_formatter lmfdbIdNoAntiquot] def lmfdbIdNoAntiquot.formatter :=
  visitAtom lmfdbIdKind

end Formatter

namespace Parenthesizer

/-- The parenthesizer for Stacks Project Tags syntax. -/
/-
**Lean.PrettyPrinter.Parenthesizer.stacksTagAntiquot.parenthesizer** 是 Mathlib 中
的一个定义，位于命名空间 `Lean.PrettyPrinter.Parenthesizer.stacksTagAntiquot`。
形式化陈述：PrettyPrinter.Parenthesizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The parenthesizer for Stacks Project Tags syntax.
-/
@[combinator_parenthesizer stacksTagNoAntiquot] def stacksTagAntiquot.parenthesizer := visitToken

/-- The parenthesizer for Wikidata identifier syntax. -/
/-
**Lean.PrettyPrinter.Parenthesizer.wikidataIdAntiquot.parenthesizer** 是 Mathlib 
中的一个定义，位于命名空间 `Lean.PrettyPrinter.Parenthesizer.wikidataIdAntiquot`。
形式化陈述：PrettyPrinter.Parenthesizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The parenthesizer for Wikidata identifier syntax.
-/
@[combinator_parenthesizer wikidataIdNoAntiquot] def wikidataIdAntiquot.parenthesizer := visitToken

/-- The parenthesizer for LMFDB identifier syntax. -/
/-
**Lean.PrettyPrinter.Parenthesizer.lmfdbIdAntiquot.parenthesizer** 是 Mathlib 中的一
个定义，位于命名空间 `Lean.PrettyPrinter.Parenthesizer.lmfdbIdAntiquot`。
形式化陈述：PrettyPrinter.Parenthesizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The parenthesizer for LMFDB identifier syntax.
-/
@[combinator_parenthesizer lmfdbIdNoAntiquot] def lmfdbIdAntiquot.parenthesizer := visitToken

end Lean.PrettyPrinter.Parenthesizer

namespace Mathlib.CrossRef

/-! ### Stacks / Kerodon attribute -/

/-- The syntax category for the database name. -/
declare_syntax_cat stacksTagDB

/-- The syntax for a "kerodon" database identifier in a `@[kerodon]` attribute. -/
syntax "kerodon" : stacksTagDB
/-- The syntax for a "stacks" database identifier in a `@[stacks]` attribute. -/
syntax "stacks" : stacksTagDB

/-- The `stacksTag` attribute.
Use it as `@[kerodon TAG "Optional comment"]` or `@[stacks TAG "Optional comment"]`
depending on the database you are referencing.

The `TAG` is mandatory and should be a sequence of 4 digits or uppercase letters.

See the [Tags page](https://stacks.math.columbia.edu/tags) in the Stacks project or
[Tags page](https://kerodon.net/tag/) in the Kerodon project for more details.
-/
syntax (name := stacksTag) stacksTagDB stacksTagParser (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `stacksTag
  descr := "Apply a Stacks or Kerodon project tag to a theorem."
  add := fun decl stx _attrKind => do
    let (db, tag, comment) ← match stx with
      | `(attr| stacks $tag $[$comment]?) => pure (Database.stacks, tag, comment)
      | `(attr| kerodon $tag $[$comment]?) => pure (Database.kerodon, tag, comment)
      | _ => throwUnsupportedSyntax
    addCrossRefDoc db decl (← tag.getStacksTag) ((comment.map (·.getString)).getD "")
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

/-! ### Wikidata attribute -/

/-- The `wikidata` attribute.
Use it as `@[wikidata Q12345 "Optional comment"]` to associate a Mathlib declaration with
the corresponding [Wikidata](https://www.wikidata.org) item.

The identifier must be the letter `Q` followed by one or more digits.
-/
syntax (name := wikidataTag) "wikidata" wikidataIdParser (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `wikidataTag
  descr := "Apply a Wikidata identifier to a declaration."
  add := fun decl stx _attrKind => do
    let (id, comment) ← match stx with
      | `(attr| wikidata $id $[$comment]?) => pure (id, comment)
      | _ => throwUnsupportedSyntax
    addCrossRefDoc .wikidata decl (← id.getWikidataId) ((comment.map (·.getString)).getD "")
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

/-! ### LMFDB attribute -/

/-- The `lmfdb` attribute.
Use it as `@[lmfdb foo.bar "Optional comment"]` to associate a Mathlib declaration with
the corresponding [LMFDB](https://www.lmfdb.org) item.
-/
syntax (name := lmfdbTag) "lmfdb" lmfdbIdParser (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `lmfdbTag
  descr := "Apply an LMFDB identifier to a declaration."
  add := fun decl stx _attrKind => do
    let (id, comment) ← match stx with
      | `(attr| lmfdb $id $[$comment]?) => pure (id, comment)
      | _ => throwUnsupportedSyntax
    addCrossRefDoc .lmfdb decl (← id.getLmfdbId) ((comment.map (·.getString)).getD "")
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

end Mathlib.CrossRef

/-- Returns the array of `Tag`s in the environment, sorted alphabetically by tag. -/
/-
**Lean.Environment.getSortedCrossRefs** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the array of `Tag`s in the environment, sorted alphabetically by tag.
-/
private def Lean.Environment.getSortedCrossRefs (env : Environment) : Array Tag :=
  let tags := PersistentEnvExtension.getState tagExt env
  tags.2.flatten.appendList tags.1 |>.qsort (·.tag < ·.tag)

/-- Returns the declaration names of results carrying the cross-reference `tag`. -/
/-
**Lean.Environment.getCrossRefDeclNames** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the declaration names of results carrying the cross-reference `tag`.
-/
private def Lean.Environment.getCrossRefDeclNames (env : Environment) (tag : String) :
    Array Name :=
  env.getSortedCrossRefs.filterMap fun d => if d.tag == tag then some d.declName else none

namespace Mathlib.CrossRef

/-- `traceCrossRefs db verbose` prints the cross-references of database `db` and
inlines the declaration types if `verbose` is `true`. -/
/-
**Mathlib.CrossRef.traceCrossRefs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.CrossRef`。
形式化陈述：Mathlib.CrossRef.Database → optParam Bool false → CommandElabM Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`traceCrossRefs db verbose` prints the cross-references of database `db` and
inlines the declaration types if `verbose` is `true`.
-/
def traceCrossRefs (db : Database) (verbose : Bool := false) :
    Command.CommandElabM Unit := do
  let env ← getEnv
  let entries := env.getSortedCrossRefs |>.filter (·.database == db)
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    msgs := msgs.push
      m!"[{db.label} {d.tag}]({db.url ++ d.tag}) \
        corresponds to declaration '{.ofConstName d.declName}'.{cmt}"
    if verbose then
      let dType := ((env.find? d.declName).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg

/--
`#stacks_tags` retrieves all declarations that have the `stacks` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#stacks_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := stacksTags) "#stacks_tags" tk:("!")? : command =>
  traceCrossRefs .stacks (tk.isSome)

/-- The `#kerodon_tags` command retrieves all declarations that have the `kerodon` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#kerodon_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := kerodonTags) "#kerodon_tags" tk:("!")? : command =>
  traceCrossRefs .kerodon (tk.isSome)

/-- The `#wikidata_tags` command retrieves all declarations that have the `wikidata` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#wikidata_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := wikidataTags) "#wikidata_tags" tk:("!")? : command =>
  traceCrossRefs .wikidata (tk.isSome)

/-- The `#lmfdb_tags` command retrieves all declarations that have the `lmfdb` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#lmfdb_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := lmfdbTags) "#lmfdb_tags" tk:("!")? : command =>
  traceCrossRefs .lmfdb (tk.isSome)

end Mathlib.CrossRef

