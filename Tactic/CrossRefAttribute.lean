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

/--
Inductive type `Database` / 归纳类型 `Database`

English:
inductive Database
  parameters: where
  constructors (4):
    - kerodon: 
    - lmfdb: 
    - stacks: 
    - wikidata: 

中文:
归纳类型 Database
  参数: where
  构造子 (4 个):
    - kerodon: 
    - lmfdb: 
    - stacks: 
    - wikidata: 
-/
inductive Database where
  | kerodon
  | lmfdb
  | stacks
  | wikidata
  deriving BEq, Hashable, Ord

namespace Database

/--
Definition of `url` / `url` 的定义

English:
definition url
  signature: : Database -> String

中文:
定义 url
  签名: : Database -> String
-/
def url : Database -> String
  | .kerodon => "https://kerodon.net/tag/"
  | .lmfdb => "https://www.lmfdb.org/knowledge/show/"
  | .stacks => "https://stacks.math.columbia.edu/tag/"
  | .wikidata => "https://www.wikidata.org/wiki/"

/--
Definition of `label` / `label` 的定义

English:
definition label
  signature: : Database -> String

中文:
定义 label
  签名: : Database -> String
-/
def label : Database -> String
  | .kerodon => "Kerodon Tag"
  | .lmfdb => "LMFDB"
  | .stacks => "Stacks Tag"
  | .wikidata => "Wikidata"

/--
Definition of `shortName` / `shortName` 的定义

English:
definition shortName
  signature: : Database -> String

中文:
定义 shortName
  签名: : Database -> String
-/
def shortName : Database -> String
  | .kerodon => "kerodon"
  | .lmfdb => "lmfdb"
  | .stacks => "stacks"
  | .wikidata => "wikidata"

end Database

/--
Definition of `Tag` / `Tag` 的定义

English:
structure Tag
  parameters: where
  axioms and operations (4):
    - declName : Name
    - database : Database
    - tag : String
    - comment : String

中文:
结构 Tag
  参数: where
  公理与运算 (4 个):
    - declName : Name
    - database : Database
    - tag : String
    - comment : String
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

/--
Definition of `addTagEntry` / `addTagEntry` 的定义

English:
definition addTagEntry
  signature: {m : Type -> Type} [MonadEnv m]
  body: modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

中文:
定义 addTagEntry
  签名: {m : Type -> Type} [MonadEnv m]
  定义体: modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

Depends on / 依赖: addEntry, comment, database, declName, modifyEnv, tagExt, tagExt.addEntry
-/
def addTagEntry {m : Type -> Type} [MonadEnv m]
    (declName : Name) (db : Database) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

/--
Definition of `addCrossRefDoc` / `addCrossRefDoc` 的定义

English:
definition addCrossRefDoc
  signature: (db : Database) (decl : Name) (idStr comment : String)
  body: do
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  let commentInDoc := if comment.isEmpty then "" else s!" ({comment})"
  let link := s!"[{db.label} {idStr}]({db.url}{idStr}){commentInDoc}"
addDocStringCore decl "\n\n".intercalate ([oldDoc, link].filter (· != ""))
  addTagEntry decl db 

中文:
定义 addCrossRefDoc
  签名: (db : Database) (decl : Name) (idStr comment : String)
  定义体: do
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  let commentInDoc := if comment.isEmpty then "" else s!" ({comment})"
  let link := s!"[{db.label} {idStr}]({db.url}{idStr}){commentInDoc}"
addDocStringCore decl "\n\n".intercalate ([oldDoc, link].filter (· != ""))
  addTagEntry decl db 
-/
def addCrossRefDoc (db : Database) (decl : Name) (idStr comment : String) : CoreM Unit := do
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  let commentInDoc := if comment.isEmpty then "" else s!" ({comment})"
  let link := s!"[{db.label} {idStr}]({db.url}{idStr}){commentInDoc}"
addDocStringCore decl "\n\n".intercalate ([oldDoc, link].filter (· != ""))
  addTagEntry decl db idStr comment

open Parser

/-! ### Stacks (and Kerodon) parser -/

/--
Definition of `stacksTagKind` / `stacksTagKind` 的定义

English:
abbreviation stacksTagKind
  signature: : SyntaxNodeKind
  body: `stacksTag

中文:
缩写 stacksTagKind
  签名: : SyntaxNodeKind
  定义体: `stacksTag

Depends on / 依赖: stacksTag
-/
abbrev stacksTagKind : SyntaxNodeKind := `stacksTag

/--
Definition of `stacksTagFn` / `stacksTagFn` 的定义

English:
definition stacksTagFn
  signature: : ParserFn
  body: fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "stacks tag"
  else
    let tag := c.extract i s.pos
    if !tag.all fun (c : Char) => c.isDigit || c.isUpper then
      ParserState.mkUnexpec

中文:
定义 stacksTagFn
  签名: : ParserFn
  定义体: fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "stacks tag"
  else
    let tag := c.extract i s.pos
    if !tag.all fun (c : Char) => c.isDigit || c.isUpper then
      ParserState.mkUnexpec
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
/--
Definition of `stacksTagNoAntiquot` / `stacksTagNoAntiquot` 的定义

English:
definition stacksTagNoAntiquot
  signature: : Parser
  body: {
  fn := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]

中文:
定义 stacksTagNoAntiquot
  签名: : Parser
  定义体: {
  fn := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
-/
def stacksTagNoAntiquot : Parser := {
  fn := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
/--
Definition of `stacksTagParser` / `stacksTagParser` 的定义

English:
definition stacksTagParser
  signature: : Parser
  body: withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

中文:
定义 stacksTagParser
  签名: : Parser
  定义体: withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

Depends on / 依赖: mkAntiquot, stacksTag, stacksTagKind, stacksTagNoAntiquot, withAntiquot
-/
def stacksTagParser : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

/-! ### Wikidata parser -/

/--
Definition of `wikidataIdKind` / `wikidataIdKind` 的定义

English:
abbreviation wikidataIdKind
  signature: : SyntaxNodeKind
  body: `wikidataId

中文:
缩写 wikidataIdKind
  签名: : SyntaxNodeKind
  定义体: `wikidataId

Depends on / 依赖: wikidataId
-/
abbrev wikidataIdKind : SyntaxNodeKind := `wikidataId

/--
Definition of `wikidataIdFn` / `wikidataIdFn` 的定义

English:
definition wikidataIdFn
  signature: : ParserFn
  body: fun c s =>
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
      if rest.all Char.isDigit the

中文:
定义 wikidataIdFn
  签名: : ParserFn
  定义体: fun c s =>
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
      if rest.all Char.isDigit the
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
/--
Definition of `wikidataIdNoAntiquot` / `wikidataIdNoAntiquot` 的定义

English:
definition wikidataIdNoAntiquot
  signature: : Parser
  body: {
  fn := wikidataIdFn
  info := mkAtomicInfo "wikidataId"
}

@[inherit_doc wikidataIdFn]

中文:
定义 wikidataIdNoAntiquot
  签名: : Parser
  定义体: {
  fn := wikidataIdFn
  info := mkAtomicInfo "wikidataId"
}

@[inherit_doc wikidataIdFn]
-/
def wikidataIdNoAntiquot : Parser := {
  fn := wikidataIdFn
  info := mkAtomicInfo "wikidataId"
}

@[inherit_doc wikidataIdFn]
/--
Definition of `wikidataIdParser` / `wikidataIdParser` 的定义

English:
definition wikidataIdParser
  signature: : Parser
  body: withAntiquot (mkAntiquot "wikidataId" wikidataIdKind) wikidataIdNoAntiquot

中文:
定义 wikidataIdParser
  签名: : Parser
  定义体: withAntiquot (mkAntiquot "wikidataId" wikidataIdKind) wikidataIdNoAntiquot

Depends on / 依赖: mkAntiquot, wikidataId, wikidataIdKind, wikidataIdNoAntiquot, withAntiquot
-/
def wikidataIdParser : Parser :=
  withAntiquot (mkAntiquot "wikidataId" wikidataIdKind) wikidataIdNoAntiquot

/-! # LMFDB parser -/

/--
Definition of `lmfdbIdKind` / `lmfdbIdKind` 的定义

English:
abbreviation lmfdbIdKind
  signature: : SyntaxNodeKind
  body: `lmfdbId

中文:
缩写 lmfdbIdKind
  签名: : SyntaxNodeKind
  定义体: `lmfdbId

Depends on / 依赖: lmfdbId
-/
abbrev lmfdbIdKind : SyntaxNodeKind := `lmfdbId

/--
Definition of `lmfdbIdFn` / `lmfdbIdFn` 的定义

English:
definition lmfdbIdFn
  signature: : ParserFn
  body: fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum || c == '.' || c == '_') c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "lmfdb id"
  else
    if !(c.extract i s.pos).toList.all
      (fun c => c.isLower || c.isDigit || c == '.' || c == '_

中文:
定义 lmfdbIdFn
  签名: : ParserFn
  定义体: fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum || c == '.' || c == '_') c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "lmfdb id"
  else
    if !(c.extract i s.pos).toList.all
      (fun c => c.isLower || c.isDigit || c == '.' || c == '_
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
/--
Definition of `lmfdbIdNoAntiquot` / `lmfdbIdNoAntiquot` 的定义

English:
definition lmfdbIdNoAntiquot
  signature: : Parser
  body: {
  fn := lmfdbIdFn
  info := mkAtomicInfo "lmfdbId"
}

@[inherit_doc lmfdbIdFn]

中文:
定义 lmfdbIdNoAntiquot
  签名: : Parser
  定义体: {
  fn := lmfdbIdFn
  info := mkAtomicInfo "lmfdbId"
}

@[inherit_doc lmfdbIdFn]
-/
def lmfdbIdNoAntiquot : Parser := {
  fn := lmfdbIdFn
  info := mkAtomicInfo "lmfdbId"
}

@[inherit_doc lmfdbIdFn]
/--
Definition of `lmfdbIdParser` / `lmfdbIdParser` 的定义

English:
definition lmfdbIdParser
  signature: : Parser
  body: withAntiquot (mkAntiquot "lmfdbId" lmfdbIdKind) lmfdbIdNoAntiquot

中文:
定义 lmfdbIdParser
  签名: : Parser
  定义体: withAntiquot (mkAntiquot "lmfdbId" lmfdbIdKind) lmfdbIdNoAntiquot

Depends on / 依赖: lmfdbId, lmfdbIdKind, lmfdbIdNoAntiquot, mkAntiquot, withAntiquot
-/
def lmfdbIdParser : Parser :=
  withAntiquot (mkAntiquot "lmfdbId" lmfdbIdKind) lmfdbIdNoAntiquot

end Mathlib.CrossRef

open Mathlib.CrossRef

/--
Definition of `Lean.TSyntax.getStacksTag` / `Lean.TSyntax.getStacksTag` 的定义

English:
definition Lean.TSyntax.getStacksTag
  signature: (stx : TSyntax stacksTagKind)
  body: do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val

中文:
定义 Lean.TSyntax.getStacksTag
  签名: (stx : TSyntax stacksTagKind)
  定义体: do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val
-/
def Lean.TSyntax.getStacksTag (stx : TSyntax stacksTagKind) : CoreM String := do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val

/--
Definition of `Lean.TSyntax.getWikidataId` / `Lean.TSyntax.getWikidataId` 的定义

English:
definition Lean.TSyntax.getWikidataId
  signature: (stx : TSyntax wikidataIdKind)
  body: do
  let some val := Syntax.isLit? wikidataIdKind stx | throwError "Malformed Wikidata id"
  return val

中文:
定义 Lean.TSyntax.getWikidataId
  签名: (stx : TSyntax wikidataIdKind)
  定义体: do
  let some val := Syntax.isLit? wikidataIdKind stx | throwError "Malformed Wikidata id"
  return val
-/
def Lean.TSyntax.getWikidataId (stx : TSyntax wikidataIdKind) : CoreM String := do
  let some val := Syntax.isLit? wikidataIdKind stx | throwError "Malformed Wikidata id"
  return val

/--
Definition of `Lean.TSyntax.getLmfdbId` / `Lean.TSyntax.getLmfdbId` 的定义

English:
definition Lean.TSyntax.getLmfdbId
  signature: (stx : TSyntax lmfdbIdKind)
  body: do
  let some val := Syntax.isLit? lmfdbIdKind stx | throwError "Malformed LMFDB id"
  return val

中文:
定义 Lean.TSyntax.getLmfdbId
  签名: (stx : TSyntax lmfdbIdKind)
  定义体: do
  let some val := Syntax.isLit? lmfdbIdKind stx | throwError "Malformed LMFDB id"
  return val
-/
def Lean.TSyntax.getLmfdbId (stx : TSyntax lmfdbIdKind) : CoreM String := do
  let some val := Syntax.isLit? lmfdbIdKind stx | throwError "Malformed LMFDB id"
  return val

namespace Lean.PrettyPrinter

namespace Formatter

/--
Definition of `stacksTagNoAntiquot.formatter` / `stacksTagNoAntiquot.formatter` 的定义

English:
definition stacksTagNoAntiquot.formatter
  body: visitAtom stacksTagKind

中文:
定义 stacksTagNoAntiquot.formatter
  定义体: visitAtom stacksTagKind
-/
@[combinator_formatter stacksTagNoAntiquot] def stacksTagNoAntiquot.formatter :=
  visitAtom stacksTagKind

/--
Definition of `wikidataIdNoAntiquot.formatter` / `wikidataIdNoAntiquot.formatter` 的定义

English:
definition wikidataIdNoAntiquot.formatter
  body: visitAtom wikidataIdKind

中文:
定义 wikidataIdNoAntiquot.formatter
  定义体: visitAtom wikidataIdKind
-/
@[combinator_formatter wikidataIdNoAntiquot] def wikidataIdNoAntiquot.formatter :=
  visitAtom wikidataIdKind

/--
Definition of `lmfdbIdNoAntiquot.formatter` / `lmfdbIdNoAntiquot.formatter` 的定义

English:
definition lmfdbIdNoAntiquot.formatter
  body: visitAtom lmfdbIdKind

中文:
定义 lmfdbIdNoAntiquot.formatter
  定义体: visitAtom lmfdbIdKind
-/
@[combinator_formatter lmfdbIdNoAntiquot] def lmfdbIdNoAntiquot.formatter :=
  visitAtom lmfdbIdKind

end Formatter

namespace Parenthesizer

/--
Definition of `stacksTagAntiquot.parenthesizer` / `stacksTagAntiquot.parenthesizer` 的定义

English:
definition stacksTagAntiquot.parenthesizer
  body: visitToken

中文:
定义 stacksTagAntiquot.parenthesizer
  定义体: visitToken
-/
@[combinator_parenthesizer stacksTagNoAntiquot] def stacksTagAntiquot.parenthesizer := visitToken

/--
Definition of `wikidataIdAntiquot.parenthesizer` / `wikidataIdAntiquot.parenthesizer` 的定义

English:
definition wikidataIdAntiquot.parenthesizer
  body: visitToken

中文:
定义 wikidataIdAntiquot.parenthesizer
  定义体: visitToken
-/
@[combinator_parenthesizer wikidataIdNoAntiquot] def wikidataIdAntiquot.parenthesizer := visitToken

/--
Definition of `lmfdbIdAntiquot.parenthesizer` / `lmfdbIdAntiquot.parenthesizer` 的定义

English:
definition lmfdbIdAntiquot.parenthesizer
  body: visitToken

中文:
定义 lmfdbIdAntiquot.parenthesizer
  定义体: visitToken
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

/--
Definition of `Lean.Environment.getSortedCrossRefs` / `Lean.Environment.getSortedCrossRefs` 的定义

English:
definition Lean.Environment.getSortedCrossRefs
  signature: (env : Environment)
  body: let tags := PersistentEnvExtension.getState tagExt env
.qsort (·.tag < ·.tag) tags.2.flatten.appendList tags.1

中文:
定义 Lean.Environment.getSortedCrossRefs
  签名: (env : Environment)
  定义体: let tags := PersistentEnvExtension.getState tagExt env
.qsort (·.tag < ·.tag) tags.2.flatten.appendList tags.1
-/
private def Lean.Environment.getSortedCrossRefs (env : Environment) : Array Tag :=
  let tags := PersistentEnvExtension.getState tagExt env
.qsort (·.tag < ·.tag) tags.2.flatten.appendList tags.1

/--
Definition of `Lean.Environment.getCrossRefDeclNames` / `Lean.Environment.getCrossRefDeclNames` 的定义

English:
definition Lean.Environment.getCrossRefDeclNames
  signature: (env : Environment) (tag : String)
  body: env.getSortedCrossRefs.filterMap fun d => if d.tag == tag then some d.declName else none

中文:
定义 Lean.Environment.getCrossRefDeclNames
  签名: (env : Environment) (tag : String)
  定义体: env.getSortedCrossRefs.filterMap fun d => if d.tag == tag then some d.declName else none
-/
private def Lean.Environment.getCrossRefDeclNames (env : Environment) (tag : String) :
    Array Name :=
  env.getSortedCrossRefs.filterMap fun d => if d.tag == tag then some d.declName else none

namespace Mathlib.CrossRef

/--
Definition of `traceCrossRefs` / `traceCrossRefs` 的定义

English:
definition traceCrossRefs
  signature: (db : Database) (verbose : Bool := false)
  body: do
  let env ← getEnv
.filter (·.database == db) let entries := env.getSortedCrossRefs
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment 

中文:
定义 traceCrossRefs
  签名: (db : Database) (verbose : 布尔 := false)
  定义体: do
  let env ← getEnv
.filter (·.database == db) let entries := env.getSortedCrossRefs
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment 
-/
def traceCrossRefs (db : Database) (verbose : Bool := false) :
    Command.CommandElabM Unit := do
  let env ← getEnv
.filter (·.database == db) let entries := env.getSortedCrossRefs
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
