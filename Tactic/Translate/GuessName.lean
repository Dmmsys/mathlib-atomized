/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster
-/
module

public meta import Std.Data.TreeMap.Basic
public meta import Mathlib.Data.String.Defs
public import Mathlib.Init

/-!
# Name generation APIs for `to_additive`-like attributes
-/

public meta section

open Lean Std

namespace Mathlib.Tactic.GuessName
open GuessName -- currently needed to enable projection notation

/--
Definition of `GuessNameData` / `GuessNameData` 的定义

English:
structure GuessNameData
  parameters: where
  axioms and operations (2):
    - nameDict : Std.HashMap String (List String)
    - abbreviationDict : Std.HashMap String String

中文:
结构 GuessNameData
  参数: where
  公理与运算 (2 个):
    - nameDict : Std.HashMap String (列表 String)
    - abbreviationDict : Std.HashMap String String
-/
structure GuessNameData where
  /--
  Dictionary used by `guessName` to autogenerate names.
  This only transforms single name components, unlike `abbreviationDict`.

  Note: `guessName` capitalizes the output according to the capitalization of the input.
  In order for this to work, the input should always start with a lower case letter, and the output
  should always start with an upper case letter.
  -/
  nameDict : Std.HashMap String (List String)
  /--
  We need to fix a few abbreviations after applying `nameDict`, i.e. replacing `ZeroLE` by `Nonneg`.
  This dictionary contains these fixes.
  The input should contain entries that is in `lowerCamelCase` (e.g. `ltzero`; the initial sequence
  of capital letters should be lower-cased) and the output should be in `UpperCamelCase`
  (e.g. `LTZero`).
  When applying the dictionary, we lower-case the output if the input was also given in lower-case.
  -/
  abbreviationDict : Std.HashMap String String
  deriving Inhabited

/--
Definition of `endCapitalNames` / `endCapitalNames` 的定义

English:
definition endCapitalNames
  signature: : TreeMap String (List String) compare
  body: -- todo: we want something like
  -- endCapitalNamesOfList ["LE", "LT", "GE", "GT", "WF", "CoeTC", "CoeT", "CoeHTCT"]
  .ofList [("LE", [""]), ("LT", [""]), ("GE", [""]), ("GT", [""]), ("WF", [""]),
    ("Coe", ["TC", "T", "HTCT"])]

中文:
定义 endCapitalNames
  签名: : TreeMap String (列表 String) compare
  定义体: -- todo: we want something like
  -- endCapitalNamesOfList ["LE", "LT", "GE", "GT", "WF", "CoeTC", "CoeT", "CoeHTCT"]
  .ofList [("LE", [""]), ("LT", [""]), ("GE", [""]), ("GT", [""]), ("WF", [""]),
    ("Coe", ["TC", "T", "HTCT"])]
-/
def endCapitalNames : TreeMap String (List String) compare :=
  -- todo: we want something like
  -- endCapitalNamesOfList ["LE", "LT", "GE", "GT", "WF", "CoeTC", "CoeT", "CoeHTCT"]
  .ofList [("LE", [""]), ("LT", [""]), ("GE", [""]), ("GT", [""]), ("WF", [""]),
    ("Coe", ["TC", "T", "HTCT"])]

open String in
/--
Definition of `String.splitCase` / `String.splitCase` 的定义

English:
definition String.splitCase
  signature: (s : String) (i₀ : Pos.Raw := 0) (r : List String := [])
  body: Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := i₀.next s
  if i₁.atEnd s then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when 

中文:
定义 String.splitCase
  签名: (s : String) (i₀ : Pos.Raw := 0) (r : 列表 String := [])
  定义体: Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := i₀.next s
  if i₁.atEnd s then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when 
-/
partial def String.splitCase (s : String) (i₀ : Pos.Raw := 0) (r : List String := []) :
    List String := Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := i₀.next s
  if i₁.atEnd s then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when rejoining the string;
  * We split after a name in `endCapitalNames`;
  * We split after a lower-case letter that is followed by an upper-case letter
    (unless it is part of a name in `endCapitalNames`). -/
  if i₀.get s == '_' || i₁.get s == '_' then
return splitCase (String.Pos.Raw.extract s i₁ s.rawEndPos) 0
      (String.Pos.Raw.extract s 0 i₁)::r
  if (i₁.get s).isUpper then
    if let some strs := endCapitalNames[String.Pos.Raw.extract s 0 i₁]? then
      if let some (pref, newS) := strs.findSome?
        fun x : String => (String.Pos.Raw.extract s i₁ s.rawEndPos).dropPrefix? x
.map (x, ·.toString) then
return splitCase newS 0 (String.Pos.Raw.extract s 0 i₁ ++ pref)::r
    if !(i₀.get s).isUpper then
return splitCase (String.Pos.Raw.extract s i₁ s.rawEndPos) 0
        (String.Pos.Raw.extract s 0 i₁)::r
  return splitCase s i₁ r

/--
Definition of `String.decapitalizeSeq` / `String.decapitalizeSeq` 的定义

English:
definition String.decapitalizeSeq
  signature: (s : String) (i : String.Pos.Raw := 0)
  body: if i.atEnd s || !(i.get s).isUpper then
    s
  else
decapitalizeSeq (i.set s (i.get s).toLower) i.next s

中文:
定义 String.decapitalizeSeq
  签名: (s : String) (i : String.Pos.Raw := 0)
  定义体: if i.atEnd s || !(i.get s).isUpper then
    s
  else
decapitalizeSeq (i.set s (i.get s).toLower) i.next s
-/
partial def String.decapitalizeSeq (s : String) (i : String.Pos.Raw := 0) : String :=
  if i.atEnd s || !(i.get s).isUpper then
    s
  else
decapitalizeSeq (i.set s (i.get s).toLower) i.next s

/--
Definition of `decapitalizeLike` / `decapitalizeLike` 的定义

English:
definition decapitalizeLike
  signature: (r : String) (s : String)
  body: .isUpper then s else s.decapitalizeSeq if String.Pos.Raw.get r 0

中文:
定义 decapitalizeLike
  签名: (r : String) (s : String)
  定义体: .isUpper then s else s.decapitalizeSeq if String.Pos.Raw.get r 0

Depends on / 依赖: String.Pos.Raw.get, decapitalizeSeq, isUpper, s.decapitalizeSeq
-/
def decapitalizeLike (r : String) (s : String) :=
.isUpper then s else s.decapitalizeSeq if String.Pos.Raw.get r 0

/--
Definition of `decapitalizeFirstLike` / `decapitalizeFirstLike` 的定义

English:
definition decapitalizeFirstLike
  signature: (s : String)

中文:
定义 decapitalizeFirstLike
  签名: (s : String)
-/
def decapitalizeFirstLike (s : String) : List String -> List String
  | x :: r => decapitalizeLike s x :: r
  | [] => []

/--
Definition of `applyNameDict` / `applyNameDict` 的定义

English:
definition applyNameDict
  signature: (g : GuessNameData)
  body: match g.nameDict.get? x.toLower with
      | some y => decapitalizeFirstLike x y
      | none => [x]
    z ++ applyNameDict g s
  | [] => []

中文:
定义 applyNameDict
  签名: (g : GuessNameData)
  定义体: match g.nameDict.get? x.toLower with
      | some y => decapitalizeFirstLike x y
      | none => [x]
    z ++ applyNameDict g s
  | [] => []

Depends on / 依赖: g.nameDict.get, nameDict, toLower, x.toLower
-/
def applyNameDict (g : GuessNameData) : List String -> List String
  | x :: s =>
    let z := match g.nameDict.get? x.toLower with
      | some y => decapitalizeFirstLike x y
      | none => [x]
    z ++ applyNameDict g s
  | [] => []

/--
Definition of `fixAbbreviationAux` / `fixAbbreviationAux` 的定义

English:
definition fixAbbreviationAux
  signature: (g : GuessNameData)
  body: s' ++ [pre]
    let t := String.join s
    /- If a name starts with upper-case, and contains an underscore, it cannot match anything in
    the abbreviation dictionary. This is necessary to correctly translate something like
    `fixAbbreviation ["eventually", "LE", "_", "one"]` to `"eventuallyLE_on

中文:
定义 fixAbbreviationAux
  签名: (g : GuessNameData)
  定义体: s' ++ [pre]
    let t := String.join s
    /- If a name starts with upper-case, and contains an underscore, it cannot match anything in
    the abbreviation dictionary. This is necessary to correctly translate something like
    `fixAbbreviation ["eventually", "LE", "_", "one"]` to `"eventuallyLE_on
-/
def fixAbbreviationAux (g : GuessNameData) : List String -> List String -> String
  | [], [] => ""
  | [], x::s => x ++ fixAbbreviationAux g s []
  | pre::l, s' =>
    let s := s' ++ [pre]
    let t := String.join s
    /- If a name starts with upper-case, and contains an underscore, it cannot match anything in
    the abbreviation dictionary. This is necessary to correctly translate something like
    `fixAbbreviation ["eventually", "LE", "_", "one"]` to `"eventuallyLE_one"`, since otherwise the
    substring `LE_zero` gets replaced by `Nonpos`. -/
    if pre == "_" && (String.Pos.Raw.get t 0).isUpper then
      s[0]! ++ fixAbbreviationAux g (s.drop 1 ++ l) []
    else match g.abbreviationDict.get? t.decapitalizeSeq with
    | some post => decapitalizeLike t post ++ fixAbbreviationAux g l []
    | none => fixAbbreviationAux g l s
  termination_by l s => (l.length + s.length, l.length)
  decreasing_by all_goals grind

/--
Definition of `fixAbbreviation` / `fixAbbreviation` 的定义

English:
definition fixAbbreviation
  signature: (g : GuessNameData) (l : List String)
  body: fixAbbreviationAux g l []

中文:
定义 fixAbbreviation
  签名: (g : GuessNameData) (l : 列表 String)
  定义体: fixAbbreviationAux g l []

Depends on / 依赖: fixAbbreviationAux
-/
def fixAbbreviation (g : GuessNameData) (l : List String) : String :=
  fixAbbreviationAux g l []

/--
Definition of `guessName` / `guessName` 的定义

English:
definition guessName
  signature: (g : GuessNameData)
  body: String.mapTokens '\''
  fun s =>
fixAbbreviation g
applyNameDict g
    s.splitCase

中文:
定义 guessName
  签名: (g : GuessNameData)
  定义体: String.mapTokens '\''
  fun s =>
fixAbbreviation g
applyNameDict g
    s.splitCase

Depends on / 依赖: String.mapTokens, applyNameDict, fixAbbreviation, mapTokens, s.splitCase, splitCase
-/
def guessName (g : GuessNameData) : String -> String :=
String.mapTokens '\''
  fun s =>
fixAbbreviation g
applyNameDict g
    s.splitCase

/--
Definition of `GuessNameExt` / `GuessNameExt` 的定义

English:
abbreviation GuessNameExt
  body: EnvExtension GuessNameData

中文:
缩写 GuessNameExt
  定义体: EnvExtension GuessNameData

Depends on / 依赖: EnvExtension, GuessNameData
-/
abbrev GuessNameExt := EnvExtension GuessNameData

/--
Definition of `registerGuessNameExt` / `registerGuessNameExt` 的定义

English:
definition registerGuessNameExt
  signature: (data : GuessNameData)
  body: do
  registerEnvExtension (pure data)

中文:
定义 registerGuessNameExt
  签名: (data : GuessNameData)
  定义体: do
  registerEnvExtension (pure data)
-/
def registerGuessNameExt (data : GuessNameData) : IO GuessNameExt := do
  registerEnvExtension (pure data)

/--
Definition of `GuessNameExt.addTranslation` / `GuessNameExt.addTranslation` 的定义

English:
definition GuessNameExt.addTranslation
  signature: (ext : GuessNameExt) (srcId tgtId : Ident)
  body: do
  let src := srcId.getId.toString
  let tgt := tgtId.getId.toString
  unless src.front.isUpper do throwErrorAt srcId "`{src}` should be capitalized"
  unless tgt.front.isUpper do throwErrorAt tgtId "`{tgt}` should be capitalized"
  modifyEnv fun env => ext.modifyState env fun data =>
    let src 

中文:
定义 GuessNameExt.addTranslation
  签名: (ext : GuessNameExt) (srcId tgtId : Ident)
  定义体: do
  let src := srcId.getId.toString
  let tgt := tgtId.getId.toString
  unless src.front.isUpper do throwErrorAt srcId "`{src}` should be capitalized"
  unless tgt.front.isUpper do throwErrorAt tgtId "`{tgt}` should be capitalized"
  modifyEnv fun env => ext.modifyState env fun data =>
    let src 
-/
def GuessNameExt.addTranslation (ext : GuessNameExt) (srcId tgtId : Ident) :
    Elab.Command.CommandElabM Unit := do
  let src := srcId.getId.toString
  let tgt := tgtId.getId.toString
  unless src.front.isUpper do throwErrorAt srcId "`{src}` should be capitalized"
  unless tgt.front.isUpper do throwErrorAt tgtId "`{tgt}` should be capitalized"
  modifyEnv fun env => ext.modifyState env fun data =>
    let src := src.decapitalizeSeq
    if src.splitCase matches [_] then
      { data with nameDict := data.nameDict.insert src tgt.splitCase }
    else
      { data with abbreviationDict := data.abbreviationDict.insert src tgt }

end Mathlib.Tactic.GuessName
