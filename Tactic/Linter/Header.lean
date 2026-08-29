/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.ParseImportsFast
public meta import Std.Sync.Mutex
public import Lean.Parser.Module
public import Mathlib.Tactic.Linter.DirectoryDependency

/-!
# The "header" linter

The "header" style linter checks that a file starts with
```
/-
Copyright ...
Apache ...
Authors ...
-/

import statements*

module doc-string*

remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.

The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.

## Implementation
The strategy used by the linter is as follows.
The linter computes the end position of the first module doc-string of the file,
resorting to the end of the file, if there is no module doc-string.
Next, the linter tries to parse the file up to the position determined above.

If the parsing is successful, the linter checks the resulting `Syntax` and behaves accordingly.

If the parsing is not successful, this already means there is some "problematic" command
after the imports. In particular, there is a command that is not a module doc-string
immediately following the last import: the file should be flagged by the linter.
Hence, the linter then falls back to parsing the header of the file, adding a spurious `section`
after it.
This makes it possible for the linter to check the entire header of the file, emit warnings that
could arise from this part and also flag that the file should contain a module doc-string after
the `import` statements.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
Definition of `firstNonImport?` / `firstNonImport?` 的定义

English:
definition firstNonImport?
  signature: : Syntax -> Option Syntax

中文:
定义 firstNonImport?
  签名: : Syntax -> 选项类型 Syntax
-/
def firstNonImport? : Syntax -> Option Syntax
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] => args[0]?
  | _=> some .missing -- this is unreachable, if the input comes from `testParseModule`

/-- `getImports s` takes as input `s : Syntax`.
It returns the array of all `import` statement syntax nodes in `s`. -/
partial
/--
Definition of `getImports` / `getImports` 的定义

English:
definition getImports
  signature: (s : Syntax)
  body: let rest : Array Syntax := (s.getArgs.map getImports).flatten
  if s.isOfKind `Lean.Parser.Module.import then
    rest.push s
  else
    rest

中文:
定义 getImports
  签名: (s : Syntax)
  定义体: let rest : Array Syntax := (s.getArgs.map getImports).flatten
  if s.isOfKind `Lean.Parser.Module.import then
    rest.push s
  else
    rest

Depends on / 依赖: Lean.Parser.Module.import, Module, Parser, Syntax, flatten, getArgs, getImports, import, isOfKind, rest.push, s.getArgs.map, s.isOfKind
-/
def getImports (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImports).flatten
  if s.isOfKind `Lean.Parser.Module.import then
    rest.push s
  else
    rest

/-- `getImportIds s` takes as input `s : Syntax`.
It returns the array of all `import` identifiers in `s`. -/
-- We cannot use `importsOf` instead, as
-- - that function is defined in the `ImportGraph` project; we would like to minimise imports
-- to Mathlib.Init (where this linter is imported)
-- - that function does not return the Syntax corresponding to each import,
-- which we use to log more precise warnings.
-- This function is public as the `DeprecatedModule` linter also uses it.
public partial def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  -- Check if this is an import node by kind, rather than pattern matching all optional modifiers.
  -- This is more robust if the import syntax changes.
  if s.isOfKind `Lean.Parser.Module.import then
    -- The module name is the last identifier in the import node arguments
.back? with match s.getArgs.filter (·.isIdent)
    | some n => rest.push n
    | none => rest
  else
    rest

/--
Definition of `parseUpToHere` / `parseUpToHere` 的定义

English:
definition parseUpToHere
  signature: (pos : String.Pos.Raw) (post : String := "")
  body: do
  let upToHere : Substring.Raw := { str := (← getFileMap).source, startPos := ⟨0⟩, stopPos := pos }
  -- Append a further string after the content of `upToHere`.
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

中文:
定义 parseUpToHere
  签名: (pos : String.Pos.Raw) (post : String := "")
  定义体: do
  let upToHere : Substring.Raw := { str := (← getFileMap).source, startPos := ⟨0⟩, stopPos := pos }
  -- Append a further string after the content of `upToHere`.
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

Depends on / 依赖: CommandElabM, Syntax
-/
def parseUpToHere (pos : String.Pos.Raw) (post : String := "") : CommandElabM Syntax := do
  let upToHere : Substring.Raw := { str := (← getFileMap).source, startPos := ⟨0⟩, stopPos := pos }
  -- Append a further string after the content of `upToHere`.
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

/--
Definition of `toSyntax` / `toSyntax` 的定义

English:
definition toSyntax
  signature: (s pattern : String) (offset : String.Pos.Raw := 0)
  body: let beg := ((s.splitOn pattern).getD 0 "").rawEndPos.offsetBy offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).rawEndPos.offsetBy offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern

中文:
定义 toSyntax
  签名: (s pattern : String) (offset : String.Pos.Raw := 0)
  定义体: let beg := ((s.splitOn pattern).getD 0 "").rawEndPos.offsetBy offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).rawEndPos.offsetBy offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern

Depends on / 依赖: Syntax
-/
def toSyntax (s pattern : String) (offset : String.Pos.Raw := 0) : Syntax :=
  let beg := ((s.splitOn pattern).getD 0 "").rawEndPos.offsetBy offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).rawEndPos.offsetBy offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern

/--
Definition of `authorsLineChecks` / `authorsLineChecks` 的定义

English:
definition authorsLineChecks
  signature: (line : String) (offset : String.Pos.Raw)
  body: Id.run do
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the line starting wrongly, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.

中文:
定义 authorsLineChecks
  签名: (line : String) (offset : String.Pos.Raw)
  定义体: Id.run do
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the line starting wrongly, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.

Depends on / 依赖: Id.run
-/
def authorsLineChecks (line : String) (offset : String.Pos.Raw) : Array (Syntax × String) :=
  Id.run do
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the line starting wrongly, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.push
      (toSyntax line (line.take "Authors: ".length |>.copy) offset,
       s!"The authors line should begin with 'Authors: '")
  if (line.splitOn " ").length != 1 then
    stxs := stxs.push (toSyntax line " " offset, s!"Double spaces are not allowed.")
  if (line.splitOn " and ").length != 1 then
    stxs := stxs.push (toSyntax line " and " offset, s!"Please, do not use 'and'; use ',' instead.")
  if line.back == '.' then
    stxs := stxs.push
      (toSyntax line "." offset,
       s!"Please, do not end the authors' line with a period.")
  -- If there are no previous exceptions, then we try to validate the names.
  if !stxs.isEmpty then
    return stxs
  if (line.drop "Authors:".length).trimAscii.isEmpty then
    return #[(toSyntax line "Authors:" offset,
       s!"Please, add at least one author!")]
  else
    return #[]

/-- The main function to validate the copyright string.
The input is the copyright string, the output is an array of `Syntax × String` encoding:
* the `Syntax` factors are atoms whose ranges are "best guesses" for where the changes should
  take place; the embedded string is the current text that the linter flagged;
* the `String` factor is the linter message.

The linter checks that
* the first and last line of the copyright are a `("/-", "-/")` pair, each on its own line;
* the first line is begins with `Copyright (c) 20` and ends with `. All rights reserved.`;
* the second line equals `expectedLicense` (determined by the `linter.style.header.license` option,
  defaults to the Mathlib default);
* the remainder of the string begins with `Authors: `, does not end with `.` and
  contains no ` and ` nor a double space, except possibly after a line break.
-/
public def copyrightHeaderChecks (copyright : String) (expectedLicense : String) :
    Array (Syntax × String) := Id.run do
  -- First, we merge lines ending in `,`: two spaces after the line-break are ok,
  -- but so is only one or none. We take care of *not* adding more consecutive spaces, though.
  -- This is to allow the copyright or authors' lines to span several lines.
  -- We also allow the "All rights reserved" line to be on a separate line.
  let preprocessCopyright := (copyright.replace ",\n " ", ").replace ",\n" ","
.replace ".\nAll rights reserved." ". All rights reserved."
  -- Filter out everything after the first isolated `-/`.
  let pieces := preprocessCopyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdText (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut output := #[]
  if (pieces.getD 1 "\n").take 1 != "\n".toSlice then
    output := output.push (toSyntax copyright "-/", s!"{stdText "-/"}")
  let lines := copyright.splitOn "\n"
  let closeComment := lines.getLastD ""
  match lines with
  | openComment :: copyrightAuthor :: license :: authorsLines =>
    -- The header should start and end with blank comments.
    match openComment, closeComment with
    | "/-", "-/" => output := output
    | "/-", _ =>
      output := output.push (toSyntax copyright closeComment, s!"{stdText "-/"}")
    | _, _ =>
      output := output.push (toSyntax copyright openComment, s!"{stdText ("/".push '-')}")
    -- Validate the first copyright line.
    let copStart := "Copyright (c) 20"
    let copStop := ". All rights reserved."
    if !copyrightAuthor.startsWith copStart then
      output := output.push
        (toSyntax copyright (copyrightAuthor.take copStart.length).copy,
         s!"Copyright line should start with 'Copyright (c) YYYY'")
    let author := (copyrightAuthor.drop (copStart.length + 2))
    if output.isEmpty && author.take 1 != " ".toSlice then
      output := output.push
        (toSyntax copyright (copyrightAuthor.drop (copStart.length + 2)).copy,
         s!"'Copyright (c) YYYY' should be followed by a space")
    if output.isEmpty && #["", ".", ","].contains ((author.drop 1).take 1).trimAscii.copy then
      output := output.push
        (toSyntax copyright (copyrightAuthor.drop (copStart.length + 3)).copy,
         s!"There should be at least one copyright author, separated from the year by exactly one space.")
    if !copyrightAuthor.endsWith copStop then
      output := output.push
        (toSyntax copyright (copyrightAuthor.takeEnd copStop.length).copy,
         s!"Copyright line should end with '. All rights reserved.'")
    -- Validate the authors line(s). The last line is the closing comment: trim that off right away.
    let authorsLines := authorsLines.dropLast
    -- Complain about a missing authors line.
    if authorsLines.length == 0 then
      output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
    else
    -- If the list of authors spans multiple lines, all but the last line should end with a trailing
    -- comma. This excludes e.g. other comments in the copyright header.
    let authorsLine := "\n".intercalate authorsLines
    let authorsStart := (("\n".intercalate [openComment, copyrightAuthor, license, ""])).rawEndPos
    if authorsLines.length > 1 && !authorsLines.dropLast.all (·.endsWith ",") then
      output := output.push ((toSyntax copyright authorsLine),
        "If an authors line spans multiple lines, \
        each line but the last must end with a trailing comma")
    output := output.append (authorsLineChecks authorsLine authorsStart)
    if license != expectedLicense then
      output := output.push (toSyntax copyright license,
        s!"Second copyright line should be \"{expectedLicense}\"")
  | _ =>
    output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
  return output

/--
Definition of `isInLibraryRoot` / `isInLibraryRoot` 的定义

English:
definition isInLibraryRoot
  signature: (modName : Name)
  body: do
  let rootPath := (modName.getRoot.toString : System.FilePath).addExtension "lean"
  if ← rootPath.pathExists then
    let res ← parseImports' (← IO.FS.readFile rootPath) ""
    return res.imports.any (·.module == modName)
  else return false

中文:
定义 isInLibraryRoot
  签名: (modName : Name)
  定义体: do
  let rootPath := (modName.getRoot.toString : System.FilePath).addExtension "lean"
  if ← rootPath.pathExists then
    let res ← parseImports' (← IO.FS.readFile rootPath) ""
    return res.imports.any (·.module == modName)
  else return false
-/
def isInLibraryRoot (modName : Name) : IO Bool := do
  let rootPath := (modName.getRoot.toString : System.FilePath).addExtension "lean"
  if ← rootPath.pathExists then
    let res ← parseImports' (← IO.FS.readFile rootPath) ""
    return res.imports.any (·.module == modName)
  else return false

/-- `inLibraryRootMutex` caches whether the current file is imported in the library root file
(e.g. `Mathlib.lean`), as computed by `isInLibraryRoot`. It is
* `none` at initialization time;
* `some true` if the `header` linter has already discovered that the current file
  is imported in the library root file;
* `some false` if the `header` linter has already discovered that the current file
  is *not* imported in the library root file.
-/
initialize inLibraryRootMutex : Std.Mutex (Option Bool) ← Std.Mutex.new none

/--
The "header" style linter checks that a file starts with
```
/-
Copyright ...
Apache ...
Authors ...
-/

import statements*
module doc-string*
remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.

The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.
-/
public register_option linter.style.header : Bool := {
  defValue := false
  descr := "enable the header style linter"
}

/-- The text required by `linter.style.header` as the second line of the header. -/
public register_option linter.style.header.license : String := {
  defValue := "Released under Apache 2.0 license as described in the file LICENSE."
  descr := "The text required as the second line of the copyright header."
}

namespace Style.header

/--
Definition of `broadImportsCheck` / `broadImportsCheck` 的定义

English:
definition broadImportsCheck
  signature: (imports : Array Syntax) (mainModule : Name)
  body: do
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic | `Lean | `Lean.Meta | `Lean.Elab | `Lean.Elab.Tactic | `Std =>
      Linter.logLint linter.style.header i
        s!"Files in mathlib cannot import the whole `{i.getId}` folder. \
        Doing so would cause imports to be unnece

中文:
定义 broadImportsCheck
  签名: (imports : 数组 Syntax) (mainModule : Name)
  定义体: do
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic | `Lean | `Lean.Meta | `Lean.Elab | `Lean.Elab.Tactic | `Std =>
      Linter.logLint linter.style.header i
        s!"Files in mathlib cannot import the whole `{i.getId}` folder. \
        Doing so would cause imports to be unnece
-/
def broadImportsCheck (imports : Array Syntax) (mainModule : Name) : CommandElabM Unit := do
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic | `Lean | `Lean.Meta | `Lean.Elab | `Lean.Elab.Tactic | `Std =>
      Linter.logLint linter.style.header i
        s!"Files in mathlib cannot import the whole `{i.getId}` folder. \
        Doing so would cause imports to be unnecessarily slow."
    | `Mathlib.Tactic.Replace =>
      if mainModule != `Mathlib.Tactic then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Replace' defines a deprecated form of the 'replace' tactic; \
          please do not use it in mathlib."
    | `Mathlib.Tactic.Have =>
      if ![`Mathlib.Tactic, `Mathlib.Tactic.Replace].contains mainModule then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Have' defines a deprecated form of the 'have' tactic; \
          please do not use it in mathlib."
    | modName =>
      if modName.getRoot == `Lake then
      Linter.logLint linter.style.header i
        "In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter \
        (see e.g. https://github.com/leanprover-community/mathlib4/pull/13779). Please consider carefully if this import is useful and \
        make sure to benchmark it. If this is fine, feel free to silence this linter."

/--
Definition of `collectAtoms` / `collectAtoms` 的定义

English:
definition collectAtoms
  signature: (s : Syntax)
  body: if s.isAtom then
    #[s.getAtomVal]
  else
    (s.getArgs.map collectAtoms).flatten

中文:
定义 collectAtoms
  签名: (s : Syntax)
  定义体: if s.isAtom then
    #[s.getAtomVal]
  else
    (s.getArgs.map collectAtoms).flatten
-/
partial def collectAtoms (s : Syntax) : Array String :=
  if s.isAtom then
    #[s.getAtomVal]
  else
    (s.getArgs.map collectAtoms).flatten

/--
Definition of `importInfo` / `importInfo` 的定义

English:
definition importInfo
  signature: (importStx : Syntax)
  body: do
  guard (importStx.isOfKind `Lean.Parser.Module.import)
  let args := importStx.getArgs
.back? let moduleId ← args.filter (·.isIdent)
  -- Check for modifiers by collecting all atoms and checking for keywords
  let allAtoms := collectAtoms importStx
  let isPublic := allAtoms.contains "public"
  

中文:
定义 importInfo
  签名: (importStx : Syntax)
  定义体: do
  guard (importStx.isOfKind `Lean.Parser.Module.import)
  let args := importStx.getArgs
.back? let moduleId ← args.filter (·.isIdent)
  -- Check for modifiers by collecting all atoms and checking for keywords
  let allAtoms := collectAtoms importStx
  let isPublic := allAtoms.contains "public"
  
-/
def importInfo (importStx : Syntax) : Option (Syntax × Bool × Bool × Bool) := do
  guard (importStx.isOfKind `Lean.Parser.Module.import)
  let args := importStx.getArgs
.back? let moduleId ← args.filter (·.isIdent)
  -- Check for modifiers by collecting all atoms and checking for keywords
  let allAtoms := collectAtoms importStx
  let isPublic := allAtoms.contains "public"
  let isMeta := allAtoms.contains "meta"
  let isAll := allAtoms.contains "all"
  return (moduleId, isPublic, isMeta, isAll)

/--
Definition of `duplicateImportsCheck` / `duplicateImportsCheck` 的定义

English:
definition duplicateImportsCheck
  signature: (imports : Array Syntax)
  body: do
  let mut importsSoFar := #[]
  for imp in imports do
    if let some info := importInfo imp then
      if importsSoFar.contains info then
        let (modId, _, _, _) := info
        Linter.logLint linter.style.header modId m!"Duplicate imports: '{modId}' already imported"
      else
        imp

中文:
定义 duplicateImportsCheck
  签名: (imports : 数组 Syntax)
  定义体: do
  let mut importsSoFar := #[]
  for imp in imports do
    if let some info := importInfo imp then
      if importsSoFar.contains info then
        let (modId, _, _, _) := info
        Linter.logLint linter.style.header modId m!"Duplicate imports: '{modId}' already imported"
      else
        imp
-/
def duplicateImportsCheck (imports : Array Syntax) : CommandElabM Unit := do
  let mut importsSoFar := #[]
  for imp in imports do
    if let some info := importInfo imp then
      if importsSoFar.contains info then
        let (modId, _, _, _) := info
        Linter.logLint linter.style.header modId m!"Duplicate imports: '{modId}' already imported"
      else
        importsSoFar := importsSoFar.push info

/--
Definition of `headerTestFiles` / `headerTestFiles` 的定义

English:
definition headerTestFiles
  signature: : NameSet
  body: .ofList
  [`MathlibTest.Linter.Header.Basic, `MathlibTest.Linter.Header.Fail, `MathlibTest.Linter.Header.Verso,
  `MathlibTest.DirectoryDependencyLinter.Test]

@[inherit_doc Mathlib.Linter.linter.style.header]

中文:
定义 headerTestFiles
  签名: : NameSet
  定义体: .ofList
  [`MathlibTest.Linter.Header.Basic, `MathlibTest.Linter.Header.Fail, `MathlibTest.Linter.Header.Verso,
  `MathlibTest.DirectoryDependencyLinter.Test]

@[inherit_doc Mathlib.Linter.linter.style.header]

Depends on / 依赖: ofList
-/
def headerTestFiles : NameSet := .ofList
  [`MathlibTest.Linter.Header.Basic, `MathlibTest.Linter.Header.Fail, `MathlibTest.Linter.Header.Verso,
  `MathlibTest.DirectoryDependencyLinter.Test]

@[inherit_doc Mathlib.Linter.linter.style.header]
/--
Definition of `headerLinter` / `headerLinter` 的定义

English:
definition headerLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  let mainModule ← getMainModule
  unless getLinterValue linter.style.header (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let inLibraryRoot? ← inLibraryRootMutex.atomically do
    match ← get with
    | some d => return d
    | no

中文:
定义 headerLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  let mainModule ← getMainModule
  unless getLinterValue linter.style.header (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let inLibraryRoot? ← inLibraryRootMutex.atomically do
    match ← get with
    | some d => return d
    | no

Depends on / 依赖: withSetOptionIn
-/
def headerLinter : Linter where run := withSetOptionIn fun stx => do
  let mainModule ← getMainModule
  unless getLinterValue linter.style.header (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let inLibraryRoot? ← inLibraryRootMutex.atomically do
    match ← get with
    | some d => return d
    | none =>
      let val ← isInLibraryRoot mainModule
      -- We cache the answer to avoid recomputing it on every command. The fill runs under the mutex
      -- so that concurrent (async) linter runs don't all miss the cache and each redundantly parse
      -- the library root file; `mainModule` is fixed for the duration of the elaboration.
      set (some val)
      return val
  -- The linter skips files not imported in their library root (e.g. `Mathlib.lean`), to avoid
  -- linting "scratch files". It is however active in the test files for the linter itself.
  unless inLibraryRoot? || headerTestFiles.contains mainModule do return
  -- Skip linting the library root file itself.
  -- In practice, the `inLibraryRoot?` check above already covers this (a well-formed `<root>.lean`
  -- does not import itself), but a root module could appear in `headerTestFiles`.
  if mainModule == mainModule.getRoot then return
  let fm ← getFileMap
  let mdDocs := (getMainModuleDoc (← getEnv)).toArray
  let versoDocs := (getMainVersoModuleDocs (← getEnv)).snippets
  -- The end of the first module doc-string, or the end of the file if there is none.
  -- For robustness, we assume Markdown and Verso docstrings can be arbitrarily mixed,
  -- so we get the end pos for both types of docstrings and take their minimum as the first.
  let firstMDDocModPos := match mdDocs[0]? with
  | none => fm.positions.back!
  | some doc => fm.ofPosition doc.declarationRange.endPos
  let firstVersoDocModPos := match versoDocs[0]? with
  | none => fm.positions.back!
  | some doc => fm.ofPosition doc.declarationRange.endPos
  let firstDocModPos := min firstMDDocModPos firstVersoDocModPos
  unless stx.getTailPos?.getD default <= firstDocModPos do
    return
  -- We try to parse the file up to `firstDocModPos`.
let upToStx ← parseUpToHere firstDocModPos > (do
    -- If parsing failed, there is some command which is not a module docstring.
    -- In that case, we parse until the end of the imports and add an extra `section` afterwards,
    -- so we trigger a "no module doc-string" warning.
    let fil ← getFileName
    let (stx, _) ← Parser.parseHeader { inputString := fm.source, fileName := fil, fileMap := fm }
    parseUpToHere (stx.raw.getTailPos?.getD default) "\nsection")
  let importIds := getImportIds upToStx
  let imports := getImports upToStx
  let afterImports := firstNonImport? upToStx
  -- Deprecated module files are exempt from all header style checks (copyright, doc-string,
  -- directory dependency, etc.) since they are just import-redirect stubs.
  if let some (.node _ ``Lean.Parser.Command.deprecated_module _) := afterImports then return
  -- Report on broad or duplicate imports.
  broadImportsCheck importIds mainModule
  duplicateImportsCheck imports
  let errors ← directoryDependencyCheck mainModule
  if errors.size > 0 then
    let mut msgs := ""
    for msg in errors do
      msgs := msgs ++ "\n\n" ++ (← msg.toString)
    Linter.logLint linter.directoryDependency stx msgs.trimAsciiStart.copy
  if afterImports.isNone then return
  let copyright := match upToStx.getHeadInfo with
    | .original lead .. => lead.toString
    | _ => ""
  -- Report any errors about the copyright line.
  if mainModule != `Mathlib.Init && mainModule != `Mathlib.Tactic then
    let expectedLicense := linter.style.header.license.get (← getOptions)
    for (stx, m) in copyrightHeaderChecks copyright expectedLicense do
      Linter.logLint linter.style.header stx m!"* '{stx.getAtomVal}':\n{m}\n"
  -- Report a missing module doc-string.
  match afterImports with
    | none => return
    | some (.node _ ``Lean.Parser.Command.moduleDoc _) => return
    | some (.node _ ``Lean.Parser.Command.eoi _) => return
    | some rest =>
    Linter.logLint linter.style.header rest
      m!"The module doc-string for a file should be the first command after the imports.\n\
       Please, add a module doc-string before `{stx}`."

initialize addLinter headerLinter

end Style.header

end Mathlib.Linter
