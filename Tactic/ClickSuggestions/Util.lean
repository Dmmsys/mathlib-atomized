/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import ProofWidgets.Component.MakeEditLink
public import ProofWidgets.Component.RefreshComponent
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.DepRewrite
public import Batteries.Tactic.PermuteGoals
public meta import Mathlib.Data.String.Defs
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-!
# Various utilities used in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx Server

section

open Widget PrettyPrinter.Delaborator

/--
Definition of `exprToHtml` / `exprToHtml` 的定义

English:
definition exprToHtml
  signature: (e : Expr)
  body: return <InteractiveCode fmt={← Widget.ppExprTagged e}/>

中文:
定义 exprToHtml
  签名: (e : Expr)
  定义体: return <InteractiveCode fmt={← Widget.ppExprTagged e}/>

Depends on / 依赖: InteractiveCode, Widget, Widget.ppExprTagged, ppExprTagged, return
-/
def exprToHtml (e : Expr) : MetaM Html :=
  return <InteractiveCode fmt={← Widget.ppExprTagged e}/>

/--
Definition of `constToHtml` / `constToHtml` 的定义

English:
definition constToHtml
  signature: (n : Name)
  body: do
let delab := withOptionAtCurrPos `pp.tagAppFns true delabConst
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos (delab := delab) (← mkConstWithLevelParams n)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt}/>

中文:
定义 constToHtml
  签名: (n : Name)
  定义体: do
let delab := withOptionAtCurrPos `pp.tagAppFns true delabConst
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos (delab := delab) (← mkConstWithLevelParams n)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt}/>
-/
def constToHtml (n : Name) : MetaM Html := do
let delab := withOptionAtCurrPos `pp.tagAppFns true delabConst
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos (delab := delab) (← mkConstWithLevelParams n)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt}/>

/--
Definition of `formatToHtmlWithDoc` / `formatToHtmlWithDoc` 的定义

English:
definition formatToHtmlWithDoc
  signature: (fmt : Format) (n : Name)
  body: do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
let infos := .insert ∅ tag .ofCommandInfo
    { elaborator := `ClickSuggestions, stx := .node .none n #[] }
let tt := TaggedText.prettyTagged .tag tag fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  -- TODO: I would love to print this using the same keyword colour used by the editor,
  -- but I don't think this is possible. Additionally, `InteractiveCode` already overwrites the
  -- colour and style of the text (namely the expression style)
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt} />

中文:
定义 formatToHtmlWithDoc
  签名: (fmt : Format) (n : Name)
  定义体: do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
let infos := .insert ∅ tag .ofCommandInfo
    { elaborator := `ClickSuggestions, stx := .node .none n #[] }
let tt := TaggedText.prettyTagged .tag tag fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  -- TODO: I would love to print this using the same keyword colour used by the editor,
  -- but I don't think this is possible. Additionally, `InteractiveCode` already overwrites the
  -- colour and style of the text (namely the expression style)
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt} />
-/
def formatToHtmlWithDoc (fmt : Format) (n : Name) : MetaM Html := do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
let infos := .insert ∅ tag .ofCommandInfo
    { elaborator := `ClickSuggestions, stx := .node .none n #[] }
let tt := TaggedText.prettyTagged .tag tag fmt
  let ctx := {
    env := (← getEnv)
    mctx := (← getMCtx)
    options := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls := (← getOpenDecls)
    fileMap := default
    ngen := (← getNGen)
  }
  -- TODO: I would love to print this using the same keyword colour used by the editor,
  -- but I don't think this is possible. Additionally, `InteractiveCode` already overwrites the
  -- colour and style of the text (namely the expression style)
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt} />


/--
Definition of `tacticToHtml` / `tacticToHtml` 的定义

English:
definition tacticToHtml
  signature: (tac : TSyntax `tactic)
  body: do
  formatToHtmlWithDoc (← PrettyPrinter.ppTactic tac) tac.1.getKind

中文:
定义 tacticToHtml
  签名: (tac : TSyntax `tactic)
  定义体: do
  formatToHtmlWithDoc (← PrettyPrinter.ppTactic tac) tac.1.getKind
-/
def tacticToHtml (tac : TSyntax `tactic) : MetaM Html := do
  formatToHtmlWithDoc (← PrettyPrinter.ppTactic tac) tac.1.getKind

end

/-- Let `#click_suggestions` show the candidate lemmas that failed to apply. -/
register_option click_suggestions.debug : Bool := {
  defValue := false
  descr := "let `#click_suggestions` show the candidate lemmas that failed to apply"
}

/--
Inductive type `Premise` / 归纳类型 `Premise`

English:
inductive Premise
  parameters: where
  constructors (2):
    - const: (declName : Name)
    - fvar: (fvarId : FVarId)

中文:
归纳类型 Premise
  参数: where
  构造子 (2 个):
    - const: (declName : Name)
    - fvar: (fvarId : FVarId)
-/
inductive Premise where
  /-- A global constant. -/
  | const (declName : Name)
  /-- A free variable. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited

namespace Premise

/--
Definition of `toString` / `toString` 的定义

English:
definition toString
  signature: : Premise -> String

中文:
定义 toString
  签名: : Premise -> String
-/
def toString : Premise -> String
  | .const name | .fvar ⟨name⟩ => name.toString

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (premise : Premise)
  body: premise.toString.length

中文:
定义 length
  签名: (premise : Premise)
  定义体: premise.toString.length

Depends on / 依赖: length, premise, premise.toString.length, toString
-/
def length (premise : Premise) : Nat :=
  premise.toString.length

/--
Definition of `getType` / `getType` 的定义

English:
definition getType
  signature: : Premise -> MetaM Expr

中文:
定义 getType
  签名: : Premise -> MetaM Expr
-/
def getType : Premise -> MetaM Expr
| .const name => (·.type) < > getConstInfo name
  | .fvar fvarId => fvarId.getType

/--
Definition of `forallMetaTelescopeReducing` / `forallMetaTelescopeReducing` 的定义

English:
definition forallMetaTelescopeReducing
  signature: : Premise -> MetaM (Expr × Array Expr × Array BinderInfo × Expr)

中文:
定义 对任意MetaTelescopeReducing
  签名: : Premise -> MetaM (Expr × 数组 Expr × 数组 BinderInfo × Expr)
-/
def forallMetaTelescopeReducing : Premise -> MetaM (Expr × Array Expr × Array BinderInfo × Expr)
  | .const name => do
    let thm ← mkConstWithFreshMVarLevels name
    let result ← Meta.forallMetaTelescopeReducing (← inferType thm)
    return (mkAppN thm result.1, result)
  | .fvar fvarId => do
    let decl ← fvarId.getDecl
    let result ← Meta.forallMetaTelescopeReducing (← instantiateMVars decl.type)
    return (mkAppN decl.toExpr result.1, result)

/--
Definition of `unresolveName` / `unresolveName` 的定义

English:
definition unresolveName
  signature: : Premise -> MetaM Name

中文:
定义 unresolveName
  签名: : Premise -> MetaM Name

Depends on / 依赖: getOptions, getPPFullNames
-/
def unresolveName : Premise -> MetaM Name
  | .const name => do
    unresolveNameGlobalAvoidingLocals name (fullNames := getPPFullNames (← getOptions))
  | .fvar fvarId => fvarId.getUserName

/--
Definition of `toMessageData` / `toMessageData` 的定义

English:
definition toMessageData
  signature: : Premise -> MessageData

中文:
定义 toMessageData
  签名: : Premise -> MessageData
-/
def toMessageData : Premise -> MessageData
  | .const name => .ofConstName name
  | .fvar fvarId => .ofExpr (.fvar fvarId)

/--
Definition of `toHtml` / `toHtml` 的定义

English:
definition toHtml
  signature: : Premise -> MetaM Html

中文:
定义 toHtml
  签名: : Premise -> MetaM Html
-/
def toHtml : Premise -> MetaM Html
  | .const name => constToHtml name
  | .fvar fvarId => exprToHtml (.fvar fvarId)

end Premise

/--
Definition of `State` / `State` 的定义

English:
structure State
  parameters: where
  axioms and operations (3):
    - status : Std.HashMap String Nat  [default: {}]
    - progress : Bool  [default: false]
    - solvedSuggestions : Array Html  [default: #[]]

中文:
结构 State
  参数: where
  公理与运算 (3 个):
    - status : Std.HashMap String 自然数  [默认: {}]
    - progress : 布尔值  [默认: false]
    - solvedSuggestions : 数组 Html  [默认: #[]]
-/
structure State where
  /-- The ongoing computations. -/
  status : Std.HashMap String Nat := {}
  /-- Whether any progress has been made at all. If all computations have been finished
  and no progress has been made, then inform the user. -/
  progress : Bool := false
  /-- The suggestions that close the goal. -/
  solvedSuggestions : Array Html := #[]

/--
Definition of `Context` / `Context` 的定义

English:
structure Context
  parameters: where
  axioms and operations (10):
    - «meta» : DocumentMeta
    - cursorPos : Lsp.Position
    - onGoal : Option Nat
    - stx : Option (TSyntax `tactic)
    - masterToken : RefreshToken
    - statusToken : RefreshToken
    - solvedToken : RefreshToken
    - goal : MVarId
    - hyp? : Option FVarId
    - pos : SubExpr.Pos

中文:
结构 余ntext
  参数: where
  公理与运算 (10 个):
    - «meta» : DocumentMeta
    - cursorPos : Lsp.Position
    - onGoal : 选项类型 自然数
    - stx : 选项类型 (TSyntax `tactic)
    - masterToken : RefreshToken
    - statusToken : RefreshToken
    - solvedToken : RefreshToken
    - goal : MVarId
    - hyp? : 选项类型 FVarId
    - pos : SubExpr.Pos
-/
structure Context where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  cursorPos : Lsp.Position
  /-- Whether to use the `on_goal n =>` combinator. -/
  onGoal : Option Nat
  /-- The preceding piece of syntax, if available. It is not available if the cursor is
  at the start of the next tactic. This is used for merging consecutive `rw` tactics. -/
  stx : Option (TSyntax `tactic)
  /-- The token for updating the main HTML body of suggestions.
  This is used for displaying a message that no progress has happened. -/
  masterToken : RefreshToken
  /-- The token for the `⏳️` HTML that represents the state of the ongoing computations. -/
  statusToken : RefreshToken
  /-- The token for the solved goals. -/
  solvedToken : RefreshToken
  /-- The main goal. -/
  goal : MVarId
  /-- The selected hypothesis, if any. -/
  hyp? : Option FVarId
  /-- The position of the selected subexpression. -/
  pos : SubExpr.Pos

/--
Definition of `ClickSuggestionsM` / `ClickSuggestionsM` 的定义

English:
abbreviation ClickSuggestionsM
  body: ReaderT Context ReaderT (IO.Ref State) MetaM

中文:
缩写 ClickSuggestionsM
  定义体: ReaderT Context ReaderT (IO.Ref State) MetaM

Depends on / 依赖: Context, IO.Ref, ReaderT
-/
abbrev ClickSuggestionsM := ReaderT Context ReaderT (IO.Ref State) MetaM

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadStateOf State ClickSuggestionsM
  body: do (← readThe (IO.Ref State)).get
  modifyGet s := do (← readThe (IO.Ref State)).modifyGet s
  set s := do (← readThe (IO.Ref State)).set s

中文:
实例 :
  签名: MonadStateOf State ClickSuggestionsM
  定义体: do (← readThe (IO.Ref State)).get
  modifyGet s := do (← readThe (IO.Ref State)).modifyGet s
  set s := do (← readThe (IO.Ref State)).set s

Depends on / 依赖: IO.Ref, readThe
-/
instance : MonadStateOf State ClickSuggestionsM where
  get := do (← readThe (IO.Ref State)).get
  modifyGet s := do (← readThe (IO.Ref State)).modifyGet s
  set s := do (← readThe (IO.Ref State)).set s

/--
Definition of `markProgress` / `markProgress` 的定义

English:
definition markProgress
  signature: : ClickSuggestionsM Unit
  body: do
  if !(← get).progress then
    modify ({ · with progress := true })

中文:
定义 markProgress
  签名: : ClickSuggestionsM 单元
  定义体: do
  if !(← get).progress then
    modify ({ · with progress := true })
-/
def markProgress : ClickSuggestionsM Unit := do
  if !(← get).progress then
    modify ({ · with progress := true })

/--
Definition of `checkProgress` / `checkProgress` 的定义

English:
definition checkProgress
  signature: : ClickSuggestionsM Unit
  body: do
  if !(← get).progress then
    if ((← get).status).isEmpty then
(← read).masterToken.update .text "No suggestions were found."

中文:
定义 checkProgress
  签名: : ClickSuggestionsM 单元
  定义体: do
  if !(← get).progress then
    if ((← get).status).isEmpty then
(← read).masterToken.update .text "No suggestions were found."
-/
private def checkProgress : ClickSuggestionsM Unit := do
  if !(← get).progress then
    if ((← get).status).isEmpty then
(← read).masterToken.update .text "No suggestions were found."

/--
Definition of `getHypIdent?` / `getHypIdent?` 的定义

English:
definition getHypIdent?
  signature: : ClickSuggestionsM (Option Ident)
  body: do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)

中文:
定义 getHypIdent?
  签名: : ClickSuggestionsM (选项类型 Ident)
  定义体: do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)
-/
def getHypIdent? : ClickSuggestionsM (Option Ident) := do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)

/--
Definition of `getHypIdent!` / `getHypIdent!` 的定义

English:
definition getHypIdent!
  signature: : ClickSuggestionsM Ident
  body: do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)

中文:
定义 getHypIdent!
  签名: : ClickSuggestionsM Ident
  定义体: do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)
-/
def getHypIdent! : ClickSuggestionsM Ident := do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)

/--
Definition of `trackingComputation` / `trackingComputation` 的定义

English:
definition trackingComputation
  signature: {α} (name : String) (k : ClickSuggestionsM α)
  body: do
  modify (fun s => { s with status := s.status.alter name fun
    | none => some 0
    | some n => some (n + 1) })
  renderStatus
  try k
  finally
    modify (fun s => { s with status := s.status.alter name fun
      | some (n + 1) => some n
      | _ => none })
    renderStatus
    checkProgress

中文:
定义 trackingComputation
  签名: {α} (name : String) (k : ClickSuggestionsM α)
  定义体: do
  modify (fun s => { s with status := s.status.alter name fun
    | none => some 0
    | some n => some (n + 1) })
  renderStatus
  try k
  finally
    modify (fun s => { s with status := s.status.alter name fun
      | some (n + 1) => some n
      | _ => none })
    renderStatus
    checkProgress
-/
def trackingComputation {α} (name : String) (k : ClickSuggestionsM α) : ClickSuggestionsM α := do
  modify (fun s => { s with status := s.status.alter name fun
    | none => some 0
    | some n => some (n + 1) })
  renderStatus
  try k
  finally
    modify (fun s => { s with status := s.status.alter name fun
      | some (n + 1) => some n
      | _ => none })
    renderStatus
    checkProgress
where
  /-- If the set of computations is non-empty, display a `⏳️` symbol with hover information that
  shows all of the ongoing computations. -/
  renderStatus : ClickSuggestionsM Unit := do
    let { status, .. } ← get
    let { statusToken, .. } ← read
statusToken.update
      if status.isEmpty then
        .text ""
      else
        -- TODO: use a fancier throbber instead of `⏳️`?
        let title := "ongoing computations: " ++ String.intercalate ", " status.keys;
        <span title={title}> {.text "⏳️"} </span>

section Meta

/--
Definition of `isExplicitEq` / `isExplicitEq` 的定义

English:
definition isExplicitEq
  signature: (t s : Expr)
  body: do
  let t := t.cleanupAnnotations; let s := s.cleanupAnnotations
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  -- TODO: let's just use `getFunInfo`.
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
withNewMCtxDepth withReducibleAndInstances isDefEq tArgs[i]! sArgs[i]!

中文:
定义 isExplicitEq
  签名: (t s : Expr)
  定义体: do
  let t := t.cleanupAnnotations; let s := s.cleanupAnnotations
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  -- TODO: let's just use `getFunInfo`.
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
withNewMCtxDepth withReducibleAndInstances isDefEq tArgs[i]! sArgs[i]!
-/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  let t := t.cleanupAnnotations; let s := s.cleanupAnnotations
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  -- TODO: let's just use `getFunInfo`.
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
withNewMCtxDepth withReducibleAndInstances isDefEq tArgs[i]! sArgs[i]!
where
  /-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
  getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
    let mut fnType ← inferType fn
    let mut result := Array.mkEmpty args.size
    let mut j := 0
    for i in [:args.size] do
      unless fnType.isForall do
        fnType ← whnfD (fnType.instantiateRevRange j i args)
        j := i
      let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
      fnType := b
      result := result.push bi
    return result

end Meta

section Syntax
open Syntax Parser.Tactic

/--
Inductive type `RwKind` / 归纳类型 `RwKind`

English:
inductive RwKind
  parameters: where
  constructors (2):
    - hasBVars: 
    - valid: (motiveTypeCorrect : Bool) (occ : Option Nat)

中文:
归纳类型 RwKind
  参数: where
  构造子 (2 个):
    - hasBVars: 
    - valid: (motiveTypeCorrect : 布尔值) (occ : 选项类型 自然数)

Depends on / 依赖: instead, suggest
-/
inductive RwKind where
  /-- `rw` cannot rewrite here, because the subexpression contains bound variables.
  So, we suggest `simp_rw`. -/
  | hasBVars
  /-- If `motiveTypeCorrect := true`, we suggest `rw!` instead of `rw`.
  If `occ := some n`, we suggest `nth_rw n` instead of `rw`. -/
  | valid (motiveTypeCorrect : Bool) (occ : Option Nat)

/--
Definition of `mkRewrite` / `mkRewrite` 的定义

English:
definition mkRewrite
  signature: (kind : RwKind) (symm : Bool) (e : Term) (loc : Option Ident)
  body: do
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  if grw then
    match kind with
    | .valid _ none => `(tactic| grw [$rule] $[at $loc:term]?)
    | .valid _ (some n) => `(tactic| nth_grw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| grw [$rule] $[at $loc:term]?)
  else
    match kind with
    | .valid true none => `(tactic| rw [$rule] $[at $loc:term]?)
    | .valid true (some n) => `(tactic| nth_rw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .valid false none => `(tactic| rw! [$rule] $[at $loc:term]?)
    | .valid false (some n) =>
      let occs ← `(optConfig| ($(mkIdent `occs):ident := .$(mkIdent `pos) [$(mkNatLit n)]))
      `(tactic| rw! $occs [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| simp_rw [$rule] $[at $loc:term]?)

中文:
定义 mkRewrite
  签名: (kind : RwKind) (symm : 布尔值) (e : 项) (loc : 选项类型 Ident)
  定义体: do
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  if grw then
    match kind with
    | .valid _ none => `(tactic| grw [$rule] $[at $loc:term]?)
    | .valid _ (some n) => `(tactic| nth_grw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| grw [$rule] $[at $loc:term]?)
  else
    match kind with
    | .valid true none => `(tactic| rw [$rule] $[at $loc:term]?)
    | .valid true (some n) => `(tactic| nth_rw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .valid false none => `(tactic| rw! [$rule] $[at $loc:term]?)
    | .valid false (some n) =>
      let occs ← `(optConfig| ($(mkIdent `occs):ident := .$(mkIdent `pos) [$(mkNatLit n)]))
      `(tactic| rw! $occs [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| simp_rw [$rule] $[at $loc:term]?)

Depends on / 依赖: TSyntax, tactic
-/
def mkRewrite (kind : RwKind) (symm : Bool) (e : Term) (loc : Option Ident)
    (grw := false) : CoreM (TSyntax `tactic) := do
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  if grw then
    match kind with
    | .valid _ none => `(tactic| grw [$rule] $[at $loc:term]?)
    | .valid _ (some n) => `(tactic| nth_grw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| grw [$rule] $[at $loc:term]?)
  else
    match kind with
    | .valid true none => `(tactic| rw [$rule] $[at $loc:term]?)
    | .valid true (some n) => `(tactic| nth_rw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .valid false none => `(tactic| rw! [$rule] $[at $loc:term]?)
    | .valid false (some n) =>
      let occs ← `(optConfig| ($(mkIdent `occs):ident := .$(mkIdent `pos) [$(mkNatLit n)]))
      `(tactic| rw! $occs [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| simp_rw [$rule] $[at $loc:term]?)

/--
Definition of `mergeTactics?` / `mergeTactics?` 的定义

English:
definition mergeTactics?
  signature: {m} [Monad m] [MonadQuotation m] (stx₁ stx₂ : TSyntax `tactic)
  body: do
  match stx₁, stx₂ with
  | `(tactic| on_goal $n₁ => $tac₁:tactic), `(tactic| on_goal $n₂ => $tac₂:tactic) =>
    if n₁.getNat == n₂.getNat then
      if let some tac ← mergeTactics? tac₁ tac₂ then
        return ← `(tactic| on_goal $n₁ => $tac:tactic)
  | `(tactic| rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| simp_rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| simp_rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| simp_rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| grw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| grw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| grw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | _, _ => pure ()
  return none

中文:
定义 mergeTactics?
  签名: {m} [单子 m] [MonadQuotation m] (stx₁ stx₂ : TSyntax `tactic)
  定义体: do
  match stx₁, stx₂ with
  | `(tactic| on_goal $n₁ => $tac₁:tactic), `(tactic| on_goal $n₂ => $tac₂:tactic) =>
    if n₁.getNat == n₂.getNat then
      if let some tac ← mergeTactics? tac₁ tac₂ then
        return ← `(tactic| on_goal $n₁ => $tac:tactic)
  | `(tactic| rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| simp_rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| simp_rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| simp_rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| grw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| grw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| grw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | _, _ => pure ()
  return none
-/
partial def mergeTactics? {m} [Monad m] [MonadQuotation m] (stx₁ stx₂ : TSyntax `tactic) :
    m (Option (TSyntax `tactic)) := do
  match stx₁, stx₂ with
  | `(tactic| on_goal $n₁ => $tac₁:tactic), `(tactic| on_goal $n₂ => $tac₂:tactic) =>
    if n₁.getNat == n₂.getNat then
      if let some tac ← mergeTactics? tac₁ tac₂ then
        return ← `(tactic| on_goal $n₁ => $tac:tactic)
  | `(tactic| rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| simp_rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| simp_rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| simp_rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| grw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| grw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| grw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | _, _ => pure ()
  return none

/--
Definition of `tacticPasteString` / `tacticPasteString` 的定义

English:
definition tacticPasteString
  signature: (tac : TSyntax `tactic)
  body: do
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

中文:
定义 tacticPasteString
  签名: (tac : TSyntax `tactic)
  定义体: do
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column
-/
def tacticPasteString (tac : TSyntax `tactic) : ClickSuggestionsM String := do
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

/--
Definition of `mkInsertion` / `mkInsertion` 的定义

English:
definition mkInsertion
  signature: (tac : TSyntax `tactic)
  body: do
  if let some stx := (← read).stx then
    if let some tac ← mergeTactics? stx tac then
      if let some range := stx.raw.getRange? then
        let text := (← read).meta.text
        let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
        let extraWhitespace := range.stop.extract text.source endPos
        let tactic ← tacticPasteString tac
        return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac}\n{String.replicate (← read).cursorPos.character ' '}")

中文:
定义 mkInsertion
  签名: (tac : TSyntax `tactic)
  定义体: do
  if let some stx := (← read).stx then
    if let some tac ← mergeTactics? stx tac then
      if let some range := stx.raw.getRange? then
        let text := (← read).meta.text
        let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
        let extraWhitespace := range.stop.extract text.source endPos
        let tactic ← tacticPasteString tac
        return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac}\n{String.replicate (← read).cursorPos.character ' '}")
-/
def mkInsertion (tac : TSyntax `tactic) : ClickSuggestionsM (Lsp.Range × String) := do
  if let some stx := (← read).stx then
    if let some tac ← mergeTactics? stx tac then
      if let some range := stx.raw.getRange? then
        let text := (← read).meta.text
        let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
        let extraWhitespace := range.stop.extract text.source endPos
        let tactic ← tacticPasteString tac
        return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac}\n{String.replicate (← read).cursorPos.character ' '}")

end Syntax

section Widget

open Widget

/--
Definition of `mkSuggestion` / `mkSuggestion` 的定义

English:
definition mkSuggestion
  signature: (tac : TSyntax `tactic) (html : Html) (isClosing := false)
  body: do
  let tac ← match (← read).onGoal with
    | some n => `(tactic| on_goal $(Syntax.mkNatLit (n + 1)) => $tac:tactic)
    | none => pure tac
  let (range, newText) ← mkInsertion tac (← read)
  let buttonText := if isClosing then "[done] " else "[apply] "
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span style={json% { "white-space" : "pre"}} className="font-code">
    { .ofComponent MakeEditLink (.ofReplaceRange (← read).meta range newText) #[.text buttonText] }
    </span>;
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>

中文:
定义 mkSuggestion
  签名: (tac : TSyntax `tactic) (html : Html) (isClosing := false)
  定义体: do
  let tac ← match (← read).onGoal with
    | some n => `(tactic| on_goal $(Syntax.mkNatLit (n + 1)) => $tac:tactic)
    | none => pure tac
  let (range, newText) ← mkInsertion tac (← read)
  let buttonText := if isClosing then "[done] " else "[apply] "
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span style={json% { "white-space" : "pre"}} className="font-code">
    { .ofComponent MakeEditLink (.ofReplaceRange (← read).meta range newText) #[.text buttonText] }
    </span>;
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>
-/
def mkSuggestion (tac : TSyntax `tactic) (html : Html) (isClosing := false) :
    ClickSuggestionsM Html := do
  let tac ← match (← read).onGoal with
    | some n => `(tactic| on_goal $(Syntax.mkNatLit (n + 1)) => $tac:tactic)
    | none => pure tac
  let (range, newText) ← mkInsertion tac (← read)
  let buttonText := if isClosing then "[done] " else "[apply] "
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span style={json% { "white-space" : "pre"}} className="font-code">
    { .ofComponent MakeEditLink (.ofReplaceRange (← read).meta range newText) #[.text buttonText] }
    </span>;
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>

/--
Definition of `addSolvedSuggestion` / `addSolvedSuggestion` 的定义

English:
definition addSolvedSuggestion
  signature: (tac : TSyntax `tactic)
  body: do
  let html ← mkSuggestion tac (.text (← PrettyPrinter.ppTactic tac).pretty) (isClosing := true)
  modify fun s => { s with solvedSuggestions := s.solvedSuggestions.push html }
  (← read).solvedToken.update <details «open»={true}>
    <summary className="mv2 pointer">
    These tactics solve the goal: 🎉️
    </summary>
    {.element "div" #[] (← get).solvedSuggestions}
    </details>

中文:
定义 addSolvedSuggestion
  签名: (tac : TSyntax `tactic)
  定义体: do
  let html ← mkSuggestion tac (.text (← PrettyPrinter.ppTactic tac).pretty) (isClosing := true)
  modify fun s => { s with solvedSuggestions := s.solvedSuggestions.push html }
  (← read).solvedToken.update <details «open»={true}>
    <summary className="mv2 pointer">
    These tactics solve the goal: 🎉️
    </summary>
    {.element "div" #[] (← get).solvedSuggestions}
    </details>
-/
def addSolvedSuggestion (tac : TSyntax `tactic) : ClickSuggestionsM Unit := do
  let html ← mkSuggestion tac (.text (← PrettyPrinter.ppTactic tac).pretty) (isClosing := true)
  modify fun s => { s with solvedSuggestions := s.solvedSuggestions.push html }
  (← read).solvedToken.update <details «open»={true}>
    <summary className="mv2 pointer">
    These tactics solve the goal: 🎉️
    </summary>
    {.element "div" #[] (← get).solvedSuggestions}
    </details>

end Widget

/--
Definition of `kabstractFindsPositions` / `kabstractFindsPositions` 的定义

English:
definition kabstractFindsPositions
  signature: (e p : Expr) (targetPos : SubExpr.Pos)
  body: do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let foundRef ← IO.mkRef false
  let rec visit (e : Expr) (pos : SubExpr.Pos) : MetaM Unit := do
    let visitChildren : MetaM Unit := do
      match e with
      | .app f a => visit f pos.pushAppFn; visit a pos.pushAppArg
      | .mdata _ e => visit e pos
      | .proj _ _ e => visit e pos.pushProj
      | .letE _ t v b _ =>
        visit t pos.pushLetVarType; visit v pos.pushLetValue; visit b pos.pushLetBody
      | .lam _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | _ => pure ()
    if e.hasLooseBVars then
      visitChildren
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren
    else
      if ← isDefEq e p then
        if pos == targetPos then
          foundRef.set true
        else
          throwError "{p} unified with {e}"
      else
        if pos == targetPos then
          throwError "{p} did not unify with {e}"
        else
          visitChildren
  try
    visit e .root
    foundRef.get
  catch _ =>
    return false

中文:
定义 kabstractFindsPositions
  签名: (e p : Expr) (targetPos : SubExpr.Pos)
  定义体: do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let foundRef ← IO.mkRef false
  let rec visit (e : Expr) (pos : SubExpr.Pos) : MetaM Unit := do
    let visitChildren : MetaM Unit := do
      match e with
      | .app f a => visit f pos.pushAppFn; visit a pos.pushAppArg
      | .mdata _ e => visit e pos
      | .proj _ _ e => visit e pos.pushProj
      | .letE _ t v b _ =>
        visit t pos.pushLetVarType; visit v pos.pushLetValue; visit b pos.pushLetBody
      | .lam _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | _ => pure ()
    if e.hasLooseBVars then
      visitChildren
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren
    else
      if ← isDefEq e p then
        if pos == targetPos then
          foundRef.set true
        else
          throwError "{p} unified with {e}"
      else
        if pos == targetPos then
          throwError "{p} did not unify with {e}"
        else
          visitChildren
  try
    visit e .root
    foundRef.get
  catch _ =>
    return false
-/
def kabstractFindsPositions (e p : Expr) (targetPos : SubExpr.Pos) : MetaM Bool := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let foundRef ← IO.mkRef false
  let rec visit (e : Expr) (pos : SubExpr.Pos) : MetaM Unit := do
    let visitChildren : MetaM Unit := do
      match e with
      | .app f a => visit f pos.pushAppFn; visit a pos.pushAppArg
      | .mdata _ e => visit e pos
      | .proj _ _ e => visit e pos.pushProj
      | .letE _ t v b _ =>
        visit t pos.pushLetVarType; visit v pos.pushLetValue; visit b pos.pushLetBody
      | .lam _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | _ => pure ()
    if e.hasLooseBVars then
      visitChildren
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren
    else
      if ← isDefEq e p then
        if pos == targetPos then
          foundRef.set true
        else
          throwError "{p} unified with {e}"
      else
        if pos == targetPos then
          throwError "{p} did not unify with {e}"
        else
          visitChildren
  try
    visit e .root
    foundRef.get
  catch _ =>
    return false

end Mathlib.Tactic.ClickSuggestions
