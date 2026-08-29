/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module

public meta import Lean.Elab.MacroArgUtil
public meta import Lean.PrettyPrinter.Delaborator -- shake: keep (dependency of elaborator output)
public meta import Mathlib.Lean.PrettyPrinter.Delaborator
public meta import Batteries.Lean.Syntax
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Batteries.Linter.UnreachableTactic
public import Batteries.Util.ExtendedBinder
public import Lean.Elab.AuxDef
public import Mathlib.Lean.Elab.Term
public import Mathlib.Tactic.ScopedNS

/-!
# The notation3 macro, simulating Lean 3's notation.
-/

public meta section

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Mathlib.Notation3
open Lean Parser Meta Elab Command PrettyPrinter.Delaborator SubExpr
open Batteries.ExtendedBinder

initialize registerTraceClass `notation3

/-! ### Syntaxes supporting `notation3` -/

/--
Expands binders into nested combinators.
For example, the familiar exists is given by:
`expand_binders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expand_binders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expand_binders% ($x => $term) $y:extBinder, $res) =>
    `(expand_binders% ($x => $term) ($y:extBinder), $res)
  | `(expand_binders% ($_ => $_), $res) => pure res
macro_rules
  | `(expand_binders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident : $ty => expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) (_%$ph $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun _%$ph : $ty => expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) ($y:binderIdent $pred:binderPred) $binders*, $res) => do
    let y ←
      match y with
      | `(binderIdent| $y:ident) => pure y
      | `(binderIdent| _) => Term.mkFreshIdent y
      | _ => Macro.throwUnsupported
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident => expand_binders% ($x => $term) (h : satisfies_binder_pred% $y $pred)
 [$binders]*, res)

macro (name := expandFoldl) "expand_foldl% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg => do
    term.replaceM fun e =>
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expand_foldr% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res => do
    term.replaceM fun e =>
      return if e == x then some arg else if e == y then some res else none

/-- Keywording indicating whether to use a left- or right-fold. -/
syntax foldKind := &"foldl" > &"foldr"
/-- `notation3` argument matching `extBinders`. -/
syntax bindersItem := atomic("(" "..." ")")
/-- `notation3` argument simulating a Lean 3 fold notation. -/
syntax foldAction := "(" ident ppSpace strLit "*" (precedence)? " => " foldKind
  " (" ident ppSpace ident " => " term ") " term ")"
/-- `notation3` argument binding a name. -/
syntax identOptScoped :=
  ident (notFollowedBy(":" "(" "scoped") precedence)? (":" "(" "scoped " ident " => " term ")")?
/-- `notation3` argument. -/
-- Note: there is deliberately no ppSpace between items
-- so that the space in the literals themselves stands out
syntax notation3Item := strLit > bindersItem > identOptScoped > foldAction

/-! ### Expression matching

A more complicated part of `notation3` is the delaborator generator.
While `notation` relies on generating app unexpanders, we instead generate a
delaborator directly so that we can control how binders are formatted (we want
to be able to know the types of binders, whether a lambda is a constant function,
and whether it is `Prop`-valued, which are not things we can answer once we pass
to app unexpanders).
-/

/--
Definition of `MatchState` / `MatchState` 的定义

English:
structure MatchState
  parameters: where
  axioms and operations (3):
    - vars : Std.HashMap Name (SubExpr × LocalContext × LocalInstances)
    - scopeState : Option (Array (TSyntax ``extBinderParenthesized))
    - foldState : Std.HashMap Name (Array Term)

中文:
结构 MatchState
  参数: where
  公理与运算 (3 个):
    - vars : Std.HashMap Name (SubExpr × LocalContext × LocalInstances)
    - scopeState : Option (Array (TSyntax ``extBinderParenthesized))
    - foldState : Std.HashMap Name (Array Term)
-/
structure MatchState where
  /-- This stores the assignments of variables to subexpressions (and their contexts)
  that have been found so far during the course of the matching algorithm.
  We store the contexts since we need to delaborate expressions after we leave
  scoping constructs. -/
  vars : Std.HashMap Name (SubExpr × LocalContext × LocalInstances)
  /-- The binders accumulated while matching a `scoped` expression. -/
  scopeState : Option (Array (TSyntax ``extBinderParenthesized))
  /-- The arrays of delaborated `Term`s accumulated while matching
  `foldl` and `foldr` expressions. For `foldl`, the arrays are stored in reverse order. -/
  foldState : Std.HashMap Name (Array Term)

/--
Definition of `Matcher` / `Matcher` 的定义

English:
definition Matcher
  body: MatchState -> DelabM MatchState
  deriving Inhabited

中文:
定义 Matcher
  定义体: MatchState -> DelabM MatchState
  deriving Inhabited
-/
@[expose] def Matcher := MatchState -> DelabM MatchState
  deriving Inhabited

/--
Definition of `MatchState.empty` / `MatchState.empty` 的定义

English:
definition MatchState.empty
  signature: : MatchState where
  body: {}
  scopeState := none
  foldState := {}

中文:
定义 MatchState.empty
  签名: : MatchState where
  定义体: {}
  scopeState := none
  foldState := {}
-/
def MatchState.empty : MatchState where
  vars := {}
  scopeState := none
  foldState := {}

/--
Definition of `MatchState.withVar` / `MatchState.withVar` 的定义

English:
definition MatchState.withVar
  signature: {α : Type} (s : MatchState) (name : Name)
  body: do
  let some (se, lctx, linsts) := s.vars[name]? | failure
withLCtx lctx linsts withTheReader SubExpr (fun _ => se) m

中文:
定义 MatchState.withVar
  签名: {α : Type} (s : MatchState) (name : Name)
  定义体: do
  let some (se, lctx, linsts) := s.vars[name]? | failure
withLCtx lctx linsts withTheReader SubExpr (fun _ => se) m
-/
def MatchState.withVar {α : Type} (s : MatchState) (name : Name)
    (m : DelabM α) : DelabM α := do
  let some (se, lctx, linsts) := s.vars[name]? | failure
withLCtx lctx linsts withTheReader SubExpr (fun _ => se) m

/--
Definition of `MatchState.delabVar` / `MatchState.delabVar` 的定义

English:
definition MatchState.delabVar
  signature: (s : MatchState) (name : Name) (checkNot? : Option Expr := none)
  body: s.withVar name do
    if let some checkNot := checkNot? then
guard checkNot != (← getExpr)
    delab

中文:
定义 MatchState.delabVar
  签名: (s : MatchState) (name : Name) (checkNot? : Option Expr := none)
  定义体: s.withVar name do
    if let some checkNot := checkNot? then
guard checkNot != (← getExpr)
    delab
-/
def MatchState.delabVar (s : MatchState) (name : Name) (checkNot? : Option Expr := none) :
    DelabM Term :=
  s.withVar name do
    if let some checkNot := checkNot? then
guard checkNot != (← getExpr)
    delab

/--
Definition of `MatchState.captureSubexpr` / `MatchState.captureSubexpr` 的定义

English:
definition MatchState.captureSubexpr
  signature: (s : MatchState) (name : Name)
  body: do
  return {s with vars := s.vars.insert name (← readThe SubExpr, ← getLCtx, ← getLocalInstances)}

中文:
定义 MatchState.captureSubexpr
  签名: (s : MatchState) (name : Name)
  定义体: do
  return {s with vars := s.vars.insert name (← readThe SubExpr, ← getLCtx, ← getLocalInstances)}
-/
def MatchState.captureSubexpr (s : MatchState) (name : Name) : DelabM MatchState := do
  return {s with vars := s.vars.insert name (← readThe SubExpr, ← getLCtx, ← getLocalInstances)}

/--
Definition of `MatchState.getFoldArray` / `MatchState.getFoldArray` 的定义

English:
definition MatchState.getFoldArray
  signature: (s : MatchState) (name : Name)
  body: s.foldState[name]?.getD #[]

中文:
定义 MatchState.getFoldArray
  签名: (s : MatchState) (name : Name)
  定义体: s.foldState[name]?.getD #[]

Depends on / 依赖: foldState, s.foldState
-/
def MatchState.getFoldArray (s : MatchState) (name : Name) : Array Term :=
  s.foldState[name]?.getD #[]

/--
Definition of `MatchState.getBinders` / `MatchState.getBinders` 的定义

English:
definition MatchState.getBinders
  signature: (s : MatchState)
  body: s.scopeState.getD #[]

中文:
定义 MatchState.getBinders
  签名: (s : MatchState)
  定义体: s.scopeState.getD #[]

Depends on / 依赖: s.scopeState.getD, scopeState
-/
def MatchState.getBinders (s : MatchState) : Array (TSyntax ``extBinderParenthesized) :=
  s.scopeState.getD #[]

/--
Definition of `MatchState.pushFold` / `MatchState.pushFold` 的定义

English:
definition MatchState.pushFold
  signature: (s : MatchState) (name : Name) (t : Term)
  body: let ts := (s.getFoldArray name).push t
  {s with foldState := s.foldState.insert name ts}

中文:
定义 MatchState.pushFold
  签名: (s : MatchState) (name : Name) (t : Term)
  定义体: let ts := (s.getFoldArray name).push t
  {s with foldState := s.foldState.insert name ts}

Depends on / 依赖: foldState, getFoldArray, insert, s.foldState.insert, s.getFoldArray
-/
def MatchState.pushFold (s : MatchState) (name : Name) (t : Term) : MatchState :=
  let ts := (s.getFoldArray name).push t
  {s with foldState := s.foldState.insert name ts}

/--
Definition of `matchVar` / `matchVar` 的定义

English:
definition matchVar
  signature: (c : Name)
  body: fun s => do
  if let some (se, _, _) := s.vars[c]? then
guard se.expr == (← getExpr)
    return s
  else
    s.captureSubexpr c

中文:
定义 matchVar
  签名: (c : Name)
  定义体: fun s => do
  if let some (se, _, _) := s.vars[c]? then
guard se.expr == (← getExpr)
    return s
  else
    s.captureSubexpr c
-/
def matchVar (c : Name) : Matcher := fun s => do
  if let some (se, _, _) := s.vars[c]? then
guard se.expr == (← getExpr)
    return s
  else
    s.captureSubexpr c

/--
Definition of `matchExpr` / `matchExpr` 的定义

English:
definition matchExpr
  signature: (p : Expr -> Bool)
  body: fun s => do
guard p (← getExpr)
  return s

中文:
定义 matchExpr
  签名: (p : Expr -> 布尔)
  定义体: fun s => do
guard p (← getExpr)
  return s
-/
def matchExpr (p : Expr -> Bool) : Matcher := fun s => do
guard p (← getExpr)
  return s

/--
Definition of `matchFVar` / `matchFVar` 的定义

English:
definition matchFVar
  signature: (userName : Name) (matchTy : Matcher)
  body: fun s => do
  let .fvar fvarId ← getExpr | failure
guard userName == (← fvarId.getUserName)
  withType (matchTy s)

中文:
定义 matchFVar
  签名: (userName : Name) (matchTy : Matcher)
  定义体: fun s => do
  let .fvar fvarId ← getExpr | failure
guard userName == (← fvarId.getUserName)
  withType (matchTy s)
-/
def matchFVar (userName : Name) (matchTy : Matcher) : Matcher := fun s => do
  let .fvar fvarId ← getExpr | failure
guard userName == (← fvarId.getUserName)
  withType (matchTy s)

/--
Definition of `matchTypeOf` / `matchTypeOf` 的定义

English:
definition matchTypeOf
  signature: (matchTy : Matcher)
  body: fun s => do
  withType (matchTy s)

中文:
定义 matchTypeOf
  签名: (matchTy : Matcher)
  定义体: fun s => do
  withType (matchTy s)
-/
def matchTypeOf (matchTy : Matcher) : Matcher := fun s => do
  withType (matchTy s)

/--
Definition of `natLitMatcher` / `natLitMatcher` 的定义

English:
definition natLitMatcher
  signature: (n : Nat)
  body: fun s => do
guard (← getExpr).rawNatLit? == n
  return s

中文:
定义 natLitMatcher
  签名: (n : 自然数)
  定义体: fun s => do
guard (← getExpr).rawNatLit? == n
  return s
-/
def natLitMatcher (n : Nat) : Matcher := fun s => do
guard (← getExpr).rawNatLit? == n
  return s

/--
Definition of `matchApp` / `matchApp` 的定义

English:
definition matchApp
  signature: (matchFun matchArg : Matcher)
  body: fun s => do
guard (← getExpr).isApp
let s ← withAppFn matchFun s
let s ← withAppArg matchArg s
  return s

中文:
定义 matchApp
  签名: (matchFun matchArg : Matcher)
  定义体: fun s => do
guard (← getExpr).isApp
let s ← withAppFn matchFun s
let s ← withAppArg matchArg s
  return s
-/
def matchApp (matchFun matchArg : Matcher) : Matcher := fun s => do
guard (← getExpr).isApp
let s ← withAppFn matchFun s
let s ← withAppArg matchArg s
  return s

/--
Definition of `matchForall` / `matchForall` 的定义

English:
definition matchForall
  signature: (matchDom : Matcher) (matchBody : Expr -> Matcher)
  body: fun s => do
guard (← getExpr).isForall
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s

中文:
定义 matchForall
  签名: (matchDom : Matcher) (matchBody : Expr -> Matcher)
  定义体: fun s => do
guard (← getExpr).isForall
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s
-/
def matchForall (matchDom : Matcher) (matchBody : Expr -> Matcher) : Matcher := fun s => do
guard (← getExpr).isForall
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s

/--
Definition of `matchLambda` / `matchLambda` 的定义

English:
definition matchLambda
  signature: (matchDom : Matcher) (matchBody : Expr -> Matcher)
  body: fun s => do
guard (← getExpr).isLambda
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s

中文:
定义 matchLambda
  签名: (matchDom : Matcher) (matchBody : Expr -> Matcher)
  定义体: fun s => do
guard (← getExpr).isLambda
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s
-/
def matchLambda (matchDom : Matcher) (matchBody : Expr -> Matcher) : Matcher := fun s => do
guard (← getExpr).isLambda
let s ← withBindingDomain matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s

/--
Definition of `setupLCtx` / `setupLCtx` 的定义

English:
definition setupLCtx
  signature: (lctx : LocalContext) (boundNames : Array Name)
  body: do
  let mut lctx := lctx
  let mut boundFVars := {}
  for name in boundNames do
    let fvarId ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fvarId name (← withLCtx lctx (← getLocalInstances) mkFreshTypeMVar)
    boundFVars := boundFVars.insert fvarId name
  return (lctx, boundFVars)

中文:
定义 setupLCtx
  签名: (lctx : LocalContext) (boundNames : Array Name)
  定义体: do
  let mut lctx := lctx
  let mut boundFVars := {}
  for name in boundNames do
    let fvarId ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fvarId name (← withLCtx lctx (← getLocalInstances) mkFreshTypeMVar)
    boundFVars := boundFVars.insert fvarId name
  return (lctx, boundFVars)
-/
def setupLCtx (lctx : LocalContext) (boundNames : Array Name) :
    MetaM (LocalContext × Std.HashMap FVarId Name) := do
  let mut lctx := lctx
  let mut boundFVars := {}
  for name in boundNames do
    let fvarId ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fvarId name (← withLCtx lctx (← getLocalInstances) mkFreshTypeMVar)
    boundFVars := boundFVars.insert fvarId name
  return (lctx, boundFVars)

/--
Definition of `isType'` / `isType'` 的定义

English:
definition isType'
  signature: : Expr -> Bool

中文:
定义 isType'
  签名: : Expr -> 布尔
-/
def isType' : Expr -> Bool
  | .sort u => u.dec.isSome
  | _ => false

/--
Inductive type `DelabKey` / 归纳类型 `DelabKey`

English:
inductive DelabKey
  parameters: where
  constructors (2):
    - app: (const : Option Name) (arity : Nat)
    - other: (key : Name)

中文:
归纳类型 DelabKey
  参数: where
  构造子 (2 个):
    - app: (const : Option Name) (arity : 自然数)
    - other: (key : Name)
-/
inductive DelabKey where
  /-- The key `app.const` or `app` with a specific arity. -/
  | app (const : Option Name) (arity : Nat)
  | other (key : Name)
  deriving Repr

/--
Definition of `DelabKey.key` / `DelabKey.key` 的定义

English:
definition DelabKey.key
  signature: : DelabKey -> Name

中文:
定义 DelabKey.key
  签名: : DelabKey -> Name
-/
def DelabKey.key : DelabKey -> Name
  | .app none _ => `app
  | .app (some n) _ => `app ++ n
  | .other key => key

/--
Definition of `exprToMatcher` / `exprToMatcher` 的定义

English:
definition exprToMatcher
  signature: (boundFVars : Std.HashMap FVarId Name)
  body: do
  match e with
  | .mvar .. => return ([], ← `(pure))
  | .const n _ => return ([.app n 0], ← ``(matchExpr (Expr.isConstOf · $(quote n))))
  | .sort u =>
    /-
    We should try being more accurate here.
    Prop / Type / Type _ / Sort _ is at least an OK approximation.
    We mimic the core Sor

中文:
定义 exprToMatcher
  签名: (boundFVars : Std.HashMap FVarId Name)
  定义体: do
  match e with
  | .mvar .. => return ([], ← `(pure))
  | .const n _ => return ([.app n 0], ← ``(matchExpr (Expr.isConstOf · $(quote n))))
  | .sort u =>
    /-
    We should try being more accurate here.
    Prop / Type / Type _ / Sort _ is at least an OK approximation.
    We mimic the core Sor
-/
partial def exprToMatcher (boundFVars : Std.HashMap FVarId Name)
    (localFVars : Std.HashMap FVarId Term) (e : Expr) :
    OptionT TermElabM (List DelabKey × Term) := do
  match e with
  | .mvar .. => return ([], ← `(pure))
  | .const n _ => return ([.app n 0], ← ``(matchExpr (Expr.isConstOf · $(quote n))))
  | .sort u =>
    /-
    We should try being more accurate here.
    Prop / Type / Type _ / Sort _ is at least an OK approximation.
    We mimic the core Sort delaborator `Lean.PrettyPrinter.Delaborator.delabSort`.
    -/
    let matcher ←
      if u.isZero then
        ``(matchExpr Expr.isProp)
      else if e.isType0 then
        ``(matchExpr Expr.isType0)
      else if u.dec.isSome then
        ``(matchExpr isType')
      else
        ``(matchExpr Expr.isSort)
    return ([.other `sort], matcher)
  | .fvar fvarId =>
    if let some n := boundFVars[fvarId]? then
      -- This fvar is a pattern variable.
      return ([], ← ``(matchVar $(quote n)))
    else if let some s := localFVars[fvarId]? then
      -- This fvar is bound by a lambda or forall expression in the pattern itself
      return ([], ← ``(matchExpr (· == $s)))
    else
      let n ← fvarId.getUserName
      if n.hasMacroScopes then
        -- Match by just the type; this is likely an unnamed instance for example
        let (_, m) ← exprToMatcher boundFVars localFVars (← instantiateMVars (← inferType e))
        return ([.other `fvar], ← ``(matchTypeOf $m))
      else
        -- This is an fvar from a `variable`. Match by name and type.
        let (_, m) ← exprToMatcher boundFVars localFVars (← instantiateMVars (← inferType e))
        return ([.other `fvar], ← ``(matchFVar $(quote n) $m))
  | .app .. =>
    e.withApp fun f args => do
      let (keys, matchF) ←
        if let .const n _ := f then
          pure ([.app n args.size], ← ``(matchExpr (Expr.isConstOf · $(quote n))))
        else
          let (_, matchF) ← exprToMatcher boundFVars localFVars f
          pure ([.app none args.size], matchF)
      let mut fty ← inferType f
      let mut matcher := matchF
      for arg in args do
        fty ← whnf fty
        guard fty.isForall
        let bi := fty.bindingInfo!
        fty := fty.bindingBody!.instantiate1 arg
        if bi.isInstImplicit then
          -- Assumption: elaborated instances are canonical, so no need to match.
          -- The type of the instance is already accounted for by the previous arguments
          -- and the type of `f`.
          matcher ← ``(matchApp $matcher pure)
        else
          let (_, matchArg) ← exprToMatcher boundFVars localFVars arg
          matcher ← ``(matchApp $matcher $matchArg)
      return (keys, matcher)
  | .lit (.natVal n) => return ([.other `lit], ← ``(natLitMatcher $(quote n)))
  | .forallE n t b bi =>
    let (_, matchDom) ← exprToMatcher boundFVars localFVars t
    withLocalDecl n bi t fun arg => withFreshMacroScope do
      let n' ← `(n)
      let body := b.instantiate1 arg
      let localFVars' := localFVars.insert arg.fvarId! n'
      let (_, matchBody) ← exprToMatcher boundFVars localFVars' body
      return ([.other `forallE], ← ``(matchForall $matchDom (fun $n' => $matchBody)))
  | .lam n t b bi =>
    let (_, matchDom) ← exprToMatcher boundFVars localFVars t
    withLocalDecl n bi t fun arg => withFreshMacroScope do
      let n' ← `(n)
      let body := b.instantiate1 arg
      let localFVars' := localFVars.insert arg.fvarId! n'
      let (_, matchBody) ← exprToMatcher boundFVars localFVars' body
      return ([.other `lam], ← ``(matchLambda $matchDom (fun $n' => $matchBody)))
  | _ =>
    trace[notation3] "can't generate matcher for {e}"
    failure

/--
Definition of `mkExprMatcher` / `mkExprMatcher` 的定义

English:
definition mkExprMatcher
  signature: (stx : Term) (boundNames : Array Name)
  body: do
  let (lctx, boundFVars) ← setupLCtx (← getLCtx) boundNames
  withLCtx lctx (← getLocalInstances) do
    let patt ←
      try
        Term.elabPattern stx none
      catch e =>
        logException e
        trace[notation3] "Could not elaborate pattern{indentD stx}\nError: {e.toMessageData}"
   

中文:
定义 mkExprMatcher
  签名: (stx : Term) (boundNames : Array Name)
  定义体: do
  let (lctx, boundFVars) ← setupLCtx (← getLCtx) boundNames
  withLCtx lctx (← getLocalInstances) do
    let patt ←
      try
        Term.elabPattern stx none
      catch e =>
        logException e
        trace[notation3] "Could not elaborate pattern{indentD stx}\nError: {e.toMessageData}"
   
-/
partial def mkExprMatcher (stx : Term) (boundNames : Array Name) :
    OptionT TermElabM (List DelabKey × Term) := do
  let (lctx, boundFVars) ← setupLCtx (← getLCtx) boundNames
  withLCtx lctx (← getLocalInstances) do
    let patt ←
      try
        Term.elabPattern stx none
      catch e =>
        logException e
        trace[notation3] "Could not elaborate pattern{indentD stx}\nError: {e.toMessageData}"
        -- Convert the exception into an `OptionT` failure so that the `(prettyPrint := false)`
        -- suggestion appears.
        failure
    trace[notation3] "Generating matcher for pattern {patt}"
    exprToMatcher boundFVars {} patt

/--
Definition of `matchScoped` / `matchScoped` 的定义

English:
definition matchScoped
  signature: (lit scopeId : Name) (smatcher : Matcher)
  body: go #[] where
  /-- Variant of `matchScoped` after some number of `binders` have already been captured. -/
  go (binders : Array (TSyntax ``extBinderParenthesized)) : Matcher := fun s => do
    -- `lit` is bound to the SubExpr that the `scoped` syntax produced
    s.withVar lit do
    try
      -- Ru

中文:
定义 matchScoped
  签名: (lit scopeId : Name) (smatcher : Matcher)
  定义体: go #[] where
  /-- Variant of `matchScoped` after some number of `binders` have already been captured. -/
  go (binders : Array (TSyntax ``extBinderParenthesized)) : Matcher := fun s => do
    -- `lit` is bound to the SubExpr that the `scoped` syntax produced
    s.withVar lit do
    try
      -- Ru
-/
partial def matchScoped (lit scopeId : Name) (smatcher : Matcher) : Matcher := go #[] where
  /-- Variant of `matchScoped` after some number of `binders` have already been captured. -/
  go (binders : Array (TSyntax ``extBinderParenthesized)) : Matcher := fun s => do
    -- `lit` is bound to the SubExpr that the `scoped` syntax produced
    s.withVar lit do
    try
      -- Run `smatcher` at `lit`, clearing the `scopeId` variable so that it can get a fresh value
      let s ← smatcher {s with vars := s.vars.erase scopeId}
      s.withVar scopeId do
        guard (← getExpr).isLambda
        let prop ← try Meta.isProp (← getExpr).bindingDomain! catch _ => pure false
        let isDep := (← getExpr).bindingBody!.hasLooseBVar 0
        let ppTypes ← getPPOption getPPPiBinderTypes -- the same option controlling ∀
        let dom ← withBindingDomain delab
        withBindingBodyUnusedName fun x => do
          let x : Ident := ⟨x⟩
          let binder ←
            if prop && !isDep then
              -- this underscore is used to support binder predicates, since it indicates
              -- the variable is unused and this binder is safe to merge into another
              `(extBinderParenthesized|(_ : $dom))
            else if prop || ppTypes then
              `(extBinderParenthesized|($x:ident : $dom))
            else
              `(extBinderParenthesized|($x:ident))
          -- Now use the body of the lambda for `lit` for the next iteration
          let s ← s.captureSubexpr lit
          -- TODO merge binders as an inverse to `satisfies_binder_pred%`
          let binders := binders.push binder
          go binders s
    catch _ =>
guard !binders.isEmpty
      if let some binders₂ := s.scopeState then
guard binders == binders₂-- TODO: this might be a bit too strict, but it seems to work
        return s
      else
        return {s with scopeState := binders}

/--
Definition of `mkScopedMatcher` / `mkScopedMatcher` 的定义

English:
definition mkScopedMatcher
  signature: (lit scopeId : Name) (scopedTerm : Term) (boundNames : Array Name)
  body: do
  -- Build the matcher for `scopedTerm` with `scopeId` as an additional variable
  let (keys, smatcher) ← mkExprMatcher scopedTerm (boundNames.push scopeId)
  return (keys, ← ``(matchScoped $(quote lit) $(quote scopeId) $smatcher))

中文:
定义 mkScopedMatcher
  签名: (lit scopeId : Name) (scopedTerm : Term) (boundNames : Array Name)
  定义体: do
  -- Build the matcher for `scopedTerm` with `scopeId` as an additional variable
  let (keys, smatcher) ← mkExprMatcher scopedTerm (boundNames.push scopeId)
  return (keys, ← ``(matchScoped $(quote lit) $(quote scopeId) $smatcher))
-/
partial def mkScopedMatcher (lit scopeId : Name) (scopedTerm : Term) (boundNames : Array Name) :
    OptionT TermElabM (List DelabKey × Term) := do
  -- Build the matcher for `scopedTerm` with `scopeId` as an additional variable
  let (keys, smatcher) ← mkExprMatcher scopedTerm (boundNames.push scopeId)
  return (keys, ← ``(matchScoped $(quote lit) $(quote scopeId) $smatcher))

/--
Definition of `matchFoldl` / `matchFoldl` 的定义

English:
definition matchFoldl
  signature: (lit x y : Name) (smatcher : Matcher) (sinit : Matcher)
  body: fun s => do
  s.withVar lit do
    let expr ← getExpr
    -- Clear x and y state before running smatcher so it can store new values
    let s := {s with vars := s.vars |>.erase x |>.erase y}
let some s ← try some < > smatcher s catch _ => pure none
      | -- We put this here rather than using a big

中文:
定义 matchFoldl
  签名: (lit x y : Name) (smatcher : Matcher) (sinit : Matcher)
  定义体: fun s => do
  s.withVar lit do
    let expr ← getExpr
    -- Clear x and y state before running smatcher so it can store new values
    let s := {s with vars := s.vars |>.erase x |>.erase y}
let some s ← try some < > smatcher s catch _ => pure none
      | -- We put this here rather than using a big
-/
partial def matchFoldl (lit x y : Name) (smatcher : Matcher) (sinit : Matcher) :
    Matcher := fun s => do
  s.withVar lit do
    let expr ← getExpr
    -- Clear x and y state before running smatcher so it can store new values
    let s := {s with vars := s.vars |>.erase x |>.erase y}
let some s ← try some < > smatcher s catch _ => pure none
      | -- We put this here rather than using a big try block to prevent backtracking.
        -- We have `smatcher` match greedily, and then require that `sinit` *must* succeed
        sinit s
    -- y gives the next element of the list
    let s := s.pushFold lit (← s.delabVar y expr)
    -- x gives the next lit
    let some newLit := s.vars[x]? | failure
    -- If progress was not made, fail
    if newLit.1.expr == expr then failure
    -- Progress was made, so recurse
    let s := {s with vars := s.vars.insert lit newLit}
    matchFoldl lit x y smatcher sinit s

/--
Definition of `mkFoldlMatcher` / `mkFoldlMatcher` 的定义

English:
definition mkFoldlMatcher
  signature: (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name)
  body: do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quo

中文:
定义 mkFoldlMatcher
  签名: (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name)
  定义体: do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quo
-/
partial def mkFoldlMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name) :
    OptionT TermElabM (List DelabKey × Term) := do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote x) $(quote y) $smatcher $sinit))

/--
Definition of `mkFoldrMatcher` / `mkFoldrMatcher` 的定义

English:
definition mkFoldrMatcher
  signature: (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name)
  body: do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  -- N.B. by swapping `x` and `y` we can just use the foldl

中文:
定义 mkFoldrMatcher
  签名: (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name)
  定义体: do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  -- N.B. by swapping `x` and `y` we can just use the foldl
-/
partial def mkFoldrMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name) :
    OptionT TermElabM (List DelabKey × Term) := do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
.push y .push x let boundNames' := boundNames
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  -- N.B. by swapping `x` and `y` we can just use the foldl matcher
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote y) $(quote x) $smatcher $sinit))

/-! ### The `notation3` command -/

/--
Inductive type `BoundValueType` / 归纳类型 `BoundValueType`

English:
inductive BoundValueType
  constructors (3):
    - normal: 
    - foldl: 
    - foldr: 

中文:
归纳类型 BoundValueType
  构造子 (3 个):
    - normal: 
    - foldl: 
    - foldr: 

Depends on / 依赖: prettyPrint
-/
inductive BoundValueType
  /-- A normal variable, delaborate its expression. -/
  | normal
  /-- A fold variable, use the fold state (but reverse the array). -/
  | foldl
  /-- A fold variable, use the fold state (do not reverse the array). -/
  | foldr

syntax prettyPrintOpt := "(" &"prettyPrint" " := " (&"true" <|> &"false") ")"

/--
Definition of `getPrettyPrintOpt` / `getPrettyPrintOpt` 的定义

English:
definition getPrettyPrintOpt
  signature: (opt? : Option (TSyntax ``prettyPrintOpt))
  body: if let some opt := opt? then
    match opt with
    | `(prettyPrintOpt| (prettyPrint := false)) => false
    | _ => true
  else
    true

中文:
定义 getPrettyPrintOpt
  签名: (opt? : Option (TSyntax ``prettyPrintOpt))
  定义体: if let some opt := opt? then
    match opt with
    | `(prettyPrintOpt| (prettyPrint := false)) => false
    | _ => true
  else
    true

Depends on / 依赖: prettyPrint, prettyPrintOpt
-/
def getPrettyPrintOpt (opt? : Option (TSyntax ``prettyPrintOpt)) : Bool :=
  if let some opt := opt? then
    match opt with
    | `(prettyPrintOpt| (prettyPrint := false)) => false
    | _ => true
  else
    true

/--
Definition of `withHeadRefIfTagAppFns` / `withHeadRefIfTagAppFns` 的定义

English:
definition withHeadRefIfTagAppFns
  signature: (d : Delab)
  body: do
  let tagAppFns ← getPPOption getPPTagAppFns
  if tagAppFns && (← getExpr).getAppFn.consumeMData.isConst then
    -- Delaborate the head to register term info and get a syntax we can use for the ref.
    -- The syntax `f` itself is thrown away.
let f ← withNaryFn withOptionAtCurrPos `pp.tagAppFns

中文:
定义 withHeadRefIfTagAppFns
  签名: (d : Delab)
  定义体: do
  let tagAppFns ← getPPOption getPPTagAppFns
  if tagAppFns && (← getExpr).getAppFn.consumeMData.isConst then
    -- Delaborate the head to register term info and get a syntax we can use for the ref.
    -- The syntax `f` itself is thrown away.
let f ← withNaryFn withOptionAtCurrPos `pp.tagAppFns
-/
def withHeadRefIfTagAppFns (d : Delab) : Delab := do
  let tagAppFns ← getPPOption getPPTagAppFns
  if tagAppFns && (← getExpr).getAppFn.consumeMData.isConst then
    -- Delaborate the head to register term info and get a syntax we can use for the ref.
    -- The syntax `f` itself is thrown away.
let f ← withNaryFn withOptionAtCurrPos `pp.tagAppFns true delab
    let stx ← withRef f d
    -- Annotate to ensure that the full syntax still refers to the whole expression.
    annotateTermInfo stx
  else
    d

/--
`notation3` declares notation using Lean-3-style syntax.

Examples:
```
notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r
notation3 "MyList[" (x", "* => foldr (a b => MyList.cons a b) MyList.nil) "]" => x
```
By default notation is unable to mention any variables defined using `variable`, but
`local notation3` is able to use such local variables.

Use `notation3 (prettyPrint := false)` to keep the command from generating a pretty printer
for the notation.

This command can be used in mathlib4 but it has an uncertain future and was created primarily
for backward compatibility.
-/
elab (name := notation3) doc:(docComment)? attrs?:(Parser.Term.attributes)? attrKind:Term.attrKind
    "notation3" prec?:(precedence)? name?:(namedName)? prio?:(namedPrio)?
    pp?:(ppSpace prettyPrintOpt)? items:(ppSpace notation3Item)+ " => " val:term : command => do
  -- We use raw `Name`s for variables. This maps variable names back to the
  -- identifiers that appear in `items`
  let mut boundIdents : Std.HashMap Name Ident := {}
  -- Replacements to use for the `macro`
  let mut boundValues : Std.HashMap Name Syntax := {}
  -- The names of the bound names in order, used when constructing patterns for delaboration.
  let mut boundNames : Array Name := #[]
  -- The normal/foldl/foldr type of each variable (for delaborator)
  let mut boundType : Std.HashMap Name BoundValueType := {}
  -- Function to update `syntaxArgs` and `pattArgs` using `macroArg` syntax
  let pushMacro (syntaxArgs : Array (TSyntax `stx)) (pattArgs : Array Syntax)
      (mac : TSyntax ``macroArg) := do
    let (syntaxArg, pattArg) ← expandMacroArg mac
    return (syntaxArgs.push syntaxArg, pattArgs.push pattArg)
  -- Arguments for the `syntax` command
  let mut syntaxArgs := #[]
  -- Arguments for the LHS pattern in the `macro`. Also used to construct the syntax
  -- when delaborating
  let mut pattArgs := #[]
  -- The matchers to assemble into a delaborator
  let mut matchers := #[]
  -- Whether we've seen a `(...)` item
  let mut hasBindersItem := false
  -- Whether we've seen a `scoped` item
  let mut hasScoped := false
  for item in items do
    match item with
    | `(notation3Item| $lit:str) =>
      -- Can't use `pushMacro` since it inserts an extra variable into the pattern for `str`, which
      -- breaks our delaborator
      syntaxArgs := syntaxArgs.push (← `(stx| $lit:str))
pattArgs := pattArgs.push mkAtomFrom lit lit.1.isStrLit?.get!
    | `(notation3Item| $_:bindersItem) =>
      if hasBindersItem then
        throwErrorAt item "Cannot have more than one `(...)` item."
      hasBindersItem := true
      -- HACK: Lean 3 traditionally puts a space after the main binder atom, resulting in
      -- notation3 "∑ "(...)", "r:(scoped f => sum f) => r
      -- but extBinders already has a space before it so we strip the trailing space of "∑ "
      if let `(stx| $lit:str) := syntaxArgs.back! then
        syntaxArgs := syntaxArgs.pop.push (← `(stx| $(quote lit.getString.trimAsciiEnd.copy):str))
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* $(prec?)? => $kind ($x $y => $scopedTerm) $init)) =>
(syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs ←
        `(macroArg| $id:ident:sepBy(term $(prec?)?, $sep:str))
      -- N.B. `Syntax.getId` returns `.anonymous` for non-idents
      let scopedTerm' ← scopedTerm.replaceM fun s => pure boundValues[s.getId]?
      let init' ← init.replaceM fun s => pure boundValues[s.getId]?
      boundIdents := boundIdents.insert id.getId id
      match kind with
        | `(foldKind| foldl) =>
boundValues := boundValues.insert id.getId ←
            `(expand_foldl% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundNames := boundNames.push id.getId
          boundType := boundType.insert id.getId .foldl
matchers := matchers.push
            mkFoldlMatcher id.getId x.getId y.getId scopedTerm init boundNames
        | `(foldKind| foldr) =>
boundValues := boundValues.insert id.getId ←
            `(expand_foldr% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundNames := boundNames.push id.getId
          boundType := boundType.insert id.getId .foldr
matchers := matchers.push
            mkFoldrMatcher id.getId x.getId y.getId scopedTerm init boundNames
        | _ => throwUnsupportedSyntax
    | `(notation3Item| $lit:ident $(prec?)? : (scoped $scopedId:ident => $scopedTerm)) =>
      hasScoped := true
(syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs ←
        `(macroArg| $lit:ident:term $(prec?)?)
matchers := matchers.push
        mkScopedMatcher lit.getId scopedId.getId scopedTerm boundNames
      let scopedTerm' ← scopedTerm.replaceM fun s => pure boundValues[s.getId]?
      boundIdents := boundIdents.insert lit.getId lit
boundValues := boundValues.insert lit.getId ←
        `(expand_binders% ($scopedId => $scopedTerm') $$binders:extBinders,
 (⟨lit.1.mkAntiquotNode `term⟩):term)
      boundNames := boundNames.push lit.getId
    | `(notation3Item| $lit:ident $(prec?)?) =>
(syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs ←
        `(macroArg| $lit:ident:term $(prec?)?)
      boundIdents := boundIdents.insert lit.getId lit
boundValues := boundValues.insert lit.getId lit.1.mkAntiquotNode `term
      boundNames := boundNames.push lit.getId
    | _stx => throwUnsupportedSyntax
  if hasScoped && !hasBindersItem then
    throwError "If there is a `scoped` item then there must be a `(...)` item for binders."

  -- 1. The `syntax` command
  let fullName ← elabSyntax (← `(command|
 [$doc]? (attrs?)? attrKind
syntax (prec?)? [$name?:namedName]? (prio?)? [$syntaxArgs]* : term))

  -- 2. The `macro_rules`
  trace[notation3] "syntax declaration has name {fullName}"
  let pat : Term := ⟨mkNode fullName pattArgs⟩
  let val' ← val.replaceM fun s => pure boundValues[s.getId]?
  let mut macroDecl ← `($attrKind:attrKind macro_rules | `($pat) => `($val'))
  if isLocalAttrKind attrKind then
    -- For local notation, take section variables into account
    macroDecl ← `(command| set_option quotPrecheck.allowSectionVars true in $macroDecl)
  elabCommand macroDecl

  -- 3. Create a delaborator
  if getPrettyPrintOpt pp? then
matchers := matchers.push Mathlib.Notation3.mkExprMatcher val boundNames
    -- The matchers need to run in reverse order, so may as well reverse them here.
    let matchersM? := (matchers.reverse.mapM id).run
    -- We let local notations have access to `variable` declarations
    let matchers? ← if isLocalAttrKind attrKind then
      runTermElabM fun _ => matchersM?
    else
      liftTermElabM matchersM?
    if let some ms := matchers? then
      trace[notation3] "Matcher creation succeeded; assembling delaborator"
      let matcher ← ms.foldrM (fun m t => `($(m.2) >=> $t)) (← `(pure))
      trace[notation3] "matcher:{indentD matcher}"
      let mut result ← `(withHeadRefIfTagAppFns `($pat))
      for (name, id) in boundIdents.toArray do
        match boundType.getD name .normal with
        | .normal => result ← `(MatchState.delabVar s $(quote name) (some e) >>= fun $id => $result)
        | .foldl => result ←
          `(let $id := (MatchState.getFoldArray s $(quote name)).reverse; $result)
        | .foldr => result ←
          `(let $id := MatchState.getFoldArray s $(quote name); $result)
      if hasBindersItem then
        result ← `(`(extBinders| $$(MatchState.getBinders s)*) >>= fun binders => $result)
      let delabKeys : List DelabKey := ms.foldr (·.1 ++ ·) []
      let vis ← if let `(attrKind| local) := attrKind then
        `(visibility| private) else `(visibility| public)
      for key in delabKeys do
        trace[notation3] "Creating delaborator for key {repr key}"
        let bodyCore ← `(getExpr >>= fun e => $matcher MatchState.empty >>= fun s => $result)
        let body ←
          match key with
          | .app _ arity => ``(withOverApp $(quote arity) $bodyCore)
          | _ => pure bodyCore
elabCommand ← `(
          /-- Pretty printer defined by `notation3` command. -/
          @[$attrKind delab $(mkIdent key.key)]
 vis:visibility aux_def delab_app (mkIdent fullName) : Delab :=
whenPPOption getPPNotation whenNotPPOption getPPExplicit body)
    else
      logWarning s!"\
        Was not able to generate a pretty printer for this notation. \
        If you do not expect it to be pretty printable, then you can use \
        `notation3 (prettyPrint := false)`. \
        If the notation expansion refers to section variables, be sure to do `local notation3`. \
        Otherwise, you might be able to adjust the notation expansion to make it matchable; \
        pretty printing relies on deriving an expression matcher from the expansion. \
        (Use `set_option trace.notation3 true` to get some debug information.)"

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``«notation3»

/-! `scoped[ns]` support -/

macro_rules
  | `($[$doc]? $(attr)? scoped[$ns] notation3 $(prec)? $(n)? $(prio)? $(pp)? $items* => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
 [$doc]? (attr)? scoped notation3 (prec)? (n)? (prio)? (pp)? items* => t)

end Notation3

end Mathlib
