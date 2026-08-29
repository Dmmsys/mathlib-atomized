/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Aurélien Saue, Mario Carneiro
-/
module

public meta import Lean.Elab.PreDefinition.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.RCases
public meta import Batteries.Lean.Expr
public import Mathlib.Init

/-!
# Generally useful tactics.

-/

public meta section

open Lean.Elab.Tactic

namespace Lean

open Elab Meta

/--
Definition of `toModifiers` / `toModifiers` 的定义

English:
definition toModifiers
  signature: (nm : Name) (newDoc : Option (TSyntax `Lean.Parser.Command.docComment) := none)
  body: do
  let env ← getEnv
  let d ← getConstInfo nm
  let mods : Modifiers :=
  { docString? := newDoc
    visibility :=
    if isPrivateName nm then
      Visibility.private
    else
      Visibility.regular
    isProtected := isProtected env nm
    computeKind := if (env.find? <| nm.mkStr "_cstage1").

中文:
定义 toModifiers
  签名: (nm : Name) (newDoc : Option (TSyntax `Lean.Parser.Command.docComment) := none)
  定义体: do
  let env ← getEnv
  let d ← getConstInfo nm
  let mods : Modifiers :=
  { docString? := newDoc
    visibility :=
    if isPrivateName nm then
      Visibility.private
    else
      Visibility.regular
    isProtected := isProtected env nm
    computeKind := if (env.find? <| nm.mkStr "_cstage1").
-/
def toModifiers (nm : Name) (newDoc : Option (TSyntax `Lean.Parser.Command.docComment) := none) :
    CoreM Modifiers := do
  let env ← getEnv
  let d ← getConstInfo nm
  let mods : Modifiers :=
  { docString? := newDoc
    visibility :=
    if isPrivateName nm then
      Visibility.private
    else
      Visibility.regular
    isProtected := isProtected env nm
    computeKind := if (env.find? <| nm.mkStr "_cstage1").isSome then .regular else .noncomputable
    recKind := RecKind.default -- nonrec only matters for name resolution, so is irrelevant (?)
    isUnsafe := d.isUnsafe
    attrs := #[] }
  return mods

/--
Definition of `toPreDefinition` / `toPreDefinition` 的定义

English:
definition toPreDefinition
  signature: (nm newNm : Name) (newType newValue : Expr)
  body: do
  let d ← getConstInfo nm
  let mods ← toModifiers nm newDoc
  let predef : PreDefinition :=
  { ref := Syntax.missing
    binders := mkNullNode #[]
    kind := if d.isDef then DefKind.def else DefKind.theorem
    levelParams := d.levelParams
    modifiers := mods
    declName := newNm
    type :

中文:
定义 toPreDefinition
  签名: (nm newNm : Name) (newType newValue : Expr)
  定义体: do
  let d ← getConstInfo nm
  let mods ← toModifiers nm newDoc
  let predef : PreDefinition :=
  { ref := Syntax.missing
    binders := mkNullNode #[]
    kind := if d.isDef then DefKind.def else DefKind.theorem
    levelParams := d.levelParams
    modifiers := mods
    declName := newNm
    type :
-/
def toPreDefinition (nm newNm : Name) (newType newValue : Expr)
    (newDoc : Option (TSyntax `Lean.Parser.Command.docComment) := none) :
    CoreM PreDefinition := do
  let d ← getConstInfo nm
  let mods ← toModifiers nm newDoc
  let predef : PreDefinition :=
  { ref := Syntax.missing
    binders := mkNullNode #[]
    kind := if d.isDef then DefKind.def else DefKind.theorem
    levelParams := d.levelParams
    modifiers := mods
    declName := newNm
    type := newType
    value := newValue
    termination := .none }
  return predef

/--
Definition of `setProtected` / `setProtected` 的定义

English:
definition setProtected
  signature: {m : Type -> Type} [MonadEnv m] (nm : Name)
  body: modifyEnv (addProtected · nm)

中文:
定义 setProtected
  签名: {m : Type -> Type} [MonadEnv m] (nm : Name)
  定义体: modifyEnv (addProtected · nm)

Depends on / 依赖: BoundedLENhdsClass, OrderTop, OrderTop.to_BoundedLENhdsClass, addProtected, modifyEnv, to_BoundedLENhdsClass
-/
def setProtected {m : Type -> Type} [MonadEnv m] (nm : Name) : m Unit :=
  modifyEnv (addProtected · nm)

/--
Definition of `MVarId.rintroWithPats` / `MVarId.rintroWithPats` 的定义

English:
definition MVarId.rintroWithPats
  signature: (g : MVarId) (patterns : List (TSyntax `rintroPat))
  body: do
  let n ← numIntros?.getDM (return getIntrosSize (← instantiateMVars (← g.getType)))
  if n == 0 then
    return ([g], patterns)
  let (pats, remaining) := patterns.splitAt n
  let pats := pats.toArray
  let pats := (n - pats.size).repeat (·.push (Unhygienic.run `(rintroPat| _))) pats
  return (←

中文:
定义 MVarId.rintroWithPats
  签名: (g : MVarId) (patterns : List (TSyntax `rintroPat))
  定义体: do
  let n ← numIntros?.getDM (return getIntrosSize (← instantiateMVars (← g.getType)))
  if n == 0 then
    return ([g], patterns)
  let (pats, remaining) := patterns.splitAt n
  let pats := pats.toArray
  let pats := (n - pats.size).repeat (·.push (Unhygienic.run `(rintroPat| _))) pats
  return (←

Depends on / 依赖: BoundedGENhdsClass, MVarId, OrderBot, OrderBot.to_BoundedGENhdsClass, TSyntax, rintroPat, to_BoundedGENhdsClass
-/
def MVarId.rintroWithPats (g : MVarId) (patterns : List (TSyntax `rintroPat))
    (numIntros? : Option Nat := none) : MetaM (List MVarId × List (TSyntax `rintroPat)) := do
  let n ← numIntros?.getDM (return getIntrosSize (← instantiateMVars (← g.getType)))
  if n == 0 then
    return ([g], patterns)
  let (pats, remaining) := patterns.splitAt n
  let pats := pats.toArray
  let pats := (n - pats.size).repeat (·.push (Unhygienic.run `(rintroPat| _))) pats
  return (← RCases.rintro pats none g |>.run', remaining)

/-- Introduce variables, giving them names from a specified list. -/
@[deprecated MVarId.rintroWithPats (since := "2026-04-17")]
/--
Definition of `MVarId.introsWithBinderIdents` / `MVarId.introsWithBinderIdents` 的定义

English:
definition MVarId.introsWithBinderIdents
  body: do
  let type ← g.getType
  let type ← Lean.instantiateMVars type
  let n := getIntrosSize type
  let n := match maxIntros? with | none => n | some maxIntros => min n maxIntros
  if n == 0 then
    return (ids, #[], g)
  let mut ids := ids
  let mut names := #[]
  for _ in [0:n] do
    names := name

中文:
定义 MVarId.introsWithBinderIdents
  定义体: do
  let type ← g.getType
  let type ← Lean.instantiateMVars type
  let n := getIntrosSize type
  let n := match maxIntros? with | none => n | some maxIntros => min n maxIntros
  if n == 0 then
    return (ids, #[], g)
  let mut ids := ids
  let mut names := #[]
  for _ in [0:n] do
    names := name

Depends on / 依赖: BoundedLENhdsClass, BoundedLENhdsClass.of_closedIciTopology, LinearOrder, of_closedIciTopology
-/
def MVarId.introsWithBinderIdents
    (g : MVarId) (ids : List (TSyntax ``binderIdent)) (maxIntros? : Option Nat := none) :
    MetaM (List (TSyntax ``binderIdent) × Array FVarId × MVarId) := do
  let type ← g.getType
  let type ← Lean.instantiateMVars type
  let n := getIntrosSize type
  let n := match maxIntros? with | none => n | some maxIntros => min n maxIntros
  if n == 0 then
    return (ids, #[], g)
  let mut ids := ids
  let mut names := #[]
  for _ in [0:n] do
    names := names.push (ids.headD (Unhygienic.run `(binderIdent| _)))
    ids := ids.tail
let (xs, g) ← g.introN n names.toList.map fun stx =>
    match stx.raw with
    | `(binderIdent| $n:ident) => n.getId
    | _ => `_
  g.withContext do
    for n in names, fvar in xs do
      (Expr.fvar fvar).addLocalVarInfoForBinderIdent n
  return (ids, xs, g)

end Lean

namespace Mathlib.Tactic

-- FIXME: we cannot write this line when `Lean.Parser.Tactic` is open,
-- or it will get an extra `group`
syntax withArgs := " with" (ppSpace colGt ident)+
syntax usingArg := " using " term

open Lean Parser.Tactic

/--
Definition of `getSimpArgs` / `getSimpArgs` 的定义

English:
definition getSimpArgs
  signature: : Syntax -> TacticM (Array Syntax)

中文:
定义 getSimpArgs
  签名: : Syntax -> TacticM (Array Syntax)

Depends on / 依赖: BoundedGENhdsClass, BoundedGENhdsClass.of_closedIicTopology, LinearOrder, of_closedIicTopology
-/
def getSimpArgs : Syntax -> TacticM (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _ => Elab.throwUnsupportedSyntax

/--
Definition of `getDSimpArgs` / `getDSimpArgs` 的定义

English:
definition getDSimpArgs
  signature: : Syntax -> TacticM (Array Syntax)

中文:
定义 getDSimpArgs
  签名: : Syntax -> TacticM (Array Syntax)
-/
def getDSimpArgs : Syntax -> TacticM (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _ => Elab.throwUnsupportedSyntax

/--
Definition of `getWithArgs` / `getWithArgs` 的定义

English:
definition getWithArgs
  signature: : Syntax -> TacticM (Array Syntax)

中文:
定义 getWithArgs
  签名: : Syntax -> TacticM (Array Syntax)
-/
def getWithArgs : Syntax -> TacticM (Array Syntax)
  | `(withArgs| with $args*) => pure args
  | _ => Elab.throwUnsupportedSyntax

/--
Definition of `getUsingArg` / `getUsingArg` 的定义

English:
definition getUsingArg
  signature: : Syntax -> TacticM Syntax

中文:
定义 getUsingArg
  签名: : Syntax -> TacticM Syntax
-/
def getUsingArg : Syntax -> TacticM Syntax
  | `(usingArg| using $e) => pure e
  | _ => Elab.throwUnsupportedSyntax

/--
`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| (($seq); repeat $seq))

end Mathlib.Tactic

namespace Lean.Elab.Tactic

/--
Definition of `filterOutImplementationDetails` / `filterOutImplementationDetails` 的定义

English:
definition filterOutImplementationDetails
  signature: (lctx : LocalContext) (fvarIds : Array FVarId)
  body: fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

中文:
定义 filterOutImplementationDetails
  签名: (lctx : LocalContext) (fvarIds : Array FVarId)
  定义体: fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

Depends on / 依赖: filter, fvarIdToDecl, fvarIds, fvarIds.filter, isImplementationDetail, lctx.fvarIdToDecl.find
-/
def filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVarId) : Array FVarId :=
  fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

/--
Definition of `getFVarIdAt` / `getFVarIdAt` 的定义

English:
definition getFVarIdAt
  signature: (goal : MVarId) (id : Syntax)
  body: withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _ => throwError "unexpected term '{e}'; expected single reference to variabl

中文:
定义 getFVarIdAt
  签名: (goal : MVarId) (id : Syntax)
  定义体: withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _ => throwError "unexpected term '{e}'; expected single reference to variabl

Depends on / 依赖: withRef
-/
def getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId := withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _ => throwError "unexpected term '{e}'; expected single reference to variable"

/--
Definition of `getFVarIdsAt` / `getFVarIdsAt` 的定义

English:
definition getFVarIdsAt
  signature: (goal : MVarId) (ids : Option (Array Syntax) := none)
  body: goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
| some ids => ids.mapM getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds

中文:
定义 getFVarIdsAt
  签名: (goal : MVarId) (ids : Option (Array Syntax) := none)
  定义体: goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
| some ids => ids.mapM getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds
-/
def getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax) := none)
    (includeImplementationDetails : Bool := false) : TacticM (Array FVarId) :=
  goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
| some ids => ids.mapM getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds

/--
Definition of `allGoals` / `allGoals` 的定义

English:
definition allGoals
  signature: (tac : TacticM Unit)
  body: do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
 

中文:
定义 allGoals
  签名: (tac : TacticM Unit)
  定义体: do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
 
-/
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/--
Definition of `andThenOnSubgoals` / `andThenOnSubgoals` 的定义

English:
definition andThenOnSubgoals
  signature: (tac1 : TacticM Unit) (tac2 : TacticM Unit)
  body: focus do tac1; allGoals tac2

universe u

中文:
定义 andThenOnSubgoals
  签名: (tac1 : TacticM Unit) (tac2 : TacticM Unit)
  定义体: focus do tac1; allGoals tac2

universe u

Depends on / 依赖: allGoals
-/
def andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2

universe u
variable {m : Type -> Type u} [Monad m] [MonadExcept Exception m]

/--
Definition of `iterateAtMost` / `iterateAtMost` 的定义

English:
definition iterateAtMost
  signature: : Nat -> m Unit -> m Unit

中文:
定义 iterateAtMost
  签名: : 自然数 -> m Unit -> m Unit
-/
def iterateAtMost : Nat -> m Unit -> m Unit
  | 0, _ => pure ()
  | n + 1, tac => try tac; iterateAtMost n tac catch _ => pure ()

/--
Definition of `iterateExactly'` / `iterateExactly'` 的定义

English:
definition iterateExactly'
  signature: : Nat -> m Unit -> m Unit

中文:
定义 iterateExactly'
  签名: : 自然数 -> m Unit -> m Unit
-/
def iterateExactly' : Nat -> m Unit -> m Unit
  | 0, _ => pure ()
  | n + 1, tac => tac *> iterateExactly' n tac

/--
Definition of `iterateRange` / `iterateRange` 的定义

English:
definition iterateRange
  signature: : Nat -> Nat -> m Unit -> m Unit

中文:
定义 iterateRange
  签名: : 自然数 -> 自然数 -> m Unit -> m Unit

Depends on / 依赖: iterateUntilFailure
-/
def iterateRange : Nat -> Nat -> m Unit -> m Unit
  | 0, 0, _ => pure ()
  | 0, b, tac => iterateAtMost b tac
  | (a+1), n, tac => do tac; iterateRange a (n-1) tac

/--
Definition of `iterateUntilFailure` / `iterateUntilFailure` 的定义

English:
definition iterateUntilFailure
  signature: (tac : m Unit)
  body: try tac; iterateUntilFailure tac catch _ => pure ()

中文:
定义 iterateUntilFailure
  签名: (tac : m Unit)
  定义体: try tac; iterateUntilFailure tac catch _ => pure ()
-/
partial def iterateUntilFailure (tac : m Unit) : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()

/--
Definition of `iterateUntilFailureWithResults` / `iterateUntilFailureWithResults` 的定义

English:
definition iterateUntilFailureWithResults
  signature: {α : Type} (tac : m α)
  body: do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []

中文:
定义 iterateUntilFailureWithResults
  签名: {α : Type} (tac : m α)
  定义体: do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []
-/
partial def iterateUntilFailureWithResults {α : Type} (tac : m α) : m (List α) := do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []

/--
Definition of `iterateUntilFailureCount` / `iterateUntilFailureCount` 的定义

English:
definition iterateUntilFailureCount
  signature: {α : Type} (tac : m α)
  body: do
  let r ← iterateUntilFailureWithResults tac
  return r.length

中文:
定义 iterateUntilFailureCount
  签名: {α : Type} (tac : m α)
  定义体: do
  let r ← iterateUntilFailureWithResults tac
  return r.length
-/
def iterateUntilFailureCount {α : Type} (tac : m α) : m Nat := do
  let r ← iterateUntilFailureWithResults tac
  return r.length

end Lean.Elab.Tactic

namespace Mathlib
open Lean

/--
Definition of `getPackageDir` / `getPackageDir` 的定义

English:
definition getPackageDir
  signature: (pkg : String)
  body: do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
(p / pkg).isDir ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
throw IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."

中文:
定义 getPackageDir
  签名: (pkg : String)
  定义体: do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
(p / pkg).isDir ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
throw IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."
-/
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
(p / pkg).isDir ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
throw IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."

/--
Definition of `getMathlibDir` / `getMathlibDir` 的定义

English:
definition getMathlibDir
  body: getPackageDir "Mathlib"

中文:
定义 getMathlibDir
  定义体: getPackageDir "Mathlib"

Depends on / 依赖: Mathlib, getPackageDir
-/
def getMathlibDir := getPackageDir "Mathlib"

end Mathlib
