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
Return the modifiers of declaration `nm` with (optional) docstring `newDoc`.
Currently, recursive or partial definitions are not supported, and no attributes are provided.
-/
/-
**Lean.toModifiers** 是 Mathlib 中的一个定义，位于命名空间 `Lean`。
形式化陈述：toModifiers (nm : Name) (newDoc : Option (TSyntax `Lean.Parser.Command.doc
Comment)
参数：nm : Name。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the modifiers of declaration `nm` with (optional) docstring `newDoc`.
Currently, recursive or partial definitions are not supported, and no attributes
 are provided.
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
Make a PreDefinition taking some metadata from declaration `nm`.
You can provide a new type, value and (optional) docstring, but the remaining information is taken
from `nm`.
Currently only implemented for definitions and theorems. Also see docstring of `toModifiers`
-/
/-
**Lean.toPreDefinition** 是 Mathlib 中的一个定义，位于命名空间 `Lean`。
形式化陈述：toPreDefinition (nm newNm : Name) (newType newValue : Expr) (newDoc : Opti
on (TSyntax `Lean.Parser.Command.docComment)
参数：nm newNm : Name；newType newValue : Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a PreDefinition taking some metadata from declaration `nm`.
You can provide a new type, value and (optional) docstring, but the remaining in
formation is taken
from `nm`.
Currently only implemented for definitions and theorems. Also see docstring of `
toModifiers`
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

/-- Make `nm` protected. -/
/-
**Lean.setProtected** 是 Mathlib 中的一个定义，位于命名空间 `Lean`。
形式化陈述：setProtected {m : Type -> Type} [MonadEnv m] (nm : Name) : m Unit
参数：nm : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make `nm` protected.
-/
def setProtected {m : Type → Type} [MonadEnv m] (nm : Name) : m Unit :=
  modifyEnv (addProtected · nm)

/-- Introduce variables, using rintro patterns from a specified list. -/
/-
**Lean.MVarId.rintroWithPats** 是 Mathlib 中的一个定义，位于命名空间 `Lean.MVarId`。
形式化陈述：MVarId → List (TSyntax `rintroPat) → optParam (Option ℕ) none → MetaM (Lis
t MVarId × List (TSyntax `rintroPat))
参数：TSyntax `rintroPat；Option ℕ；List MVarId × List (TSyntax `rintroPat)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Introduce variables, using rintro patterns from a specified list.
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
/-
**Lean.MVarId.introsWithBinderIdents** 是 Mathlib 中的一个定义，位于命名空间 `Lean.MVarId`。
形式化陈述：MVarId →   List (TSyntax `Lean.binderIdent) →     optParam (Option ℕ) none
 → MetaM (List (TSyntax `Lean.binderIdent) × Array FVarId × MVarId)
参数：TSyntax `Lean.binderIdent；Option ℕ；List (TSyntax `Lean.binderIdent) × Array F
VarId × MVarId。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Introduce variables, giving them names from a specified list.
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
  let (xs, g) ← g.introN n <| names.toList.map fun stx =>
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

/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
/-
**Mathlib.Tactic.getSimpArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：Syntax → Elab.Tactic.TacticM (Array Syntax)
参数：Array Syntax。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the arguments from a `simpArgs` syntax as an array of syntaxes
-/
def getSimpArgs : Syntax → TacticM (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _                      => Elab.throwUnsupportedSyntax

/-- Extract the arguments from a `dsimpArgs` syntax as an array of syntaxes -/
/-
**Mathlib.Tactic.getDSimpArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：Syntax → Elab.Tactic.TacticM (Array Syntax)
参数：Array Syntax。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the arguments from a `dsimpArgs` syntax as an array of syntaxes
-/
def getDSimpArgs : Syntax → TacticM (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _                       => Elab.throwUnsupportedSyntax

/-- Extract the arguments from a `withArgs` syntax as an array of syntaxes -/
/-
**Mathlib.Tactic.getWithArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：Syntax → Elab.Tactic.TacticM (Array Syntax)
参数：Array Syntax。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the arguments from a `withArgs` syntax as an array of syntaxes
-/
def getWithArgs : Syntax → TacticM (Array Syntax)
  | `(withArgs| with $args*) => pure args
  | _                        => Elab.throwUnsupportedSyntax

/-- Extract the argument from a `usingArg` syntax as a syntax term -/
/-
**Mathlib.Tactic.getUsingArg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：Syntax → Elab.Tactic.TacticM Syntax
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the argument from a `usingArg` syntax as a syntax term
-/
def getUsingArg : Syntax → TacticM Syntax
  | `(usingArg| using $e) => pure e
  | _                     => Elab.throwUnsupportedSyntax

/--
`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| (($seq); repeat $seq))

end Mathlib.Tactic

namespace Lean.Elab.Tactic

/-- Given a local context and an array of `FVarIds` assumed to be in that local context, remove all
implementation details. -/
/-
**Lean.Elab.Tactic.filterOutImplementationDetails** 是 Mathlib 中的一个定义，位于命名空间 `Lea
n.Elab.Tactic`。
形式化陈述：filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVar
Id) : Array FVarId
参数：lctx : LocalContext；fvarIds : Array FVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a local context and an array of `FVarIds` assumed to be in that local cont
ext, remove all
implementation details.
-/
def filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVarId) : Array FVarId :=
  fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

/-- Elaborate syntax for an `FVarId` in the local context of the given goal. -/
/-
**Lean.Elab.Tactic.getFVarIdAt** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId
参数：goal : MVarId；id : Syntax。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elaborate syntax for an `FVarId` in the local context of the given goal.
-/
def getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId := withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _                => throwError "unexpected term '{e}'; expected single reference to variable"

/-- Get the array of `FVarId`s in the local context of the given `goal`.

If `ids` is specified, elaborate them in the local context of the given goal to obtain the array of
`FVarId`s.

If `includeImplementationDetails` is `false` (the default), we filter out implementation details
(`implDecl`s and `auxDecl`s) from the resulting list of `FVarId`s. -/
/-
**Lean.Elab.Tactic.getFVarIdsAt** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax)
参数：goal : MVarId。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the array of `FVarId`s in the local context of the given `goal`.

If `ids` is specified, elaborate them in the local context of the given goal to 
obtain the array of
`FVarId`s.

If `includeImplementationDetails` is `false` (the default), we filter out implem
entation details
(`implDecl`s and `auxDecl`s) from the resulting list of `FVarId`s.
-/
def getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax) := none)
    (includeImplementationDetails : Bool := false) : TacticM (Array FVarId) :=
  goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
    | some ids => ids.mapM <| getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds

/--
Run a tactic on all goals, and always succeeds.

(This is parallel to `Lean.Elab.Tactic.evalAllGoals` in core,
which takes a `Syntax` rather than `TacticM Unit`.
This function could be moved to core and `evalAllGoals` refactored to use it.)
-/
/-
**Lean.Elab.Tactic.allGoals** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：allGoals (tac : TacticM Unit) : TacticM Unit
参数：tac : TacticM Unit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run a tactic on all goals, and always succeeds.

(This is parallel to `Lean.Elab.Tactic.evalAllGoals` in core,
which takes a `Syntax` rather than `TacticM Unit`.
This function could be moved to core and `evalAllGoals` refactored to use it.)
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

/-- Simulates the `<;>` tactic combinator.
First runs `tac1` and then runs `tac2` on all newly-generated subgoals.
-/
/-
**Lean.Elab.Tactic.andThenOnSubgoals** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic
`。
形式化陈述：andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Un
it
参数：tac1 : TacticM Unit；tac2 : TacticM Unit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simulates the `<;>` tactic combinator.
First runs `tac1` and then runs `tac2` on all newly-generated subgoals.
-/
def andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2

universe u
variable {m : Type → Type u} [Monad m] [MonadExcept Exception m]

/-- Repeats a tactic at most `n` times, stopping sooner if the
tactic fails. Always succeeds. -/
/-
**Lean.Elab.Tactic.iterateAtMost** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：{m : Type → Type u} → [Monad m] → [MonadExcept Exception m] → ℕ → m Unit →
 m Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Repeats a tactic at most `n` times, stopping sooner if the
tactic fails. Always succeeds.
-/
def iterateAtMost : Nat → m Unit → m Unit
  | 0, _ => pure ()
  | n + 1, tac => try tac; iterateAtMost n tac catch _ => pure ()

/-- `iterateExactly' n t` executes `t` `n` times. If any iteration fails, the whole tactic fails.
-/
/-
**Lean.Elab.Tactic.iterateExactly'** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：{m : Type → Type u} → [Monad m] → ℕ → m Unit → m Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iterateExactly' n t` executes `t` `n` times. If any iteration fails, the whole 
tactic fails.
-/
def iterateExactly' : Nat → m Unit → m Unit
  | 0, _ => pure ()
  | n + 1, tac => tac *> iterateExactly' n tac

/--
`iterateRange m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` times.
-/
/-
**Lean.Elab.Tactic.iterateRange** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：iterateRange : Nat -> Nat -> m Unit -> m Unit | 0, 0, _ => pure () | 0, b,
 tac => iterateAtMost b tac | (a+1), n, tac => do tac; iterateRange a (n-1) tac 
 /-- Repeats a tactic until it fails. Always succeeds. -/ partial def iterateUnt
ilFailure (tac : m Unit) : m Unit
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iterateRange m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` tim
es.
-/
def iterateRange : Nat → Nat → m Unit → m Unit
  | 0, 0, _   => pure ()
  | 0, b, tac => iterateAtMost b tac
  | (a+1), n, tac => do tac; iterateRange a (n-1) tac

/-- Repeats a tactic until it fails. Always succeeds. -/
/-
**Lean.Elab.Tactic.iterateUntilFailure** 是 Mathlib 中的一个不透明定义，位于命名空间 `Lean.Elab.T
actic`。
形式化陈述：{m : Type → Type u} → [Monad m] → [MonadExcept Exception m] → m Unit → m U
nit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Repeats a tactic until it fails. Always succeeds.
-/
partial def iterateUntilFailure (tac : m Unit) : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()

/-- `iterateUntilFailureWithResults` is a helper tactic which accumulates the list of results
obtained from iterating `tac` until it fails. Always succeeds.
-/
/-
**Lean.Elab.Tactic.iterateUntilFailureWithResults** 是 Mathlib 中的一个不透明定义，位于命名空间 `
Lean.Elab.Tactic`。
形式化陈述：{m : Type → Type u} → [Monad m] → [MonadExcept Exception m] → {α : Type} →
 m α → m (List α)
参数：List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iterateUntilFailureWithResults` is a helper tactic which accumulates the list o
f results
obtained from iterating `tac` until it fails. Always succeeds.
-/
partial def iterateUntilFailureWithResults {α : Type} (tac : m α) : m (List α) := do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []

/-- `iterateUntilFailureCount` is similar to `iterateUntilFailure` except it counts
the number of successful calls to `tac`. Always succeeds.
-/
/-
**Lean.Elab.Tactic.iterateUntilFailureCount** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab
.Tactic`。
形式化陈述：iterateUntilFailureCount {α : Type} (tac : m α) : m Nat
参数：tac : m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iterateUntilFailureCount` is similar to `iterateUntilFailure` except it counts
the number of successful calls to `tac`. Always succeeds.
-/
def iterateUntilFailureCount {α : Type} (tac : m α) : m Nat := do
  let r ← iterateUntilFailureWithResults tac
  return r.length

end Lean.Elab.Tactic

namespace Mathlib
open Lean

/-- Returns the root directory which contains the package root file, e.g. `Mathlib.lean`. -/
/-
**Mathlib.getPackageDir** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib`。
形式化陈述：getPackageDir (pkg : String) : IO System.FilePath
参数：pkg : String。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the root directory which contains the package root file, e.g. `Mathlib.l
ean`.
-/
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
  throw <| IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."

/-- Returns the mathlib root directory. -/
/-
**Mathlib.getMathlibDir** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib`。
形式化陈述：getMathlibDir
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the mathlib root directory.
-/
def getMathlibDir := getPackageDir "Mathlib"

end Mathlib

