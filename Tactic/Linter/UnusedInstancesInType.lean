/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Mathlib.Lean.Expr.Basic
public meta import Mathlib.Lean.Environment
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Lean.Linter.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Misc

/-!
# Linters for Unused Instances in Types

This file declares linters which detect certain instance hypotheses in declarations that are unused
in the remainder of the type.

Currently, these linters only handle theorems. (This also includes `lemma`s and `instance`s of
`Prop` classes.)

- `unusedDecidableInType` linter (currently off by default): suggests replacing type-unused
  `Decidable*` instance hypotheses, and could therefore be replaced by `classical` in the proof.

TODO: log on type signature instead of whole command
TODO: add more linters!
TODO: create Try This suggestions
-/

meta section

open Lean Meta Elab Command Linter

namespace Mathlib.Linter.UnusedInstancesInType

/--
Definition of `Parameter` / `Parameter` 的定义

English:
structure Parameter
  parameters: where
  axioms and operations (4):
    - fvar? : Option Expr
    - type? : Option Expr
    - idx : Nat
    - appearsInTypeProof : Bool

中文:
结构 参数
  参数: where
  公理与运算 (4 个):
    - fvar? : 选项类型 Expr
    - type? : 选项类型 Expr
    - idx : 自然数
    - appearsInTypeProof : 布尔值
-/
structure Parameter where
  /- TODO: include syntax references to the binders here, and use the "real" fvars created during
  elaboration if possible -/
  /-- The free variable of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  fvar? : Option Expr
  /-- The type of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  type? : Option Expr
  /-- The index of the parameter among the `forall` binders in the type (starting at 0). -/
  idx : Nat
  /-- Whether the parameter appears in a proof in the type. -/
  appearsInTypeProof : Bool

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToMessageData Parameter
  body: Id.run do
    let mut msg := if let some type := param.type? then
      m!"[{type}] (#{param.idx + 1})"
    else
      m!"parameter #{param.idx + 1}"
    if param.appearsInTypeProof then
      msg := m!"{msg} (used in type, but only in a proof)"
    return msg

中文:
实例 :
  签名: ToMessageData 参数
  定义体: Id.run do
    let mut msg := if let some type := param.type? then
      m!"[{type}] (#{param.idx + 1})"
    else
      m!"parameter #{param.idx + 1}"
    if param.appearsInTypeProof then
      msg := m!"{msg} (used in type, but only in a proof)"
    return msg

Depends on / 依赖: Id.run
-/
instance : ToMessageData Parameter where
  toMessageData (param : Parameter) := Id.run do
    let mut msg := if let some type := param.type? then
      m!"[{type}] (#{param.idx + 1})"
    else
      m!"parameter #{param.idx + 1}"
    if param.appearsInTypeProof then
      msg := m!"{msg} (used in type, but only in a proof)"
    return msg

/--
Definition of `_root_.Lean.Name.unusedInstancesMsg` / `_root_.Lean.Name.unusedInstancesMsg` 的定义

English:
definition _root_.Lean.Name.unusedInstancesMsg
  signature: (declName : Name)
  body: let anyAppearsInTypeProof := unusedInstanceBinders.any (·.appearsInTypeProof)
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` does not use the following \
  {if unusedInstanceBinders.size = 1 then "hypothesis" else "hypotheses"} \
  in its type{i

中文:
定义 _root_.Lean.Name.unusedInstancesMsg
  签名: (declName : Name)
  定义体: let anyAppearsInTypeProof := unusedInstanceBinders.any (·.appearsInTypeProof)
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` does not use the following \
  {if unusedInstanceBinders.size = 1 then "hypothesis" else "hypotheses"} \
  in its type{i

Depends on / 依赖: anyAppearsInTypeProof, appearsInTypeProof, compose, declName, following, hypotheses, hypothesis, ofConstName, outside, proofs, toMessageData, unusedInstanceBinders, unusedInstanceBinders.any, unusedInstanceBinders.map, unusedInstanceBinders.size
-/
def _root_.Lean.Name.unusedInstancesMsg (declName : Name)
    (unusedInstanceBinders : Array Parameter): MessageData :=
  let anyAppearsInTypeProof := unusedInstanceBinders.any (·.appearsInTypeProof)
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` does not use the following \
  {if unusedInstanceBinders.size = 1 then "hypothesis" else "hypotheses"} \
  in its type{if anyAppearsInTypeProof then " outside of proofs" else ""}:\
  {(unusedInstanceBinders.map (m!"\n • {·}") |>.foldl (init := .nil) .compose)}"

/- Perf note: could cache visited exprs like `collectFVars` does. -/
/--
Definition of `collectFVarsOutsideOfProofs` / `collectFVarsOutsideOfProofs` 的定义

English:
definition collectFVarsOutsideOfProofs
  signature: (e : Expr)
  body: Meta.forEachExpr' e fun subExpr =>
    -- If it doesn't have an fvar, or it's a sorry, or it's a proof, don't descend further.
    pure (subExpr.hasFVar && !subExpr.isSorryAx) <&&> notM (Meta.isProof subExpr) <&&> do
      let .fvar fvarId := subExpr | return true -- not an fvar, but there's one bel

中文:
定义 collectFVarsOutsideOfProofs
  签名: (e : Expr)
  定义体: Meta.forEachExpr' e fun subExpr =>
    -- If it doesn't have an fvar, or it's a sorry, or it's a proof, don't descend further.
    pure (subExpr.hasFVar && !subExpr.isSorryAx) <&&> notM (Meta.isProof subExpr) <&&> do
      let .fvar fvarId := subExpr | return true -- not an fvar, but there's one bel

Depends on / 依赖: Meta.forEachExpr, forEachExpr, subExpr
-/
def collectFVarsOutsideOfProofs (e : Expr) : StateRefT FVarIdSet MetaM Unit :=
  Meta.forEachExpr' e fun subExpr =>
    -- If it doesn't have an fvar, or it's a sorry, or it's a proof, don't descend further.
    pure (subExpr.hasFVar && !subExpr.isSorryAx) <&&> notM (Meta.isProof subExpr) <&&> do
      let .fvar fvarId := subExpr | return true -- not an fvar, but there's one below us; continue
      modifyThe FVarIdSet (·.insert fvarId)
      /- Note: return value is irrelevant here (`false` says "do not visit the children of this
      fvar", but fvars are atomic anyway) -/
      return false

/--
Definition of `InstanceOfConcern` / `InstanceOfConcern` 的定义

English:
structure InstanceOfConcern
  parameters: where
  axioms and operations (2):
    - fvarId : FVarId
    - idx : Nat

中文:
结构 InstanceOfConcern
  参数: where
  公理与运算 (2 个):
    - fvarId : FVarId
    - idx : 自然数
-/
structure InstanceOfConcern where
  /-- The `FVarId` of the instance of concern within the current telescope. -/
  fvarId : FVarId
  /-- The index of the binder that this instance came from. The first binder is `0`, and we do not
  increment this index when seeing through `let`s. -/
  idx : Nat

/--
Definition of `_root_.Lean.Expr.collectUnnecessaryInstanceBinderIdxsWhere` / `_root_.Lean.Expr.collectUnnecessaryInstanceBinderIdxsWhere` 的定义

English:
definition _root_.Lean.Expr.collectUnnecessaryInstanceBinderIdxsWhere
  signature: (p : Expr -> Bool)
  body: do
.run {} let (instances, fvarIdSet) ← go e 0 #[]
  return instances.filterMap fun i => if fvarIdSet.contains i.fvarId then none else some i.idx

中文:
定义 _root_.Lean.Expr.collectUnnecessaryInstanceBinderIdxsWhere
  签名: (p : Expr -> 布尔值)
  定义体: do
.run {} let (instances, fvarIdSet) ← go e 0 #[]
  return instances.filterMap fun i => if fvarIdSet.contains i.fvarId then none else some i.idx
-/
partial def _root_.Lean.Expr.collectUnnecessaryInstanceBinderIdxsWhere (p : Expr -> Bool)
    (e : Expr) : MetaM (Array Nat) := do
.run {} let (instances, fvarIdSet) ← go e 0 #[]
  return instances.filterMap fun i => if fvarIdSet.contains i.fvarId then none else some i.idx
where
  /-- Enter foralls recursively, creating a telescope for binders which are instances of concern
  and instantiating all other bvars with `sorry`. The only free variables therefore arise from
  instances of concern which we want to track the usage of.

  By instantiating ordinary binders with `sorry`, `collectFVarsOutsideOfProofs` can use the
  computed field accessed by `hasFVar` (in constant time) to avoid traversing any subexpressions
  that do not contain a free variable for an instance of concern, which helps performance.

  Used fvarIds (i.e., instances of concern) are recorded in the `StateRefT`'s `FVarIdSet`; the
  returned `Array InstanceOfConcern` records all instances of concern that have been introduced,
  used or not. -/
  go (e : Expr) (currentBinderIdx : Nat) (currentFVars : Array InstanceOfConcern) :
      StateRefT FVarIdSet MetaM (Array InstanceOfConcern) := do
    let e := e.cleanupAnnotations
    if h : e.isForall then
      -- Collect instances in the forall domain.
      collectFVarsOutsideOfProofs (e.forallDomain h)
      if e.binderInfo.isInstImplicit && p (e.forallDomain h) then
        -- This forall introduces an instance of concern; make it an fvar.
        forallBoundedTelescope e (some 1) fun fvar e => do
          let fvarId := fvar[0]!.fvarId!
          go e (currentBinderIdx + 1) (currentFVars.push { fvarId, idx := currentBinderIdx })
      else
        -- This forall does not introduce a binder of concern. Instantiate the bvar with `sorry`.
        /- Perf note: Could possibly do better by taking a `forallTelescope`-like approach and going
        as many foralls forward as possible before instantiating, and instantiating the binding
        domains separately along the way. Not worth the complexity yet. -/
        let e := (e.forallBody h).instantiate1 (← mkSorry (e.forallDomain h) false)
        go e (currentBinderIdx + 1) currentFVars
    else
      match e with
      | .letE _ type value body _ =>
        -- See through `let`s
        collectFVarsOutsideOfProofs type
        collectFVarsOutsideOfProofs value
        /- Note: we could instantiate with `value`, but we risk redoing work if it has an fvar.
        The `let` value may in the future be necessary for certain purposes; if so, we could
        instantiate with `← mkExpectedTypeHint type value` plus metadata, and check for (and avoid)
        this metadata in `collectFVarsOutsideOfProofs`. -/
        let e := body.instantiate1 (← mkSorry type false)
        -- do not increment binder index, to retain compatibility with `forallTelescope` and friends
        go e currentBinderIdx currentFVars
      | e =>
        collectFVarsOutsideOfProofs e
        return currentFVars

/--
Definition of `_root_.Lean.ConstantVal.onUnusedInstancesWhere` / `_root_.Lean.ConstantVal.onUnusedInstancesWhere` 的定义

English:
definition _root_.Lean.ConstantVal.onUnusedInstancesWhere
  signature: (decl : ConstantVal)
  body: do
  let unusedInstances ← decl.type.collectUnnecessaryInstanceBinderIdxsWhere p
  if let some maxIdx := unusedInstances.back? then
    unless decl.type.hasSorry do -- only check for `sorry` in the "expensive" interactive case
      forallBoundedTelescope decl.type (some <| maxIdx + 1)
        (clea

中文:
定义 _root_.Lean.ConstantVal.onUnusedInstancesWhere
  签名: (decl : ConstantVal)
  定义体: do
  let unusedInstances ← decl.type.collectUnnecessaryInstanceBinderIdxsWhere p
  if let some maxIdx := unusedInstances.back? then
    unless decl.type.hasSorry do -- only check for `sorry` in the "expensive" interactive case
      forallBoundedTelescope decl.type (some <| maxIdx + 1)
        (clea
-/
def _root_.Lean.ConstantVal.onUnusedInstancesWhere (decl : ConstantVal)
    (p : Expr -> Bool) (logOnUnused : Array Parameter -> TermElabM Unit) :
    TermElabM Unit := do
  let unusedInstances ← decl.type.collectUnnecessaryInstanceBinderIdxsWhere p
  if let some maxIdx := unusedInstances.back? then
    unless decl.type.hasSorry do -- only check for `sorry` in the "expensive" interactive case
      forallBoundedTelescope decl.type (some <| maxIdx + 1)
        (cleanupAnnotations := true) fun fvars _ => do
          /- If the binder is not unused in the type per se (by bvar dependence), but is considered
          unused by `collectUnusedInstanceIdxsOf`, then it must have been used in a proof.
          We record this in the `appearsInTypeProof` field. -/
          let unusedEverywhereInstances := decl.type.getUnusedForallInstanceBinderIdxsWhere p
          let unusedInstances : Array Parameter ← unusedInstances.mapM fun idx =>
            return {
                fvar? := fvars[idx]?
                type? := ← fvars[idx]?.mapM (inferType ·)
                idx
                appearsInTypeProof := !unusedEverywhereInstances.contains idx
              }
          logOnUnused unusedInstances

/--
Finds theorems whose bodies were elaborated in the current infotrees and whose (full)
declaration names satisfy `nameFilter`. Checks their type to see if it contains instance hypotheses
that (1) are unused in the remainder of the type (2) have types which satisfy `instanceTypeFilter`.
(Note: `instanceTypeFilter` is non-monadic, and may encounter bound variables in its argument. This
is a performance optimization. `isAppOrForallOfConstP` may be useful in detecting constant
applications and types of the form `∀ (...), bar ..` here.)

If any such parameters are found in the type of a theorem `foo`, we create a telescope in which the
types and free variables of the unused parameters are available as
`unusedParams : Array Parameter := #[p₁, p₂, ..., pₙ]`, as well as the theorem `thm : ConstantVal`
and current infotree `t`, and run `log t thm unusedParams`.

A simple pattern is therefore
```
fun _ thm unusedParams => do
  logLint linter.fooLinter (← getRef) m!"\
    {thm.name.unusedInstancesMsg unusedParams}\n\n\
    <extra caption>"
```
which logs
```null
`{foo}` has the hypothes(is/es):
  • {p₁}
  • {p₂}
  ⋮
  • {pₙ}
which (is/are) not used in the remainder of the type.

<extra caption>

Note: This linter can be disabled with `set_option {linter.fooLinter.name} false`
```
pluralizing as appropriate.
-/
@[nolint unusedArguments] -- TODO: we plan to use `_cmd` in future
/--
Definition of `_root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere` / `_root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere` 的定义

English:
definition _root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere
  signature: (_cmd : Syntax)
  body: do
  for t in ← getInfoTrees do
.filter fun thm => let thms := t.getTheorems (← getEnv)
      declFilter thm && thm.type.hasInstanceBinderOf instanceTypeFilter
    -- use `liftTermElabM` on the outside in the hopes of sharing a cache
    unless thms.isEmpty do liftTermElabM do for thm in thms do
   

中文:
定义 _root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere
  签名: (_cmd : Syntax)
  定义体: do
  for t in ← getInfoTrees do
.filter fun thm => let thms := t.getTheorems (← getEnv)
      declFilter thm && thm.type.hasInstanceBinderOf instanceTypeFilter
    -- use `liftTermElabM` on the outside in the hopes of sharing a cache
    unless thms.isEmpty do liftTermElabM do for thm in thms do
   
-/
def _root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere (_cmd : Syntax)
    (instanceTypeFilter : Expr -> Bool)
    (log : InfoTree -> ConstantVal -> Array Parameter -> TermElabM Unit)
    (declFilter : ConstantVal -> Bool := fun _ => true) :
    CommandElabM Unit := do
  for t in ← getInfoTrees do
.filter fun thm => let thms := t.getTheorems (← getEnv)
      declFilter thm && thm.type.hasInstanceBinderOf instanceTypeFilter
    -- use `liftTermElabM` on the outside in the hopes of sharing a cache
    unless thms.isEmpty do liftTermElabM do for thm in thms do
      thm.onUnusedInstancesWhere instanceTypeFilter
        fun unusedParams =>
          -- TODO: restore in order to log on type signature. See (#31729)[https://github.com/leanprover-community/mathlib4/pull/31729].
          -- t.withDeclSigRef cmd thm.name do
          log t thm unusedParams

section Decidable

/--
Definition of `isDecidableVariant` / `isDecidableVariant` 的定义

English:
definition isDecidableVariant
  signature: (type : Expr)
  body: type.isAppOrForallOfConstP fun n =>
    n == ``Decidable ||
    n == ``DecidablePred ||
    n == ``DecidableRel ||
    n == ``DecidableEq ||
    n == ``DecidableLE ||
    n == ``DecidableLT

中文:
定义 isDecidableVariant
  签名: (type : Expr)
  定义体: type.isAppOrForallOfConstP fun n =>
    n == ``Decidable ||
    n == ``DecidablePred ||
    n == ``DecidableRel ||
    n == ``DecidableEq ||
    n == ``DecidableLE ||
    n == ``DecidableLT

Depends on / 依赖: Decidable, DecidableEq, DecidableLE, DecidableLT, DecidablePred, DecidableRel, isAppOrForallOfConstP, type.isAppOrForallOfConstP
-/
def isDecidableVariant (type : Expr) : Bool :=
  type.isAppOrForallOfConstP fun n =>
    n == ``Decidable ||
    n == ``DecidablePred ||
    n == ``DecidableRel ||
    n == ``DecidableEq ||
    n == ``DecidableLE ||
    n == ``DecidableLT

/-- `withSetOptionIn` currently breaks infotree searches, so we simply set `Bool` options
until this is fixed in [lean4#11313](https://github.com/leanprover/lean4/pull/11313). -/
public partial def withSetBoolOptionIn (x : CommandElab) : CommandElab
  | `(command| set_option $opt:ident $val in $cmd:command) => do
    match val.raw with
    | Syntax.atom _ "true" =>
withBoolOption opt.getId true withSetBoolOptionIn x cmd
    | Syntax.atom _ "false" =>
withBoolOption opt.getId false withSetBoolOptionIn x cmd
    | _ => withSetBoolOptionIn x cmd
  | `(command| $_:command in $cmd:command) => withSetBoolOptionIn x cmd
  | stx => x stx
where
  /-- Set a `Bool` option in `CommandElabM`. Ideally, `CommandElabM` would have a
  `MonadWithOptions` instance to this effect. -/
  withBoolOption (n : Name) (val : Bool) (k : CommandElabM Unit) : CommandElabM Unit := do
    let opts := (← getOptions).setBool n val
    Command.withScope (fun scope => { scope with opts }) k

/--
The `unusedDecidableInType` linter checks if a theorem's hypotheses include `Decidable*` instances
which are not used in the remainder of the type. If so, it suggests removing the instances and using
`classical` or `open scoped Classical in`, as appropriate, in the theorem's proof instead.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)

Note: `set_option linter.unusedDecidableInType _ in <command>` currently only works at the
outermost level of a command due to working around [lean4#11313](https://github.com/leanprover/lean4/pull/11313).
-/
public register_option linter.unusedDecidableInType : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a use of `classical` in the proof."
}

/--
Definition of `unusedDecidableInType` / `unusedDecidableInType` 的定义

English:
definition unusedDecidableInType
  signature: : Linter where
  body: withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedDecidableInType (← getLinterOptions) do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      /- Theorems in the `Decidable` namespace such as `Decidable.eq_or_ne` are allowed to depend
      on decidable instances witho

中文:
定义 unusedDecidableInType
  签名: : Linter where
  定义体: withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedDecidableInType (← getLinterOptions) do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      /- Theorems in the `Decidable` namespace such as `Decidable.eq_or_ne` are allowed to depend
      on decidable instances witho

Depends on / 依赖: withSetBoolOptionIn
-/
def unusedDecidableInType : Linter where
  run := withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedDecidableInType (← getLinterOptions) do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      /- Theorems in the `Decidable` namespace such as `Decidable.eq_or_ne` are allowed to depend
      on decidable instances without using them in the type. -/
      (declFilter := (!(`Decidable).isPrefixOf ·.name))
      isDecidableVariant
      fun _ thm unusedParams => do
        logLint linter.unusedDecidableInType (← getRef) m!"\
          {thm.name.unusedInstancesMsg unusedParams}\n\n\
          Consider removing \
          {if unusedParams.size = 1 then "this hypothesis" else "these hypotheses"} \
          and using `classical` in the proof instead. \
          For terms, consider using `open scoped Classical in` at the term level (not the \
          command level)."

initialize addLinter unusedDecidableInType

end Decidable

section Fintype

/--
The `unusedFintypeInType` linter checks if a theorem's hypotheses include `Fintype` instances
which are not used in the remainder of the type. If so, it suggests modifying the instances to
`Finite _` and using `Fintype.ofFinite` in the proof, or removing them entirely.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)
-/
public register_option linter.unusedFintypeInType : Bool := {
  defValue := false
  descr := "enable the unused `Fintype` instance linter, which lints against `Fintype` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a hypothesis of `Finite` or removed entirely."
}

/--
Definition of `unusedFintypeInType` / `unusedFintypeInType` 的定义

English:
definition unusedFintypeInType
  signature: : Linter where
  body: withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedFintypeInType (← getLinterOptions) do
      return
    -- Cheap early exit if `Fintype` is not imported.
    unless (← getEnv).isImportedConst `Fintype do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      (·.isAppOrF

中文:
定义 unusedFintypeInType
  签名: : Linter where
  定义体: withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedFintypeInType (← getLinterOptions) do
      return
    -- Cheap early exit if `Fintype` is not imported.
    unless (← getEnv).isImportedConst `Fintype do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      (·.isAppOrF

Depends on / 依赖: withSetBoolOptionIn
-/
def unusedFintypeInType : Linter where
  run := withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedFintypeInType (← getLinterOptions) do
      return
    -- Cheap early exit if `Fintype` is not imported.
    unless (← getEnv).isImportedConst `Fintype do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      (·.isAppOrForallOfConst `Fintype)
      fun _ thm unusedParams => do
        let importFintypeOfFiniteNote? :=
          if (← getEnv).isImportedConst `Fintype.ofFinite then none else
some .note "Add `import Mathlib.Data.Fintype.EquivFin` \
              to make `Fintype.ofFinite` available."
        logLint linter.unusedFintypeInType (← getRef) m!"\
          {thm.name.unusedInstancesMsg unusedParams}\n\n\
          Consider replacing \
          {if unusedParams.size = 1 then "this hypothesis" else "these hypotheses"} with the \
          corresponding {if unusedParams.size = 1 then "instance" else "instances"} of \
          `{.ofConstName `Finite}` and using \
          `{.ofConstName `Fintype.ofFinite}` in the proof, or removing \
          {if unusedParams.size = 1 then "it" else "them"} entirely.\
          {importFintypeOfFiniteNote?.getD m!""}"

initialize addLinter unusedFintypeInType

end Fintype

end Mathlib.Linter.UnusedInstancesInType
