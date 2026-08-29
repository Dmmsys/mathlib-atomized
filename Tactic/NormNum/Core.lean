/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Mathlib.Lean.Expr.Rat
public import Mathlib.Tactic.Hint
public import Mathlib.Tactic.NormNum.Result
public meta import Mathlib.Util.Qq
public import Lean.Elab.Tactic.Try -- shake: keep (`register_try?_tactic` command dependency)

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/

public meta section

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- `@[norm_num e]`, where `e` is an expression (optionally with `_`s) adds the tagged definition,
of type `NormNumExt`, to the set of normalization procedures used by the `norm_num` tactic, such
that it will fire on expressions matching the form `e`. Use holes in `e` to indicate arbitrary
subexpressions, for example `@[norm_num _ + _]` will match any addition.

* `@[norm_num e1, e2, ...]` will match either `e1` or `e2` or ...

Example:
```lean
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
  ra.neg
```
-/
syntax (name := norm_num) "norm_num " term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

/--
Definition of `NormNumExt` / `NormNumExt` 的定义

English:
structure NormNumExt
  parameters: where
  axioms and operations (4):
    - pre : = true
    - post : = true
    - eval({u : Level} {α : Q(Type u)} (e : Q($α))) : MetaM (Result e)
    - name : Name  [default: by exact decl_name%]

中文:
结构 NormNumExt
  参数: where
  公理与运算 (4 个):
    - pre : = true
    - post : = true
    - eval({u : Level} {α : Q(类型u)} (e : Q($α))) : MetaM (Result e)
    - name : Name  [默认: by exact decl_name%]

Depends on / 依赖: induced
-/
structure NormNumExt where
  /-- The extension should be run in the `pre` phase when used as simp plugin. -/
  pre := true
  /-- The extension should be run in the `post` phase when used as simp plugin. -/
  post := true
  /-- Attempts to prove an expression is equal to some explicit number of the relevant type. -/
  eval {u : Level} {α : Q(Type u)} (e : Q($α)) : MetaM (Result e)
  /-- The name of the `norm_num` extension. -/
  name : Name := by exact decl_name%

variable {u : Level}

/--
Definition of `mkNormNumExt` / `mkNormNumExt` 的定义

English:
definition mkNormNumExt
  signature: (n : Name)
  body: do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n

中文:
定义 mkNormNumExt
  签名: (n : Name)
  定义体: do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n
-/
def mkNormNumExt (n : Name) : ImportM NormNumExt := do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n

/--
Definition of `Entry` / `Entry` 的定义

English:
abbreviation Entry
  body: Array (Array DiscrTree.Key) × Name

中文:
缩写 Entry
  定义体: Array (Array DiscrTree.Key) × Name

Depends on / 依赖: DiscrTree, DiscrTree.Key, TopologicalSpace, WeaklyLocallyCompactSpace
-/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/--
Definition of `NormNums` / `NormNums` 的定义

English:
structure NormNums
  parameters: where
  axioms and operations (2):
    - tree : DiscrTree NormNumExt  [default: {}]
    - erased : PHashSet Name  [default: {}]

中文:
结构 NormNums
  参数: where
  公理与运算 (2 个):
    - tree : DiscrTree NormNumExt  [默认: {}]
    - erased : PHashSet Name  [默认: {}]
-/
structure NormNums where
  /-- The tree of `norm_num` extensions. -/
  tree : DiscrTree NormNumExt := {}
  /-- Erased `norm_num`s. -/
  erased : PHashSet Name := {}
  deriving Inhabited

/-- Environment extensions for `norm_num` declarations -/
initialize normNumExt : ScopedEnvExtension Entry (Entry × NormNumExt) NormNums ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq NormNumExt := ⟨fun _ _ => false⟩
  /- Insert `v : NormNumExt` into the tree `dt` on all key sequences given in `kss`. -/
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) => return (e, ← mkNormNumExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) =>
      { tree := insert kss ext tree, erased := erased.erase n }
  }

/--
Definition of `derive` / `derive` 的定义

English:
definition derive
  signature: {α : Q(Type u)} (e : Q($α)) (post := false)
  body: do
  if e.isRawNatLit then
    let lit : Q(Nat) := e
    return .isNat (q(Nat.instAddMonoidWithOne) : Q(AddMonoidWithOne Nat))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    le

中文:
定义 derive
  签名: {α : Q(类型u)} (e : Q($α)) (post := false)
  定义体: do
  if e.isRawNatLit then
    let lit : Q(Nat) := e
    return .isNat (q(Nat.instAddMonoidWithOne) : Q(AddMonoidWithOne Nat))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    le

Depends on / 依赖: Result
-/
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isRawNatLit then
    let lit : Q(Nat) := e
    return .isNat (q(Nat.instAddMonoidWithOne) : Q(AddMonoidWithOne Nat))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    let arr ← normNums.tree.getMatch e
    for ext in arr do
      if (bif post then ext.post else ext.pre) && ! normNums.erased.contains ext.name then
        try
let new ← withReducibleAndInstances ext.eval e
          trace[Tactic.norm_num] "{ext.name}:\n{e} ==> {new}"
          return new
        catch err =>
          trace[Tactic.norm_num] "{ext.name} failed {e}: {err.toMessageData}"
          s.restore
    throwError "{e}: no norm_nums apply"

/--
Definition of `deriveNat` / `deriveNat` 的定义

English:
definition deriveNat
  signature: {α : Q(Type u)} (e : Q($α))
  body: do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

中文:
定义 deriveNat
  签名: {α : Q(类型u)} (e : Q($α))
  定义体: do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

Depends on / 依赖: derive, failure, with_reducible
-/
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
    MetaM ((lit : Q(Nat)) × Q(IsNat $e $lit)) := do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

/--
Definition of `deriveInt` / `deriveInt` 的定义

English:
definition deriveInt
  signature: {α : Q(Type u)} (e : Q($α))
  body: do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

中文:
定义 deriveInt
  签名: {α : Q(类型u)} (e : Q($α))
  定义体: do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

Depends on / 依赖: derive, failure, with_reducible
-/
def deriveInt {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Ring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(Int)) × Q(IsInt $e $lit)) := do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

/--
Definition of `deriveRat` / `deriveRat` 的定义

English:
definition deriveRat
  signature: {α : Q(Type u)} (e : Q($α))
  body: do
  let some res := (← derive e).toRat' | failure
  pure res

中文:
定义 deriveRat
  签名: {α : Q(类型u)} (e : Q($α))
  定义体: do
  let some res := (← derive e).toRat' | failure
  pure res

Depends on / 依赖: derive, failure, with_reducible
-/
def deriveRat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(DivisionRing $α) := by with_reducible assumption) :
    MetaM (Rat × (n : Q(Int)) × (d : Q(Nat)) × Q(IsRat $e $n $d)) := do
  let some res := (← derive e).toRat' | failure
  pure res

/--
Definition of `deriveBool` / `deriveBool` 的定义

English:
definition deriveBool
  signature: (p : Q(Prop))
  body: do
  let .isBool b prf ← derive q($p) | failure
  pure ⟨b, prf⟩

中文:
定义 deriveBool
  签名: (p : Q(命题))
  定义体: do
  let .isBool b prf ← derive q($p) | failure
  pure ⟨b, prf⟩

Depends on / 依赖: LocallyCompactSpace, WeaklyLocallyCompactSpace, WeaklyLocallyCompactSpace.locallyCompactSpace, locallyCompactSpace
-/
def deriveBool (p : Q(Prop)) : MetaM ((b : Bool) × BoolResult p b) := do
  let .isBool b prf ← derive q($p) | failure
  pure ⟨b, prf⟩

/--
Definition of `deriveBoolOfIff` / `deriveBoolOfIff` 的定义

English:
definition deriveBoolOfIff
  signature: (p p' : Q(Prop)) (hp : Q($p ↔ $p'))
  body: do
  let ⟨b, pb⟩ ← deriveBool p
  match (dependent := true) b with
  | true => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩

中文:
定义 deriveBoolOfIff
  签名: (p p' : Q(命题)) (hp : Q($p ↔ $p'))
  定义体: do
  let ⟨b, pb⟩ ← deriveBool p
  match (dependent := true) b with
  | true => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩
-/
def deriveBoolOfIff (p p' : Q(Prop)) (hp : Q($p ↔ $p')) :
    MetaM ((b : Bool) × BoolResult p' b) := do
  let ⟨b, pb⟩ ← deriveBool p
  match (dependent := true) b with
  | true => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (e : Expr) (post := false)
  body: do
  if e.isExplicitNumber then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult

中文:
定义 eval
  签名: (e : Expr) (post := false)
  定义体: do
  if e.isExplicitNumber then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult

Depends on / 依赖: Result, Simp.Result
-/
def eval (e : Expr) (post := false) : MetaM Simp.Result := do
  if e.isExplicitNumber then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult

/--
Definition of `NormNums.eraseCore` / `NormNums.eraseCore` 的定义

English:
definition NormNums.eraseCore
  signature: (d : NormNums) (declName : Name)
  body: { d with erased := d.erased.insert declName }

中文:
定义 NormNums.eraseCore
  签名: (d : NormNums) (declName : Name)
  定义体: { d with erased := d.erased.insert declName }

Depends on / 依赖: d.erased.insert, declName, erased, insert
-/
def NormNums.eraseCore (d : NormNums) (declName : Name) : NormNums :=
  { d with erased := d.erased.insert declName }

/--
Definition of `NormNums.erase` / `NormNums.erase` 的定义

English:
definition NormNums.erase
  signature: {m : Type -> Type} [Monad m] [MonadError m] (d : NormNums) (declName : Name)
  body: do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName

中文:
定义 NormNums.erase
  签名: {m : Type -> Type} [Monad m] [MonadError m] (d : NormNums) (declName : Name)
  定义体: do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName
-/
def NormNums.erase {m : Type -> Type} [Monad m] [MonadError m] (d : NormNums) (declName : Name) :
    m NormNums := do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName

initialize registerBuiltinAttribute {
  name := `norm_num
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| norm_num $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `norm_num declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkNormNumExt declName
let keys ← MetaM.run' es.getElems.mapM fun stx => do
let e ← TermElabM.run' withSaveInfoContext withAutoBoundImplicit
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      normNumExt.add ((keys, declName), ext) kind
      -- TODO: track what `[norm_num]` decls are actually used at use sites
      recordExtraRevUseOfCurrentModule
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := normNumExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => normNumExt.modifyState env fun _ => s
}

/--
Definition of `tryNormNum` / `tryNormNum` 的定义

English:
definition tryNormNum
  signature: (post := false) (e : Expr)
  body: do
  try
    return .done (← eval e post)
  catch _ =>
    return .continue

中文:
定义 tryNormNum
  签名: (post := false) (e : Expr)
  定义体: do
  try
    return .done (← eval e post)
  catch _ =>
    return .continue

Depends on / 依赖: Simp.Step
-/
def tryNormNum (post := false) (e : Expr) : SimpM Simp.Step := do
  try
    return .done (← eval e post)
  catch _ =>
    return .continue

/--
Definition of `methods` / `methods` 的定义

English:
definition methods
  signature: (useSimp := true)
  body: if useSimp then {
    pre := Simp.preDefault #[] >> tryNormNum
    post := Simp.postDefault #[] >> tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  } else {
    pre := tryNormNum
    post := tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  }

中文:
定义 methods
  签名: (useSimp := true)
  定义体: if useSimp then {
    pre := Simp.preDefault #[] >> tryNormNum
    post := Simp.postDefault #[] >> tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  } else {
    pre := tryNormNum
    post := tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  }

Depends on / 依赖: Methods, Simp.Methods
-/
def methods (useSimp := true) : Simp.Methods :=
  if useSimp then {
    pre := Simp.preDefault #[] >> tryNormNum
    post := Simp.postDefault #[] >> tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  } else {
    pre := tryNormNum
    post := tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  }

/--
Definition of `deriveSimp` / `deriveSimp` 的定义

English:
definition deriveSimp
  signature: (ctx : Simp.Context) (useSimp := true) (e : Expr)
  body: (·.1) < > Simp.main e ctx (methods := methods useSimp)

中文:
定义 deriveSimp
  签名: (ctx : Simp.Context) (useSimp := true) (e : Expr)
  定义体: (·.1) < > Simp.main e ctx (methods := methods useSimp)

Depends on / 依赖: Result, Simp.Result
-/
def deriveSimp (ctx : Simp.Context) (useSimp := true) (e : Expr) : MetaM Simp.Result :=
(·.1) < > Simp.main e ctx (methods := methods useSimp)

/--
Definition of `discharge` / `discharge` 的定义

English:
definition discharge
  signature: (useSimp := true) (e : Expr)
  body: do
  (← deriveSimp (← readThe Simp.Context) useSimp e).ofTrue

中文:
定义 discharge
  签名: (useSimp := true) (e : Expr)
  定义体: do
  (← deriveSimp (← readThe Simp.Context) useSimp e).ofTrue

Depends on / 依赖: IsInducing, Topology, Topology.IsInducing.subtypeVal.completelyRegularSpace, completelyRegularSpace, subtypeVal
-/
def discharge (useSimp := true) (e : Expr) : SimpM (Option Expr) := do
  (← deriveSimp (← readThe Simp.Context) useSimp e).ofTrue

open Tactic in
/--
Definition of `getSimpContext` / `getSimpContext` 的定义

English:
definition getSimpContext
  signature: (cfg args : Syntax) (simpOnly := false)
  body: do
  let { config, userConfig } ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let { ctx, .. } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := {})
      (← Simp.mkContext config (simpTh

中文:
定义 getSimpContext
  签名: (cfg args : Syntax) (simpOnly := false)
  定义体: do
  let { config, userConfig } ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let { ctx, .. } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := {})
      (← Simp.mkContext config (simpTh

Depends on / 依赖: Context, Simp.Context, TacticM
-/
def getSimpContext (cfg args : Syntax) (simpOnly := false) : TacticM Simp.Context := do
  let { config, userConfig } ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let { ctx, .. } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := {})
      (← Simp.mkContext config (simpTheorems := #[simpTheorems])
        (congrTheorems := ← getSimpCongrTheorems) (userConfig := userConfig))
  return ctx

open Elab Tactic in
/--
Definition of `elabNormNum` / `elabNormNum` 的定义

English:
definition elabNormNum
  signature: (cfg args loc : Syntax) (simpOnly := false) (useSimp := true)
  body: withMainContext do
  let ctx ← getSimpContext cfg args (!useSimp || simpOnly)
  let loc := expandOptLocation loc
  transformAtNondepPropLocation (fun e ctx => deriveSimp ctx useSimp e) "norm_num" loc
    (ifUnchanged := .silent) (mayCloseGoalFromHyp := true) ctx

中文:
定义 elabNormNum
  签名: (cfg args loc : Syntax) (simpOnly := false) (useSimp := true)
  定义体: withMainContext do
  let ctx ← getSimpContext cfg args (!useSimp || simpOnly)
  let loc := expandOptLocation loc
  transformAtNondepPropLocation (fun e ctx => deriveSimp ctx useSimp e) "norm_num" loc
    (ifUnchanged := .silent) (mayCloseGoalFromHyp := true) ctx

Depends on / 依赖: useSimp
-/
def elabNormNum (cfg args loc : Syntax) (simpOnly := false) (useSimp := true) :
    TacticM Unit := withMainContext do
  let ctx ← getSimpContext cfg args (!useSimp || simpOnly)
  let loc := expandOptLocation loc
  transformAtNondepPropLocation (fun e ctx => deriveSimp ctx useSimp e) "norm_num" loc
    (ifUnchanged := .silent) (mayCloseGoalFromHyp := true) ctx

end Meta.NormNum

namespace Tactic
open Lean.Parser.Tactic Meta.NormNum

/--
`norm_num` normalizes numerical expressions in the goal. By default, it supports the operations
`+` `-` `*` `/` `⁻¹` `^` and `%` over types with (at least) an `AddMonoidWithOne` instance, such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`. In addition to evaluating numerical expressions, `norm_num` will use `simp`
to simplify the goal. If the goal has the form `A = B`, `A ≠ B`, `A < B` or `A ≤ B`, where `A` and
`B` are numerical expressions, `norm_num` will try to close it. It also has a relatively simple
primality prover (available if you import `Mathlib.Tactic.NormNum.Prime`).

This tactic is extensible. Extensions can allow `norm_num` to evaluate more kinds of expressions, or
to prove more kinds of propositions (such as, primality of natural numbers). See the `@[norm_num]`
attribute for further information on extending `norm_num`.

* `norm_num at l` normalizes at location(s) `l`.
* `norm_num [h1, ...]` adds the arguments `h1, ...` to the `simp` set in addition to the default
  `simp` set. All options for `simp` arguments are supported, in particular `←`, `↑` and `↓`.
* `norm_num only` does not use the default `simp` set for simplification. `norm_num only [h1, ...]`
  uses only the arguments `h1, ...` in addition to the routines tagged `@[norm_num]`.
  `norm_num only` still performs post-processing steps, like `simp only`, use `norm_num1` if you
  exclusively want to normalize numerical expressions.
* `norm_num (config := cfg)` uses `cfg` as configuration for `simp` calls (see the `simp` tactic for
  further details).

Examples:
```lean
example : 43 ≤ 74 + (33 : ℤ) := by norm_num
example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num
```
-/
elab (name := normNum)
    "norm_num" cfg:optConfig only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum cfg args loc (simpOnly := only.isSome) (useSimp := true)

/--
`norm_num1` normalizes numerical expressions in the goal. It is a basic version of `norm_num`
that does not call `simp`.

By default, it supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%` over types with (at least)
an `AddMonoidWithOne` instance, such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`. If the goal has the form `A = B`,
`A ≠ B`, `A < B` or `A ≤ B`, where `A` and `B` are numerical expressions, `norm_num1` will try to
close it. It also has a relatively simple primality prover.
:e
This tactic is extensible. Extensions can allow `norm_num1` to evaluate more kinds of expressions,
or to prove more kinds of propositions. See the `@[norm_num]` attribute for further information on
extending `norm_num1`.

* `norm_num1 at l` normalizes at location(s) `l`.

Examples:
```lean
example : 43 ≤ 74 + (33 : ℤ) := by norm_num1
example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num1
```
-/
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode mkNullNode loc (simpOnly := true) (useSimp := false)

open Lean Elab Tactic

@[inherit_doc normNum1] syntax (name := normNum1Conv) "norm_num1" : conv

/--
Definition of `elabNormNum1Conv` / `elabNormNum1Conv` 的定义

English:
definition elabNormNum1Conv
  signature: : Tactic
  body: fun _ => withMainContext do
  let ctx ← getSimpContext mkNullNode mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv)
    "norm_num" optConfig &" only"? (simpArgs)? : conv

中文:
定义 elabNormNum1Conv
  签名: : Tactic
  定义体: fun _ => withMainContext do
  let ctx ← getSimpContext mkNullNode mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv)
    "norm_num" optConfig &" only"? (simpArgs)? : conv
-/
@[tactic normNum1Conv] def elabNormNum1Conv : Tactic := fun _ => withMainContext do
  let ctx ← getSimpContext mkNullNode mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv)
    "norm_num" optConfig &" only"? (simpArgs)? : conv

/--
Definition of `elabNormNumConv` / `elabNormNumConv` 的定义

English:
definition elabNormNumConv
  signature: : Tactic
  body: fun stx => withMainContext do
  let ctx ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

中文:
定义 elabNormNumConv
  签名: : Tactic
  定义体: fun stx => withMainContext do
  let ctx ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

Depends on / 依赖: completelyRegularSpace_iInf, completelyRegularSpace_induced
-/
@[tactic normNumConv] def elabNormNumConv : Tactic := fun stx => withMainContext do
  let ctx ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

/-- `#norm_num e`, where `e` is an expression, will print the `norm_num` form of `e`.
Unlike `norm_num`, this command does not fail when no simplifications are made.
`#norm_num` understands local variables, so you can use them to introduce parameters.

(In the variants below, the `:` is optional but helpful for the parser.)

* `#norm_num [h1, ...] : e` adds the arguments `h1, ...` to the `simp` set in addition to the
  default `simp` set. All options for `simp` arguments are supported, in particular `←`, `↑`
  and `↓`.
* `#norm_num only : e` and `#norm_num only [h1, ...] : e` do not use the default `simp` set for
  simplification.
* `#norm_num (config := cfg) : e` uses `cfg` as configuration for `simp` calls (see the `simp`
  tactic for further details).
-/
macro (name := normNumCmd) "#norm_num" cfg:optConfig o:(&" only")?
    args:(Parser.Tactic.simpArgs)? " :"? ppSpace e:term : command =>
  `(command| #conv norm_num $cfg:optConfig $[only%$o]? $(args)? => $e)

end Mathlib.Tactic

/-!
We register `norm_num` with the `hint` tactic.
-/

register_hint 1000 norm_num
register_try?_tactic (priority := 1000) norm_num
