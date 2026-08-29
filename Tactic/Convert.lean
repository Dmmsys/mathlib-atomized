/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Kyle Miller
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.CongrExclamation

/-!
# The `convert` tactic.

The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine e`,
but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal using the same strategies as the `congr!` tactic.
For example, in the proof state

```lean
n : ℕ,
e : Prime (2 * n + 1)
⊢ Prime (n + n + 1)
```

the tactic `convert e` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The `convert` tactic applies congruence lemmas eagerly before reducing,
therefore it can fail in cases where `exact` succeeds:
```lean
def p (n : ℕ) := True
example (h : p 0) : p 1 := by exact h -- succeeds
example (h : p 0) : p 1 := by convert h -- fails, with leftover goal `1 = 0`
```
Limiting the depth of recursion can help with this. For example, `convert h using 0` will work
in this case.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr!`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr! n`). In the example, `convert e using 1`
would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.

Refer to the `congr!` tactic to understand the congruence operations. One of its many
features is that if `x y : t` and an instance `Subsingleton t` is in scope,
then any goals of the form `x = y` are solved automatically.

Like `congr!`, `convert` takes an optional `with` clause of `rintro` patterns,
for example `convert e using n with x y z`.

The `convert` tactic also takes a configuration option, for example
```lean
convert (config := {transparency := .default}) h
```
These are passed to `congr!`. See `Congr!.Config` for options.
-/

public meta section

open Lean Meta Elab Tactic

/--
Definition of `Convert.CheapConfig` / `Convert.CheapConfig` 的定义

English:
structure Convert.CheapConfig
  parameters: extends Congr!.Config
  extends: Congr!.Config
  axioms and operations (2):
    - postTransparency : = .reducible
    - sameFun : = true

中文:
结构 Convert.CheapConfig
  参数: extends 余ngr!.余nfig
  继承: 余ngr!.余nfig
  公理与运算 (2 个):
    - postTransparency : = .reducible
    - sameFun : = true

Depends on / 依赖: reducible
-/
structure Convert.CheapConfig extends Congr!.Config where
  postTransparency := .reducible
  sameFun := true

/-- Internal elaborator for `Convert.CheapConfig`: use `Convert.elabConfig` instead. -/
declare_config_elab Convert.elabCheapConfig Convert.CheapConfig

/--
Definition of `Convert.ExpensiveConfig` / `Convert.ExpensiveConfig` 的定义

English:
structure Convert.ExpensiveConfig
  parameters: extends Congr!.Config
  extends: Congr!.Config
  (no additional axioms)

中文:
结构 Convert.ExpensiveConfig
  参数: extends 余ngr!.余nfig
  继承: 余ngr!.余nfig
  (无附加公理)
-/
structure Convert.ExpensiveConfig extends Congr!.Config where
  -- TODO: also enable this in the future?
  -- preTransparency := .default
  -- transparency := .default

/-- Internal elaborator for `Convert.ExpensiveConfig`: use `Convert.elabConfig` instead. -/
declare_config_elab Convert.elabExpensiveConfig Convert.ExpensiveConfig

/--
Definition of `Convert.elabConfig` / `Convert.elabConfig` 的定义

English:
definition Convert.elabConfig
  signature: (expensive : Bool) (stx : Syntax)
  body: do
  -- Implement overridable fields by choosing to elaborate one of two structures,
  -- which have different defaults (that can later be overridden by the user).
  if expensive then
    pure { ← Convert.elabExpensiveConfig stx with }
  else
    pure { ← Convert.elabCheapConfig stx with }

中文:
定义 Convert.elabConfig
  签名: (expensive : 布尔值) (stx : Syntax)
  定义体: do
  -- Implement overridable fields by choosing to elaborate one of two structures,
  -- which have different defaults (that can later be overridden by the user).
  if expensive then
    pure { ← Convert.elabExpensiveConfig stx with }
  else
    pure { ← Convert.elabCheapConfig stx with }
-/
def Convert.elabConfig (expensive : Bool) (stx : Syntax) : TacticM Congr!.Config := do
  -- Implement overridable fields by choosing to elaborate one of two structures,
  -- which have different defaults (that can later be overridden by the user).
  if expensive then
    pure { ← Convert.elabExpensiveConfig stx with }
  else
    pure { ← Convert.elabCheapConfig stx with }

/--
Definition of `Lean.MVarId.convert` / `Lean.MVarId.convert` 的定义

English:
definition Lean.MVarId.convert
  signature: (e : Expr) (symm : Bool)
  body: g.withContext do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if symm then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if symm then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns

中文:
定义 Lean.MVarId.convert
  签名: (e : Expr) (symm : 布尔值)
  定义体: g.withContext do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if symm then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if symm then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns

Depends on / 依赖: Config, config
-/
def Lean.MVarId.convert (e : Expr) (symm : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rintroPat) := []) (g : MVarId) :
    MetaM (List MVarId) := g.withContext do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if symm then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if symm then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns

/--
Definition of `Lean.MVarId.convertLocalDecl` / `Lean.MVarId.convertLocalDecl` 的定义

English:
definition Lean.MVarId.convertLocalDecl
  signature: (g : MVarId) (fvarId : FVarId) (typeNew : Expr) (symm : Bool)
  body: g.withContext do
  let typeOld ← fvarId.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq
    (if symm then #[typeNew, typeOld] else #[typeOld, typeNew]))
  let pf ← if symm then mkEqSymm v else pure v
  let res ← g.replaceLocalDecl fvarId typeNew pf
  let gs ← v.mvarId!.congrN! depth config patterns
  return (res.mvarId, gs)

中文:
定义 Lean.MVarId.convertLocalDecl
  签名: (g : MVarId) (fvarId : FVarId) (typeNew : Expr) (symm : 布尔值)
  定义体: g.withContext do
  let typeOld ← fvarId.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq
    (if symm then #[typeNew, typeOld] else #[typeOld, typeNew]))
  let pf ← if symm then mkEqSymm v else pure v
  let res ← g.replaceLocalDecl fvarId typeNew pf
  let gs ← v.mvarId!.congrN! depth config patterns
  return (res.mvarId, gs)

Depends on / 依赖: Config, config
-/
def Lean.MVarId.convertLocalDecl (g : MVarId) (fvarId : FVarId) (typeNew : Expr) (symm : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rintroPat) := []) :
    MetaM (MVarId × List MVarId) := g.withContext do
  let typeOld ← fvarId.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq
    (if symm then #[typeNew, typeOld] else #[typeOld, typeNew]))
  let pf ← if symm then mkEqSymm v else pure v
  let res ← g.replaceLocalDecl fvarId typeNew pf
  let gs ← v.mvarId!.congrN! depth config patterns
  return (res.mvarId, gs)

namespace Mathlib.Tactic

/--
`convert e`, where the term `e` is inferred to have type `t`, replaces the main goal `⊢ t'` with new
goals for proving the equality `t' = t` using congruence. The goals are created like `congr!` would.
Like `refine e`, any holes (`?_` or `?x`) in `e` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

See also `convert_to t`, where `t` specifies the expected type, instead of a proof term of type `t`.
In other words, `convert_to t` works like `convert (?_ : t)`. Both tactics use the same options.

* `convert! e` uses default transparency, rather than reducible, when solving side goals, and
  it tries to apply congruence even if the two expressions do not have the same head constant.
* `convert ← e` creates equality goals in the opposite direction (with the goal type on the right).
* `convert e using n`, where `n` is a numeral, controls the depth with which congruence is
  applied. For example, if the main goal is `⊢ Prime (n + n + 1)` and `e : Prime (2 * n + 1)`, then
  `convert e using 2` results in one goal, `⊢ n + n = 2 * n`, and `convert e using 3` (or more)
  results in two (impossible) goals `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  By default, the depth is unlimited.
* `convert e with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `convert (config := cfg) e` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).

Examples:

```lean
example {n : ℕ} (e : Prime (2 * n + 1)) :
    Prime (n + n + 1) := by
  convert e
  -- One goal: ⊢ n + n = 2 * n
  ring

-- `convert` can fail where `exact` succeeds.
def p (n : ℕ) := True
example (h : p 0) : p 1 := by
  fail_if_success
    convert h -- fails, left-over goal 1 = 0
    done
  exact h -- succeeds

-- `convert with` names introduced variables.
example (p q : Nat → Prop) (h : ∀ ε > 0, p ε) :
    ∀ ε > 0, q ε := by
  convert h with ε hε
  -- Goal now looks like:
  -- hε : ε > 0
  -- ⊢ q ε ↔ p ε
  sorry
```
-/
syntax (name := convert) "convert" "!"? Lean.Parser.Tactic.optConfig " ←"? ppSpace term
  (" using " num)? (" with" (ppSpace colGt rintroPat)*)? : tactic

@[tactic_alt convert]
syntax (name := convert!) "convert!" Lean.Parser.Tactic.optConfig " ←"? ppSpace term
  (" using " num)? (" with" (ppSpace colGt rintroPat)*)? : tactic

macro_rules
| `(tactic| convert! $cfg $[←%$l]? $t $[using $n]? $[with $[$w]*]?) =>
    `(tactic| convert ! $cfg $[←%$l]? $t:term $[using $n]? $[with $[$w]*]?)

/--
Definition of `elabTermForConvert` / `elabTermForConvert` 的定义

English:
definition elabTermForConvert
  signature: (term : Syntax) (expectedType? : Option Expr)
  body: do
  withCollectingNewGoalsFrom (parentTag := ← getMainTag) (tagSuffix := `convert)
      (allowNaturalHoles := true) do
    -- Allow typeclass inference failures since these will be inferred by unification
    -- or else become new goals
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
      let t ← elabTermEnsuringType (mayPostpone := true) term expectedType?
      -- Process everything so that tactics get run, but again allow TC failures
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      return t

elab_rules : tactic
| `(tactic| convert $[!%$expensive]? $cfg $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← Convert.elabConfig expensive.isSome cfg
    let patterns := (ps?.getD #[]).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ← elabTermForConvert term expectedType
    liftMetaTactic fun g =>
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs

中文:
定义 elabTermForConvert
  签名: (term : Syntax) (expectedType? : 选项类型 Expr)
  定义体: do
  withCollectingNewGoalsFrom (parentTag := ← getMainTag) (tagSuffix := `convert)
      (allowNaturalHoles := true) do
    -- Allow typeclass inference failures since these will be inferred by unification
    -- or else become new goals
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
      let t ← elabTermEnsuringType (mayPostpone := true) term expectedType?
      -- Process everything so that tactics get run, but again allow TC failures
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      return t

elab_rules : tactic
| `(tactic| convert $[!%$expensive]? $cfg $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← Convert.elabConfig expensive.isSome cfg
    let patterns := (ps?.getD #[]).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ← elabTermForConvert term expectedType
    liftMetaTactic fun g =>
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs
-/
def elabTermForConvert (term : Syntax) (expectedType? : Option Expr) :
    TacticM (Expr × List MVarId) := do
  withCollectingNewGoalsFrom (parentTag := ← getMainTag) (tagSuffix := `convert)
      (allowNaturalHoles := true) do
    -- Allow typeclass inference failures since these will be inferred by unification
    -- or else become new goals
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
      let t ← elabTermEnsuringType (mayPostpone := true) term expectedType?
      -- Process everything so that tactics get run, but again allow TC failures
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      return t

elab_rules : tactic
| `(tactic| convert $[!%$expensive]? $cfg $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← Convert.elabConfig expensive.isSome cfg
    let patterns := (ps?.getD #[]).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ← elabTermForConvert term expectedType
    liftMetaTactic fun g =>
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs

/--
`convert_to t` on a goal `⊢ t'` changes the goal to `⊢ t` and adds new goals for proving the
equality `t' = t` using congruence. The goals are created like `congr!` would.
Any remaining congruence goals come before the main goal.
Like `refine e`, any holes (`?_` or `?x`) in `t` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert_to` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

`convert e`, where `e` is a term of type `t`, uses `e` to close the new main goal. In other words,
`convert e` works like `convert_to t; refine e`. Both tactics use the same options.

* `convert_to! t` uses default transparency, rather than reducible, when solving side goals.
* `convert_to ty at h` changes the type of the local hypothesis `h` to `ty`. If later local
  hypotheses or the goal depend on `h`, then `convert_to t at h` may leave a copy of `h`.
* `convert_to ← t` creates equality goals in the opposite direction (with the original goal type on
  the right).
* `convert_to t using n`, where `n` is a positive numeral, controls the depth with which congruence
  is applied. For example, if the main goal is `⊢ Prime (n + n + 1)`,
  then `convert_to Prime (2 * n + 1) using 2` results in one goal, `⊢ n + n = 2 * n`, and
  `convert_to Prime (2 * n + 1) using 3` (or more) results in two (impossible) goals
  `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  The default value for `n` is 1.
* `convert_to t with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `convert_to (config := cfg) t` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).
-/
syntax (name := convertTo) "convert_to" ("!")? Lean.Parser.Tactic.optConfig " ←"? ppSpace term
  (" using " num)? (" with" (ppSpace colGt rintroPat)*)? (Parser.Tactic.location)? : tactic

@[tactic_alt convertTo]
syntax (name := convert_to!) "convert_to!" Lean.Parser.Tactic.optConfig " ←"? ppSpace term
  (" using " num)? (" with" (ppSpace colGt rintroPat)*)? (Parser.Tactic.location)? : tactic

macro_rules
| `(tactic| convert_to! $cfg $[←%$l]? $t $[using $n]? $[with $w]? $[$loc]?) =>
    `(tactic| convert_to ! $cfg $[←%$l]? $t:term $[using $n]? $[with $w]? $[$loc]?)

elab_rules : tactic
| `(tactic| convert_to $[!%$expensive]? $cfg $[←%$sym]? $newType $[using $n]?
 [with $ps?*]? [$loc?:location]?) => do
.getD 1 .map (·.getNat) let n : Nat := n
  let config ← Convert.elabConfig expensive.isSome cfg
  let patterns := (ps?.getD #[]).toList
  withLocation (expandOptLocation (mkOptionalNode loc?))
    (atLocal := fun fvarId => do
      let (e, gs) ← elabTermForConvert newType (← inferType (← fvarId.getType))
      liftMetaTactic fun g => do
        let (g', gs') ← g.convertLocalDecl fvarId e sym.isSome n config patterns
        return (gs' ++ (g' :: gs)))
    (atTarget := do
      let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
      let (e, gs) ← elabTermForConvert (← `((id ?_ : $newType))) expectedType
      liftMetaTactic fun g =>
        return (← g.convert e sym.isSome n config patterns) ++ gs)
    (failed := fun _ => throwError "convert_to failed")

/--
`ac_change t` on a goal `⊢ t'` changes the goal to `⊢ t` and adds new goals for proving the equality
`t' = t` using congruence, then tries proving these goals by associativity and commutativity. The
goals are created like `congr!` would.
In other words, `ac_change t` is like `convert_to t` followed by `ac_refl`.

Like `refine e`, any holes (`?_` or `?x`) in `t` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert_to` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

* `ac_change! t` uses default transparency, rather than reducible, when solving side goals.
* `ac_change t using n`, where `n` is a positive numeral, controls the depth with which congruence
  is applied. For example, if the main goal is `⊢ Prime ((a * b + 1) + c)`,
  then `ac_change Prime ((1 + a * b) + c) using 2` solves the side goals, and
  `ac_change Prime ((1 + a * b) + c) using 3` (or more) results in two (impossible) goals
  `⊢ 1 = a * b` and `⊢ a * b = 1`.
  The default value for `n` is 1.

Example:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```
-/
syntax (name := acChange) "ac_change " term (" using " num)? : tactic
@[tactic_alt acChange]
syntax (name := acChange!) "ac_change! " term (" using " num)? : tactic

macro_rules
| `(tactic| ac_change $t $[using $n]?) =>
    `(tactic| convert_to $t:term $[using $n]? <;> try ac_rfl)
| `(tactic| ac_change! $t $[using $n]?) =>
    `(tactic| convert_to! $t:term $[using $n]? <;> try ac_rfl)

end Mathlib.Tactic
