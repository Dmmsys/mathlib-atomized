/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.RCases
public meta import Lean.Meta.Tactic.Assumption
public meta import Lean.Meta.Tactic.Rfl
public meta import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Logic.Basic
public import Mathlib.Lean.Meta.CongrTheorems

/-!
# The `congr!` tactic

This is a more powerful version of the `congr` tactic that knows about more congruence lemmas and
can apply to more situations. It is similar to the `congr'` tactic from Mathlib 3.

The `congr!` tactic is used by the `convert` and `convert_to` tactics.

## Detailed description

`congr!` equates pieces of the left-hand side of a goal to corresponding pieces of the right-hand
side by recursively applying congruence lemmas. For example, with `⊢ f as = g bs` we could get
two goals `⊢ f = g` and `⊢ as = bs`.

Syntax:
```
congr!
congr! n
congr! with x y z
congr! n with x y z
```
Here, `n` is a natural number and `x`, `y`, `z` are `rintro` patterns (like `h`, `rfl`, `⟨x, y⟩`,
`_`, `-`, `(h | h)`, etc.).

The `congr!` tactic is similar to `congr` but is more insistent in trying to equate left-hand sides
to right-hand sides of goals. Here is an exhaustive list of things it can try:

- If `R` in `⊢ R x y` is a reflexive relation, it will convert the goal to `⊢ x = y` if possible.
  The list of reflexive relations is maintained using the `@[refl]` attribute.
  As a special case, `⊢ p ↔ q` is converted to `⊢ p = q` during congruence processing and then
  returned to `⊢ p ↔ q` form at the end.

- If there is a user congruence lemma associated to the goal (for instance, a `@[congr]`-tagged
  lemma applying to `⊢ List.map f xs = List.map g ys`), then it will use that.

- It uses a congruence lemma generator at least as capable as the one used by `congr` and `simp`.
  If there is a subexpression that can be rewritten by `simp`, then `congr!` should be able
  to generate an equality for it.

- It can do congruences of pi types using lemmas like `implies_congr` and `pi_congr`.

- Before applying congruences, it will run the `intros` tactic automatically.
  The introduced variables can be given names using a `with` clause.
  This helps when congruence lemmas provide additional assumptions in hypotheses.

- When there is an equality between functions, so long as at least one is obviously a lambda, we
  apply `funext` or `Function.hfunext`, which allows for congruence of lambda bodies.

- It can try to close goals using a few strategies, including checking
  definitional equality, trying to apply `Subsingleton.elim` or `proof_irrel_heq`, and using the
  `assumption` tactic. Discharging is done at default transparency (unless specified otherwise),
  but this will become reducible transparency in the future.

The optional parameter is the depth of the recursive applications.
This is useful when `congr!` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr!` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr! 2` produces the intended `⊢ x + y = y + x`.

The `congr!` tactic also takes a configuration option, for example
```lean
congr! (transparency := .default) 2
```
This overrides the default, which is to apply congruence lemmas at reducible transparency.

The `congr!` tactic is aggressive with equating two sides of everything. There is a predefined
configuration that uses a different strategy:
```lean
congr! (config := .unfoldSameFun)
```
This only allows congruences between functions applications of definitionally equal functions,
and it applies congruence lemmas at default transparency (rather than just reducible).
This is somewhat like `congr`.

See `Congr!.Config` for all options.
-/

public meta section

universe u v

open Lean Meta Elab Tactic

initialize registerTraceClass `congr!
initialize registerTraceClass `congr!.synthesize

/--
Definition of `Congr!.Config` / `Congr!.Config` 的定义

English:
structure Congr!.Config
  parameters: where
  axioms and operations (13):
    - closePre : Bool  [default: true]
    - closePost : Bool  [default: true]
    - transparency : TransparencyMode  [default: TransparencyMode.reducible]
    - preTransparency : TransparencyMode  [default: TransparencyMode.reducible]
    - postTransparency : TransparencyMode  [default: TransparencyMode.default]
    - preferLHS : Bool  [default: true]
    - partialApp : Bool  [default: true]
    - sameFun : Bool  [default: false]
    - maxArgs : Option Nat  [default: none]
    - typeEqs : Bool  [default: false]
    - etaExpand : Bool  [default: false]
    - useCongrSimp : Bool  [default: false]
    - beqEq : Bool  [default: true]

中文:
结构 Congr!.Config
  参数: where
  公理与运算 (13 个):
    - closePre : 布尔  [默认: true]
    - closePost : 布尔  [默认: true]
    - transparency : TransparencyMode  [默认: TransparencyMode.reducible]
    - preTransparency : TransparencyMode  [默认: TransparencyMode.reducible]
    - postTransparency : TransparencyMode  [默认: TransparencyMode.default]
    - preferLHS : 布尔  [默认: true]
    - partialApp : 布尔  [默认: true]
    - sameFun : 布尔  [默认: false]
    - maxArgs : Option 自然数  [默认: none]
    - typeEqs : 布尔  [默认: false]
    - etaExpand : 布尔  [默认: false]
    - useCongrSimp : 布尔  [默认: false]
    - beqEq : 布尔  [默认: true]

Depends on / 依赖: applying, before, congruence, lemmas
-/
structure Congr!.Config where
  /-- If `closePre := true`, then try to close goals before applying congruence lemmas
  using tactics such as `rfl` and `assumption`. These tactics are applied with the
  transparency level specified by `preTransparency`, which is `.reducible` by default. -/
  closePre : Bool := true
  /-- If `closePost := true`, then try to close goals that remain after no more congruence
  lemmas can be applied, using the same tactics as `closePre`. These tactics are applied
  with the transparency level specified by `postTransparency`, which is currently default
  transparency but in the future will become `.reducible` by default. -/
  closePost : Bool := true
  /-- The transparency level to use when applying a congruence theorem.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  transparency : TransparencyMode := TransparencyMode.reducible
  /-- The transparency level to use when trying to close goals before applying congruence lemmas.
  This includes trying to prove the goal by `rfl` and using the `assumption` tactic.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  preTransparency : TransparencyMode := TransparencyMode.reducible
  /-- The transparency level to use when trying to close goals after no more congruence lemmas can
  be applied. This includes trying to prove the goal by `rfl` and using the `assumption` tactic.
  For backwards compatibility this is set to `.default`, which will be changed in the future to
  `.reducible`.
  -/
  postTransparency : TransparencyMode := TransparencyMode.default
  /-- For passes that synthesize a congruence lemma using one side of the equality,
  we run the pass both for the left-hand side and the right-hand side. If `preferLHS` is `true`
  then we start with the left-hand side.

  This can be used to control which side's definitions are expanded when applying the
  congruence lemma (if `preferLHS = true` then the RHS can be expanded). -/
  preferLHS : Bool := true
  /-- Allow both sides to be partial applications, and allow overapplications.
  When false, given an equality `f a b = g x y z` this means we never consider
  proving `f a = g x y`.

  In this case, we might still consider `f = g x` if a pass generates a congruence lemma using the
  left-hand side. Use `sameFun := true` to ensure both sides are applications
  of the same function (making it be similar to the `congr` tactic). -/
  partialApp : Bool := true
  /-- Whether to require that both sides of an equality be applications of defeq functions.
  That is, if true, `f a = g x` is only considered if `f` and `g` are defeq (making it be similar
  to the `congr` tactic). -/
  sameFun : Bool := false
  /-- The maximum number of arguments to consider when doing congruence of function applications.
  For example, with `f a b c = g w x y z`, setting `maxArgs := some 2` means it will only consider
  either `f a b = g w x y` and `c = z` or `f a = g w x`, `b = y`, and `c = z`. Setting
  `maxArgs := none` (the default) means no limit.

  When the functions are dependent, `maxArgs` can prevent congruence from working at all.
  In `Fintype.card α = Fintype.card β`, one needs to have `maxArgs` at `2` or higher since
  there is a `Fintype` instance argument that depends on the first.

  When there aren't such dependency issues, setting `maxArgs := some 1` causes `congr!` to
  do congruence on a single argument at a time. This can be used in conjunction with the
  iteration limit to control exactly how many arguments are to be processed by congruence. -/
  maxArgs : Option Nat := none
  /-- For type arguments that are implicit or have forward dependencies, whether or not `congr!`
  should generate equalities even if the types do not look plausibly equal.

  We have a heuristic in the main congruence generator that types
  `α` and `β` are *plausibly equal* according to the following algorithm:

  - If the types are both propositions, they are plausibly equal (`Iff`s are plausible).
  - If the types are from different universes, they are not plausibly equal.
  - Suppose in whnf we have `α = f a₁ ... aₘ` and `β = g b₁ ... bₘ`. If `f` is not definitionally
    equal to `g` or `m ≠ n`, then `α` and `β` are not plausibly equal.
  - If there is some `i` such that `aᵢ` and `bᵢ` are not plausibly equal, then `α` and `β` are
    not plausibly equal.
  - Otherwise, `α` and `β` are plausibly equal.

  The purpose of this is to prevent considering equalities like `ℕ = ℤ` while allowing equalities
  such as `Fin n = Fin m` or `Subtype p = Subtype q` (so long as these are subtypes of the
  same type).

  The way this is implemented is that when the congruence generator is comparing arguments when
  looking at an equality of function applications, it marks a function parameter as "fixed" if the
  provided arguments are types that are not plausibly equal. The effect of this is that congruence
  succeeds only if those arguments are defeq at `transparency` transparency. -/
  typeEqs : Bool := false
  /-- As a last pass, perform eta expansion of both sides of an equality. For example,
  this transforms a bare `HAdd.hAdd` into `fun x y => x + y`. -/
  etaExpand : Bool := false
  /-- Whether to use the congruence generator that is used by `simp` and `congr`. This generator
  is more strict, and it does not respect all configuration settings. It does respect
  `preferLHS`, `partialApp` and `maxArgs` and transparency settings. It acts as if `sameFun := true`
  and it ignores `typeEqs`. -/
  useCongrSimp : Bool := false
  /-- Whether to use a special congruence lemma for `BEq` instances.
  This synthesizes `LawfulBEq` instances to discharge equalities of `BEq` instances. -/
  beqEq : Bool := true

/--
Definition of `Congr!.Config.unfoldSameFun` / `Congr!.Config.unfoldSameFun` 的定义

English:
definition Congr!.Config.unfoldSameFun
  signature: : Congr!.Config where
  body: false
  sameFun := true
  transparency := .default
  preTransparency := .default
  postTransparency := .default

中文:
定义 Congr!.Config.unfoldSameFun
  签名: : Congr!.Config where
  定义体: false
  sameFun := true
  transparency := .default
  preTransparency := .default
  postTransparency := .default
-/
@[expose] def Congr!.Config.unfoldSameFun : Congr!.Config where
  partialApp := false
  sameFun := true
  transparency := .default
  preTransparency := .default
  postTransparency := .default

/--
Definition of `Congr!.Config.numArgsOk` / `Congr!.Config.numArgsOk` 的定义

English:
definition Congr!.Config.numArgsOk
  signature: (config : Config) (numArgs : Nat)
  body: numArgs <= config.maxArgs.getD numArgs

中文:
定义 Congr!.Config.numArgsOk
  签名: (config : Config) (numArgs : 自然数)
  定义体: numArgs <= config.maxArgs.getD numArgs
-/
def Congr!.Config.numArgsOk (config : Config) (numArgs : Nat) : Bool :=
  numArgs <= config.maxArgs.getD numArgs

/--
Definition of `Congr!.Config.maxArgsFor` / `Congr!.Config.maxArgsFor` 的定义

English:
definition Congr!.Config.maxArgsFor
  signature: (config : Config) (numArgs : Nat)
  body: min numArgs (config.maxArgs.getD numArgs)

中文:
定义 Congr!.Config.maxArgsFor
  签名: (config : Config) (numArgs : 自然数)
  定义体: min numArgs (config.maxArgs.getD numArgs)
-/
def Congr!.Config.maxArgsFor (config : Config) (numArgs : Nat) : Nat :=
  min numArgs (config.maxArgs.getD numArgs)

/--
Definition of `applyCongrThm?` / `applyCongrThm?` 的定义

English:
definition applyCongrThm?
  body: do
  trace[congr!] "trying to apply congr lemma {congrThmType}"
  try
    let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
    let (fvarId, mvarId) ← mvarId.intro1P
let mvarIds ← withTransparency config.transparency
      mvarId.apply (mkFVar fvarId) { synthAssi

中文:
定义 applyCongrThm?
  定义体: do
  trace[congr!] "trying to apply congr lemma {congrThmType}"
  try
    let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
    let (fvarId, mvarId) ← mvarId.intro1P
let mvarIds ← withTransparency config.transparency
      mvarId.apply (mkFVar fvarId) { synthAssi
-/
private def applyCongrThm?
    (config : Congr!.Config) (mvarId : MVarId) (congrThmType congrThmProof : Expr) :
    MetaM (List MVarId) := do
  trace[congr!] "trying to apply congr lemma {congrThmType}"
  try
    let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
    let (fvarId, mvarId) ← mvarId.intro1P
let mvarIds ← withTransparency config.transparency
      mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
    mvarIds.mapM fun mvarId => mvarId.tryClear fvarId
  catch e =>
    withTraceNode `congr! (fun _ => pure m!"failed to apply congr lemma") do
      trace[congr!] "{e.toMessageData}"
    throw e

/--
Definition of `Congr!.plausiblyEqualTypes` / `Congr!.plausiblyEqualTypes` 的定义

English:
definition Congr!.plausiblyEqualTypes
  signature: (ty1 ty2 : Expr) (maxDepth : Nat := 5)
  body: match maxDepth with
  | 0 => return false
  | maxDepth + 1 => do
    -- Props are plausibly equal
    if (← isProp ty1) && (← isProp ty2) then
      return true
    -- Types from different type universes are not plausibly equal.
    -- This is redundant, but it saves carrying out the remaining check

中文:
定义 Congr!.plausiblyEqualTypes
  签名: (ty1 ty2 : Expr) (maxDepth : 自然数 := 5)
  定义体: match maxDepth with
  | 0 => return false
  | maxDepth + 1 => do
    -- Props are plausibly equal
    if (← isProp ty1) && (← isProp ty2) then
      return true
    -- Types from different type universes are not plausibly equal.
    -- This is redundant, but it saves carrying out the remaining check
-/
def Congr!.plausiblyEqualTypes (ty1 ty2 : Expr) (maxDepth : Nat := 5) : MetaM Bool :=
  match maxDepth with
  | 0 => return false
  | maxDepth + 1 => do
    -- Props are plausibly equal
    if (← isProp ty1) && (← isProp ty2) then
      return true
    -- Types from different type universes are not plausibly equal.
    -- This is redundant, but it saves carrying out the remaining checks.
unless ← withNewMCtxDepth isDefEq (← inferType ty1) (← inferType ty2) do
      return false
    -- Now put the types into whnf, check they have the same head, and then recurse on arguments
    let ty1 ← whnfD ty1
    let ty2 ← whnfD ty2
unless ← withNewMCtxDepth isDefEq ty1.getAppFn ty2.getAppFn do
      return false
    for arg1 in ty1.getAppArgs, arg2 in ty2.getAppArgs do
      if (← isType arg1) && (← isType arg2) then
        unless ← plausiblyEqualTypes arg1 arg2 maxDepth do
          return false
    return true

/--
This is like `Lean.MVarId.hcongr?` but (1) looks at both sides when generating the congruence lemma
and (2) inserts additional hypotheses from equalities from previous arguments.

It uses `Lean.Meta.mkRichHCongr` to generate the congruence lemmas.

If the goal is an `Eq`, it uses `eq_of_heq` first.

As a backup strategy, it uses the LHS/RHS method like in `Lean.MVarId.congrSimp?`
(where `Congr!.Config.preferLHS` determines which side to try first). This uses a particular side
of the target, generates the congruence lemma, then tries applying it. This can make progress
with higher transparency settings. To help the unifier, in this mode it assumes both sides have the
exact same function.
-/
partial
/--
Definition of `Lean.MVarId.smartHCongr?` / `Lean.MVarId.smartHCongr?` 的定义

English:
definition Lean.MVarId.smartHCongr?
  signature: (config : Congr!.Config) (mvarId : MVarId)
  body: mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs [] [] then
        return mvars
      -- The "cor

中文:
定义 Lean.MVarId.smartHCongr?
  签名: (config : Congr!.Config) (mvarId : MVarId)
  定义体: mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs [] [] then
        return mvars
      -- The "cor

Depends on / 依赖: checkNotAssigned, commitWhenSome, eqOfHEq, getType, mvarId, mvarId.checkNotAssigned, mvarId.eqOfHEq, mvarId.getType, mvarId.withContext, return, withContext, withReducible
-/
def Lean.MVarId.smartHCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs [] [] then
        return mvars
      -- The "correct" behavior failed. However, it's often useful
      -- to apply congruence lemmas while unfolding definitions, which is what the
      -- basic `congr` tactic does due to limitations in how congruence lemmas are generated.
      -- We simulate this behavior here by generating congruence lemmas for the LHS and RHS and
      -- then applying them.
      trace[congr!] "Default smartHCongr? failed, trying LHS/RHS method"
      let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
      if let some mvars ← forSide mvarId fst then
        return mvars
      else if let some mvars ← forSide mvarId snd then
        return mvars
      else
        return none
where
  loop (mvarId : MVarId) (numArgs : Nat) (lhs rhs : Expr) (lhsArgs rhsArgs : List Expr) :
      MetaM (Option (List MVarId)) :=
    match lhs.cleanupAnnotations, rhs.cleanupAnnotations with
    | .app f a, .app f' b => do
      if not (config.numArgsOk (numArgs + 1)) then
        return none
      let lhsArgs' := a :: lhsArgs
      let rhsArgs' := b :: rhsArgs
      -- We try to generate a theorem for the maximal number of arguments
      if let some mvars ← loop mvarId (numArgs + 1) f f' lhsArgs' rhsArgs' then
        return mvars
      -- That failing, we now try for the present number of arguments.
      if not config.partialApp && f.isApp && f'.isApp then
        -- It's a partial application on both sides though.
        return none
      -- The congruence generator only handles the case where both functions have
      -- definitionally equal types.
unless ← withNewMCtxDepth isDefEq (← inferType f) (← inferType f') do
        return none
let funDefEq ← withReducible withNewMCtxDepth isDefEq f f'
      if config.sameFun && not funDefEq then
        return none
      let info ← getFunInfoNArgs f (numArgs + 1)
      let mut fixed : Array Bool := #[]
      for larg in lhsArgs', rarg in rhsArgs', pinfo in info.paramInfo do
        if !config.typeEqs && (!pinfo.isExplicit || pinfo.hasFwdDeps) then
          -- When `typeEqs = false` then for non-explicit arguments or
          -- arguments with forward dependencies, we want type arguments
          -- to be plausibly equal.
          if ← isType larg then
            -- ^ since `f` and `f'` have defeq types, this implies `isType rarg`.
            unless ← Congr!.plausiblyEqualTypes larg rarg do
              fixed := fixed.push true
              continue
        fixed := fixed.push (← withReducible <| withNewMCtxDepth <| isDefEq larg rarg)
      let cthm ← mkRichHCongr (forceHEq := true) (← inferType f) info
                  (fixedFun := funDefEq) (fixedParams := fixed)
      -- Now see if the congruence theorem actually applies in this situation by applying it!
      let (congrThm', congrProof') :=
        if funDefEq then
          (cthm.type.bindingBody!.instantiate1 f, cthm.proof.beta #[f])
        else
          (cthm.type.bindingBody!.bindingBody!.instantiateRev #[f, f'],
           cthm.proof.beta #[f, f'])
observing? applyCongrThm? config mvarId congrThm' congrProof'
    | _, _ => return none
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let numArgs := config.maxArgsFor side.getAppNumArgs
    if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
    let mut f := side
    for _ in [:numArgs] do
      f := f.appFn!'
    let info ← getFunInfoNArgs f numArgs
    let mut fixed : Array Bool := #[]
    if !config.typeEqs then
      -- We need some strategy for fixed parameters to keep `forSide` from applying
      -- in cases where `Congr!.possiblyEqualTypes` suggested not to in the previous pass.
      for pinfo in info.paramInfo, arg in side.getAppArgs do
        if pinfo.isProp || !(← isType arg) then
          fixed := fixed.push false
        else if pinfo.isExplicit && !pinfo.hasFwdDeps then
          -- It's fine generating equalities for explicit type arguments without forward
          -- dependencies. Only allowing these is a little strict, because an argument
          -- might be something like `Fin n`. We might consider being able to generate
          -- congruence lemmas that only allow equalities where they can plausibly go,
          -- but that would take looking at a whole application tree.
          fixed := fixed.push false
        else
          fixed := fixed.push true
    let cthm ← mkRichHCongr (forceHEq := true) (← inferType f) info
                (fixedFun := true) (fixedParams := fixed)
    let congrThm' := cthm.type.bindingBody!.instantiate1 f
    let congrProof' := cthm.proof.beta #[f]
observing? applyCongrThm? config mvarId congrThm' congrProof'

/--
Definition of `Lean.MVarId.congrSimp?` / `Lean.MVarId.congrSimp?` 的定义

English:
definition Lean.MVarId.congrSimp?
  signature: (config : Congr!.Config) (mvarId : MVarId)
  body: mvarId.withContext do
    mvarId.checkNotAssigned `congrSimp?
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide mvarId fst then
      return mvars
    else if let

中文:
定义 Lean.MVarId.congrSimp?
  签名: (config : Congr!.Config) (mvarId : MVarId)
  定义体: mvarId.withContext do
    mvarId.checkNotAssigned `congrSimp?
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide mvarId fst then
      return mvars
    else if let

Depends on / 依赖: checkNotAssigned, config, config.preferLHS, congrSimp, forSide, getType, mvarId, mvarId.checkNotAssigned, mvarId.getType, mvarId.withContext, preferLHS, return, withContext, withReducible
-/
def Lean.MVarId.congrSimp? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congrSimp?
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide mvarId fst then
      return mvars
    else if let some mvars ← forSide mvarId snd then
      return mvars
    else
      return none
where
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) :=
    commitWhenSome? do
      let side := side.cleanupAnnotations
      if not side.isApp then return none
      let numArgs := config.maxArgsFor side.getAppNumArgs
      if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
      let mut f := side
      for _ in [:numArgs] do
        f := f.appFn!'
      let some congrThm ← mkCongrSimpNArgs f numArgs
        | return none
observing? applyCongrThm? config mvarId congrThm.type congrThm.proof
  /-- Like `mkCongrSimp?` but takes in a specific arity. -/
  mkCongrSimpNArgs (f : Expr) (nArgs : Nat) : MetaM (Option CongrTheorem) := do
    let f := (← Lean.instantiateMVars f).cleanupAnnotations
    let info ← getFunInfoNArgs f nArgs
    mkCongrSimpCore? f info
      (← getCongrSimpKinds f info) (subsingletonInstImplicitRhs := false)

/--
Definition of `Lean.MVarId.userCongr?` / `Lean.MVarId.userCongr?` 的定义

English:
definition Lean.MVarId.userCongr?
  signature: (config : Congr!.Config) (mvarId : MVarId)
  body: mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, rhs) := (← withReducible mvarId.getType').eqOrIff? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide fst then
      return mvars
    else if let some

中文:
定义 Lean.MVarId.userCongr?
  签名: (config : Congr!.Config) (mvarId : MVarId)
  定义体: mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, rhs) := (← withReducible mvarId.getType').eqOrIff? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide fst then
      return mvars
    else if let some

Depends on / 依赖: checkNotAssigned, config, config.preferLHS, eqOrIff, forSide, getType, mvarId, mvarId.checkNotAssigned, mvarId.getType, mvarId.withContext, preferLHS, return, userCongr, withContext, withReducible
-/
def Lean.MVarId.userCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, rhs) := (← withReducible mvarId.getType').eqOrIff? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide fst then
      return mvars
    else if let some mvars ← forSide snd then
      return mvars
    else
      return none
where
  forSide (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let some name := side.getAppFn.constName? | return none
    let congrTheorems := (← getSimpCongrTheorems).get name
    -- Note: congruence theorems are provided in decreasing order of priority.
    for congrTheorem in congrTheorems do
      let res ← observing? do
        let cinfo ← getConstInfo congrTheorem.theoremName
        let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let proof := mkConst congrTheorem.theoremName us
        let ptype ← instantiateTypeLevelParams cinfo.toConstantVal us
        applyCongrThm? config mvarId ptype proof
      if let some mvars := res then
        return mvars
    return none

/--
Definition of `Lean.MVarId.congrPi?` / `Lean.MVarId.congrPi?` 的定义

English:
definition Lean.MVarId.congrPi?
  signature: (mvarId : MVarId)
  body: observing? do withReducible mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)

中文:
定义 Lean.MVarId.congrPi?
  签名: (mvarId : MVarId)
  定义体: observing? do withReducible mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)

Depends on / 依赖: mkConstWithFreshMVarLevels, mvarId, mvarId.apply, observing, pi_congr, withReducible
-/
def Lean.MVarId.congrPi? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
observing? do withReducible mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)

/--
Definition of `Lean.MVarId.obviousFunext?` / `Lean.MVarId.obviousFunext?` 的定义

English:
definition Lean.MVarId.obviousFunext?
  signature: (mvarId : MVarId)
  body: mvarId.withContext observing? do
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)

中文:
定义 Lean.MVarId.obviousFunext?
  签名: (mvarId : MVarId)
  定义体: mvarId.withContext observing? do
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)

Depends on / 依赖: cleanupAnnotations, failure, getType, isLambda, lhs.cleanupAnnotations.isLambda, mkConstWithFreshMVarLevels, mvarId, mvarId.apply, mvarId.getType, mvarId.withContext, observing, rhs.cleanupAnnotations.isLambda, withContext, withReducible
-/
def Lean.MVarId.obviousFunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
mvarId.withContext observing? do
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)

/--
Definition of `Lean.MVarId.obviousHfunext?` / `Lean.MVarId.obviousHfunext?` 的定义

English:
definition Lean.MVarId.obviousHfunext?
  signature: (mvarId : MVarId)
  body: mvarId.withContext observing? do
    let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)

中文:
定义 Lean.MVarId.obviousHfunext?
  签名: (mvarId : MVarId)
  定义体: mvarId.withContext observing? do
    let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)

Depends on / 依赖: Function, Function.hfunext, cleanupAnnotations, failure, getType, hfunext, isLambda, lhs.cleanupAnnotations.isLambda, mkConstWithFreshMVarLevels, mvarId, mvarId.apply, mvarId.getType, mvarId.withContext, observing, rhs.cleanupAnnotations.isLambda, withContext, withReducible
-/
def Lean.MVarId.obviousHfunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
mvarId.withContext observing? do
    let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)

/--
theorem `implies_congr'` / 定理 `implies_congr'`

English:
theorem implies_congr'
  given: {α α' : Sort u} {β β' : Sort v} (h : α = α') (h' : α' -> β = β')
  proof: by
  cases h
  change (forall (x : α), (fun _ => β) x) = _
  rw [funext h']

中文:
定理 implies_congr'
  条件: {α α' : Sort u} {β β' : Sort v} (h : α = α') (h' : α' -> β = β')
  证明: by
  cases h
  change (forall (x : α), (fun _ => β) x) = _
  rw [funext h']
-/
private theorem implies_congr' {α α' : Sort u} {β β' : Sort v} (h : α = α') (h' : α' -> β = β') :
    (α -> β) = (α' -> β') := by
  cases h
  change (forall (x : α), (fun _ => β) x) = _
  rw [funext h']

/--
Definition of `Lean.MVarId.congrImplies?'` / `Lean.MVarId.congrImplies?'` 的定义

English:
definition Lean.MVarId.congrImplies?'
  signature: (mvarId : MVarId)
  body: observing? do
    let [mvarId₁, mvarId₂] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr')
      | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]

中文:
定义 Lean.MVarId.congrImplies?'
  签名: (mvarId : MVarId)
  定义体: observing? do
    let [mvarId₁, mvarId₂] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr')
      | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]

Depends on / 依赖: implies_congr, mkConstWithFreshMVarLevels, mvarId, mvarId.apply, number, observing, return, throwError, unexpected
-/
def Lean.MVarId.congrImplies?' (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let [mvarId₁, mvarId₂] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr')
      | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]

/--
Definition of `Lean.MVarId.subsingletonHelim?` / `Lean.MVarId.subsingletonHelim?` 的定义

English:
definition Lean.MVarId.subsingletonHelim?
  signature: (mvarId : MVarId)
  body: mvarId.withContext observing? do
    mvarId.checkNotAssigned `subsingletonHelim
    let some (α, lhs, β, rhs) := (← withReducible mvarId.getType').heq? | failure
    withSubsingletonAsFast fun elim => do
      let eqmvar ← mkFreshExprSyntheticOpaqueMVar (← mkEq α β) (← mvarId.getTag)
      -- First 

中文:
定义 Lean.MVarId.subsingletonHelim?
  签名: (mvarId : MVarId)
  定义体: mvarId.withContext observing? do
    mvarId.checkNotAssigned `subsingletonHelim
    let some (α, lhs, β, rhs) := (← withReducible mvarId.getType').heq? | failure
    withSubsingletonAsFast fun elim => do
      let eqmvar ← mkFreshExprSyntheticOpaqueMVar (← mkEq α β) (← mvarId.getTag)
      -- First 

Depends on / 依赖: checkNotAssigned, eqmvar, failure, getTag, getType, mkFreshExprSyntheticOpaqueMVar, mvarId, mvarId.checkNotAssigned, mvarId.getTag, mvarId.getType, mvarId.withContext, observing, subsingletonHelim, withContext, withReducible, withSubsingletonAsFast
-/
def Lean.MVarId.subsingletonHelim? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
mvarId.withContext observing? do
    mvarId.checkNotAssigned `subsingletonHelim
    let some (α, lhs, β, rhs) := (← withReducible mvarId.getType').heq? | failure
    withSubsingletonAsFast fun elim => do
      let eqmvar ← mkFreshExprSyntheticOpaqueMVar (← mkEq α β) (← mvarId.getTag)
      -- First try synthesizing using the left-hand side for the Subsingleton instance
      if let some pf ← observing? (mkAppM ``FastSubsingleton.helim #[eqmvar, lhs, rhs]) then
mvarId.assign elim pf
        return [eqmvar.mvarId!]
      let eqsymm ← mkAppM ``Eq.symm #[eqmvar]
      -- Second try synthesizing using the right-hand side for the Subsingleton instance
      if let some pf ← observing? (mkAppM ``FastSubsingleton.helim #[eqsymm, rhs, lhs]) then
mvarId.assign elim (← mkAppM ``HEq.symm #[pf])
        return [eqmvar.mvarId!]
      failure

/--
Definition of `Lean.MVarId.beqInst?` / `Lean.MVarId.beqInst?` 的定义

English:
definition Lean.MVarId.beqInst?
  signature: (mvarId : MVarId)
  body: observing? do withReducible mvarId.applyConst ``lawful_beq_subsingleton

中文:
定义 Lean.MVarId.beqInst?
  签名: (mvarId : MVarId)
  定义体: observing? do withReducible mvarId.applyConst ``lawful_beq_subsingleton

Depends on / 依赖: applyConst, lawful_beq_subsingleton, mvarId, mvarId.applyConst, observing, withReducible
-/
def Lean.MVarId.beqInst? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
observing? do withReducible mvarId.applyConst ``lawful_beq_subsingleton

/--
Definition of `Lean.MVarId.congrPasses!` / `Lean.MVarId.congrPasses!` 的定义

English:
definition Lean.MVarId.congrPasses!
  signature: :
  body: [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   ("congr simp lemma", when (·.useCongrSimp) congrSimp?),
   ("Subsingleton.helim", fun _ => subsingletonHelim?),
   ("BEq instances", when (·.beqEq) fun _ => beqInst?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfun

中文:
定义 Lean.MVarId.congrPasses!
  签名: :
  定义体: [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   ("congr simp lemma", when (·.useCongrSimp) congrSimp?),
   ("Subsingleton.helim", fun _ => subsingletonHelim?),
   ("BEq instances", when (·.beqEq) fun _ => beqInst?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfun

Depends on / 依赖: Subsingleton, Subsingleton.helim, beqInst, congrImplies, congrPi, congrSimp, congr_implies, congr_pi, hcongr, hfunext, instances, obvious, obviousFunext, obviousHfunext, smartHCongr, subsingletonHelim, useCongrSimp, userCongr
-/
def Lean.MVarId.congrPasses! :
    List (String × (Congr!.Config -> MVarId -> MetaM (Option (List MVarId)))) :=
  [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   ("congr simp lemma", when (·.useCongrSimp) congrSimp?),
   ("Subsingleton.helim", fun _ => subsingletonHelim?),
   ("BEq instances", when (·.beqEq) fun _ => beqInst?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfunext", fun _ => obviousHfunext?),
   ("congr_implies", fun _ => congrImplies?'),
   ("congr_pi", fun _ => congrPi?)]
where
  /--
  Conditionally runs a congruence strategy depending on the predicate `b` applied to the config.
  -/
  when (b : Congr!.Config -> Bool) (f : Congr!.Config -> MVarId -> MetaM (Option (List MVarId)))
      (config : Congr!.Config) (mvar : MVarId) : MetaM (Option (List MVarId)) := do
    unless b config do return none
    f config mvar

/--
Definition of `CongrState` / `CongrState` 的定义

English:
structure CongrState
  parameters: where
  axioms and operations (2):
    - goals : Array MVarId
    - patterns : List (TSyntax `rintroPat)

中文:
结构 CongrState
  参数: where
  公理与运算 (2 个):
    - goals : Array MVarId
    - patterns : List (TSyntax `rintroPat)
-/
structure CongrState where
  /-- Accumulated goals that `congr!` could not handle. -/
  goals : Array MVarId
  /-- Patterns to use when doing intro. -/
  patterns : List (TSyntax `rintroPat)

/--
Definition of `CongrMetaM` / `CongrMetaM` 的定义

English:
abbreviation CongrMetaM
  body: StateRefT CongrState MetaM

中文:
缩写 CongrMetaM
  定义体: StateRefT CongrState MetaM

Depends on / 依赖: CongrState, StateRefT
-/
abbrev CongrMetaM := StateRefT CongrState MetaM

/--
Definition of `CongrMetaM.nextPattern` / `CongrMetaM.nextPattern` 的定义

English:
definition CongrMetaM.nextPattern
  signature: : CongrMetaM (Option (TSyntax `rintroPat))
  body: do
  modifyGet fun s =>
    if let p :: ps := s.patterns then
      (p, {s with patterns := ps})
    else
      (none, s)

中文:
定义 CongrMetaM.nextPattern
  签名: : CongrMetaM (Option (TSyntax `rintroPat))
  定义体: do
  modifyGet fun s =>
    if let p :: ps := s.patterns then
      (p, {s with patterns := ps})
    else
      (none, s)
-/
def CongrMetaM.nextPattern : CongrMetaM (Option (TSyntax `rintroPat)) := do
  modifyGet fun s =>
    if let p :: ps := s.patterns then
      (p, {s with patterns := ps})
    else
      (none, s)

/--
theorem `heq_imp_of_eq_imp` / 定理 `heq_imp_of_eq_imp`

English:
theorem heq_imp_of_eq_imp
  statement: {α : Sort*} {x y : α} {p : x ≍ y -> Prop}
  proof: by
  cases he
  exact h rfl

中文:
定理 heq_imp_of_eq_imp
  结论: {α : Sort*} {x y : α} {p : x ≍ y -> 命题}
  证明: by
  cases he
  exact h rfl
-/
private theorem heq_imp_of_eq_imp {α : Sort*} {x y : α} {p : x ≍ y -> Prop}
    (h : (he : x = y) -> p (heq_of_eq he)) (he : x ≍ y) : p he := by
  cases he
  exact h rfl

/--
theorem `eq_imp_of_iff_imp` / 定理 `eq_imp_of_iff_imp`

English:
theorem eq_imp_of_iff_imp
  statement: {x y : Prop} {p : x = y -> Prop}
  proof: by
  cases he
  exact h Iff.rfl

中文:
定理 eq_imp_of_iff_imp
  结论: {x y : 命题} {p : x = y -> 命题}
  证明: by
  cases he
  exact h Iff.rfl
-/
private theorem eq_imp_of_iff_imp {x y : Prop} {p : x = y -> Prop}
    (h : (he : x ↔ y) -> p (propext he)) (he : x = y) : p he := by
  cases he
  exact h Iff.rfl

/--
Does `Lean.MVarId.intros` but then cleans up the introduced hypotheses, removing anything
that is trivial. If there are any patterns in the current `CongrMetaM` state then instead
of `Lean.MVarId.intros` it does `Lean.Elab..Tactic.RCases.rintro`.

Cleaning up includes:
- deleting hypotheses of the form `x ≍ x`, `x = x`, and `x ↔ x`.
- deleting Prop hypotheses that are already in the local context.
- converting `x ≍ y` to `x = y` if possible.
- converting `x = y` to `x ↔ y` if possible.
-/
partial
/--
Definition of `Lean.MVarId.introsClean` / `Lean.MVarId.introsClean` 的定义

English:
definition Lean.MVarId.introsClean
  signature: (mvarId : MVarId)
  body: loop mvarId

中文:
定义 Lean.MVarId.introsClean
  签名: (mvarId : MVarId)
  定义体: loop mvarId

Depends on / 依赖: mvarId
-/
def Lean.MVarId.introsClean (mvarId : MVarId) : CongrMetaM (List MVarId) :=
  loop mvarId
where
  heqImpOfEqImp (mvarId : MVarId) : MetaM (Option MVarId) :=
observing? withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``heq_imp_of_eq_imp) | failure
      return mvarId
  eqImpOfIffImp (mvarId : MVarId) : MetaM (Option MVarId) :=
observing? withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``eq_imp_of_iff_imp) | failure
      return mvarId
  loop (mvarId : MVarId) : CongrMetaM (List MVarId) :=
    mvarId.withContext do
let ty ← withReducible mvarId.getType'
      if ty.isForall then
        let mvarId := (← heqImpOfEqImp mvarId).getD mvarId
        let mvarId := (← eqImpOfIffImp mvarId).getD mvarId
let ty ← withReducible mvarId.getType'
        if ty.isArrow then
          if ← (isTrivialType ty.bindingDomain!
 (← getLCtx).anyM (fun decl => do
                        return (← Lean.instantiateMVars decl.type) == ty.bindingDomain!)) then
            -- Don't intro, clear it
            let mvar ← mkFreshExprSyntheticOpaqueMVar ty.bindingBody! (← mvarId.getTag)
mvarId.assign .lam .anonymous ty.bindingDomain! mvar .default
            return ← loop mvar.mvarId!
        if let some patt ← CongrMetaM.nextPattern then
let gs ← Term.TermElabM.run' Lean.Elab.Tactic.RCases.rintro #[patt] none mvarId
List.flatten < > gs.mapM loop
        else
          let (_, mvarId) ← mvarId.intro1
          loop mvarId
      else
        return [mvarId]
  isTrivialType (ty : Expr) : MetaM Bool := do
    unless ← Meta.isProp ty do
      return false
    let ty ← Lean.instantiateMVars ty
    if let some (lhs, rhs) := ty.eqOrIff? then
      if lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    if let some (α, lhs, β, rhs) := ty.heq? then
      if α.cleanupAnnotations == β.cleanupAnnotations
          && lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    return false

/--
Definition of `Lean.MVarId.preCongr!` / `Lean.MVarId.preCongr!` 的定义

English:
definition Lean.MVarId.preCongr!
  signature: (mvarId : MVarId) (tryClose : Bool)
  body: do
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  if tryClose then
    -- This is a good time to check whether we have a relevant hypothesis.
    if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  if tryClose then
    -- Now try definitional equali

中文:
定义 Lean.MVarId.preCongr!
  签名: (mvarId : MVarId) (tryClose : 布尔)
  定义体: do
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  if tryClose then
    -- This is a good time to check whether we have a relevant hypothesis.
    if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  if tryClose then
    -- Now try definitional equali
-/
def Lean.MVarId.preCongr! (mvarId : MVarId) (tryClose : Bool) : MetaM (Option MVarId) := do
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  if tryClose then
    -- This is a good time to check whether we have a relevant hypothesis.
    if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  if tryClose then
    -- Now try definitional equality. No need to try `mvarId.hrefl` since we already did `heqOfEq`.
    -- We allow synthetic opaque metavariables to be assigned to fill in `x = _` goals that might
    -- appear (for example, due to using `convert` with placeholders).
    try withAssignableSyntheticOpaque mvarId.refl; return none catch _ => pure ()
    -- Now we go for (heterogeneous) equality via subsingleton considerations
    if ← Lean.Meta.fastSubsingletonElim mvarId then return none
    if ← mvarId.proofIrrelHeq then return none
  return some mvarId

/--
Definition of `Lean.MVarId.congrCore!` / `Lean.MVarId.congrCore!` 的定义

English:
definition Lean.MVarId.congrCore!
  signature: (config : Congr!.Config) (mvarId : MVarId)
  body: do
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want to commit to it
     if there are no relevant congr lemmas. -/
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some

中文:
定义 Lean.MVarId.congrCore!
  签名: (config : Congr!.Config) (mvarId : MVarId)
  定义体: do
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want to commit to it
     if there are no relevant congr lemmas. -/
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some
-/
def Lean.MVarId.congrCore! (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want to commit to it
     if there are no relevant congr lemmas. -/
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some mvarIds ← pass config mvarId then
        trace[congr!] "pass succeeded: {passName}"
        return mvarIds
    catch e =>
      throwTacticEx `congr! mvarId
        m!"internal error in congruence pass {passName}, {e.toMessageData}"
    if ← mvarId.isAssigned then
      throwTacticEx `congr! mvarId
        s!"congruence pass {passName} assigned metavariable but failed"
  restoreState s
  trace[congr!] "no passes succeeded"
  return none

/--
Definition of `Lean.MVarId.postCongr!` / `Lean.MVarId.postCongr!` 的定义

English:
definition Lean.MVarId.postCongr!
  signature: (config : Congr!.Config) (mvarId : MVarId)
  body: withTransparency config.postTransparency do
  let some mvarId ← mvarId.preCongr! config.closePost | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if config.closePost then
    -- `preCongr` sees `p = q`, but now we've put it back in

中文:
定义 Lean.MVarId.postCongr!
  签名: (config : Congr!.Config) (mvarId : MVarId)
  定义体: withTransparency config.postTransparency do
  let some mvarId ← mvarId.preCongr! config.closePost | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if config.closePost then
    -- `preCongr` sees `p = q`, but now we've put it back in

Depends on / 依赖: closePost, config, config.closePost, config.postTransparency, mvarId, mvarId.preCongr, postTransparency, preCongr, return, withTransparency
-/
def Lean.MVarId.postCongr! (config : Congr!.Config) (mvarId : MVarId) : MetaM (Option MVarId) :=
  withTransparency config.postTransparency do
  let some mvarId ← mvarId.preCongr! config.closePost | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if config.closePost then
    -- `preCongr` sees `p = q`, but now we've put it back into `p ↔ q` form.
    if ← mvarId.assumptionCore then return none
  if config.etaExpand then
    if let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? then
      let lhs' ← Meta.etaExpand lhs
      let rhs' ← Meta.etaExpand rhs
      return ← mvarId.change (← mkEq lhs' rhs')
  return mvarId

/--
Definition of `Lean.MVarId.congrN!` / `Lean.MVarId.congrN!` 的定义

English:
definition Lean.MVarId.congrN!
  signature: (mvarId : MVarId)
  body: do
let ty ← withReducible mvarId.getType'
  -- A reasonably large yet practically bounded default recursion depth.
  let defaultDepth := min 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
.run {goals := #[], patterns := patterns} let (_, s) ← go depth depth mvarId
 

中文:
定义 Lean.MVarId.congrN!
  签名: (mvarId : MVarId)
  定义体: do
let ty ← withReducible mvarId.getType'
  -- A reasonably large yet practically bounded default recursion depth.
  let defaultDepth := min 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
.run {goals := #[], patterns := patterns} let (_, s) ← go depth depth mvarId
 

Depends on / 依赖: Config, config
-/
def Lean.MVarId.congrN! (mvarId : MVarId)
    (depth? : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rintroPat) := []) :
    MetaM (List MVarId) := do
let ty ← withReducible mvarId.getType'
  -- A reasonably large yet practically bounded default recursion depth.
  let defaultDepth := min 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
.run {goals := #[], patterns := patterns} let (_, s) ← go depth depth mvarId
  return s.goals.toList
where
  post (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
      if let some mvarId ← mvarId.postCongr! config then
        modify (fun s => {s with goals := s.goals.push mvarId})
      else
        trace[congr!] "Dispatched goal by post-processing step."
  go (depth : Nat) (n : Nat) (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
if let some mvarId ← withTransparency config.preTransparency
                              mvarId.preCongr! config.closePre then
        match n with
          | 0 =>
            trace[congr!] "At level {depth - n}, doing post-processing. {mvarId}"
            post mvarId
          | n + 1 =>
            trace[congr!] "At level {depth - n}, trying congrCore!. {mvarId}"
            if let some mvarIds ← mvarId.congrCore! config then
              mvarIds.forM (go depth n)
            else
              post mvarId

namespace Congr!

declare_config_elab elabConfig Config

/--
`congr!` tries to prove the main goal by repeatedly applying congruence rules. For example, on a
goal of the form `⊢ f a1 a2 ... = f b1 b2 ...`, `congr!` will make new goals `⊢ a1 = b1`,
`⊢ a2 = b2`, ...

`congr!` is a more powerful version of the `congr` tactic that uses congruence lemmas (tagged with
`@[congr]`), reflexivity rules (tagged with `@[refl]`) and proof discharging strategies. The full
list of congruence proof strategies is documented in the module `Mathlib.Tactic.CongrExclamation`.
The `congr!` tactic is used by the `convert` and `convert_to` tactics.

* `congr! n`, where `n` is a positive numeral, controls the depth with which congruence is
  applied. For example, if the main goal is `n + n + 1 = 2 * n + 1`, then `congr! 1` results in one
  goal, `⊢ n + n = 2 * n`, and `congr! 2` (or more) results in two (impossible) goals
  `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  By default, the depth is unlimited.
* `congr! with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `congr! (config := cfg)` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).
-/
syntax (name := congr!) "congr!" Parser.Tactic.optConfig (ppSpace num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic

elab_rules : tactic
| `(tactic| congr! $cfg:optConfig $[$n]? $[with $ps?*]?) => do
  let config ← elabConfig cfg
  let patterns := (ps?.getD #[]).toList
  liftMetaTactic fun g =>
    let depth := n.map (·.getNat)
    g.congrN! depth config patterns

end Congr!
