/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Tactic.FunProp.Theorems
public meta import Mathlib.Tactic.FunProp.ToBatteries
public meta import Mathlib.Tactic.FunProp.Types
public meta import Mathlib.Lean.Expr.Basic
public import Batteries.Tactic.Exact
public import Mathlib.Tactic.FunProp.Theorems
public import Qq

/-!
# Tactic `fun_prop` for proving function properties like `Continuous f`, `Differentiable ℝ f`, ...
-/

public meta section

namespace Mathlib
open Lean Meta Qq

namespace Meta.FunProp


/--
Definition of `synthesizeInstance` / `synthesizeInstance` 的定义

English:
definition synthesizeInstance
  signature: (thmId : Origin) (x type : Expr)
  body: do
  match (← trySynthInstance type) with
  | .some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
synthesized value{indentExpr val}\nis not definitionally 

中文:
定义 synthesizeInstance
  签名: (thmId : Origin) (x type : Expr)
  定义体: do
  match (← trySynthInstance type) with
  | .some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
synthesized value{indentExpr val}\nis not definitionally 
-/
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | .some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
synthesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fun_prop]
      "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false



/--
Definition of `synthesizeArgs` / `synthesizeArgs` 的定义

English:
definition synthesizeArgs
  signature: (thmId : Origin) (xs : Array Expr)
  body: do
  let mut postponed : Array Expr := #[]
  for x in xs do
    let type ← inferType x
    if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue
      else if (← isFunPropGoal type)

中文:
定义 synthesizeArgs
  签名: (thmId : Origin) (xs : 数组 Expr)
  定义体: do
  let mut postponed : Array Expr := #[]
  for x in xs do
    let type ← inferType x
    if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue
      else if (← isFunPropGoal type)
-/
def synthesizeArgs (thmId : Origin) (xs : Array Expr)
    (funProp : Expr -> FunPropM (Option Result)) :
    FunPropM Bool := do
  let mut postponed : Array Expr := #[]
  for x in xs do
    let type ← inferType x
    if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue
      else if (← isFunPropGoal type) then
        -- try function property
        if let some ⟨proof⟩ ← funProp type then
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fun_prop]
              "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return false
      else
        -- try user provided discharger
        let ctx : Context ← read
        -- To use `fun_prop` in the manifold library
        -- (with the predicates `MDifferentiable`, `ContMDiff` and friends),
        -- we need provide specialize a specialized discharger for `ModelWithCorners`:
        -- lemmas like `ContMDiff.comp` require inferring the model with corners on the
        -- intermediate space.
        -- In the future, we might want to allow the discharger to execute on other Type-valued
        -- hypotheses. In this case, we could create an environment extension to register such
        -- types. However, right now we could not think of any other use cases --- therefore,
        -- we hard-code `ModelWithCorners`.
        if ((← isProp type) || type.isAppOfArity' `ModelWithCorners 7) then
          if let some proof ← ctx.disch type then
            if (← isDefEq x proof) then
              continue
            else do
              trace[Meta.Tactic.fun_prop]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false
          else
            logError s!"Failed to prove necessary assumption `{← ppExpr type}` \
                        when applying theorem `{← ppOrigin' thmId}`."

      if ¬(← isProp type) then
        postponed := postponed.push x
        continue
      else
        trace[Meta.Tactic.fun_prop]
          "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
        return false

  for x in postponed do
    if (← instantiateMVars x).isMVar then
      logError s!"Failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})` \
      when applying theorem `{← ppOrigin' thmId}`."

      trace[Meta.Tactic.fun_prop]
        "{← ppOrigin thmId}, failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})`"
      return false

  return true


/--
Definition of `tryTheoremCore` / `tryTheoremCore` 的定义

English:
definition tryTheoremCore
  signature: (xs : Array Expr) (val : Expr) (type : Expr) (e : Expr)
  body: do
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => return s!"applying: {← ppOrigin' thmId}") do

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    return some { proof := proof }
  else
    trace[

中文:
定义 tryTheoremCore
  签名: (xs : 数组 Expr) (val : Expr) (type : Expr) (e : Expr)
  定义体: do
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => return s!"applying: {← ppOrigin' thmId}") do

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    return some { proof := proof }
  else
    trace[
-/
def tryTheoremCore (xs : Array Expr) (val : Expr) (type : Expr) (e : Expr)
    (thmId : Origin) (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => return s!"applying: {← ppOrigin' thmId}") do

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    return some { proof := proof }
  else
    trace[Meta.Tactic.fun_prop] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


/--
Definition of `tryTheoremWithHint?` / `tryTheoremWithHint?` 的定义

English:
definition tryTheoremWithHint?
  signature: (e : Expr) (thmOrigin : Origin)
  body: do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    -- for `fvar`s we need to instantiate the metavariables of its type.
let type ← instantiateMVars ← inferType thmProof
    let (xs, _, type) ← forallMetaTelescope type

    for (i,x) in hint do
      try
        fo

中文:
定义 tryTheoremWithHint?
  签名: (e : Expr) (thmOrigin : Origin)
  定义体: do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    -- for `fvar`s we need to instantiate the metavariables of its type.
let type ← instantiateMVars ← inferType thmProof
    let (xs, _, type) ← forallMetaTelescope type

    for (i,x) in hint do
      try
        fo
-/
def tryTheoremWithHint? (e : Expr) (thmOrigin : Origin)
    (hint : Array (Nat × Expr))
    (funProp : Expr -> FunPropM (Option Result)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    -- for `fvar`s we need to instantiate the metavariables of its type.
let type ← instantiateMVars ← inferType thmProof
    let (xs, _, type) ← forallMetaTelescope type

    for (i,x) in hint do
      try
        for (id,v) in hint do
          xs[id]!.mvarId!.assignIfDefEq v
      catch _ =>
        trace[Debug.Meta.Tactic.fun_prop]
          "failed to use hint {i} `{← ppExpr x} when applying theorem {← ppOrigin thmOrigin}"

    tryTheoremCore xs thmProof type e thmOrigin funProp

  -- `simp` introduces new meta variable context depth for some reason
  -- This is probably to avoid mvar assignment when trying a theorem fails
  --
  -- However, in `fun_prop` case this is not completely desirable
  -- For example, I want to be able to solve a goal with mvars like `ContDiff ℝ ?n f` using local
  -- hypothesis `(h : ContDiff ℝ ∞ f)` and assign `∞` to the mvar `?n`.
  --
  -- This could be problematic if there are two local hypothesis `(hinf : ContDiff ℝ ∞ f)` and
  -- `(h1 : ContDiff ℝ 1 f)` and apart from solving `ContDiff ℝ ?n f` there is also a subgoal
  -- `2 ≤ ?n`. If `fun_prop` decides to try `h1` first it would assign `1` to `?n` and then there
  -- is no hope solving `2 ≤ 1` and it won't be able to apply `hinf` after trying `h1` as `n?` is
  -- assigned already. Ideally `fun_prop` would roll back the `MetaM.State`. This issue did not
  -- come up yet so I didn't bother and I'm worried about the performance impact.
  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go


/--
Definition of `tryTheorem?` / `tryTheorem?` 的定义

English:
definition tryTheorem?
  signature: (e : Expr) (thmOrigin : Origin) (funProp : Expr -> FunPropM (Option Result))
  body: tryTheoremWithHint? e thmOrigin #[] funProp newMCtxDepth

中文:
定义 tryTheorem?
  签名: (e : Expr) (thmOrigin : Origin) (funProp : Expr -> FunPropM (选项类型 Result))
  定义体: tryTheoremWithHint? e thmOrigin #[] funProp newMCtxDepth

Depends on / 依赖: FunPropM, Result
-/
def tryTheorem? (e : Expr) (thmOrigin : Origin) (funProp : Expr -> FunPropM (Option Result))
    (newMCtxDepth : Bool := false) : FunPropM (Option Result) :=
  tryTheoremWithHint? e thmOrigin #[] funProp newMCtxDepth


/--
Definition of `applyIdRule` / `applyIdRule` 的定义

English:
definition applyIdRule
  signature: (funPropDecl : FunPropDecl) (e : Expr)
  body: do
  let thms ← getLambdaTheorems funPropDecl.funPropName .id
  if thms.size = 0 then
    let msg := s!"missing identity rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmNa

中文:
定义 applyIdRule
  签名: (funPropDecl : FunPropDecl) (e : Expr)
  定义体: do
  let thms ← getLambdaTheorems funPropDecl.funPropName .id
  if thms.size = 0 then
    let msg := s!"missing identity rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmNa
-/
def applyIdRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .id
  if thms.size = 0 then
    let msg := s!"missing identity rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r

  return none

/--
Definition of `applyConstRule` / `applyConstRule` 的定义

English:
definition applyConstRule
  signature: (funPropDecl : FunPropDecl) (e : Expr)
  body: do
  let thms ← getLambdaTheorems funPropDecl.funPropName .const
  if thms.size = 0 then
    let msg := s!"missing constant rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .const := thm.thmArgs | return none
    if let s

中文:
定义 applyConstRule
  签名: (funPropDecl : FunPropDecl) (e : Expr)
  定义体: do
  let thms ← getLambdaTheorems funPropDecl.funPropName .const
  if thms.size = 0 then
    let msg := s!"missing constant rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .const := thm.thmArgs | return none
    if let s
-/
def applyConstRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .const
  if thms.size = 0 then
    let msg := s!"missing constant rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .const := thm.thmArgs | return none
    if let some r ← tryTheorem? e (.decl thm.thmName) funProp then
      return r

  return none

/--
Definition of `applyApplyRule` / `applyApplyRule` 的定义

English:
definition applyApplyRule
  signature: (funPropDecl : FunPropDecl) (e : Expr)
  body: do
  let thms := (← getLambdaTheorems funPropDecl.funPropName .apply)
  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r

  return none

中文:
定义 applyApplyRule
  签名: (funPropDecl : FunPropDecl) (e : Expr)
  定义体: do
  let thms := (← getLambdaTheorems funPropDecl.funPropName .apply)
  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r

  return none
-/
def applyApplyRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms := (← getLambdaTheorems funPropDecl.funPropName .apply)
  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r

  return none

/--
Definition of `applyCompRule` / `applyCompRule` 的定义

English:
definition applyCompRule
  signature: (funPropDecl : FunPropDecl) (e f g : Expr)
  body: do

  let thms ← getLambdaTheorems funPropDecl.funPropName .comp
  if thms.size = 0 then
    let msg := s!"missing composition rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | return none

中文:
定义 applyCompRule
  签名: (funPropDecl : FunPropDecl) (e f g : Expr)
  定义体: do

  let thms ← getLambdaTheorems funPropDecl.funPropName .comp
  if thms.size = 0 then
    let msg := s!"missing composition rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | return none
-/
def applyCompRule (funPropDecl : FunPropDecl) (e f g : Expr)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do

  let thms ← getLambdaTheorems funPropDecl.funPropName .comp
  if thms.size = 0 then
    let msg := s!"missing composition rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | return none
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[(id_f, f), (id_g, g)] funProp then
      return r

  return none

/--
Definition of `applyPiRule` / `applyPiRule` 的定义

English:
definition applyPiRule
  signature: (funPropDecl : FunPropDecl) (e : Expr)
  body: do

  let thms ← getLambdaTheorems funPropDecl.funPropName .pi
  if thms.size = 0 then
    let msg := s!"missing pi rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #

中文:
定义 applyPiRule
  签名: (funPropDecl : FunPropDecl) (e : Expr)
  定义体: do

  let thms ← getLambdaTheorems funPropDecl.funPropName .pi
  if thms.size = 0 then
    let msg := s!"missing pi rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #
-/
def applyPiRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do

  let thms ← getLambdaTheorems funPropDecl.funPropName .pi
  if thms.size = 0 then
    let msg := s!"missing pi rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r

  return none


/--
Definition of `letCase` / `letCase` 的定义

English:
definition letCase
  signature: (funPropDecl : FunPropDecl) (e : Expr) (f : Expr)
  body: do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody := yBody.consumeMData
    -- We perform reduction because the type is quite often of the form
    -- `(fun x ↦ Y) #0` which is j

中文:
定义 letCase
  签名: (funPropDecl : FunPropDecl) (e : Expr) (f : Expr)
  定义体: do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody := yBody.consumeMData
    -- We perform reduction because the type is quite often of the form
    -- `(fun x ↦ Y) #0` which is j
-/
def letCase (funPropDecl : FunPropDecl) (e : Expr) (f : Expr)
    (funProp : Expr -> FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody := yBody.consumeMData
    -- We perform reduction because the type is quite often of the form
    -- `(fun x ↦ Y) #0` which is just `Y`
    -- Usually this is caused by the usage of `FunLike`
    let yType := yType.headBeta
    if (yType.hasLooseBVar 0) then
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

    -- let binding can be pulled out of the lambda function
    if ¬(yValue.hasLooseBVar 0) then
      let body := yBody.swapBVars 0 1
      let e' := mkLet yName yType yValue
        (e.setArg (funPropDecl.funArgId) (.lam xName xType body xBi))
      return ← funProp e'

    match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
    | true, true =>
      let f ← mkUncurryFun 2 (Expr.lam xName xType (.lam yName yType yBody default) xBi)
      let g := Expr.lam xName xType (binderInfo := default)
        (mkAppN (← mkConstWithFreshMVarLevels ``Prod.mk) #[xType,yType,.bvar 0, yValue])
      applyCompRule funPropDecl e f g funProp

    | true, false =>
      let f := Expr.lam yName yType yBody default
      let g := Expr.lam xName xType yValue default
      applyCompRule funPropDecl e f g funProp

    | false, _ =>
      let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
      funProp (e.setArg (funPropDecl.funArgId) f)

  | _ => throwError "expected expression of the form `fun x => lam y := ..; ..`"


/--
Definition of `applyMorRules` / `applyMorRules` 的定义

English:
definition applyMorRules
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do
  trace[Debug.Meta.Tactic.fun_prop] "applying morphism theorems to {← ppExpr e}"

  -- get theorems
  let candidates ← getMorphismTheorems e
  trace[Meta.Tactic.fun_prop]
    "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  -- try theorems
  for c in candi

中文:
定义 applyMorRules
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do
  trace[Debug.Meta.Tactic.fun_prop] "applying morphism theorems to {← ppExpr e}"

  -- get theorems
  let candidates ← getMorphismTheorems e
  trace[Meta.Tactic.fun_prop]
    "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  -- try theorems
  for c in candi
-/
def applyMorRules (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do
  trace[Debug.Meta.Tactic.fun_prop] "applying morphism theorems to {← ppExpr e}"

  -- get theorems
  let candidates ← getMorphismTheorems e
  trace[Meta.Tactic.fun_prop]
    "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  -- try theorems
  for c in candidates do
    if let some r ← tryTheorem? e (.decl c.thmName) funProp then
      return r

  -- if all failed try to add/remove arguments
  match ← fData.isMorApplication with
  | .none => throwError "fun_prop bug: invalid use of mor rules on {← ppExpr e}"
  | .underApplied =>
    applyPiRule funPropDecl e funProp
  | .overApplied =>
    let .comp f g ← fData.peeloffArgDecomposition | return none
    applyCompRule funPropDecl e f g funProp
  | .exact =>
    trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
    return none

/--
Definition of `applyTransitionRules` / `applyTransitionRules` 的定义

English:
definition applyTransitionRules
  signature: (e : Expr) (funProp : Expr -> FunPropM (Option Result))
  body: do
  withIncreasedTransitionDepth do

  let candidates ← getTransitionTheorems e

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  for c in candidates do
    if let some r ← tryTheorem? e (.decl c.thmName) funProp then
    

中文:
定义 applyTransitionRules
  签名: (e : Expr) (funProp : Expr -> FunPropM (选项类型 Result))
  定义体: do
  withIncreasedTransitionDepth do

  let candidates ← getTransitionTheorems e

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  for c in candidates do
    if let some r ← tryTheorem? e (.decl c.thmName) funProp then
    
-/
def applyTransitionRules (e : Expr) (funProp : Expr -> FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  withIncreasedTransitionDepth do

  let candidates ← getTransitionTheorems e

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  for c in candidates do
    if let some r ← tryTheorem? e (.decl c.thmName) funProp then
      return r

  trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
  return none

/--
Definition of `removeArgRule` / `removeArgRule` 的定义

English:
definition removeArgRule
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do

  match h : fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr e}"
  | n + 1 =>
    let arg := fData.args[n]

    if arg.coe.isSome then
      -- if have to apply morphisms rules if we deal with morphisms
      return ← applyMorRules funPropDecl e fDa

中文:
定义 removeArgRule
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do

  match h : fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr e}"
  | n + 1 =>
    let arg := fData.args[n]

    if arg.coe.isSome then
      -- if have to apply morphisms rules if we deal with morphisms
      return ← applyMorRules funPropDecl e fDa
-/
def removeArgRule (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr -> FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  match h : fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr e}"
  | n + 1 =>
    let arg := fData.args[n]

    if arg.coe.isSome then
      -- if have to apply morphisms rules if we deal with morphisms
      return ← applyMorRules funPropDecl e fData funProp
    else
      let .comp f g ← fData.peeloffArgDecomposition | return none
      applyCompRule funPropDecl e f g funProp


/--
Definition of `bvarAppCase` / `bvarAppCase` 的定义

English:
definition bvarAppCase
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do

  if (← fData.isMorApplication) != .none then
    applyMorRules funPropDecl e fData funProp
  else
    if let .comp f g ← fData.decomposition then
      applyCompRule funPropDecl e f g funProp
    else
      applyApplyRule funPropDecl e funProp

中文:
定义 bvarAppCase
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do

  if (← fData.isMorApplication) != .none then
    applyMorRules funPropDecl e fData funProp
  else
    if let .comp f g ← fData.decomposition then
      applyCompRule funPropDecl e f g funProp
    else
      applyApplyRule funPropDecl e funProp
-/
def bvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do

  if (← fData.isMorApplication) != .none then
    applyMorRules funPropDecl e fData funProp
  else
    if let .comp f g ← fData.decomposition then
      applyCompRule funPropDecl e f g funProp
    else
      applyApplyRule funPropDecl e funProp

/--
Definition of `getDeclTheorems` / `getDeclTheorems` 的定义

English:
definition getDeclTheorems
  signature: (funPropDecl : FunPropDecl) (funName : Name)
  body: do

  let thms ← getTheoremsForFunction funName funPropDecl.funPropName

  let thms := thms
.filter (fun thm => (isOrderedSubsetOf mainArgs thm.mainArgs))
.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat 

中文:
定义 getDeclTheorems
  签名: (funPropDecl : FunPropDecl) (funName : Name)
  定义体: do

  let thms ← getTheoremsForFunction funName funPropDecl.funPropName

  let thms := thms
.filter (fun thm => (isOrderedSubsetOf mainArgs thm.mainArgs))
.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat 
-/
def getDeclTheorems (funPropDecl : FunPropDecl) (funName : Name)
    (mainArgs : Array Nat) (appliedArgs : Nat) : MetaM (Array FunctionTheorem) := do

  let thms ← getTheoremsForFunction funName funPropDecl.funPropName

  let thms := thms
.filter (fun thm => (isOrderedSubsetOf mainArgs thm.mainArgs))
.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)
  -- todo: sorting and filtering
  return thms

/--
Definition of `getLocalTheorems` / `getLocalTheorems` 的定义

English:
definition getLocalTheorems
  signature: (funPropDecl : FunPropDecl) (funOrigin : Origin)
  body: do

  let mut thms : Array FunctionTheorem := #[]
  let lctx ← getLCtx
  for var in lctx do
    if (var.kind = Lean.LocalDeclKind.auxDecl) then
      continue
    let type ← instantiateMVars var.type
    let thm? : Option FunctionTheorem ←
      forallTelescope type fun _ b => do
      let b ← whnfR

中文:
定义 getLocalTheorems
  签名: (funPropDecl : FunPropDecl) (funOrigin : Origin)
  定义体: do

  let mut thms : Array FunctionTheorem := #[]
  let lctx ← getLCtx
  for var in lctx do
    if (var.kind = Lean.LocalDeclKind.auxDecl) then
      continue
    let type ← instantiateMVars var.type
    let thm? : Option FunctionTheorem ←
      forallTelescope type fun _ b => do
      let b ← whnfR
-/
def getLocalTheorems (funPropDecl : FunPropDecl) (funOrigin : Origin)
    (mainArgs : Array Nat) (appliedArgs : Nat) : FunPropM (Array FunctionTheorem) := do

  let mut thms : Array FunctionTheorem := #[]
  let lctx ← getLCtx
  for var in lctx do
    if (var.kind = Lean.LocalDeclKind.auxDecl) then
      continue
    let type ← instantiateMVars var.type
    let thm? : Option FunctionTheorem ←
      forallTelescope type fun _ b => do
      let b ← whnfR b
      let some (decl, f) ← getFunProp? b | return none
      unless decl.funPropName = funPropDecl.funPropName do return none

      let .data fData ← getFunctionData? f (← unfoldNamePred)
        | return none
      unless (fData.getFnOrigin == funOrigin) do return none

      unless isOrderedSubsetOf mainArgs fData.mainArgs do return none

      let dec ← fData.decomposition
      let thm : FunctionTheorem := {
        funPropName := funPropDecl.funPropName
        thmOrigin := .fvar var.fvarId
        funOrigin := funOrigin
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := eval_prio default
        form := dec.toTheoremForm
      }

      return some thm

    if let some thm := thm? then
      thms := thms.push thm

  thms := thms
.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)

  return thms


/--
Definition of `tryTheorems` / `tryTheorems` 的定义

English:
definition tryTheorems
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do

  -- none - decomposition not tried
  -- some result - result of decomposition
  let mut dec? : Option DecompositionResult := none

  for thm in thms do

    trace[Debug.Meta.Tactic.fun_prop] s!"trying theorem {← ppOrigin' thm.thmOrigin}"

    match compare thm.appliedArgs fData.args.size with
 

中文:
定义 tryTheorems
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do

  -- none - decomposition not tried
  -- some result - result of decomposition
  let mut dec? : Option DecompositionResult := none

  for thm in thms do

    trace[Debug.Meta.Tactic.fun_prop] s!"trying theorem {← ppOrigin' thm.thmOrigin}"

    match compare thm.appliedArgs fData.args.size with
 

Depends on / 依赖: Continuous, OrderClosedTopology, OrderClosedTopology.mk, Subtype, continuous_subtype_val, continuous_subtype_val.prodMap, isClosed_le, p.fst, p.snd, preimage, prodMap, t.isClosed_le
-/
def tryTheorems (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (thms : Array FunctionTheorem) (funProp : Expr -> FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  -- none - decomposition not tried
  -- some result - result of decomposition
  let mut dec? : Option DecompositionResult := none

  for thm in thms do

    trace[Debug.Meta.Tactic.fun_prop] s!"trying theorem {← ppOrigin' thm.thmOrigin}"

    match compare thm.appliedArgs fData.args.size with
    | .lt =>
      trace[Meta.Tactic.fun_prop] s!"removing argument to later use {← ppOrigin' thm.thmOrigin}"
      if let some r ← removeArgRule funPropDecl e fData funProp then
        return r
      continue
    | .gt =>
      trace[Meta.Tactic.fun_prop] s!"adding argument to later use {← ppOrigin' thm.thmOrigin}"
      if let some r ← applyPiRule funPropDecl e funProp then
        return r
      continue
    | .eq =>
      if thm.form == .comp then
        if let some r ← tryTheorem? e thm.thmOrigin funProp then
          return r
      else

        if thm.mainArgs.size == fData.mainArgs.size then
          if dec?.isNone then
            dec? ← fData.decomposition
          match dec? with
          | some (.comp f g) =>
            trace[Meta.Tactic.fun_prop]
              s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                   ({← ppExpr f}) ∘ ({← ppExpr g})"
            if let some r ← applyCompRule funPropDecl e f g funProp then
              return r
          | some _ =>
            if let some r ← tryTheorem? e thm.thmOrigin funProp then
              return r
          | none => unreachable!
        else
          let some (f, g) ← fData.decompositionOverArgs thm.mainArgs | continue
          trace[Meta.Tactic.fun_prop]
            s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                 ({← ppExpr f}) ∘ ({← ppExpr g})"
          if let some r ← applyCompRule funPropDecl e f g funProp then
            return r
      -- todo: decompose if uncurried and arguments do not match exactly
  return none

/--
Definition of `fvarAppCase` / `fvarAppCase` 的定义

English:
definition fvarAppCase
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do

  -- fvar theorems are almost exclusively in uncurried form so we decompose if we can
  if let .comp f g ← fData.decomposition then
    applyCompRule funPropDecl e f g funProp
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalThe

中文:
定义 fvarAppCase
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do

  -- fvar theorems are almost exclusively in uncurried form so we decompose if we can
  if let .comp f g ← fData.decomposition then
    applyCompRule funPropDecl e f g funProp
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalThe
-/
def fvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do

  -- fvar theorems are almost exclusively in uncurried form so we decompose if we can
  if let .comp f g ← fData.decomposition then
    applyCompRule funPropDecl e f g funProp
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalTheorems funPropDecl (.fvar id) fData.mainArgs fData.args.size
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {←ppExpr (.fvar id)} \
         {← thms.mapM fun thm => ppOrigin' thm.thmOrigin}"

    if let some r ← tryTheorems funPropDecl e fData thms funProp then
      return r

    if let some f ← fData.unfoldHeadFVar? then
      let e' := e.setArg funPropDecl.funArgId f
      if let some r ← funProp e' then
        return r

    if (← fData.isMorApplication) != .none then
      if let some r ← applyMorRules funPropDecl e fData funProp then
        return r

    if let some r ← applyTransitionRules e funProp then
      return r

    if thms.size = 0 then
      logError s!"No theorems found for `{← ppExpr (.fvar id)}` in order to prove `{← ppExpr e}`"

    return none


/--
Definition of `constAppCase` / `constAppCase` 的定义

English:
definition constAppCase
  signature: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  body: do

  let some (funName, _) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size

  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppO

中文:
定义 constAppCase
  签名: (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
  定义体: do

  let some (funName, _) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size

  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppO
-/
def constAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr -> FunPropM (Option Result)) : FunPropM (Option Result) := do

  let some (funName, _) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size

  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppOrigin' thm.thmOrigin}"

  if let some r ← tryTheorems funPropDecl e fData globalThms funProp then
    return r

  -- Try local theorems - this is useful for recursive functions
  let localThms ← getLocalTheorems funPropDecl (.decl funName) fData.mainArgs fData.args.size
  if localThms.size != 0 then
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {funName} \
        {← localThms.mapM fun thm => ppOrigin' thm.thmOrigin}"
  if let some r ← tryTheorems funPropDecl e fData localThms funProp then
    return r

  -- log error if no global or local theorems were found
  if globalThms.size = 0 && localThms.size = 0 then
     logError s!"No theorems found for `{funName}` in order to prove `{← ppExpr e}`"

  if (← fData.isMorApplication) != .none then
    if let some r ← applyMorRules funPropDecl e fData funProp then
      return r

  if let .comp f g ← fData.decomposition then
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{funPropDecl.funPropName}` theorems for `{funName}`
         trying again after decomposing function as: `({← ppExpr f}) ∘ ({← ppExpr g})`"

    if let some r ← applyCompRule funPropDecl e f g funProp then
      return r
  else
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{funPropDecl.funPropName}` theorems for `{funName}`
         now trying to prove `{funPropDecl.funPropName}` from another function property"

    if let some r ← applyTransitionRules e funProp then
      return r


  return none


/--
Definition of `cacheResult` / `cacheResult` 的定义

English:
definition cacheResult
  signature: (e : Expr) (r : Result)
  body: do -- return proof?
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

中文:
定义 cacheResult
  签名: (e : Expr) (r : Result)
  定义体: do -- return proof?
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

Depends on / 依赖: return
-/
def cacheResult (e : Expr) (r : Result) : FunPropM Result := do -- return proof?
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

/--
Definition of `cacheFailure` / `cacheFailure` 的定义

English:
definition cacheFailure
  signature: (e : Expr)
  body: do -- return proof?
  modify (fun s => { s with failureCache := s.failureCache.insert e })


mutual
  /-- Main `funProp` function. Returns proof of `e`. -/
  partial def funProp (e : Expr) : FunPropM (Option Result) := do

    let e ← instantiateMVars e

    withTraceNode `Meta.Tactic.fun_prop
     

中文:
定义 cacheFailure
  签名: (e : Expr)
  定义体: do -- return proof?
  modify (fun s => { s with failureCache := s.failureCache.insert e })


mutual
  /-- Main `funProp` function. Returns proof of `e`. -/
  partial def funProp (e : Expr) : FunPropM (Option Result) := do

    let e ← instantiateMVars e

    withTraceNode `Meta.Tactic.fun_prop
     

Depends on / 依赖: return
-/
def cacheFailure (e : Expr) : FunPropM Unit := do -- return proof?
  modify (fun s => { s with failureCache := s.failureCache.insert e })


mutual
  /-- Main `funProp` function. Returns proof of `e`. -/
  partial def funProp (e : Expr) : FunPropM (Option Result) := do

    let e ← instantiateMVars e

    withTraceNode `Meta.Tactic.fun_prop
      (fun _ => do pure s!"{← ppExpr e}") do

    -- check cache for successful goals
    if let some { expr := _, proof? := some proof, .. } := (← get).cache.find? e then
      trace[Meta.Tactic.fun_prop] "reusing previously found proof for {e}"
      return some { proof := proof }
    else if (← get).failureCache.contains e then
      trace[Meta.Tactic.fun_prop] "skipping proof search, proving {e} was tried already and failed"
      return none
    else
      -- take care of forall and let binders and run main
      match e with
      | .letE .. =>
        letTelescope e fun xs b => do
          let some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars (generalizeNondepLet := false) xs r.proof }
      | .forallE .. =>
        forallTelescope e fun xs b => do
          let some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof }
      | .mdata _ e' => funProp e'
      | _ =>
        if let some r ← main e then
          cacheResult e r
        else
          cacheFailure e
          return none


  /-- Main `funProp` function. Returns proof of `e`. -/
  private partial def main (e : Expr) : FunPropM (Option Result) := do

    let some (funPropDecl, f) ← getFunProp? e
      | return none

    increaseSteps

    -- if function starts with let bindings move them the top of `e` and try again
    if f.isLet then
      return ← funProp (← mapLetTelescope f fun _ b => pure <| e.setArg funPropDecl.funArgId b)

    match ← getFunctionData? f (← unfoldNamePred) with
    | .letE f =>
      trace[Debug.Meta.Tactic.fun_prop] "let case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f -- update e with reduced f
      letCase funPropDecl e f funProp
    | .lam f =>
      trace[Debug.Meta.Tactic.fun_prop] "pi case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f -- update e with reduced f
      applyPiRule funPropDecl e funProp
    | .data fData =>
      let e := e.setArg funPropDecl.funArgId (← fData.toExpr) -- update e with reduced f

      if fData.isIdentityFun then
        if let some r ← applyIdRule funPropDecl e funProp then
          return r

      if fData.isConstantFun then
        if let some r ← applyConstRule funPropDecl e funProp then
          return r

      match fData.fn with
      | .fvar id =>
        if id == fData.mainVar.fvarId! then
          bvarAppCase funPropDecl e fData funProp
        else
          fvarAppCase funPropDecl e fData funProp
      | .const .. | .proj .. => do
        constAppCase funPropDecl e fData funProp
      | _ =>
        trace[Debug.Meta.Tactic.fun_prop] "unknown case, ctor: {f.ctorName}\n{e}"
        return none

end

end Meta.FunProp

end Mathlib
