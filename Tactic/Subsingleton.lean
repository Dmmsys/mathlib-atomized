/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Meta.Tactic.Refl
public import Mathlib.Logic.Basic

/-!
# `subsingleton` tactic

The `subsingleton` tactic closes `Eq` or `HEq` goals using an argument
that the types involved are subsingletons.
To first approximation, it does `apply Subsingleton.elim` but it also will try `proof_irrel_heq`,
and it is careful not to accidentally specialize `Sort _` to `Prop`.
-/

public meta section

open Lean Meta

/--
Definition of `Lean.Meta.mkSubsingleton` / `Lean.Meta.mkSubsingleton` 的定义

English:
definition Lean.Meta.mkSubsingleton
  signature: (ty : Expr)
  body: do
  let u ← getLevel ty
  return Expr.app (.const ``Subsingleton [u]) ty

中文:
定义 Lean.Meta.mkSubsingleton
  签名: (ty : Expr)
  定义体: do
  let u ← getLevel ty
  return Expr.app (.const ``Subsingleton [u]) ty

Depends on / 依赖: IsRightAdjoint
-/
def Lean.Meta.mkSubsingleton (ty : Expr) : MetaM Expr := do
  let u ← getLevel ty
  return Expr.app (.const ``Subsingleton [u]) ty

/--
Definition of `Lean.Meta.synthSubsingletonInst` / `Lean.Meta.synthSubsingletonInst` 的定义

English:
definition Lean.Meta.synthSubsingletonInst
  signature: (ty : Expr)
  body: do
  -- Synthesize a subsingleton instance. The new metacontext depth ensures that universe
  -- level metavariables are not specialized.
  withNewMCtxDepth do
    -- We need to process the local instances *under* `withNewMCtxDepth` since they might
    -- have universe parameters, which we need to 

中文:
定义 Lean.Meta.synthSubsingletonInst
  签名: (ty : Expr)
  定义体: do
  -- Synthesize a subsingleton instance. The new metacontext depth ensures that universe
  -- level metavariables are not specialized.
  withNewMCtxDepth do
    -- We need to process the local instances *under* `withNewMCtxDepth` since they might
    -- have universe parameters, which we need to 
-/
def Lean.Meta.synthSubsingletonInst (ty : Expr)
    (insts : Array (Term × AbstractMVarsResult) := #[]) :
    MetaM Expr := do
  -- Synthesize a subsingleton instance. The new metacontext depth ensures that universe
  -- level metavariables are not specialized.
  withNewMCtxDepth do
    -- We need to process the local instances *under* `withNewMCtxDepth` since they might
    -- have universe parameters, which we need to let `synthInstance` assign to.
let (insts', uss) ← Array.unzip < > insts.mapM fun inst => do
      let us ← inst.2.paramNames.mapM fun _ => mkFreshLevelMVar
pure (inst.2.expr.instantiateLevelParamsArray inst.2.paramNames us, us)
    withLocalDeclsD (insts'.map fun e => (`inst, fun _ => inferType e)) fun fvars => do
      withNewLocalInstances fvars 0 do
let res ← instantiateMVars ← synthInstance ← mkSubsingleton ty
        let res' := res.abstract fvars
        for i in [0 : fvars.size] do
          if res'.hasLooseBVar (fvars.size - i - 1) then
            uss[i]!.forM fun u => do
              let u ← instantiateLevelMVars u
              if u.isMVar then
                -- This shouldn't happen, `synthInstance` should solve for all level metavariables
                throwErrorAt insts[i]!.1 "\
                  Instance provided to 'subsingleton' has unassigned universe level metavariable\
                  {indentD insts'[i]!}"
          else
            -- Unused local instance.
            -- Not logging a warning since this might be `... <;> subsingleton [...]`
            pure ()
instantiateMVars res'.instantiateRev insts'

/--
Definition of `Lean.MVarId.subsingleton` / `Lean.MVarId.subsingleton` 的定义

English:
definition Lean.MVarId.subsingleton
  signature: (g : MVarId) (insts : Array (Term × AbstractMVarsResult) := #[])
  body: commitIfNoEx do
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      -- Proof irrelevance. This is not necessary since `rfl` suffices,
      -- but propositions are subsingletons so we may as well.
      if ← Meta.isProp ty then
g.

中文:
定义 Lean.MVarId.subsingleton
  签名: (g : MVarId) (insts : Array (Term × AbstractMVarsResult) := #[])
  定义体: commitIfNoEx do
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      -- Proof irrelevance. This is not necessary since `rfl` suffices,
      -- but propositions are subsingletons so we may as well.
      if ← Meta.isProp ty then
g.
-/
def Lean.MVarId.subsingleton (g : MVarId) (insts : Array (Term × AbstractMVarsResult) := #[]) :
    MetaM Unit := commitIfNoEx do
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      -- Proof irrelevance. This is not necessary since `rfl` suffices,
      -- but propositions are subsingletons so we may as well.
      if ← Meta.isProp ty then
g.assign mkApp3 (.const ``proof_irrel []) ty x y
        return
      -- Try `Subsingleton.elim`
      let u ← getLevel ty
      try
        let inst ← synthSubsingletonInst ty insts
g.assign mkApp4 (.const ``Subsingleton.elim [u]) ty inst x y
        return
      catch _ => pure ()
      -- Try `lawful_beq_subsingleton`
      let ty' ← whnfR ty
      if ty'.isAppOfArity ``BEq 1 then
        let α := ty'.appArg!
        try
          let some u' := u.dec | failure
let xInst ← withNewMCtxDepth Meta.synthInstance mkApp2 (.const ``LawfulBEq [u']) α x
let yInst ← withNewMCtxDepth Meta.synthInstance mkApp2 (.const ``LawfulBEq [u']) α y
g.assign mkApp5 (.const ``lawful_beq_subsingleton [u']) α x y xInst yInst
          return
        catch _ => pure ()
      throwError "\
        tactic 'subsingleton' could not prove equality since it could not synthesize\
          {indentD (← mkSubsingleton ty)}"
    else if let some (xTy, x, yTy, y) := tgt.heq? then
      -- The HEq version of proof irrelevance.
      if ← (Meta.isProp xTy <&&> Meta.isProp yTy) then
g.assign mkApp4 (.const ``proof_irrel_heq []) xTy yTy x y
        return
      throwError "tactic 'subsingleton' could not prove heterogeneous equality"
    throwError "tactic 'subsingleton' failed, goal is neither an equality nor a \
      heterogeneous equality"

namespace Mathlib.Tactic

/--
`subsingleton` proves the main goal of the form `∀ a ... b, x = y` or `∀ a ... b, x ≍ y` using the
fact that the type(s) of `x` and `y` are *subsingletons* (a type with exactly zero or one elements).
If `subsingleton` cannot close the goal, it fails.

Techniques the `subsingleton` tactic can apply:
- proof irrelevance
- heterogeneous proof irrelevance (via `proof_irrel_heq`)
- using `Subsingleton` (via `Subsingleton.elim`)
- proving instances of the type `BEq α` are equal if they are both lawful
  (via `lawful_beq_subsingleton`)

* `subsingleton [inst1, inst2, ...]` can be used to add additional `Subsingleton` instances
  to the local context. This can be more flexible than
  `have := inst1; have := inst2; ...; subsingleton` since the tactic does not require that
  all placeholders be solved for.
-/
syntax (name := subsingletonStx) "subsingleton" (ppSpace "[" term,* "]")? : tactic

open Elab Tactic

/--
Definition of `elabSubsingletonInsts` / `elabSubsingletonInsts` 的定义

English:
definition elabSubsingletonInsts
  body: do
  if let some instTerms := instTerms? then
    go instTerms.toList #[]
  else
    return #[]

中文:
定义 elabSubsingletonInsts
  定义体: do
  if let some instTerms := instTerms? then
    go instTerms.toList #[]
  else
    return #[]
-/
def elabSubsingletonInsts
    (instTerms? : Option (Array Term)) : TermElabM (Array (Term × AbstractMVarsResult)) := do
  if let some instTerms := instTerms? then
    go instTerms.toList #[]
  else
    return #[]
where
  /-- Main loop for `addSubsingletonInsts`. -/
  go (instTerms : List Term) (insts : Array (Term × AbstractMVarsResult)) :
      TermElabM (Array (Term × AbstractMVarsResult)) := do
    match instTerms with
    | [] => return insts
    | instTerm :: instTerms =>
let inst ← withNewMCtxDepth Term.withoutModifyingElabMetaStateWithInfo do
withRef instTerm Term.withoutErrToSorry do
          let e ← Term.elabTerm instTerm none
          Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
          let e ← instantiateMVars e
          unless (← isClass? (← inferType e)).isSome do
            throwError "Not an instance. Term has type{indentD <| ← inferType e}"
          if e.hasMVar then
            let r ← abstractMVars e
            -- Change all instance arguments corresponding to the mvars to be inst implicit.
            let e' ← forallBoundedTelescope (← inferType r.expr) r.numMVars fun args _ => do
              let newBIs ← args.filterMapM fun arg => do
                if (← isClass? (← inferType arg)).isSome then
                  return some (arg.fvarId!, .instImplicit)
                else
                  return none
              withNewBinderInfos newBIs do
                mkLambdaFVars args (r.expr.beta args)
            pure { r with expr := e' }
          else
            pure { paramNames := #[], mvars := #[], expr := e }
      go instTerms (insts.push (instTerm, inst))

elab_rules : tactic
  | `(tactic| subsingleton $[[$[$instTerms?],*]]?) => withMainContext do
    let recover := (← read).recover
    let insts ← elabSubsingletonInsts instTerms?
    Elab.Tactic.liftMetaTactic1 fun g => do
      let (fvars, g) ← g.intros
      -- note: `insts` are still valid after `intros`
      try
        g.subsingleton (insts := insts)
        return none
      catch e =>
        -- Try `refl` when all else fails, to give a hint to the user
        if recover then
          try
g.refl > g.hrefl
            let tac ← if !fvars.isEmpty then `(tactic| (intros; rfl)) else `(tactic| rfl)
            Meta.Tactic.TryThis.addSuggestion (← getRef) tac (origSpan? := ← getRef)
            return none
          catch _ => pure ()
        throw e

end Mathlib.Tactic
