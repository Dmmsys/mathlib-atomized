/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Conv.Basic

/-! # Tactics that transform types into definitionally equal types

This module defines a standard wrapper that can be used to create tactics that
change hypotheses and the goal to things that are definitionally equal.

It then provides a number of tactics that transform local hypotheses and/or the target.
-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Elab.Tactic

/--
Definition of `_root_.Lean.MVarId.changeLocalDecl'` / `_root_.Lean.MVarId.changeLocalDecl'` 的定义

English:
definition _root_.Lean.MVarId.changeLocalDecl'
  signature: (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
  body: do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index <= decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

中文:
定义 _root_.Lean.MVarId.changeLocalDecl'
  签名: (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
  定义体: do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index <= decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

Depends on / 依赖: MVarId
-/
def _root_.Lean.MVarId.changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index <= decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

/--
Definition of `runDefEqTactic` / `runDefEqTactic` 的定义

English:
definition runDefEqTactic
  signature: (m : Option FVarId -> Expr -> MetaM Expr)
  body: withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")

中文:
定义 runDefEqTactic
  签名: (m : 选项类型 FVarId -> Expr -> MetaM Expr)
  定义体: withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")
-/
def runDefEqTactic (m : Option FVarId -> Expr -> MetaM Expr)
    (loc? : Option (TSyntax ``Parser.Tactic.location))
    (tacticName : String)
    (checkDefEq : Bool := true) :
    TacticM Unit := withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")

/--
Definition of `runDefEqConvTactic` / `runDefEqConvTactic` 的定义

English:
definition runDefEqConvTactic
  signature: (m : Expr -> MetaM Expr)
  body: withMainContext do
Conv.changeLhs ← m (← instantiateMVars <| ← Conv.getLhs)

中文:
定义 runDefEqConvTactic
  签名: (m : Expr -> MetaM Expr)
  定义体: withMainContext do
Conv.changeLhs ← m (← instantiateMVars <| ← Conv.getLhs)

Depends on / 依赖: withMainContext
-/
def runDefEqConvTactic (m : Expr -> MetaM Expr) : TacticM Unit := withMainContext do
Conv.changeLhs ← m (← instantiateMVars <| ← Conv.getLhs)


/-! ### `whnf` -/

/--
`whnf at loc` puts the given location into weak-head normal form.
This also exists as a `conv`-mode tactic.

Weak-head normal form is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.
-/
elab "whnf" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ => whnf) loc? "whnf"


/-! ### `beta_reduce` -/

/--
`beta_reduce at loc` completely beta reduces the given location.
This also exists as a `conv`-mode tactic.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.
-/
elab (name := betaReduceStx) "beta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => Core.betaReduce e) loc? "beta_reduce"

@[inherit_doc betaReduceStx]
elab "beta_reduce" : conv => runDefEqConvTactic (Core.betaReduce ·)


/-! ### `reduce` -/

/--
`reduce at loc` completely reduces the given location.
This also exists as a `conv`-mode tactic.

This does the same transformation as the `#reduce` command.
-/
elab "reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ e => reduce e (skipTypes := false) (skipProofs := false)) loc? "reduce"


/-! ### `unfold_let` -/

/--
Definition of `unfoldFVars` / `unfoldFVars` 的定义

English:
definition unfoldFVars
  signature: (fvars : Array FVarId) (e : Expr)
  body: do
  transform (usedLetOnly := true) e fun node => do
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        if let some val ← fvarId.getValue? then
          return .visit (← instantiateMVars val)
        else
          return .continue
      else
        return .continue
    | _ => return .continue

中文:
定义 unfoldFVars
  签名: (fvars : 数组 FVarId) (e : Expr)
  定义体: do
  transform (usedLetOnly := true) e fun node => do
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        if let some val ← fvarId.getValue? then
          return .visit (← instantiateMVars val)
        else
          return .continue
      else
        return .continue
    | _ => return .continue
-/
def unfoldFVars (fvars : Array FVarId) (e : Expr) : MetaM Expr := do
  transform (usedLetOnly := true) e fun node => do
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        if let some val ← fvarId.getValue? then
          return .visit (← instantiateMVars val)
        else
          return .continue
      else
        return .continue
    | _ => return .continue

/-! ### `refold_let` -/

/--
Definition of `refoldFVars` / `refoldFVars` 的定义

English:
definition refoldFVars
  signature: (fvars : Array FVarId) (loc? : Option FVarId) (e : Expr)
  body: do
  -- Filter the fvars, only taking those that are from earlier in the local context.
  let fvars ←
    if let some loc := loc? then
      let locIndex := (← loc.getDecl).index
      fvars.filterM fun fvar => do
        let some decl ← fvar.findDecl? | return false
        return decl.index < locIndex
    else
      pure fvars
  let mut e := e
  for fvar in fvars do
    let some val ← fvar.getValue?
      | throwError "local variable {Expr.fvar fvar} has no value to refold"
    e := (← kabstract e val).instantiate1 (Expr.fvar fvar)
  return e

中文:
定义 refoldFVars
  签名: (fvars : 数组 FVarId) (loc? : 选项类型 FVarId) (e : Expr)
  定义体: do
  -- Filter the fvars, only taking those that are from earlier in the local context.
  let fvars ←
    if let some loc := loc? then
      let locIndex := (← loc.getDecl).index
      fvars.filterM fun fvar => do
        let some decl ← fvar.findDecl? | return false
        return decl.index < locIndex
    else
      pure fvars
  let mut e := e
  for fvar in fvars do
    let some val ← fvar.getValue?
      | throwError "local variable {Expr.fvar fvar} has no value to refold"
    e := (← kabstract e val).instantiate1 (Expr.fvar fvar)
  return e
-/
def refoldFVars (fvars : Array FVarId) (loc? : Option FVarId) (e : Expr) : MetaM Expr := do
  -- Filter the fvars, only taking those that are from earlier in the local context.
  let fvars ←
    if let some loc := loc? then
      let locIndex := (← loc.getDecl).index
      fvars.filterM fun fvar => do
        let some decl ← fvar.findDecl? | return false
        return decl.index < locIndex
    else
      pure fvars
  let mut e := e
  for fvar in fvars do
    let some val ← fvar.getValue?
      | throwError "local variable {Expr.fvar fvar} has no value to refold"
    e := (← kabstract e val).instantiate1 (Expr.fvar fvar)
  return e

/--
`refold_let x y z at loc` looks for the bodies of local definitions `x`, `y`, and `z` at the given
location and replaces them with `x`, `y`, or `z`. This is the inverse of "zeta reduction."
This also exists as a `conv`-mode tactic.
-/
syntax (name := refoldLetStx) "refold_let" (ppSpace colGt term:max)*
  (ppSpace Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| refold_let $hs:term* $[$loc?]?) => do
    let fvars ← getFVarIds hs
    runDefEqTactic (refoldFVars fvars) loc? "refold_let"

@[inherit_doc refoldLetStx]
syntax "refold_let" (ppSpace colGt term:max)* : conv

elab_rules : conv
  | `(conv| refold_let $hs:term*) => do
    runDefEqConvTactic (refoldFVars (← getFVarIds hs) none)


/-! ### `unfold_projs` -/

/--
Definition of `unfoldProjs` / `unfoldProjs` 的定义

English:
definition unfoldProjs
  signature: (e : Expr)
  body: do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue

中文:
定义 unfoldProjs
  签名: (e : Expr)
  定义体: do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue
-/
def unfoldProjs (e : Expr) : MetaM Expr := do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue

/--
`unfold_projs at loc` unfolds projections of class instances at the given location.
This also exists as a `conv`-mode tactic.
-/
elab (name := unfoldProjsStx) "unfold_projs" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => unfoldProjs) loc? "unfold_projs"

@[inherit_doc unfoldProjsStx]
elab "unfold_projs" : conv => runDefEqConvTactic unfoldProjs


/-! ### `eta_reduce` -/

/--
Definition of `etaReduceAll` / `etaReduceAll` 的定义

English:
definition etaReduceAll
  signature: (e : Expr)
  body: do
  transform e fun node =>
    match node.etaExpandedStrict? with
    | some e' => return .visit e'
    | none => return .continue

中文:
定义 etaReduceAll
  签名: (e : Expr)
  定义体: do
  transform e fun node =>
    match node.etaExpandedStrict? with
    | some e' => return .visit e'
    | none => return .continue
-/
def etaReduceAll (e : Expr) : MetaM Expr := do
  transform e fun node =>
    match node.etaExpandedStrict? with
    | some e' => return .visit e'
    | none => return .continue

/--
`eta_reduce at loc` eta reduces all sub-expressions at the given location.
This also exists as a `conv`-mode tactic.

For example, `fun x y => f x y` becomes `f` after eta reduction.
-/
elab (name := etaReduceStx) "eta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaReduceAll) loc? "eta_reduce"

@[inherit_doc etaReduceStx]
elab "eta_reduce" : conv => runDefEqConvTactic etaReduceAll


/-! ### `eta_expand` -/

/--
Definition of `etaExpandAll` / `etaExpandAll` 的定义

English:
definition etaExpandAll
  signature: (e : Expr)
  body: do
  if e.isLambda then
    expandSubterms e
  else
    forallTelescopeReducing (← inferType e) fun xs _ => do
      let e := mkAppN (e.instantiate xs) xs
      mkLambdaFVars xs (← expandSubterms e)

中文:
定义 etaExpandAll
  签名: (e : Expr)
  定义体: do
  if e.isLambda then
    expandSubterms e
  else
    forallTelescopeReducing (← inferType e) fun xs _ => do
      let e := mkAppN (e.instantiate xs) xs
      mkLambdaFVars xs (← expandSubterms e)
-/
partial def etaExpandAll (e : Expr) : MetaM Expr := do
  if e.isLambda then
    expandSubterms e
  else
    forallTelescopeReducing (← inferType e) fun xs _ => do
      let e := mkAppN (e.instantiate xs) xs
      mkLambdaFVars xs (← expandSubterms e)
where
  expandSubterms
  | .forallE n t b bi =>
    return .forallE n
      (← etaExpandAll t)
      (← withLocalDecl n bi t fun x => (·.abstract #[x]) <$> etaExpandAll (b.instantiate1 x))
      bi
  | .lam n t b bi =>
    return .lam n
      (← etaExpandAll t)
      (← withLocalDecl n bi t fun x => (·.abstract #[x]) <$> etaExpandAll (b.instantiate1 x))
      bi
  | .letE n t v b ndep =>
    return .letE n
      (← etaExpandAll t)
      (← etaExpandAll v)
      (← withLetDecl n t v (nondep := ndep) fun x =>
(·.abstract #[x]) < > etaExpandAll (b.instantiate1 x))
      ndep
  | e@(.app ..) =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.etaExpandedStrict?.isSome then
      expandSubterms (f.beta args)
    else
      -- We use `expandSubterms` for `f` to avoid creating a beta-redex
      return mkAppN (← expandSubterms f) (← args.mapM etaExpandAll)
  | .mdata d e =>
    return .mdata d (← etaExpandAll e)
  | .proj n i e =>
    return .proj n i (← etaExpandAll e)
  | e => return e

/--
`eta_expand at loc` eta expands all sub-expressions at the given location.
It also beta reduces any applications of eta expanded terms, so it puts it
into an eta-expanded "normal form."
This also exists as a `conv`-mode tactic.

For example, if `f` takes two arguments, then `f` becomes `fun x y => f x y`
and `f x` becomes `fun y => f x y`.

This can be useful to turn, for example, a raw `HAdd.hAdd` into `fun x y => x + y`.
-/
elab (name := etaExpandStx) "eta_expand" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaExpandAll) loc? "eta_expand"

@[inherit_doc etaExpandStx]
elab "eta_expand" : conv => runDefEqConvTactic etaExpandAll


/-! ### `eta_struct` -/

/--
Definition of `getProjectedExpr` / `getProjectedExpr` 的定义

English:
definition getProjectedExpr
  signature: (e : Expr)
  body: do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none

中文:
定义 getProjectedExpr
  签名: (e : Expr)
  定义体: do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none
-/
def getProjectedExpr (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none

/--
Definition of `etaStruct?` / `etaStruct?` 的定义

English:
definition etaStruct?
  signature: (e : Expr) (tryWhnfR : Bool := true)
  body: do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  unless isStructure (← getEnv) fVal.induct do return none
  let args := e.getAppArgs
  let mut x? ← findProj fVal args pure
  if tryWhnfR then
    if let .undef := x? then
      x? ← findProj fVal args whnfR
  if let .some x := x? then
    -- Rely on eta for structures to make the check:
    if ← isDefEq x e then
      return x
  return none

中文:
定义 etaStruct?
  签名: (e : Expr) (tryWhnfR : 布尔值 := true)
  定义体: do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  unless isStructure (← getEnv) fVal.induct do return none
  let args := e.getAppArgs
  let mut x? ← findProj fVal args pure
  if tryWhnfR then
    if let .undef := x? then
      x? ← findProj fVal args whnfR
  if let .some x := x? then
    -- Rely on eta for structures to make the check:
    if ← isDefEq x e then
      return x
  return none
-/
def etaStruct? (e : Expr) (tryWhnfR : Bool := true) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  unless isStructure (← getEnv) fVal.induct do return none
  let args := e.getAppArgs
  let mut x? ← findProj fVal args pure
  if tryWhnfR then
    if let .undef := x? then
      x? ← findProj fVal args whnfR
  if let .some x := x? then
    -- Rely on eta for structures to make the check:
    if ← isDefEq x e then
      return x
  return none
where
  /-- Check to see if there's an argument at some index `i`
  such that it's the `i`th projection of a some expression.
  Returns the expression. -/
  findProj (fVal : ConstructorVal) (args : Array Expr) (m : Expr -> MetaM Expr) :
      MetaM (LOption Expr) := do
    for i in [0 : fVal.numFields] do
      let arg ← m args[fVal.numParams + i]!
      let some (S, j, x) ← getProjectedExpr arg | continue
      if S == fVal.induct && i == j then
        return .some x
      else
        -- Then the eta rule can't apply since there's an obviously wrong projection
        return .none
    return .undef

/--
Definition of `etaStructAll` / `etaStructAll` 的定义

English:
definition etaStructAll
  signature: (e : Expr)
  body: transform e fun node => do
    if let some node' ← etaStruct? node then
      return .visit node'
    else
      return .continue

中文:
定义 etaStructAll
  签名: (e : Expr)
  定义体: transform e fun node => do
    if let some node' ← etaStruct? node then
      return .visit node'
    else
      return .continue

Depends on / 依赖: continue, etaStruct, return, transform
-/
def etaStructAll (e : Expr) : MetaM Expr :=
  transform e fun node => do
    if let some node' ← etaStruct? node then
      return .visit node'
    else
      return .continue

/--
`eta_struct at loc` transforms structure constructor applications such as `S.mk x.1 ... x.n`
(pretty printed as, for example, `{a := x.a, b := x.b, ...}`) into `x`.
This also exists as a `conv`-mode tactic.

The transformation is known as eta reduction for structures, and it yields definitionally
equal expressions.

For example, given `x : α × β`, then `(x.1, x.2)` becomes `x` after this transformation.
-/
elab (name := etaStructStx) "eta_struct" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaStructAll) loc? "eta_struct"

@[inherit_doc etaStructStx]
elab "eta_struct" : conv => runDefEqConvTactic etaStructAll

end Mathlib.Tactic
