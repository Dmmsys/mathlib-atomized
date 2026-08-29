/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module


public meta import Mathlib.Tactic.FunProp.Mor
public import Mathlib.Tactic.FunProp.Mor
public import Mathlib.Tactic.FunProp.ToBatteries

/-!
## `funProp` data structure holding information about a function

`FunctionData` holds data about function in the form `fun x ↦ f x₁ ... xₙ`.
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/--
Definition of `FunctionData` / `FunctionData` 的定义

English:
structure FunctionData
  parameters: where
  axioms and operations (6):
    - lctx : LocalContext
    - insts : LocalInstances
    - fn : Expr
    - args : Array Mor.Arg
    - mainVar : Expr
    - mainArgs : Array Nat

中文:
结构 FunctionData
  参数: where
  公理与运算 (6 个):
    - lctx : LocalContext
    - insts : LocalInstances
    - fn : Expr
    - args : 数组 态射.Arg
    - mainVar : Expr
    - mainArgs : 数组 自然数
-/
structure FunctionData where
  /-- local context where `mainVar` exists -/
  lctx : LocalContext
  /-- local instances -/
  insts : LocalInstances
  /-- main function -/
  fn : Expr
  /-- applied function arguments -/
  args : Array Mor.Arg
  /-- main variable -/
  mainVar : Expr
  /-- indices of `args` that contain `mainVars` -/
  mainArgs : Array Nat

/--
Definition of `FunctionData.toExpr` / `FunctionData.toExpr` 的定义

English:
definition FunctionData.toExpr
  signature: (f : FunctionData)
  body: do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

中文:
定义 FunctionData.toExpr
  签名: (f : FunctionData)
  定义体: do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body
-/
def FunctionData.toExpr (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

/--
Definition of `FunctionData.isIdentityFun` / `FunctionData.isIdentityFun` 的定义

English:
definition FunctionData.isIdentityFun
  signature: (f : FunctionData)
  body: (f.args.size = 0 && f.fn == f.mainVar)

中文:
定义 FunctionData.isIdentityFun
  签名: (f : FunctionData)
  定义体: (f.args.size = 0 && f.fn == f.mainVar)

Depends on / 依赖: f.args.size, f.fn, f.mainVar, mainVar
-/
def FunctionData.isIdentityFun (f : FunctionData) : Bool :=
  (f.args.size = 0 && f.fn == f.mainVar)

/--
Definition of `FunctionData.isConstantFun` / `FunctionData.isConstantFun` 的定义

English:
definition FunctionData.isConstantFun
  signature: (f : FunctionData)
  body: ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

中文:
定义 FunctionData.isConstantFun
  签名: (f : FunctionData)
  定义体: ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

Depends on / 依赖: containsFVar, f.fn.containsFVar, f.mainArgs.size, f.mainVar.fvarId, fvarId, mainArgs, mainVar
-/
def FunctionData.isConstantFun (f : FunctionData) : Bool :=
  ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

/--
Definition of `FunctionData.domainType` / `FunctionData.domainType` 的定义

English:
definition FunctionData.domainType
  signature: (f : FunctionData)
  body: withLCtx f.lctx f.insts do
    inferType f.mainVar

中文:
定义 FunctionData.domainType
  签名: (f : FunctionData)
  定义体: withLCtx f.lctx f.insts do
    inferType f.mainVar

Depends on / 依赖: f.insts, f.lctx, f.mainVar, inferType, mainVar, withLCtx
-/
def FunctionData.domainType (f : FunctionData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    inferType f.mainVar

/--
Definition of `FunctionData.getFnConstName?` / `FunctionData.getFnConstName?` 的定义

English:
definition FunctionData.getFnConstName?
  signature: (f : FunctionData)
  body: do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let some info := getStructureInfo? (← getEnv) typeName | return none
    let some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none

中文:
定义 FunctionData.getFnConstName?
  签名: (f : FunctionData)
  定义体: do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let some info := getStructureInfo? (← getEnv) typeName | return none
    let some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none
-/
def FunctionData.getFnConstName? (f : FunctionData) : MetaM (Option Name) := do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let some info := getStructureInfo? (← getEnv) typeName | return none
    let some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none


/--
Definition of `getFunctionData` / `getFunctionData` 的定义

English:
definition getFunctionData
  signature: (f : Expr)
  body: do
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mut fn := fn
      let mut args := args

      -- revert projection in fn
      if let .proj n i x := fn then
        let some info := getStructureInfo? (← getEnv) n | unreachable!
  

中文:
定义 getFunctionData
  签名: (f : Expr)
  定义体: do
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mut fn := fn
      let mut args := args

      -- revert projection in fn
      if let .proj n i x := fn then
        let some info := getStructureInfo? (← getEnv) n | unreachable!
  
-/
def getFunctionData (f : Expr) : MetaM FunctionData := do
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mut fn := fn
      let mut args := args

      -- revert projection in fn
      if let .proj n i x := fn then
        let some info := getStructureInfo? (← getEnv) n | unreachable!
        let some projName := info.getProjFn? i | unreachable!
        let p ← mkAppM projName #[x]
        fn := p.getAppFn
        args := p.getAppArgs.map (fun a => {expr:=a}) ++ args

      let mainArgs := args
.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i else none)
.filterMap id

      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }

/--
Inductive type `MaybeFunctionData` / 归纳类型 `MaybeFunctionData`

English:
inductive MaybeFunctionData
  parameters: where
  constructors (3):
    - letE: (f : Expr)
    - lam: (f : Expr)
    - data: (fData : FunctionData)

中文:
归纳类型 MaybeFunctionData
  参数: where
  构造子 (3 个):
    - letE: (f : Expr)
    - lam: (f : Expr)
    - data: (fData : FunctionData)
-/
inductive MaybeFunctionData where
  /-- Can't generate function data as function body has let binder. -/
  | letE (f : Expr)
  /-- Can't generate function data as function body has lambda binder. -/
  | lam (f : Expr)
  /-- Function data has been successfully generated. -/
  | data (fData : FunctionData)

/--
Definition of `MaybeFunctionData.get` / `MaybeFunctionData.get` 的定义

English:
definition MaybeFunctionData.get
  signature: (fData : MaybeFunctionData)
  body: match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr

中文:
定义 MaybeFunctionData.get
  签名: (fData : MaybeFunctionData)
  定义体: match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr

Depends on / 依赖: OrderClosedTopology, OrderClosedTopology.to_t2Space, T2Space, d.toExpr, toExpr, to_t2Space
-/
def MaybeFunctionData.get (fData : MaybeFunctionData) : MetaM Expr :=
  match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr

/--
Definition of `getFunctionData?` / `getFunctionData?` 的定义

English:
definition getFunctionData?
  signature: (f : Expr)
  body: do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do

  let unfold := fun e : Expr => do
    if let some n := e.getAppFn'.constName? then
      pure ((unfoldPred n) || (← isReducible n))
    else
      pure false

  let .forallE xName xType _ _ ← instantiateMVars (← inferTy

中文:
定义 getFunctionData?
  签名: (f : Expr)
  定义体: do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do

  let unfold := fun e : Expr => do
    if let some n := e.getAppFn'.constName? then
      pure ((unfoldPred n) || (← isReducible n))
    else
      pure false

  let .forallE xName xType _ _ ← instantiateMVars (← inferTy
-/
def getFunctionData? (f : Expr)
    (unfoldPred : Name -> Bool := fun _ => false) :
    MetaM MaybeFunctionData := do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do

  let unfold := fun e : Expr => do
    if let some n := e.getAppFn'.constName? then
      pure ((unfoldPred n) || (← isReducible n))
    else
      pure false

  let .forallE xName xType _ _ ← instantiateMVars (← inferType f)
    | throwError m!"fun_prop bug: function expected, got `{f} : {← inferType f}, \
                    type ctor {(← inferType f).ctorName}"
  withLocalDeclD xName xType fun x => do
headBetaThroughLet let fx' := (← Mor.whnfPred (f.beta #[x]).eta unfold)
    let f' ← mkLambdaFVars #[x] fx'
    match fx' with
    | .letE .. => return .letE f'
    | .lam .. => return .lam f'
    | _ => return .data (← getFunctionData f')

/--
Definition of `FunctionData.unfoldHeadFVar?` / `FunctionData.unfoldHeadFVar?` 的定义

English:
definition FunctionData.unfoldHeadFVar?
  signature: (fData : FunctionData)
  body: do
  let .fvar id := fData.fn | return none
  let some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f

中文:
定义 FunctionData.unfoldHeadFVar?
  签名: (fData : FunctionData)
  定义体: do
  let .fvar id := fData.fn | return none
  let some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f
-/
def FunctionData.unfoldHeadFVar? (fData : FunctionData) : MetaM (Option Expr) := do
  let .fvar id := fData.fn | return none
  let some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f

/--
Inductive type `MorApplication` / 归纳类型 `MorApplication`

English:
inductive MorApplication
  parameters: where
  constructors (4):
    - underApplied: 
    - exact: 
    - overApplied: 
    - none: 

中文:
归纳类型 MorApplication
  参数: where
  构造子 (4 个):
    - underApplied: 
    - exact: 
    - overApplied: 
    - none: 
-/
inductive MorApplication where
  /-- Of the form `⇑f` i.e. missing argument. -/
  | underApplied
  /-- Of the form `⇑f x` i.e. morphism and one argument is provided. -/
  | exact
  /-- Of the form `⇑f x y ...` i.e. additional applied arguments `y ...`. -/
  | overApplied
  /-- Not a morphism application. -/
  | none
  deriving Inhabited, BEq

/--
Definition of `FunctionData.isMorApplication` / `FunctionData.isMorApplication` 的定义

English:
definition FunctionData.isMorApplication
  signature: (f : FunctionData)
  body: do
  if let some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underA

中文:
定义 FunctionData.isMorApplication
  签名: (f : FunctionData)
  定义体: do
  if let some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underA
-/
def FunctionData.isMorApplication (f : FunctionData) : MetaM MorApplication := do
  if let some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underApplied
  match h : f.args.size with
  | 0 => return .none
  | n + 1 =>
    if f.args[n].coe.isSome then
      return .exact
    else if f.args.any (fun a => a.coe.isSome) then
      return .overApplied
    else
      return .none


/--
Inductive type `DecompositionResult` / 归纳类型 `DecompositionResult`

English:
inductive DecompositionResult
  constructors (3):
    - comp: (f g : Expr)
    - uncurried: 
    - failed: 

中文:
归纳类型 DecompositionResult
  构造子 (3 个):
    - comp: (f g : Expr)
    - uncurried: 
    - failed: 
-/
inductive DecompositionResult
  /-- The function can be decomposed in a non-trivial way. -/
  | comp (f g : Expr)
  /-- The function is in uncurried form. -/
  | uncurried
  /-- The decomposition failed for some other reason. -/
  | failed

/--
Definition of `FunctionData.peeloffArgDecomposition` / `FunctionData.peeloffArgDecomposition` 的定义

English:
definition FunctionData.peeloffArgDecomposition
  signature: (fData : FunctionData)
  body: do
  unless fData.args.size > 0 do return .failed
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return .failed

    if fData.args.size = 1 &&
       fData.mainVar == fData.

中文:
定义 FunctionData.peeloffArgDecomposition
  签名: (fData : FunctionData)
  定义体: do
  unless fData.args.size > 0 do return .failed
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return .failed

    if fData.args.size = 1 &&
       fData.mainVar == fData.
-/
def FunctionData.peeloffArgDecomposition (fData : FunctionData) : MetaM DecompositionResult := do
  unless fData.args.size > 0 do return .failed
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return .failed

    if fData.args.size = 1 &&
       fData.mainVar == fData.fn then
      return .failed

    let gBody' := Mor.mkAppN fData.fn fData.args[:n-1]
    let gBody' := if let some coe := yₙ.coe then coe.app gBody' else gBody'
    let g' ← mkLambdaFVars #[x] gBody'
    let f' := Expr.lam `f (← inferType gBody') (.app (.bvar 0) (yₙ.expr)) default
    return .comp f' g'

/--
Definition of `FunctionData.decomposition` / `FunctionData.decomposition` 的定义

English:
definition FunctionData.decomposition
  signature: (fData : FunctionData)
  body: do

    let mut lctx := fData.lctx
    let insts := fData.insts

    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName

    let fn := fData.fn
    let mut args := fData.args

    if fn.containsFVar xId then
      return ← fData.peeloffArgDecompositio

中文:
定义 FunctionData.decomposition
  签名: (fData : FunctionData)
  定义体: do

    let mut lctx := fData.lctx
    let insts := fData.insts

    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName

    let fn := fData.fn
    let mut args := fData.args

    if fn.containsFVar xId then
      return ← fData.peeloffArgDecompositio
-/
def FunctionData.decomposition (fData : FunctionData) : MetaM DecompositionResult := do

    let mut lctx := fData.lctx
    let insts := fData.insts

    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName

    let fn := fData.fn
    let mut args := fData.args

    if fn.containsFVar xId then
      return ← fData.peeloffArgDecomposition

    -- constant function can't be decomposed
    if fData.mainArgs.size == 0 then
      return .failed

    let mut yVals : Array Expr := #[]
    let mut yVars : Array Expr := #[]

    for argId in fData.mainArgs do
      let yVal := args[argId]!

      let yVal' := yVal.expr
      let yId ← withLCtx lctx insts mkFreshFVarId
      let yType ← withLCtx lctx insts (inferType yVal')
      if yType.containsFVar fData.mainVar.fvarId! then
        return .failed
      lctx := lctx.mkLocalDecl yId (xName.appendAfter (toString argId)) yType
      let yVar := Expr.fvar yId
      yVars := yVars.push yVar
      yVals := yVals.push yVal'
      args := args.set! argId ⟨yVar, yVal.coe⟩

    let g ← withLCtx lctx insts do
      mkLambdaFVars #[x] (← mkProdElem yVals)
    let f ← withLCtx lctx insts do
      (mkLambdaFVars yVars (Mor.mkAppN fn args))
      >>=
      mkUncurryFun yVars.size

    -- check non-triviality
    let f' ← fData.toExpr
if ← withReducibleAndInstances isDefEq f' f then
      return .uncurried
if ← withReducibleAndInstances isDefEq f' g then
      return .failed

    return .comp f g


/--
Definition of `FunctionData.decompositionOverArgs` / `FunctionData.decompositionOverArgs` 的定义

English:
definition FunctionData.decompositionOverArgs
  signature: (fData : FunctionData) (args : Array Nat)
  body: do

  unless isOrderedSubsetOf fData.mainArgs args do return none
  unless ¬(fData.fn.containsFVar fData.mainVar.fvarId!) do return none

  withLCtx fData.lctx fData.insts do

  let gxs := args.map (fun i => fData.args[i]!.expr)

  try
    let gx ← mkProdElem gxs -- this can crash if we have depende

中文:
定义 FunctionData.decompositionOverArgs
  签名: (fData : FunctionData) (args : 数组 自然数)
  定义体: do

  unless isOrderedSubsetOf fData.mainArgs args do return none
  unless ¬(fData.fn.containsFVar fData.mainVar.fvarId!) do return none

  withLCtx fData.lctx fData.insts do

  let gxs := args.map (fun i => fData.args[i]!.expr)

  try
    let gx ← mkProdElem gxs -- this can crash if we have depende
-/
def FunctionData.decompositionOverArgs (fData : FunctionData) (args : Array Nat) :
    MetaM (Option (Expr × Expr)) := do

  unless isOrderedSubsetOf fData.mainArgs args do return none
  unless ¬(fData.fn.containsFVar fData.mainVar.fvarId!) do return none

  withLCtx fData.lctx fData.insts do

  let gxs := args.map (fun i => fData.args[i]!.expr)

  try
    let gx ← mkProdElem gxs -- this can crash if we have dependent types
let g ← withLCtx fData.lctx fData.insts mkLambdaFVars #[fData.mainVar] gx

    withLocalDeclD `y (← inferType gx) fun y => do

      let ys ← mkProdSplitElem y gxs.size
      let args' := (args.zip ys).foldl (init := fData.args)
          (fun args' (i,y) => args'.set! i { expr := y, coe := args'[i]!.coe })

      let f ← mkLambdaFVars #[y] (Mor.mkAppN fData.fn args')
      return (f,g)
  catch _ =>
    return none

end Meta.FunProp

end Mathlib
