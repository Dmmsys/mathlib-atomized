/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Tactic.FunProp.Decl
public meta import Mathlib.Tactic.FunProp.Types
public meta import Mathlib.Tactic.FunProp.FunctionData
public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize
public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import Mathlib.Tactic.FunProp.Decl
public import Mathlib.Tactic.FunProp.Types

/-!
## `fun_prop` environment extensions storing theorems for `fun_prop`
-/

public meta section

namespace Mathlib
open Lean Meta
open Std (TreeMap)

namespace Meta.FunProp

/--
Inductive type `LambdaTheoremArgs` / 归纳类型 `LambdaTheoremArgs`

English:
inductive LambdaTheoremArgs
  constructors (5):
    - id: 
    - const: 
    - apply: 
    - comp: (fArgId gArgId : Nat)
    - pi: 

中文:
归纳类型 LambdaTheoremArgs
  构造子 (5 个):
    - id: 
    - const: 
    - apply: 
    - comp: (fArgId gArgId : 自然数)
    - pi: 
-/
inductive LambdaTheoremArgs
  /-- Identity theorem e.g. `Continuous fun x ↦ x` -/
  | id
  /-- Constant theorem e.g. `Continuous fun x ↦ y` -/
  | const
  /-- Apply theorem e.g. `Continuous fun (f : (x : X) → Y x ↦ f x)` -/
  | apply
  /-- Composition theorem e.g. `Continuous f → Continuous g → Continuous fun x ↦ f (g x)`

  The numbers `fArgId` and `gArgId` store the argument index for `f` and `g` in the composition
  theorem. -/
  | comp (fArgId gArgId : Nat)
  /-- Pi theorem e.g. `∀ y, Continuous (f · y) → Continuous fun x y ↦ f x y` -/
  | pi
  deriving Inhabited, BEq, Repr, Hashable

/--
Inductive type `LambdaTheoremType` / 归纳类型 `LambdaTheoremType`

English:
inductive LambdaTheoremType
  constructors (5):
    - id: 
    - const: 
    - apply: 
    - comp: 
    - pi: 

中文:
归纳类型 LambdaTheoremType
  构造子 (5 个):
    - id: 
    - const: 
    - apply: 
    - comp: 
    - pi: 

Depends on / 依赖: Pi.le_def, continuous_apply, isClosed_iInter, isClosed_le, le_def, ofPred_forall
-/
inductive LambdaTheoremType
  /-- Identity theorem e.g. `Continuous fun x ↦ x` -/
  | id
  /-- Constant theorem e.g. `Continuous fun x ↦ y` -/
  | const
  /-- Apply theorem e.g. `Continuous fun (f : (x : X) → Y x ↦ f x)` -/
  | apply
  /-- Composition theorem e.g. `Continuous f → Continuous g → Continuous fun x ↦ f (g x)` -/
  | comp
  /-- Pi theorem e.g. `∀ y, Continuous (f · y) → Continuous fun x y ↦ f x y` -/
  | pi
  deriving Inhabited, BEq, Repr, Hashable

/--
Definition of `LambdaTheoremArgs.type` / `LambdaTheoremArgs.type` 的定义

English:
definition LambdaTheoremArgs.type
  signature: (t : LambdaTheoremArgs)
  body: match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply => .apply
  | .pi => .pi

中文:
定义 LambdaTheoremArgs.type
  签名: (t : LambdaTheoremArgs)
  定义体: match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply => .apply
  | .pi => .pi
-/
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply => .apply
  | .pi => .pi

/--
Definition of `detectLambdaTheoremArgs` / `detectLambdaTheoremArgs` 的定义

English:
definition detectLambdaTheoremArgs
  signature: (f : Expr) (ctxVars : Array Expr)
  body: do

  -- eta expand but beta reduce body
  let f ← forallTelescope (← inferType f) fun xs _ =>
    mkLambdaFVars xs (mkAppN f xs).headBeta

  match f with
  | .lam _ _ xBody _ =>
    unless xBody.hasLooseBVars do return some .const
    match xBody with
    | .bvar 0 => return some .id
    | .app (.b

中文:
定义 detectLambdaTheoremArgs
  签名: (f : Expr) (ctxVars : 数组 Expr)
  定义体: do

  -- eta expand but beta reduce body
  let f ← forallTelescope (← inferType f) fun xs _ =>
    mkLambdaFVars xs (mkAppN f xs).headBeta

  match f with
  | .lam _ _ xBody _ =>
    unless xBody.hasLooseBVars do return some .const
    match xBody with
    | .bvar 0 => return some .id
    | .app (.b
-/
def detectLambdaTheoremArgs (f : Expr) (ctxVars : Array Expr) :
    MetaM (Option LambdaTheoremArgs) := do

  -- eta expand but beta reduce body
  let f ← forallTelescope (← inferType f) fun xs _ =>
    mkLambdaFVars xs (mkAppN f xs).headBeta

  match f with
  | .lam _ _ xBody _ =>
    unless xBody.hasLooseBVars do return some .const
    match xBody with
    | .bvar 0 => return some .id
    | .app (.bvar 0) (.fvar _) => return some .apply
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) =>
      -- fun x => f (g x)
      let some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
return some .comp argId_f argId_g
    | .lam _ _ (.app (.app (.fvar _) (.bvar 1)) (.bvar 0)) _ =>
      return some .pi
    | _ => return none
  | _ => return none


/--
Definition of `LambdaTheorem` / `LambdaTheorem` 的定义

English:
structure LambdaTheorem
  parameters: where
  axioms and operations (3):
    - funPropName : Name
    - thmName : Name
    - thmArgs : LambdaTheoremArgs

中文:
结构 LambdaTheorem
  参数: where
  公理与运算 (3 个):
    - funPropName : Name
    - thmName : Name
    - thmArgs : LambdaTheoremArgs
-/
structure LambdaTheorem where
  /-- Name of function property -/
  funPropName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- Type and important argument of the theorem. -/
  thmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq

/--
Definition of `LambdaTheorems` / `LambdaTheorems` 的定义

English:
structure LambdaTheorems
  parameters: where
  axioms and operations (1):
    - theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaTheorem)  [default: {}]

中文:
结构 LambdaTheorems
  参数: where
  公理与运算 (1 个):
    - theorems : Std.HashMap (Name × LambdaTheoremType) (数组 LambdaTheorem)  [默认: {}]
-/
structure LambdaTheorems where
  /-- map: function property name × theorem type → lambda theorem -/
  theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaTheorem) := {}
  deriving Inhabited


/--
Definition of `LambdaTheorem.getProof` / `LambdaTheorem.getProof` 的定义

English:
definition LambdaTheorem.getProof
  signature: (thm : LambdaTheorem)
  body: do
  mkConstWithFreshMVarLevels thm.thmName

中文:
定义 LambdaTheorem.getProof
  签名: (thm : LambdaTheorem)
  定义体: do
  mkConstWithFreshMVarLevels thm.thmName
-/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/--
Definition of `LambdaTheoremsExt` / `LambdaTheoremsExt` 的定义

English:
abbreviation LambdaTheoremsExt
  body: SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

中文:
缩写 LambdaTheoremsExt
  定义体: SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

Depends on / 依赖: LambdaTheorem, LambdaTheorems, SimpleScopedEnvExtension
-/
abbrev LambdaTheoremsExt := SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

/-- Environment extension storing all lambda theorems. -/
initialize lambdaTheoremsExt : LambdaTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems :=
        let es := d.theorems.getD (e.funPropName, e.thmArgs.type) #[]
        d.theorems.insert (e.funPropName, e.thmArgs.type) (es.push e)}
  }

/--
Definition of `getLambdaTheorems` / `getLambdaTheorems` 的定义

English:
definition getLambdaTheorems
  signature: (funPropName : Name) (type : LambdaTheoremType)
  body: do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]

中文:
定义 getLambdaTheorems
  签名: (funPropName : Name) (type : LambdaTheoremType)
  定义体: do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]

Depends on / 依赖: PriestleySpace, PriestleySpace.toTotallySeparatedSpace, TotallySeparatedSpace, toTotallySeparatedSpace
-/
def getLambdaTheorems (funPropName : Name) (type : LambdaTheoremType) :
    CoreM (Array LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]


--------------------------------------------------------------------------------

/--
Inductive type `TheoremForm` / 归纳类型 `TheoremForm`

English:
inductive TheoremForm
  parameters: where
  constructors (1):
    - uncurried: | comp

中文:
归纳类型 TheoremForm
  参数: where
  构造子 (1 个):
    - uncurried: | comp
-/
inductive TheoremForm where
  | uncurried | comp
  deriving Inhabited, BEq, Repr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString TheoremForm
  body: ⟨fun x => match x with | .uncurried => "simple" | .comp => "compositional"⟩

中文:
实例 :
  签名: ToString TheoremForm
  定义体: ⟨fun x => match x with | .uncurried => "simple" | .comp => "compositional"⟩

Depends on / 依赖: compositional, simple, uncurried
-/
instance : ToString TheoremForm :=
  ⟨fun x => match x with | .uncurried => "simple" | .comp => "compositional"⟩

/--
Definition of `DecompositionResult.toTheoremForm` / `DecompositionResult.toTheoremForm` 的定义

English:
definition DecompositionResult.toTheoremForm
  signature: : DecompositionResult -> TheoremForm

中文:
定义 DecompositionResult.toTheoremForm
  签名: : DecompositionResult -> TheoremForm
-/
def DecompositionResult.toTheoremForm : DecompositionResult -> TheoremForm
| .uncurried => .uncurried
| _ => .comp

/--
Definition of `FunctionTheorem` / `FunctionTheorem` 的定义

English:
structure FunctionTheorem
  parameters: where
  axioms and operations (7):
    - funPropName : Name
    - thmOrigin : Origin
    - funOrigin : Origin
    - mainArgs : Array Nat
    - appliedArgs : Nat
    - priority : Nat  [default: eval_prio default]
    - form : TheoremForm

中文:
结构 FunctionTheorem
  参数: where
  公理与运算 (7 个):
    - funPropName : Name
    - thmOrigin : Origin
    - funOrigin : Origin
    - mainArgs : 数组 自然数
    - appliedArgs : 自然数
    - priority : 自然数  [默认: eval_prio default]
    - form : TheoremForm

Depends on / 依赖: eval_prio
-/
structure FunctionTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmOrigin : Origin
  /-- function name -/
  funOrigin : Origin
  /-- array of argument indices about which this theorem is about -/
  mainArgs : Array Nat
  /-- total number of arguments applied to the function -/
  appliedArgs : Nat
  /-- priority -/
  priority : Nat := eval_prio default
  /-- form of the theorem, see documentation of TheoremForm -/
  form : TheoremForm
  deriving Inhabited, BEq

set_option linter.style.docString.empty false in
/--
Definition of `FunctionTheorems` / `FunctionTheorems` 的定义

English:
structure FunctionTheorems
  parameters: where
  axioms and operations (1):
    - theorems : TreeMap Name (TreeMap Name (Array FunctionTheorem) Name.quickCmp) Name.quickCmp  [default: {}]

中文:
结构 FunctionTheorems
  参数: where
  公理与运算 (1 个):
    - theorems : TreeMap Name (TreeMap Name (数组 FunctionTheorem) Name.quickCmp) Name.quickCmp  [默认: {}]
-/
structure FunctionTheorems where
  /-- map: function name → function property → function theorem -/
  theorems :
    TreeMap Name (TreeMap Name (Array FunctionTheorem) Name.quickCmp) Name.quickCmp := {}
  deriving Inhabited


/--
Definition of `FunctionTheorem.getProof` / `FunctionTheorem.getProof` 的定义

English:
definition FunctionTheorem.getProof
  signature: (thm : FunctionTheorem)
  body: do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id

中文:
定义 FunctionTheorem.getProof
  签名: (thm : FunctionTheorem)
  定义体: do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id
-/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id

set_option linter.style.docString.empty false in
/--
Definition of `FunctionTheoremsExt` / `FunctionTheoremsExt` 的定义

English:
abbreviation FunctionTheoremsExt
  body: SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

中文:
缩写 FunctionTheoremsExt
  定义体: SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

Depends on / 依赖: FunctionTheorem, FunctionTheorems, SimpleScopedEnvExtension
-/
abbrev FunctionTheoremsExt := SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

/-- Extension storing all function theorems. -/
initialize functionTheoremsExt : FunctionTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with
        theorems :=
          d.theorems.alter e.funOrigin.name fun funProperties =>
            let funProperties := funProperties.getD {}
            funProperties.alter e.funPropName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }

set_option linter.style.docString.empty false in
/--
Definition of `getTheoremsForFunction` / `getTheoremsForFunction` 的定义

English:
definition getTheoremsForFunction
  signature: (funName : Name) (funPropName : Name)
  body: do
  return (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}
.getD funPropName #[]

中文:
定义 getTheoremsForFunction
  签名: (funName : Name) (funPropName : Name)
  定义体: do
  return (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}
.getD funPropName #[]
-/
def getTheoremsForFunction (funName : Name) (funPropName : Name) :
    CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}
.getD funPropName #[]


--------------------------------------------------------------------------------

/--
Definition of `GeneralTheorem.getProof` / `GeneralTheorem.getProof` 的定义

English:
definition GeneralTheorem.getProof
  signature: (thm : GeneralTheorem)
  body: do
  mkConstWithFreshMVarLevels thm.thmName

中文:
定义 GeneralTheorem.getProof
  签名: (thm : GeneralTheorem)
  定义体: do
  mkConstWithFreshMVarLevels thm.thmName
-/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/--
Definition of `GeneralTheoremsExt` / `GeneralTheoremsExt` 的定义

English:
abbreviation GeneralTheoremsExt
  body: SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

中文:
缩写 GeneralTheoremsExt
  定义体: SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

Depends on / 依赖: GeneralTheorem, GeneralTheorems, SimpleScopedEnvExtension
-/
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

/-- Environment extension for transition theorems. -/
initialize transitionTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }

/--
Definition of `getTransitionTheorems` / `getTransitionTheorems` 的定义

English:
definition getTransitionTheorems
  signature: (e : Expr)
  body: do
  let thms := (← get).transitionTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with transitionTheorems := ⟨thms⟩ })
  return candidates.toArray

中文:
定义 getTransitionTheorems
  签名: (e : Expr)
  定义体: do
  let thms := (← get).transitionTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with transitionTheorems := ⟨thms⟩ })
  return candidates.toArray
-/
def getTransitionTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).transitionTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with transitionTheorems := ⟨thms⟩ })
  return candidates.toArray

/-- Environment extension for morphism theorems. -/
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }


/--
Definition of `getMorphismTheorems` / `getMorphismTheorems` 的定义

English:
definition getMorphismTheorems
  signature: (e : Expr)
  body: do
  let thms := (← get).morTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with morTheorems := ⟨thms⟩ })
  return candidates.toArray

中文:
定义 getMorphismTheorems
  签名: (e : Expr)
  定义体: do
  let thms := (← get).morTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with morTheorems := ⟨thms⟩ })
  return candidates.toArray
-/
def getMorphismTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).morTheorems.theorems
let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false })
    thms.getMatch e false true
  modify ({ · with morTheorems := ⟨thms⟩ })
  return candidates.toArray


--------------------------------------------------------------------------------


/--
Inductive type `Theorem` / 归纳类型 `Theorem`

English:
inductive Theorem
  parameters: where
  constructors (4):
    - lam: (thm : LambdaTheorem)
    - function: (thm : FunctionTheorem)
    - mor: (thm : GeneralTheorem)
    - transition: (thm : GeneralTheorem)

中文:
归纳类型 定理
  参数: where
  构造子 (4 个):
    - lam: (thm : LambdaTheorem)
    - function: (thm : FunctionTheorem)
    - mor: (thm : GeneralTheorem)
    - transition: (thm : GeneralTheorem)
-/
inductive Theorem where
  | lam (thm : LambdaTheorem)
  | function (thm : FunctionTheorem)
  | mor (thm : GeneralTheorem)
  | transition (thm : GeneralTheorem)


/--
Definition of `getTheoremFromConst` / `getTheoremFromConst` 的定义

English:
definition getTheoremFromConst
  signature: (declName : Name) (prio : Nat := eval_prio default)
  body: do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
withConfig (fun cfg => { cfg with zeta := false}) getFunc

中文:
定义 getTheoremFromConst
  签名: (declName : Name) (prio : 自然数 := eval_prio default)
  定义体: do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
withConfig (fun cfg => { cfg with zeta := false}) getFunc

Depends on / 依赖: Theorem, eval_prio
-/
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
withConfig (fun cfg => { cfg with zeta := false}) getFunctionData? f defaultUnfoldPred
    if let some thmArgs ← detectLambdaTheoremArgs (← fData?.get) xs then
      return .lam {
        funPropName := funPropName
        thmName := declName
        thmArgs := thmArgs
      }

    let .data fData := fData?
      | throwError s!"function in invalid form {← ppExpr f}"

    match fData.fn with
    | .const funName _ =>

      let dec ← fData.decomposition

      return .function {
-- funPropName funName fData.mainArgs fData.args.size thmForm
        funPropName := funPropName
        thmOrigin := .decl declName
        funOrigin := .decl funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := dec.toTheoremForm
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys ← RefinedDiscrTree.initializeLazyEntryWithEta b'
      let thm : GeneralTheorem := {
        funPropName := funPropName
        thmName := declName
        keys := keys
        priority := prio
      }
      -- todo: maybe do a little bit more careful detection of morphism and transition theorems
      match (← fData.isMorApplication) with
      | .exact | .overApplied => return .mor thm
      | .underApplied =>
        throwError "fun_prop theorem about morphism coercion has to be in fully applied form"
      | .none =>
        if fData.fn.isFVar && (fData.args.size == 1) &&
           (fData.args[0]!.expr == fData.mainVar) then
          return .transition thm

        throwError "Not a valid `fun_prop` theorem!"
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"


/--
Definition of `addTheorem` / `addTheorem` 的定义

English:
definition addTheorem
  signature: (declName : Name) (attrKind : AttributeKind := .global)
  body: do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.a

中文:
定义 addTheorem
  签名: (declName : Name) (attrKind : AttributeKind := .global)
  定义体: do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.a

Depends on / 依赖: global
-/
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
function theorem: {thm.thmOrigin.name}
function property: {thm.funPropName}
function name: {thm.funOrigin.name}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {toString thm.form} form"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
morphism theorem: {thm.thmName}
function property: {thm.funPropName}"
    morTheoremsExt.add thm attrKind
  | .transition thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
transition theorem: {thm.thmName}
function property: {thm.funPropName}"
    transitionTheoremsExt.add thm attrKind

end Meta.FunProp

end Mathlib
