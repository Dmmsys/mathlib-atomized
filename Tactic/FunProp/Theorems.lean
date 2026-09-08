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

/-- Tag for one of the 5 basic lambda theorems, that also hold extra data for composition theorem
-/
/-
**Mathlib.Meta.FunProp.LambdaTheoremArgs** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Me
ta.FunProp`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tag for one of the 5 basic lambda theorems, that also hold extra data for compos
ition theorem
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

/-- Tag for one of the 5 basic lambda theorems -/
/-
**Mathlib.Meta.FunProp.LambdaTheoremType** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Me
ta.FunProp`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tag for one of the 5 basic lambda theorems
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

/-- Convert `LambdaTheoremArgs` to `LambdaTheoremType`. -/
/-
**Mathlib.Meta.FunProp.LambdaTheoremArgs.type** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Meta.FunProp.LambdaTheoremArgs`。
形式化陈述：Mathlib.Meta.FunProp.LambdaTheoremArgs → Mathlib.Meta.FunProp.LambdaTheore
mType
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert `LambdaTheoremArgs` to `LambdaTheoremType`.
-/
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply  => .apply
  | .pi => .pi

/-- Decides whether `f` is a function corresponding to one of the lambda theorems. -/
/-
**Mathlib.Meta.FunProp.detectLambdaTheoremArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Meta.FunProp`。
形式化陈述：detectLambdaTheoremArgs (f : Expr) (ctxVars : Array Expr) : MetaM (Option 
LambdaTheoremArgs)
参数：f : Expr；ctxVars : Array Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decides whether `f` is a function corresponding to one of the lambda theorems.
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
    | .app (.bvar 0) (.fvar _) =>  return some .apply
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) =>
      -- fun x => f (g x)
      let some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
      return some <| .comp argId_f argId_g
    | .lam _ _ (.app (.app (.fvar _) (.bvar 1)) (.bvar 0)) _ =>
      return some .pi
    | _ => return none
  | _ => return none


/-- Structure holding information about lambda theorem. -/
/-
**Mathlib.Meta.FunProp.LambdaTheorem** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.F
unProp`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure holding information about lambda theorem.
-/
structure LambdaTheorem where
  /-- Name of function property -/
  funPropName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- Type and important argument of the theorem. -/
  thmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq

/-- Collection of lambda theorems -/
/-
**Mathlib.Meta.FunProp.LambdaTheorems** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.Fu
nProp`。
形式化陈述：LambdaTheorems where /-- map: function property name × theorem type → lamb
da theorem -/ theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaThe
orem)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collection of lambda theorems
-/
structure LambdaTheorems where
  /-- map: function property name × theorem type → lambda theorem -/
  theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaTheorem) := {}
  deriving Inhabited


/-- Return proof of lambda theorem -/
/-
**Mathlib.Meta.FunProp.LambdaTheorem.getProof** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Meta.FunProp.LambdaTheorem`。
形式化陈述：Mathlib.Meta.FunProp.LambdaTheorem → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return proof of lambda theorem
-/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- Environment extension storing lambda theorems. -/
/-
**Mathlib.Meta.FunProp.LambdaTheoremsExt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Me
ta.FunProp`。
形式化陈述：LambdaTheoremsExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Environment extension storing lambda theorems.
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

/-- Get lambda theorems for particular function property `funPropName`. -/
/-
**Mathlib.Meta.FunProp.getLambdaTheorems** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.FunProp`。
形式化陈述：getLambdaTheorems (funPropName : Name) (type : LambdaTheoremType) : CoreM 
(Array LambdaTheorem)
参数：funPropName : Name；type : LambdaTheoremType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get lambda theorems for particular function property `funPropName`.
-/
def getLambdaTheorems (funPropName : Name) (type : LambdaTheoremType) :
    CoreM (Array LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]


--------------------------------------------------------------------------------

/-- Function theorems are stated in uncurried or compositional form.

uncurried
```
theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
```

compositional
```
theorem Continuous_add (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ (f x) + (g x))
```
-/
/-
**Mathlib.Meta.FunProp.TheoremForm** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.Fun
Prop`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function theorems are stated in uncurried or compositional form.

uncurried
```
theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
```

compositional
```
theorem Continuous_add (hf : Continuous f) (hg : Continuous g) : Continuous (fun
 x ↦ (f x) + (g x))
```
-/
inductive TheoremForm where
  | uncurried | comp
  deriving Inhabited, BEq, Repr

/-- TheoremForm to string -/
/-
**Mathlib.Meta.FunProp.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Meta.FunProp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TheoremForm to string
-/
instance : ToString TheoremForm :=
  ⟨fun x => match x with | .uncurried => "simple" | .comp => "compositional"⟩

/-- Gives the theorem form using the result of `FunctionData.decomposition`.

Note that this returns `TheoremForm.comp` even when the decomposition failed (usually due to
dependent types). This means that the theorem will be applied directly without trying to write the
goal as a composition. -/
/-
**Mathlib.Meta.FunProp.DecompositionResult.toTheoremForm** 是 Mathlib 中的一个定义，位于命名
空间 `Mathlib.Meta.FunProp.DecompositionResult`。
形式化陈述：Mathlib.Meta.FunProp.DecompositionResult → Mathlib.Meta.FunProp.TheoremFor
m
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gives the theorem form using the result of `FunctionData.decomposition`.

Note that this returns `TheoremForm.comp` even when the decomposition failed (us
ually due to
dependent types). This means that the theorem will be applied directly without t
rying to write the
goal as a composition.
-/
def DecompositionResult.toTheoremForm : DecompositionResult → TheoremForm
| .uncurried => .uncurried
| _ => .comp

/-- theorem about specific function (either declared constant or free variable) -/
/-
**Mathlib.Meta.FunProp.FunctionTheorem** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.F
unProp`。
形式化陈述：FunctionTheorem where /-- function property name -/ funPropName : Name /--
 theorem name -/ thmOrigin : Origin /-- function name -/ funOrigin : Origin /-- 
array of argument indices about which this theorem is about -/ mainArgs : Array 
Nat /-- total number of arguments applied to the function -/ appliedArgs : Nat /
-- priority -/ priority : Nat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
theorem about specific function (either declared constant or free variable)
-/
structure FunctionTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmOrigin   : Origin
  /-- function name -/
  funOrigin   : Origin
  /-- array of argument indices about which this theorem is about -/
  mainArgs    : Array Nat
  /-- total number of arguments applied to the function -/
  appliedArgs : Nat
  /-- priority -/
  priority    : Nat  := eval_prio default
  /-- form of the theorem, see documentation of TheoremForm -/
  form : TheoremForm
  deriving Inhabited, BEq

set_option linter.style.docString.empty false in
/-- -/
/-
**Mathlib.Meta.FunProp.FunctionTheorems** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.
FunProp`。
形式化陈述：FunctionTheorems where /-- map: function name → function property → functi
on theorem -/ theorems : TreeMap Name (TreeMap Name (Array FunctionTheorem) Name
.quickCmp) Name.quickCmp
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure FunctionTheorems where
  /-- map: function name → function property → function theorem -/
  theorems :
    TreeMap Name (TreeMap Name (Array FunctionTheorem) Name.quickCmp) Name.quickCmp := {}
  deriving Inhabited


/-- return proof of function theorem -/
/-
**Mathlib.Meta.FunProp.FunctionTheorem.getProof** 是 Mathlib 中的一个定义，位于命名空间 `Mathl
ib.Meta.FunProp.FunctionTheorem`。
形式化陈述：Mathlib.Meta.FunProp.FunctionTheorem → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
return proof of function theorem
-/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id

set_option linter.style.docString.empty false in
/-- -/
/-
**Mathlib.Meta.FunProp.FunctionTheoremsExt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.
Meta.FunProp`。
形式化陈述：FunctionTheoremsExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FunctionTheoremsExt := SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

/-- Extension storing all function theorems. -/
initialize functionTheoremsExt : FunctionTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
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
/-- -/
/-
**Mathlib.Meta.FunProp.getTheoremsForFunction** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Meta.FunProp`。
形式化陈述：getTheoremsForFunction (funName : Name) (funPropName : Name) : CoreM (Arra
y FunctionTheorem)
参数：funName : Name；funPropName : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def getTheoremsForFunction (funName : Name) (funPropName : Name) :
    CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}
    |>.getD funPropName #[]


--------------------------------------------------------------------------------

/-- Get proof of a theorem. -/
/-
**Mathlib.Meta.FunProp.GeneralTheorem.getProof** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Meta.FunProp.GeneralTheorem`。
形式化陈述：Mathlib.Meta.FunProp.GeneralTheorem → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get proof of a theorem.
-/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- Extensions for transition or morphism theorems -/
/-
**Mathlib.Meta.FunProp.GeneralTheoremsExt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.M
eta.FunProp`。
形式化陈述：GeneralTheoremsExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extensions for transition or morphism theorems
-/
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

/-- Environment extension for transition theorems. -/
initialize transitionTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }

/-- Get transition theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` might return theorems implying continuity
from linearity over finite-dimensional spaces or differentiability. -/
/-
**Mathlib.Meta.FunProp.getTransitionTheorems** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Meta.FunProp`。
形式化陈述：getTransitionTheorems (e : Expr) : FunPropM (Array GeneralTheorem)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get transition theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` might return theorems implyin
g continuity
from linearity over finite-dimensional spaces or differentiability.
-/
def getTransitionTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).transitionTheorems.theorems
  let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    thms.getMatch e false true
  modify ({ · with transitionTheorems := ⟨thms⟩ })
  return candidates.toArray

/-- Environment extension for morphism theorems. -/
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }


/-- Get morphism theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` for `f : X→L[ℝ] Y` would return theorem
inferring continuity from the bundled morphism. -/
/-
**Mathlib.Meta.FunProp.getMorphismTheorems** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.FunProp`。
形式化陈述：getMorphismTheorems (e : Expr) : FunPropM (Array GeneralTheorem)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get morphism theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` for `f : X→L[ℝ] Y` would retu
rn theorem
inferring continuity from the bundled morphism.
-/
def getMorphismTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).morTheorems.theorems
  let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    thms.getMatch e false true
  modify ({ · with morTheorems := ⟨thms⟩ })
  return candidates.toArray


--------------------------------------------------------------------------------


/-- There are four types of theorems:
- lam - theorem about basic lambda calculus terms
- function - theorem about a specific function(declared or free variable) in specific arguments
- mor - special theorems talking about bundled morphisms/DFunLike.coe
- transition - theorems inferring one function property from another

Examples:
- lam
  ```
  theorem Continuous_id : Continuous fun x ↦ x
  theorem Continuous_comp (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ f (g x)
  ```
- function
  ```
  theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
  theorem Continuous_add (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ (f x) + (g x))
  ```
- mor - the head of function body has to be `DFunLike.coe`
  ```
  theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
      (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
      ContDiff 𝕜 n fun x ↦ (f x) (g x)
  theorem clm_linear {f : E →L[𝕜] F} : IsLinearMap 𝕜 f
  ```
- transition - the conclusion has to be in the form `P f` where `f` is a free variable
  ```
  theorem linear_is_continuous [FiniteDimensional ℝ E] {f : E → F} (hf : IsLinearMap 𝕜 f) :
      Continuous f
  ```
-/
/-
**Mathlib.Meta.FunProp.Theorem** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.FunProp
`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are four types of theorems:
- lam - theorem about basic lambda calculus terms
- function - theorem about a specific function(declared or free variable) in spe
cific arguments
- mor - special theorems talking about bundled morphisms/DFunLike.coe
- transition - theorems inferring one function property from another

Examples:
- lam
  ```
  theorem Continuous_id : Continuous fun x ↦ x
  theorem Continuous_comp (hf : Continuous f) (hg : Continuous g) : Continuous f
un x ↦ f (g x)
  ```
- function
  ```
  theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
  theorem Continuous_add (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ (f x) + (g x))
  ```
- mor - the head of function body has to be `DFunLike.coe`
  ```
  theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
      (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
      ContDiff 𝕜 n fun x ↦ (f x) (g x)
  theorem clm_linear {f : E →L[𝕜] F} : IsLinearMap 𝕜 f
  ```
- transition - the conclusion has to be in the form `P f` where `f` is a free va
riable
  ```
  theorem linear_is_continuous [FiniteDimensional ℝ E] {f : E → F} (hf : IsLinea
rMap 𝕜 f) :
      Continuous f
  ```
-/
inductive Theorem where
  | lam        (thm : LambdaTheorem)
  | function   (thm : FunctionTheorem)
  | mor        (thm : GeneralTheorem)
  | transition (thm : GeneralTheorem)


/-- For a theorem declaration `declName` return `fun_prop` theorem. It correctly detects which
type of theorem it is. -/
/-
**Mathlib.Meta.FunProp.getTheoremFromConst** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.FunProp`。
形式化陈述：getTheoremFromConst (declName : Name) (prio : Nat
参数：declName : Name。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a theorem declaration `declName` return `fun_prop` theorem. It correctly det
ects which
type of theorem it is.
-/
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
      withConfig (fun cfg => { cfg with zeta := false}) <| getFunctionData? f defaultUnfoldPred
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
        keys    := keys
        priority  := prio
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


/-- Register theorem `declName` with `fun_prop`. -/
/-
**Mathlib.Meta.FunProp.addTheorem** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunPro
p`。
形式化陈述：addTheorem (declName : Name) (attrKind : AttributeKind
参数：declName : Name。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register theorem `declName` with `fun_prop`.
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

