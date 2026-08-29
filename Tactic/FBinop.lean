/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Elab.App
public meta import Lean.Elab.BuiltinNotation
public import Mathlib.Tactic.ToExpr

/-! # Elaborator for functorial binary operators

`fbinop% f x y` elaborates `f x y` for `x : S α` and `y : S' β`, taking into account
any coercions that the "functors" `S` and `S'` possess.

While `binop%` tries to solve for a single minimal type, `fbinop%` tries to solve
the parameterized problem of solving for a single minimal "functor."

The code is drawn from the Lean 4 core `binop%` elaborator. Two simplifications made were
1. It is assumed that every `f` has a "homogeneous" instance
   (think `Set.prod : Set α → Set β → Set (α × β)`).
2. It is assumed that there are no "non-homogeneous" default instances.

It also makes the assumption that the binop wants to be as homogeneous as possible.
For example, when the type of an argument is unknown it will try to unify the argument's type
with `S _`, which can help certain elaboration problems proceed (like for `{a,b,c}` notation).

The main goal is to support generic set product notation and have it elaborate in a convenient way.
-/

public meta section

namespace FBinopElab
open Lean Elab Term Meta

initialize registerTraceClass `Elab.fbinop

/-- `fbinop% f x y` elaborates `f x y` for `x : S α` and `y : S' β`, taking into account
any coercions that the "functors" `S` and `S'` possess. -/
syntax:max (name := prodSyntax) "fbinop% " ident ppSpace term:max ppSpace term:max : term

/--
Inductive type `Tree` / 归纳类型 `Tree`

English:
inductive Tree
  parameters: where
  constructors (3):
    - term: (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
    - binop: (ref : Syntax) (f : Expr) (lhs rhs : Tree)
    - macroExpansion: (macroName : Name) (stx stx' : Syntax) (nested : Tree)

中文:
归纳类型 树
  参数: where
  构造子 (3 个):
    - term: (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
    - binop: (ref : Syntax) (f : Expr) (lhs rhs : 树)
    - macroExpansion: (macroName : Name) (stx stx' : Syntax) (nested : 树)
-/
private inductive Tree where
  /-- Leaf of the tree. Stores the generated `InfoTree` from elaborating `val`. -/
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  /-- An `fbinop%` node.
  `ref` is the original syntax that expanded into `binop%`.
  `f` is the constant for the binary operator -/
  | binop (ref : Syntax) (f : Expr) (lhs rhs : Tree)
  /-- Store macro expansion information to make sure that "go to definition" behaves
  similarly to notation defined without using `fbinop%`. -/
  | macroExpansion (macroName : Name) (stx stx' : Syntax) (nested : Tree)

/--
Definition of `toTree` / `toTree` 的定义

English:
definition toTree
  signature: (s : Syntax)
  body: do
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result

中文:
定义 toTree
  签名: (s : Syntax)
  定义体: do
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result
-/
private partial def toTree (s : Syntax) : TermElabM Tree := do
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result
where
  go (s : Syntax) : TermElabM Tree := do
    match s with
    | `(fbinop% $f $lhs $rhs) => processBinOp s f lhs rhs
    | `(($h:hygieneInfo $e)) =>
      if hasCDot e h.getHygieneInfo then
        processLeaf s
      else
        go e
    | _ =>
      withRef s do
match ← liftMacroM expandMacroImpl? (← getEnv) s with
        | some (macroName, s?) =>
let s' ← liftMacroM liftExcept s?
          withPushMacroExpansionStack s s' do
            return .macroExpansion macroName s s' (← go s')
        | none => processLeaf s

  processBinOp (ref : Syntax) (f lhs rhs : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return .binop ref f (← go lhs) (← go rhs)

  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e

/--
Definition of `SRec` / `SRec` 的定义

English:
structure SRec
  parameters: where
  axioms and operations (2):
    - name : Name
    - args : Array Expr

中文:
结构 SRec
  参数: where
  公理与运算 (2 个):
    - name : Name
    - args : 数组 Expr

Depends on / 依赖: Meta.isType, args.back, args.pop, args.size, e.getAppArgs, e.getAppFn, e.letBody, e.letValue, extractS, getAppArgs, getAppFn, getFunInfoNArgs, info.back, info.pop, instantiate1, isInstImplicit, isType, letBody, letValue, paramInfo
-/
structure SRec where
  name : Name
  args : Array Expr
  deriving Inhabited, ToExpr

/--
Definition of `extractS` / `extractS` 的定义

English:
definition extractS
  signature: (e : Expr)
  body: match e with
  | .letE .. => extractS (e.letBody!.instantiate1 e.letValue!)
  | .mdata _ b => extractS b
  | .app .. => do
    let f := e.getAppFn
    let .const n _ := f | return none
    let mut args := e.getAppArgs
    let mut info := (← getFunInfoNArgs f args.size).paramInfo
    for _ in [0 : ar

中文:
定义 extractS
  签名: (e : Expr)
  定义体: match e with
  | .letE .. => extractS (e.letBody!.instantiate1 e.letValue!)
  | .mdata _ b => extractS b
  | .app .. => do
    let f := e.getAppFn
    let .const n _ := f | return none
    let mut args := e.getAppArgs
    let mut info := (← getFunInfoNArgs f args.size).paramInfo
    for _ in [0 : ar
-/
private partial def extractS (e : Expr) : TermElabM (Option (SRec × Expr)) :=
  match e with
  | .letE .. => extractS (e.letBody!.instantiate1 e.letValue!)
  | .mdata _ b => extractS b
  | .app .. => do
    let f := e.getAppFn
    let .const n _ := f | return none
    let mut args := e.getAppArgs
    let mut info := (← getFunInfoNArgs f args.size).paramInfo
    for _ in [0 : args.size - 1] do
      if info.back!.isInstImplicit then
        args := args.pop
        info := info.pop
      else
        break
    let x := args.back!
    unless ← Meta.isType x do return none
    return some ({name := n, args := args.pop}, x)
  | _ => return none

/--
Definition of `applyS` / `applyS` 的定义

English:
definition applyS
  signature: (S : SRec) (x : Expr)
  body: try
    let f ← mkConstWithFreshMVarLevels S.name
    let v ← elabAppArgs f #[] ((S.args.push x).map .expr)
      (expectedType? := none) (explicit := true) (ellipsis := false)
    -- Now elaborate any remaining instance arguments
    elabAppArgs v #[] #[] (expectedType? := none) (explicit := false)

中文:
定义 applyS
  签名: (S : SRec) (x : Expr)
  定义体: try
    let f ← mkConstWithFreshMVarLevels S.name
    let v ← elabAppArgs f #[] ((S.args.push x).map .expr)
      (expectedType? := none) (explicit := true) (ellipsis := false)
    -- Now elaborate any remaining instance arguments
    elabAppArgs v #[] #[] (expectedType? := none) (explicit := false)
-/
private def applyS (S : SRec) (x : Expr) : TermElabM (Option Expr) :=
  try
    let f ← mkConstWithFreshMVarLevels S.name
    let v ← elabAppArgs f #[] ((S.args.push x).map .expr)
      (expectedType? := none) (explicit := true) (ellipsis := false)
    -- Now elaborate any remaining instance arguments
    elabAppArgs v #[] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
  catch _ =>
    return none

/--
Definition of `hasCoeS` / `hasCoeS` 的定义

English:
definition hasCoeS
  signature: (fromS toS : SRec) (x : Expr)
  body: do
  let some fromType ← applyS fromS x | return false
  let some toType ← applyS toS x | return false
  trace[Elab.fbinop] m!"fromType = {fromType}, toType = {toType}"
  withLocalDeclD `v fromType fun v => do
    match ← coerceSimple? v toType with
    | .some _ => return true
    | .none => return

中文:
定义 hasCoeS
  签名: (fromS toS : SRec) (x : Expr)
  定义体: do
  let some fromType ← applyS fromS x | return false
  let some toType ← applyS toS x | return false
  trace[Elab.fbinop] m!"fromType = {fromType}, toType = {toType}"
  withLocalDeclD `v fromType fun v => do
    match ← coerceSimple? v toType with
    | .some _ => return true
    | .none => return
-/
private def hasCoeS (fromS toS : SRec) (x : Expr) : TermElabM Bool := do
  let some fromType ← applyS fromS x | return false
  let some toType ← applyS toS x | return false
  trace[Elab.fbinop] m!"fromType = {fromType}, toType = {toType}"
  withLocalDeclD `v fromType fun v => do
    match ← coerceSimple? v toType with
    | .some _ => return true
    | .none => return false
    | .undef => return false -- TODO: should we do something smarter here?

/--
Definition of `AnalyzeResult` / `AnalyzeResult` 的定义

English:
structure AnalyzeResult
  parameters: where
  axioms and operations (2):
    - maxS? : Option SRec  [default: none]
    - hasUncomparable : Bool  [default: false]

中文:
结构 AnalyzeResult
  参数: where
  公理与运算 (2 个):
    - maxS? : 选项类型 SRec  [默认: none]
    - hasUncomparable : 布尔值  [默认: false]

Depends on / 依赖: LinearOrder, LinearOrder.supConvergenceClass, TopologicalSpace, supConvergenceClass
-/
private structure AnalyzeResult where
  maxS? : Option SRec := none
  /-- `true` if there are two types `α` and `β` where we don't have coercions in any direction. -/
  hasUncomparable : Bool := false

/--
Definition of `analyze` / `analyze` 的定义

English:
definition analyze
  signature: (t : Tree) (expectedType? : Option Expr)
  body: do
  let maxS? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if let some (S, _) ← extractS expectedType then
        pure S
      else
        pure none
  (go t *> get).run' { maxS? }

中文:
定义 analyze
  签名: (t : 树) (expectedType? : 选项类型 Expr)
  定义体: do
  let maxS? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if let some (S, _) ← extractS expectedType then
        pure S
      else
        pure none
  (go t *> get).run' { maxS? }

Depends on / 依赖: LinearOrder, LinearOrder.infConvergenceClass, TopologicalSpace, infConvergenceClass
-/
private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let maxS? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if let some (S, _) ← extractS expectedType then
        pure S
      else
        pure none
  (go t *> get).run' { maxS? }
where
  go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
    unless (← get).hasUncomparable do
      match t with
      | .macroExpansion _ _ _ nested => go nested
      | .binop _ _ lhs rhs => go lhs; go rhs
      | .term _ _ val =>
        let type ← instantiateMVars (← inferType val)
        let some (S, x) ← extractS type
          | return -- Rather than marking as incomparable, let's hope there's a coercion!
        match (← get).maxS? with
        | none => modify fun s => { s with maxS? := S }
        | some maxS =>
          let some maxSx ← applyS maxS x | return -- Same here.
unless ← withNewMCtxDepth isDefEqGuarded maxSx type do
            if ← hasCoeS S maxS x then
              return ()
            else if ← hasCoeS maxS S x then
              modify fun s => { s with maxS? := S }
            else
              trace[Elab.fbinop] "uncomparable types: {maxSx}, {type}"
              modify fun s => { s with hasUncomparable := true }

/--
Definition of `mkBinOp` / `mkBinOp` 的定义

English:
definition mkBinOp
  signature: (f : Expr) (lhs rhs : Expr)
  body: do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none)
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

中文:
定义 mkBinOp
  签名: (f : Expr) (lhs rhs : Expr)
  定义体: do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none)
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
-/
private def mkBinOp (f : Expr) (lhs rhs : Expr) : TermElabM Expr := do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none)
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/--
Definition of `toExprCore` / `toExprCore` 的定义

English:
definition toExprCore
  signature: (t : Tree)
  body: do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref f lhs rhs =>
withRef ref withTermInfoContext' .anonymous ref do
      let lhs ← toExprCore lhs
      let mut rhs ← toExprCore rhs
      mkBinOp f lhs rhs
  | .macroEx

中文:
定义 toExprCore
  签名: (t : 树)
  定义体: do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref f lhs rhs =>
withRef ref withTermInfoContext' .anonymous ref do
      let lhs ← toExprCore lhs
      let mut rhs ← toExprCore rhs
      mkBinOp f lhs rhs
  | .macroEx
-/
private def toExprCore (t : Tree) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref f lhs rhs =>
withRef ref withTermInfoContext' .anonymous ref do
      let lhs ← toExprCore lhs
      let mut rhs ← toExprCore rhs
      mkBinOp f lhs rhs
  | .macroExpansion macroName stx stx' nested =>
withRef stx withTermInfoContext' macroName stx do
      withMacroExpansion stx stx' do
        toExprCore nested

/--
Definition of `applyCoe` / `applyCoe` 的定义

English:
definition applyCoe
  signature: (t : Tree) (maxS : SRec)
  body: do
  go t none

中文:
定义 applyCoe
  签名: (t : 树) (maxS : SRec)
  定义体: do
  go t none
-/
private def applyCoe (t : Tree) (maxS : SRec) : TermElabM Tree := do
  go t none
where
  go (t : Tree) (f? : Option Expr) : TermElabM Tree := do
    match t with
    | .binop ref f lhs rhs =>
      let lhs' ← go lhs f
      let rhs' ← go rhs f
      return .binop ref f lhs' rhs'
    | .term ref trees e =>
      let type ← instantiateMVars (← inferType e)
      trace[Elab.fbinop] "visiting {e} : {type}"
      let some (_, x) ← extractS type
        | -- We want our operators to be "homogeneous" so do a defeq check as an elaboration hint
          let x' ← mkFreshExprMVar none
          let some maxType ← applyS maxS x' | trace[Elab.fbinop] "mvar apply failed"; return t
          trace[Elab.fbinop] "defeq hint {maxType} =?= {type}"
          _ ← isDefEqGuarded maxType type
          return t
      let some maxType ← applyS maxS x
        | trace[Elab.fbinop] "applying {Lean.toExpr maxS} {x} failed"
          return t
      trace[Elab.fbinop] "{type} =?= {maxType}"
      if ← isDefEqGuarded maxType type then
        return t
      else
        trace[Elab.fbinop] "added coercion: {e} : {type} => {maxType}"
withRef ref return .term ref trees (← mkCoe maxType e)
    | .macroExpansion macroName stx stx' nested =>
withRef stx withPushMacroExpansionStack stx stx' do
        return .macroExpansion macroName stx stx' (← go nested f?)

/--
Definition of `toExpr` / `toExpr` 的定义

English:
definition toExpr
  signature: (tree : Tree) (expectedType? : Option Expr)
  body: do
  let r ← analyze tree expectedType?
  trace[Elab.fbinop] "hasUncomparable: {r.hasUncomparable}, maxType: {Lean.toExpr r.maxS?}"
  if r.hasUncomparable || r.maxS?.isNone then
    let result ← toExprCore tree
    ensureHasType expectedType? result
  else
    let result ← toExprCore (← applyCoe tre

中文:
定义 toExpr
  签名: (tree : 树) (expectedType? : 选项类型 Expr)
  定义体: do
  let r ← analyze tree expectedType?
  trace[Elab.fbinop] "hasUncomparable: {r.hasUncomparable}, maxType: {Lean.toExpr r.maxS?}"
  if r.hasUncomparable || r.maxS?.isNone then
    let result ← toExprCore tree
    ensureHasType expectedType? result
  else
    let result ← toExprCore (← applyCoe tre
-/
private def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
  let r ← analyze tree expectedType?
  trace[Elab.fbinop] "hasUncomparable: {r.hasUncomparable}, maxType: {Lean.toExpr r.maxS?}"
  if r.hasUncomparable || r.maxS?.isNone then
    let result ← toExprCore tree
    ensureHasType expectedType? result
  else
    let result ← toExprCore (← applyCoe tree r.maxS?.get!)
    trace[Elab.fbinop] "result: {result}"
    ensureHasType expectedType? result

@[term_elab prodSyntax]
/--
Definition of `elabBinOp` / `elabBinOp` 的定义

English:
definition elabBinOp
  signature: : TermElab
  body: fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

中文:
定义 elabBinOp
  签名: : TermElab
  定义体: fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

Depends on / 依赖: expectedType
-/
def elabBinOp : TermElab := fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

end FBinopElab
