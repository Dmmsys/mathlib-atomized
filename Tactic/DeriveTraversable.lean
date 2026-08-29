/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public meta import Lean.Elab.Match
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.PreDefinition.Main
public import Mathlib.Control.Traversable.Lemmas
public meta import Mathlib.Tactic.ToAdditive

/-!
# Deriving handler for `Traversable` instances

This module gives deriving handlers for `Functor`, `LawfulFunctor`, `Traversable`, and
`LawfulTraversable`. These deriving handlers automatically derive their dependencies, for
example `deriving LawfulTraversable` all by itself gives all four.
-/

public meta section

namespace Mathlib.Deriving.Traversable

open Lean Meta Elab Term Command Tactic Match List Monad Functor

/--
Definition of `nestedMap` / `nestedMap` 的定义

English:
definition nestedMap
  signature: (f v t : Expr)
  body: do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Functor #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedMap f v t.appArg!
    mkAppOptM ``Functor.map #[t.appFn!, inst, none, none, f']
  else throwError "type {t} is not a functor with respect to variable {v}"

中文:
定义 nestedMap
  签名: (f v t : Expr)
  定义体: do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Functor #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedMap f v t.appArg!
    mkAppOptM ``Functor.map #[t.appFn!, inst, none, none, f']
  else throwError "type {t} is not a functor with respect to variable {v}"
-/
partial def nestedMap (f v t : Expr) : TermElabM Expr := do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Functor #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedMap f v t.appArg!
    mkAppOptM ``Functor.map #[t.appFn!, inst, none, none, f']
  else throwError "type {t} is not a functor with respect to variable {v}"

/--
Definition of `mapField` / `mapField` 的定义

English:
definition mapField
  signature: (n : Name) (cl f α β e : Expr)
  body: do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if α.eqv e then
    return β
  else if α.occurs t then
    let f' ← nestedMap f α t
    return f'.app e
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
    mkAppM ``Comp.mk #[e]
  else
    return e

中文:
定义 mapField
  签名: (n : Name) (cl f α β e : Expr)
  定义体: do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if α.eqv e then
    return β
  else if α.occurs t then
    let f' ← nestedMap f α t
    return f'.app e
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
    mkAppM ``Comp.mk #[e]
  else
    return e
-/
def mapField (n : Name) (cl f α β e : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if α.eqv e then
    return β
  else if α.occurs t then
    let f' ← nestedMap f α t
    return f'.app e
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
    mkAppM ``Comp.mk #[e]
  else
    return e

/--
Definition of `getAuxDefOfDeclName` / `getAuxDefOfDeclName` 的定义

English:
definition getAuxDefOfDeclName
  signature: : TermElabM FVarId
  body: do
  let some declName ← getDeclName? | throwError "no 'declName?'"
  let auxDeclMap := (← getLCtx).auxDeclToFullName
  let fvars := auxDeclMap.foldl (init := []) fun fvars fvar fullName =>
    if fullName = declName then fvars.concat fvar else fvars
  match fvars with
  | [] => throwError "no auxiliary local declaration corresponding to the current declaration"
  | [fvar] => return fvar
  | _ => throwError "multiple local declarations corresponding to the current declaration"

中文:
定义 getAuxDefOfDeclName
  签名: : TermElabM FVarId
  定义体: do
  let some declName ← getDeclName? | throwError "no 'declName?'"
  let auxDeclMap := (← getLCtx).auxDeclToFullName
  let fvars := auxDeclMap.foldl (init := []) fun fvars fvar fullName =>
    if fullName = declName then fvars.concat fvar else fvars
  match fvars with
  | [] => throwError "no auxiliary local declaration corresponding to the current declaration"
  | [fvar] => return fvar
  | _ => throwError "multiple local declarations corresponding to the current declaration"
-/
def getAuxDefOfDeclName : TermElabM FVarId := do
  let some declName ← getDeclName? | throwError "no 'declName?'"
  let auxDeclMap := (← getLCtx).auxDeclToFullName
  let fvars := auxDeclMap.foldl (init := []) fun fvars fvar fullName =>
    if fullName = declName then fvars.concat fvar else fvars
  match fvars with
  | [] => throwError "no auxiliary local declaration corresponding to the current declaration"
  | [fvar] => return fvar
  | _ => throwError "multiple local declarations corresponding to the current declaration"

/--
Definition of `mapConstructor` / `mapConstructor` 的定义

English:
definition mapConstructor
  signature: (c n : Name) (f α β : Expr) (args₀ : List Expr)
  body: do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN (.fvar ad) #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign

中文:
定义 mapConstructor
  签名: (c n : Name) (f α β : Expr) (args₀ : 列表 Expr)
  定义体: do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN (.fvar ad) #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign
-/
def mapConstructor (c n : Name) (f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN (.fvar ad) #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign

/--
Definition of `mkCasesOnMatch` / `mkCasesOnMatch` 的定义

English:
definition mkCasesOnMatch
  signature: (type : Name) (levels : List Level) (params : List Expr) (motive : Expr)
  body: do
  let matcherName ← getDeclName? >>= (fun n? => Lean.mkAuxDeclName (.mkStr (n?.getD type) "match"))
  let matchType ← generalizeTelescope (indices.concat val).toArray fun iargs =>
    mkForallFVars iargs (motive.beta iargs)
  let iinfo ← getConstInfoInduct type
  let lhss ← iinfo.ctors.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let catype ←
      instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams levels) params.toArray
    forallBoundedTelescope catype cinfo.numFields fun cargs _ => do
      let fvarDecls ← cargs.toList.mapM fun carg => getFVarLocalDecl carg
      let fieldPats := cargs.toList.map fun carg => Pattern.var carg.fvarId!
      let patterns := [Pattern.ctor cinfo.name levels params fieldPats]
      return { ref := .missing
               fvarDecls
               patterns }
  let mres ← Term.mkMatcher { matcherName
                              matchType
                              discrInfos := .replicate (indices.length + 1) {}
                              lhss }
  mres.addMatcher
  let rhss ← lhss.mapM fun altLHS => do
    let [.ctor ctor _ _ cpats] := altLHS.patterns | unreachable!
    withExistingLocalDecls altLHS.fvarDecls do
      let fields := altLHS.fvarDecls.map LocalDecl.fvarId
      let rhsBody ← rhss ctor fields
      if cpats.isEmpty then
        mkFunUnit rhsBody
      else
        mkLambdaFVars (fields.map Expr.fvar).toArray rhsBody
  return mkAppN mres.matcher (motive :: indices ++ [val] ++ rhss).toArray

中文:
定义 mkCasesOnMatch
  签名: (type : Name) (levels : 列表 Level) (params : 列表 Expr) (motive : Expr)
  定义体: do
  let matcherName ← getDeclName? >>= (fun n? => Lean.mkAuxDeclName (.mkStr (n?.getD type) "match"))
  let matchType ← generalizeTelescope (indices.concat val).toArray fun iargs =>
    mkForallFVars iargs (motive.beta iargs)
  let iinfo ← getConstInfoInduct type
  let lhss ← iinfo.ctors.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let catype ←
      instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams levels) params.toArray
    forallBoundedTelescope catype cinfo.numFields fun cargs _ => do
      let fvarDecls ← cargs.toList.mapM fun carg => getFVarLocalDecl carg
      let fieldPats := cargs.toList.map fun carg => Pattern.var carg.fvarId!
      let patterns := [Pattern.ctor cinfo.name levels params fieldPats]
      return { ref := .missing
               fvarDecls
               patterns }
  let mres ← Term.mkMatcher { matcherName
                              matchType
                              discrInfos := .replicate (indices.length + 1) {}
                              lhss }
  mres.addMatcher
  let rhss ← lhss.mapM fun altLHS => do
    let [.ctor ctor _ _ cpats] := altLHS.patterns | unreachable!
    withExistingLocalDecls altLHS.fvarDecls do
      let fields := altLHS.fvarDecls.map LocalDecl.fvarId
      let rhsBody ← rhss ctor fields
      if cpats.isEmpty then
        mkFunUnit rhsBody
      else
        mkLambdaFVars (fields.map Expr.fvar).toArray rhsBody
  return mkAppN mres.matcher (motive :: indices ++ [val] ++ rhss).toArray
-/
def mkCasesOnMatch (type : Name) (levels : List Level) (params : List Expr) (motive : Expr)
    (indices : List Expr) (val : Expr)
    (rhss : (ctor : Name) -> (fields : List FVarId) -> TermElabM Expr) : TermElabM Expr := do
  let matcherName ← getDeclName? >>= (fun n? => Lean.mkAuxDeclName (.mkStr (n?.getD type) "match"))
  let matchType ← generalizeTelescope (indices.concat val).toArray fun iargs =>
    mkForallFVars iargs (motive.beta iargs)
  let iinfo ← getConstInfoInduct type
  let lhss ← iinfo.ctors.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let catype ←
      instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams levels) params.toArray
    forallBoundedTelescope catype cinfo.numFields fun cargs _ => do
      let fvarDecls ← cargs.toList.mapM fun carg => getFVarLocalDecl carg
      let fieldPats := cargs.toList.map fun carg => Pattern.var carg.fvarId!
      let patterns := [Pattern.ctor cinfo.name levels params fieldPats]
      return { ref := .missing
               fvarDecls
               patterns }
  let mres ← Term.mkMatcher { matcherName
                              matchType
                              discrInfos := .replicate (indices.length + 1) {}
                              lhss }
  mres.addMatcher
  let rhss ← lhss.mapM fun altLHS => do
    let [.ctor ctor _ _ cpats] := altLHS.patterns | unreachable!
    withExistingLocalDecls altLHS.fvarDecls do
      let fields := altLHS.fvarDecls.map LocalDecl.fvarId
      let rhsBody ← rhss ctor fields
      if cpats.isEmpty then
        mkFunUnit rhsBody
      else
        mkLambdaFVars (fields.map Expr.fvar).toArray rhsBody
  return mkAppN mres.matcher (motive :: indices ++ [val] ++ rhss).toArray

/--
Definition of `getFVarIdsNotImplementationDetails` / `getFVarIdsNotImplementationDetails` 的定义

English:
definition getFVarIdsNotImplementationDetails
  signature: : MetaM (List FVarId)
  body: do
  let lctx ← getLCtx
  return lctx.decls.foldl (init := []) fun r decl? => match decl? with
    | some decl => if decl.isImplementationDetail then r else r.concat decl.fvarId
    | none => r

中文:
定义 getFVarIdsNotImplementationDetails
  签名: : MetaM (列表 FVarId)
  定义体: do
  let lctx ← getLCtx
  return lctx.decls.foldl (init := []) fun r decl? => match decl? with
    | some decl => if decl.isImplementationDetail then r else r.concat decl.fvarId
    | none => r
-/
def getFVarIdsNotImplementationDetails : MetaM (List FVarId) := do
  let lctx ← getLCtx
  return lctx.decls.foldl (init := []) fun r decl? => match decl? with
    | some decl => if decl.isImplementationDetail then r else r.concat decl.fvarId
    | none => r

/--
Definition of `getFVarsNotImplementationDetails` / `getFVarsNotImplementationDetails` 的定义

English:
definition getFVarsNotImplementationDetails
  signature: : MetaM (List Expr)
  body: List.map Expr.fvar < > getFVarIdsNotImplementationDetails

中文:
定义 getFVarsNotImplementationDetails
  签名: : MetaM (列表 Expr)
  定义体: List.map Expr.fvar < > getFVarIdsNotImplementationDetails

Depends on / 依赖: Expr.fvar, List.map, getFVarIdsNotImplementationDetails
-/
def getFVarsNotImplementationDetails : MetaM (List Expr) :=
List.map Expr.fvar < > getFVarIdsNotImplementationDetails

/--
Definition of `mkMap` / `mkMap` 的定义

English:
definition mkMap
  signature: (type : Name) (m : MVarId)
  body: do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let (#[α, β, f, x], m) ← m.introN 4 [`α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          mapConstructor
            ctor type (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

中文:
定义 mkMap
  签名: (type : Name) (m : MVarId)
  定义体: do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let (#[α, β, f, x], m) ← m.introN 4 [`α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          mapConstructor
            ctor type (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e
-/
def mkMap (type : Name) (m : MVarId) : TermElabM Unit := do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let (#[α, β, f, x], m) ← m.introN 4 [`α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          mapConstructor
            ctor type (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

/--
Definition of `deriveFunctor` / `deriveFunctor` 的定义

English:
definition deriveFunctor
  signature: (m : MVarId)
  body: do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "map"
withDeclName n' withAuxDecl (.mkSimple "map") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `specialize
                    stx := ← `(attr| specialize) }] }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

中文:
定义 deriveFunctor
  签名: (m : MVarId)
  定义体: do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "map"
withDeclName n' withAuxDecl (.mkSimple "map") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `specialize
                    stx := ← `(attr| specialize) }] }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)
-/
def deriveFunctor (m : MVarId) : TermElabM Unit := do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "map"
withDeclName n' withAuxDecl (.mkSimple "map") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `specialize
                    stx := ← `(attr| specialize) }] }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

/--
Definition of `mkInstanceNameForTypeExpr` / `mkInstanceNameForTypeExpr` 的定义

English:
definition mkInstanceNameForTypeExpr
  signature: (type : Expr)
  body: do
  let result ← do
    let ref ← IO.mkRef ""
    Meta.forEachExpr type fun e => do
      if e.isForall then ref.modify (· ++ "ForAll")
      else if e.isProp then ref.modify (· ++ "Prop")
      else if e.isType then ref.modify (· ++ "Type")
      else if e.isSort then ref.modify (· ++ "Sort")
      else if e.isConst then
        match e.constName!.eraseMacroScopes with
        | .str _ str =>
            if str.front.isLower then
              ref.modify (· ++ str.capitalize)
            else
              ref.modify (· ++ str)
        | _ => pure ()
    ref.get
liftMacroM mkUnusedBaseName Name.mkSimple ("inst" ++ result)

中文:
定义 mkInstanceNameForTypeExpr
  签名: (type : Expr)
  定义体: do
  let result ← do
    let ref ← IO.mkRef ""
    Meta.forEachExpr type fun e => do
      if e.isForall then ref.modify (· ++ "ForAll")
      else if e.isProp then ref.modify (· ++ "Prop")
      else if e.isType then ref.modify (· ++ "Type")
      else if e.isSort then ref.modify (· ++ "Sort")
      else if e.isConst then
        match e.constName!.eraseMacroScopes with
        | .str _ str =>
            if str.front.isLower then
              ref.modify (· ++ str.capitalize)
            else
              ref.modify (· ++ str)
        | _ => pure ()
    ref.get
liftMacroM mkUnusedBaseName Name.mkSimple ("inst" ++ result)
-/
def mkInstanceNameForTypeExpr (type : Expr) : TermElabM Name := do
  let result ← do
    let ref ← IO.mkRef ""
    Meta.forEachExpr type fun e => do
      if e.isForall then ref.modify (· ++ "ForAll")
      else if e.isProp then ref.modify (· ++ "Prop")
      else if e.isType then ref.modify (· ++ "Type")
      else if e.isSort then ref.modify (· ++ "Sort")
      else if e.isConst then
        match e.constName!.eraseMacroScopes with
        | .str _ str =>
            if str.front.isLower then
              ref.modify (· ++ str.capitalize)
            else
              ref.modify (· ++ str)
        | _ => pure ()
    ref.get
liftMacroM mkUnusedBaseName Name.mkSimple ("inst" ++ result)

/--
Definition of `mkOneInstance` / `mkOneInstance` 的定义

English:
definition mkOneInstance
  signature: (n cls : Name) (tac : MVarId -> TermElabM Unit)
  body: do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let docCtx := (← getLCtx, ← getLocalInstances)
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  let tgt ← forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    params.zipIdx.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
(discard <| liftM (synthInstance tgt)) > do
    let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
    let (_, m') ← m.intros
withLevelNames decl.levelParams m'.withContext tac m'
    let val ← instantiateMVars (mkMVar m)
    let isUnsafe := decl.isUnsafe || clsDecl.isUnsafe
    let instN ← m'.withContext do
      let type ← m'.getType >>= instantiateMVars
      mkInstanceNameForTypeExpr type
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := decl.levelParams
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `instance_reducible
                    stx := ← `(attr| instance_reducible) },
                  { kind := .global
                    name := `instance
                    stx := ← `(attr| instance) }] }
          declName := instN
          type := tgt
          value := val
          termination := .none }] {}

中文:
定义 mkOneInstance
  签名: (n cls : Name) (tac : MVarId -> TermElabM 单元)
  定义体: do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let docCtx := (← getLCtx, ← getLocalInstances)
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  let tgt ← forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    params.zipIdx.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
(discard <| liftM (synthInstance tgt)) > do
    let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
    let (_, m') ← m.intros
withLevelNames decl.levelParams m'.withContext tac m'
    let val ← instantiateMVars (mkMVar m)
    let isUnsafe := decl.isUnsafe || clsDecl.isUnsafe
    let instN ← m'.withContext do
      let type ← m'.getType >>= instantiateMVars
      mkInstanceNameForTypeExpr type
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := decl.levelParams
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `instance_reducible
                    stx := ← `(attr| instance_reducible) },
                  { kind := .global
                    name := `instance
                    stx := ← `(attr| instance) }] }
          declName := instN
          type := tgt
          value := val
          termination := .none }] {}

Depends on / 依赖: T0Space, TermElabM, mkAppM, t0Space
-/
def mkOneInstance (n cls : Name) (tac : MVarId -> TermElabM Unit)
    (mkInst : Name -> Expr -> TermElabM Expr := fun n arg => mkAppM n #[arg]) : TermElabM Unit := do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let docCtx := (← getLCtx, ← getLocalInstances)
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  let tgt ← forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    params.zipIdx.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
(discard <| liftM (synthInstance tgt)) > do
    let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
    let (_, m') ← m.intros
withLevelNames decl.levelParams m'.withContext tac m'
    let val ← instantiateMVars (mkMVar m)
    let isUnsafe := decl.isUnsafe || clsDecl.isUnsafe
    let instN ← m'.withContext do
      let type ← m'.getType >>= instantiateMVars
      mkInstanceNameForTypeExpr type
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := decl.levelParams
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `instance_reducible
                    stx := ← `(attr| instance_reducible) },
                  { kind := .global
                    name := `instance
                    stx := ← `(attr| instance) }] }
          declName := instN
          type := tgt
          value := val
          termination := .none }] {}

/--
Definition of `higherOrderDeriveHandler` / `higherOrderDeriveHandler` 的定义

English:
definition higherOrderDeriveHandler
  signature: (cls : Name) (tac : MVarId -> TermElabM Unit)
  body: fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  let ok ← deps.mapM fun f => f a
  unless ok.and do return false
liftTermElabM mkOneInstance n cls tac mkInst
  return true

中文:
定义 higherOrderDeriveHandler
  签名: (cls : Name) (tac : MVarId -> TermElabM 单元)
  定义体: fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  let ok ← deps.mapM fun f => f a
  unless ok.and do return false
liftTermElabM mkOneInstance n cls tac mkInst
  return true
-/
def higherOrderDeriveHandler (cls : Name) (tac : MVarId -> TermElabM Unit)
    (deps : List DerivingHandler := [])
    (mkInst : Name -> Expr -> TermElabM Expr := fun n arg => mkAppM n #[arg]) :
    DerivingHandler := fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  let ok ← deps.mapM fun f => f a
  unless ok.and do return false
liftTermElabM mkOneInstance n cls tac mkInst
  return true

/--
Definition of `functorDeriveHandler` / `functorDeriveHandler` 的定义

English:
definition functorDeriveHandler
  signature: : DerivingHandler
  body: higherOrderDeriveHandler ``Functor deriveFunctor []

中文:
定义 functorDeriveHandler
  签名: : DerivingHandler
  定义体: higherOrderDeriveHandler ``Functor deriveFunctor []

Depends on / 依赖: Functor, deriveFunctor, higherOrderDeriveHandler
-/
def functorDeriveHandler : DerivingHandler :=
  higherOrderDeriveHandler ``Functor deriveFunctor []

initialize registerDerivingHandler ``Functor functorDeriveHandler

/--
Definition of `deriveLawfulFunctor` / `deriveLawfulFunctor` 的定义

English:
definition deriveLawfulFunctor
  signature: (m : MVarId)
  body: do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext (simpTheorems := #[s])
  let .app (.app (.const ``LawfulFunctor _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mcn, mim, mcm] ← m.applyConst ``LawfulFunctor.mk | failure
  let (_, mcn) ← mcn.introN 2
  mcn.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun { mvarId := mim, .. } =>
    mim.withContext do
      if let (some (_, mim), _) ←
          simpGoal mim (← rules [(``Functor.map_id, false)] [.mkStr n "map"] true) then
        mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun { mvarId := mcm, .. } =>
    mcm.withContext do
      if let (some (_, mcm), _) ←
          simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [.mkStr n "map"] true) then
        mcm.refl

中文:
定义 deriveLawfulFunctor
  签名: (m : MVarId)
  定义体: do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext (simpTheorems := #[s])
  let .app (.app (.const ``LawfulFunctor _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mcn, mim, mcm] ← m.applyConst ``LawfulFunctor.mk | failure
  let (_, mcn) ← mcn.introN 2
  mcn.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun { mvarId := mim, .. } =>
    mim.withContext do
      if let (some (_, mim), _) ←
          simpGoal mim (← rules [(``Functor.map_id, false)] [.mkStr n "map"] true) then
        mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun { mvarId := mcm, .. } =>
    mcm.withContext do
      if let (some (_, mcm), _) ←
          simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [.mkStr n "map"] true) then
        mcm.refl
-/
def deriveLawfulFunctor (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext (simpTheorems := #[s])
  let .app (.app (.const ``LawfulFunctor _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mcn, mim, mcm] ← m.applyConst ``LawfulFunctor.mk | failure
  let (_, mcn) ← mcn.introN 2
  mcn.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun { mvarId := mim, .. } =>
    mim.withContext do
      if let (some (_, mim), _) ←
          simpGoal mim (← rules [(``Functor.map_id, false)] [.mkStr n "map"] true) then
        mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun { mvarId := mcm, .. } =>
    mcm.withContext do
      if let (some (_, mcm), _) ←
          simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [.mkStr n "map"] true) then
        mcm.refl

/--
Definition of `lawfulFunctorDeriveHandler` / `lawfulFunctorDeriveHandler` 的定义

English:
definition lawfulFunctorDeriveHandler
  signature: : DerivingHandler
  body: higherOrderDeriveHandler ``LawfulFunctor deriveLawfulFunctor [functorDeriveHandler]
    (fun n arg => mkAppOptM n #[arg, none])

中文:
定义 lawfulFunctorDeriveHandler
  签名: : DerivingHandler
  定义体: higherOrderDeriveHandler ``LawfulFunctor deriveLawfulFunctor [functorDeriveHandler]
    (fun n arg => mkAppOptM n #[arg, none])

Depends on / 依赖: LawfulFunctor, deriveLawfulFunctor, functorDeriveHandler, higherOrderDeriveHandler, mkAppOptM
-/
def lawfulFunctorDeriveHandler : DerivingHandler :=
  higherOrderDeriveHandler ``LawfulFunctor deriveLawfulFunctor [functorDeriveHandler]
    (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulFunctor lawfulFunctorDeriveHandler

/--
Definition of `nestedTraverse` / `nestedTraverse` 的定义

English:
definition nestedTraverse
  signature: (f v t : Expr)
  body: do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Traversable #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedTraverse f v t.appArg!
    mkAppOptM ``Traversable.traverse #[t.appFn!, inst, none, none, none, none, f']
  else throwError "type {t} is not traversable with respect to variable {v}"

中文:
定义 nestedTraverse
  签名: (f v t : Expr)
  定义体: do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Traversable #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedTraverse f v t.appArg!
    mkAppOptM ``Traversable.traverse #[t.appFn!, inst, none, none, none, none, f']
  else throwError "type {t} is not traversable with respect to variable {v}"
-/
partial def nestedTraverse (f v t : Expr) : TermElabM Expr := do
  let t ← instantiateMVars t
if ← withNewMCtxDepth isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Traversable #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedTraverse f v t.appArg!
    mkAppOptM ``Traversable.traverse #[t.appFn!, inst, none, none, none, none, f']
  else throwError "type {t} is not traversable with respect to variable {v}"

/--
Definition of `traverseField` / `traverseField` 的定义

English:
definition traverseField
  signature: (n : Name) (cl f v e : Expr)
  body: do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if v.occurs t then
    let f' ← nestedTraverse f v t
    return (true, f'.app e)
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
Prod.mk true < > mkAppM ``Comp.mk #[e]
  else
    return (false, e)

中文:
定义 traverseField
  签名: (n : Name) (cl f v e : Expr)
  定义体: do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if v.occurs t then
    let f' ← nestedTraverse f v t
    return (true, f'.app e)
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
Prod.mk true < > mkAppM ``Comp.mk #[e]
  else
    return (false, e)

Depends on / 依赖: ContinuousInf, IsLower, IsLower.toContinuousInf, toContinuousInf
-/
def traverseField (n : Name) (cl f v e : Expr) : TermElabM (Bool × Expr) := do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if v.occurs t then
    let f' ← nestedTraverse f v t
    return (true, f'.app e)
  else if ←
      (match t with
| .app t' _ => withNewMCtxDepth isDefEq t' cl
        | _ => return false) then
Prod.mk true < > mkAppM ``Comp.mk #[e]
  else
    return (false, e)

/--
Definition of `traverseConstructor` / `traverseConstructor` 的定义

English:
definition traverseConstructor
  signature: (c n : Name) (applInst f α β : Expr) (args₀ : List Expr)
  body: do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return (true, mkAppN (.fvar ad) #[g.appFn!, applInst, α, β, f, y.2])
      else traverseField n g.appFn! f α y.2)
  let gargs := args'.filterMap (fun y => if y.1 then some y.2 else none)
  let v ← mkFunCtor c (args₀.map (fun e => (false, e)) ++ args')
  let pureInst ← mkAppOptM ``Applicative.toPure #[none, applInst]
  let constr' ← mkAppOptM ``Pure.pure #[none, pureInst, none, v]
  let r ← gargs.foldlM
      (fun e garg => mkFunUnit garg >>= fun e' => mkAppM ``Seq.seq #[e, e']) constr'
  m.assign r

中文:
定义 traverseConstructor
  签名: (c n : Name) (applInst f α β : Expr) (args₀ : 列表 Expr)
  定义体: do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return (true, mkAppN (.fvar ad) #[g.appFn!, applInst, α, β, f, y.2])
      else traverseField n g.appFn! f α y.2)
  let gargs := args'.filterMap (fun y => if y.1 then some y.2 else none)
  let v ← mkFunCtor c (args₀.map (fun e => (false, e)) ++ args')
  let pureInst ← mkAppOptM ``Applicative.toPure #[none, applInst]
  let constr' ← mkAppOptM ``Pure.pure #[none, pureInst, none, v]
  let r ← gargs.foldlM
      (fun e garg => mkFunUnit garg >>= fun e' => mkAppM ``Seq.seq #[e, e']) constr'
  m.assign r

Depends on / 依赖: ContinuousSup, IsUpper, IsUpper.toContinuousInf, toContinuousInf
-/
def traverseConstructor (c n : Name) (applInst f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return (true, mkAppN (.fvar ad) #[g.appFn!, applInst, α, β, f, y.2])
      else traverseField n g.appFn! f α y.2)
  let gargs := args'.filterMap (fun y => if y.1 then some y.2 else none)
  let v ← mkFunCtor c (args₀.map (fun e => (false, e)) ++ args')
  let pureInst ← mkAppOptM ``Applicative.toPure #[none, applInst]
  let constr' ← mkAppOptM ``Pure.pure #[none, pureInst, none, v]
  let r ← gargs.foldlM
      (fun e garg => mkFunUnit garg >>= fun e' => mkAppM ``Seq.seq #[e, e']) constr'
  m.assign r
where
  /-- `mkFunCtor ctor [(true, (arg₁ : m type₁)), (false, (arg₂ : type₂)), (true, (arg₃ : m type₃)),
  (false, (arg₄ : type₄))]` makes `fun (x₁ : type₁) (x₃ : type₃) => ctor x₁ arg₂ x₃ arg₄`. -/
  mkFunCtor (c : Name) (args : List (Bool × Expr)) (fvars : Array Expr := #[])
      (aargs : Array Expr := #[]) : TermElabM Expr := do
    match args with
    | (true, x) :: xs =>
      let n ← mkFreshUserName `x
      let t ← inferType x
      withLocalDeclD n t.appArg! fun y => mkFunCtor c xs (fvars.push y) (aargs.push y)
    | (false, x) :: xs => mkFunCtor c xs fvars (aargs.push x)
| [] => liftM mkAppOptM c (aargs.map some) >>= mkLambdaFVars fvars

/--
Definition of `mkTraverse` / `mkTraverse` 的定义

English:
definition mkTraverse
  signature: (type : Name) (m : MVarId)
  body: do
  let vars ← getFVarsNotImplementationDetails
  let levels ← getLevelNames
  let (#[_, applInst, α, β, f, x], m) ← m.introN 6 [`m, `applInst, `α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          traverseConstructor
            ctor type (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

中文:
定义 mkTraverse
  签名: (type : Name) (m : MVarId)
  定义体: do
  let vars ← getFVarsNotImplementationDetails
  let levels ← getLevelNames
  let (#[_, applInst, α, β, f, x], m) ← m.introN 6 [`m, `applInst, `α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          traverseConstructor
            ctor type (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e
-/
def mkTraverse (type : Name) (m : MVarId) : TermElabM Unit := do
  let vars ← getFVarsNotImplementationDetails
  let levels ← getLevelNames
  let (#[_, applInst, α, β, f, x], m) ← m.introN 6 [`m, `applInst, `α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          traverseConstructor
            ctor type (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

/--
Definition of `deriveTraversable` / `deriveTraversable` 的定义

English:
definition deriveTraversable
  signature: (m : MVarId)
  body: do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Traversable _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { traverse := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "traverse"
withDeclName n' withAuxDecl (.mkSimple "traverse") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkTraverse n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              isProtected := true }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

中文:
定义 deriveTraversable
  签名: (m : MVarId)
  定义体: do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Traversable _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { traverse := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "traverse"
withDeclName n' withAuxDecl (.mkSimple "traverse") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkTraverse n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              isProtected := true }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)
-/
def deriveTraversable (m : MVarId) : TermElabM Unit := do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Traversable _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
let [m] ← run m evalTactic (← `(tactic| refine { traverse := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "traverse"
withDeclName n' withAuxDecl (.mkSimple "traverse") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkTraverse n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions docCtx
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          binders := mkNullNode #[]
          modifiers :=
            { isUnsafe := d.isUnsafe
              isProtected := true }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

/--
Definition of `traversableDeriveHandler` / `traversableDeriveHandler` 的定义

English:
definition traversableDeriveHandler
  signature: : DerivingHandler
  body: higherOrderDeriveHandler ``Traversable deriveTraversable [functorDeriveHandler]

中文:
定义 traversableDeriveHandler
  签名: : DerivingHandler
  定义体: higherOrderDeriveHandler ``Traversable deriveTraversable [functorDeriveHandler]

Depends on / 依赖: Traversable, deriveTraversable, functorDeriveHandler, higherOrderDeriveHandler
-/
def traversableDeriveHandler : DerivingHandler :=
  higherOrderDeriveHandler ``Traversable deriveTraversable [functorDeriveHandler]

initialize registerDerivingHandler ``Traversable traversableDeriveHandler

/--
Definition of `simpFunctorGoal` / `simpFunctorGoal` 的定义

English:
definition simpFunctorGoal
  signature: (m : MVarId) (s : Simp.Context) (simprocs : Simp.SimprocsArray := {})
  body: do
  let some e ← getSimpExtension? `functor_norm | failure
  let s' ← e.getTheorems
  simpGoal m (s.setSimpTheorems (s.simpTheorems.push s')) simprocs discharge? simplifyTarget
    fvarIdsToSimp stats

中文:
定义 simpFunctorGoal
  签名: (m : MVarId) (s : Simp.余ntext) (simprocs : Simp.SimprocsArray := {})
  定义体: do
  let some e ← getSimpExtension? `functor_norm | failure
  let s' ← e.getTheorems
  simpGoal m (s.setSimpTheorems (s.simpTheorems.push s')) simprocs discharge? simplifyTarget
    fvarIdsToSimp stats
-/
def simpFunctorGoal (m : MVarId) (s : Simp.Context) (simprocs : Simp.SimprocsArray := {})
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Simp.Stats := {}) :
    MetaM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  let some e ← getSimpExtension? `functor_norm | failure
  let s' ← e.getTheorems
  simpGoal m (s.setSimpTheorems (s.simpTheorems.push s')) simprocs discharge? simplifyTarget
    fvarIdsToSimp stats
/--
Definition of `traversableLawStarter` / `traversableLawStarter` 的定义

English:
definition traversableLawStarter
  signature: (m : MVarId) (n : Name) (s : MetaM Simp.Context)
  body: do
  let s' ← [``Traversable.traverse, ``Functor.map].foldlM
      (fun s n => s.addDeclToUnfold n) ({} : SimpTheorems)
  let (fi, m) ← m.intros
  m.withContext do
    if let (some m, _) ← dsimpGoal m (← Simp.mkContext (simpTheorems := #[s'])) then
      let ma ← m.induction fi.back! (mkRecName n)
      ma.forM fun is =>
        is.mvarId.withContext do
          if let (some (_, m), _) ← simpFunctorGoal is.mvarId (← s) then
            tac fi is m

中文:
定义 traversableLawStarter
  签名: (m : MVarId) (n : Name) (s : MetaM Simp.余ntext)
  定义体: do
  let s' ← [``Traversable.traverse, ``Functor.map].foldlM
      (fun s n => s.addDeclToUnfold n) ({} : SimpTheorems)
  let (fi, m) ← m.intros
  m.withContext do
    if let (some m, _) ← dsimpGoal m (← Simp.mkContext (simpTheorems := #[s'])) then
      let ma ← m.induction fi.back! (mkRecName n)
      ma.forM fun is =>
        is.mvarId.withContext do
          if let (some (_, m), _) ← simpFunctorGoal is.mvarId (← s) then
            tac fi is m
-/
def traversableLawStarter (m : MVarId) (n : Name) (s : MetaM Simp.Context)
    (tac : Array FVarId -> InductionSubgoal -> MVarId -> MetaM Unit) : MetaM Unit := do
  let s' ← [``Traversable.traverse, ``Functor.map].foldlM
      (fun s n => s.addDeclToUnfold n) ({} : SimpTheorems)
  let (fi, m) ← m.intros
  m.withContext do
    if let (some m, _) ← dsimpGoal m (← Simp.mkContext (simpTheorems := #[s'])) then
      let ma ← m.induction fi.back! (mkRecName n)
      ma.forM fun is =>
        is.mvarId.withContext do
          if let (some (_, m), _) ← simpFunctorGoal is.mvarId (← s) then
            tac fi is m

/--
Definition of `deriveLawfulTraversable` / `deriveLawfulTraversable` 的定义

English:
definition deriveLawfulTraversable
  signature: (m : MVarId)
  body: do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext { failIfUnchanged := false, unfoldPartialApp := true } (simpTheorems := #[s])
  let .app (.app (.const ``LawfulTraversable _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mit, mct, mtmi, mn] ← m.applyConst ``LawfulTraversable.mk | failure
  let defEqns : MetaM Simp.Context := rules [] [.mkStr n "map", .mkStr n "traverse"] true
  traversableLawStarter mit n defEqns fun _ _ m => m.refl
  traversableLawStarter mct n defEqns fun _ _ m => do
    if let (some (_, m), _) ← simpFunctorGoal m
        (← rules [] [.mkStr n "map", .mkStr n "traverse", ``Function.comp] true) then
      m.refl
  traversableLawStarter mtmi n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.traverse_eq_map_id', false)] [] false) then
    m.refl
  traversableLawStarter mn n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.naturality_pf, false)] [] false) then
    m.refl

中文:
定义 deriveLawfulTraversable
  签名: (m : MVarId)
  定义体: do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext { failIfUnchanged := false, unfoldPartialApp := true } (simpTheorems := #[s])
  let .app (.app (.const ``LawfulTraversable _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mit, mct, mtmi, mn] ← m.applyConst ``LawfulTraversable.mk | failure
  let defEqns : MetaM Simp.Context := rules [] [.mkStr n "map", .mkStr n "traverse"] true
  traversableLawStarter mit n defEqns fun _ _ m => m.refl
  traversableLawStarter mct n defEqns fun _ _ m => do
    if let (some (_, m), _) ← simpFunctorGoal m
        (← rules [] [.mkStr n "map", .mkStr n "traverse", ``Function.comp] true) then
      m.refl
  traversableLawStarter mtmi n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.traverse_eq_map_id', false)] [] false) then
    m.refl
  traversableLawStarter mn n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.naturality_pf, false)] [] false) then
    m.refl
-/
def deriveLawfulTraversable (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    Simp.mkContext { failIfUnchanged := false, unfoldPartialApp := true } (simpTheorems := #[s])
  let .app (.app (.const ``LawfulTraversable _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mit, mct, mtmi, mn] ← m.applyConst ``LawfulTraversable.mk | failure
  let defEqns : MetaM Simp.Context := rules [] [.mkStr n "map", .mkStr n "traverse"] true
  traversableLawStarter mit n defEqns fun _ _ m => m.refl
  traversableLawStarter mct n defEqns fun _ _ m => do
    if let (some (_, m), _) ← simpFunctorGoal m
        (← rules [] [.mkStr n "map", .mkStr n "traverse", ``Function.comp] true) then
      m.refl
  traversableLawStarter mtmi n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.traverse_eq_map_id', false)] [] false) then
    m.refl
  traversableLawStarter mn n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.naturality_pf, false)] [] false) then
    m.refl

/--
Definition of `lawfulTraversableDeriveHandler` / `lawfulTraversableDeriveHandler` 的定义

English:
definition lawfulTraversableDeriveHandler
  signature: : DerivingHandler
  body: higherOrderDeriveHandler ``LawfulTraversable deriveLawfulTraversable
    [traversableDeriveHandler, lawfulFunctorDeriveHandler] (fun n arg => mkAppOptM n #[arg, none])

中文:
定义 lawfulTraversableDeriveHandler
  签名: : DerivingHandler
  定义体: higherOrderDeriveHandler ``LawfulTraversable deriveLawfulTraversable
    [traversableDeriveHandler, lawfulFunctorDeriveHandler] (fun n arg => mkAppOptM n #[arg, none])

Depends on / 依赖: LawfulTraversable, deriveLawfulTraversable, higherOrderDeriveHandler, lawfulFunctorDeriveHandler, mkAppOptM, traversableDeriveHandler
-/
def lawfulTraversableDeriveHandler : DerivingHandler :=
  higherOrderDeriveHandler ``LawfulTraversable deriveLawfulTraversable
    [traversableDeriveHandler, lawfulFunctorDeriveHandler] (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulTraversable lawfulTraversableDeriveHandler

end Mathlib.Deriving.Traversable
