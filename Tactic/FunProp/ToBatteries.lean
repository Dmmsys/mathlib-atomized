/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Init

/-!
## `funProp` missing function from standard library
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

/--
Definition of `isOrderedSubsetOf` / `isOrderedSubsetOf` 的定义

English:
definition isOrderedSubsetOf
  signature: {α} [Inhabited α] [DecidableEq α] (a b : Array α)
  body: Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for h' : j in [0:b.size] do
    if i = a.size then
      break

    if a[i]! = b[j] then
      i := i+1

  if i = a.size then
    return true
  else
    return false

中文:
定义 isOrderedSubsetOf
  签名: {α} [可居 α] [DecidableEq α] (a b : 数组 α)
  定义体: Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for h' : j in [0:b.size] do
    if i = a.size then
      break

    if a[i]! = b[j] then
      i := i+1

  if i = a.size then
    return true
  else
    return false

Depends on / 依赖: Id.run, a.size, b.size, return
-/
def isOrderedSubsetOf {α} [Inhabited α] [DecidableEq α] (a b : Array α) : Bool :=
  Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for h' : j in [0:b.size] do
    if i = a.size then
      break

    if a[i]! = b[j] then
      i := i+1

  if i = a.size then
    return true
  else
    return false

/--
Definition of `_root_.Lean.Expr.swapBVars` / `_root_.Lean.Expr.swapBVars` 的定义

English:
definition _root_.Lean.Expr.swapBVars
  signature: (e : Expr) (i j : Nat)
  body: let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray

中文:
定义 _root_.Lean.Expr.swapBVars
  签名: (e : Expr) (i j : 自然数)
  定义体: let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray
-/
def _root_.Lean.Expr.swapBVars (e : Expr) (i j : Nat) : Expr :=

  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray

/--
Definition of `mkProdElem` / `mkProdElem` 的定义

English:
definition mkProdElem
  signature: (xs : Array Expr)
  body: do
  match h : xs.size with
  | 0 => return default
  | 1 => return xs[0]
  | n + 1 =>
    xs[0:n].foldrM (init := xs[n]) fun x p => mkAppM ``Prod.mk #[x,p]

中文:
定义 mkProdElem
  签名: (xs : 数组 Expr)
  定义体: do
  match h : xs.size with
  | 0 => return default
  | 1 => return xs[0]
  | n + 1 =>
    xs[0:n].foldrM (init := xs[n]) fun x p => mkAppM ``Prod.mk #[x,p]
-/
def mkProdElem (xs : Array Expr) : MetaM Expr := do
  match h : xs.size with
  | 0 => return default
  | 1 => return xs[0]
  | n + 1 =>
    xs[0:n].foldrM (init := xs[n]) fun x p => mkAppM ``Prod.mk #[x,p]

/--
Definition of `mkProdProj` / `mkProdProj` 的定义

English:
definition mkProdProj
  signature: (x : Expr) (i : Nat) (n : Nat)
  body: do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM ``Prod.fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM ``Prod.snd #[x]) i' n'

中文:
定义 mkProdProj
  签名: (x : Expr) (i : 自然数) (n : 自然数)
  定义体: do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM ``Prod.fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM ``Prod.snd #[x]) i' n'
-/
def mkProdProj (x : Expr) (i : Nat) (n : Nat) : MetaM Expr := do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM ``Prod.fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM ``Prod.snd #[x]) i' n'

/--
Definition of `mkProdSplitElem` / `mkProdSplitElem` 的定义

English:
definition mkProdSplitElem
  signature: (xs : Expr) (n : Nat)
  body: (Array.range n)
.mapM (fun i => mkProdProj xs i n)

中文:
定义 mkProdSplitElem
  签名: (xs : Expr) (n : 自然数)
  定义体: (Array.range n)
.mapM (fun i => mkProdProj xs i n)

Depends on / 依赖: Array.range, mkProdProj
-/
def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) :=
  (Array.range n)
.mapM (fun i => mkProdProj xs i n)

/--
Definition of `mkUncurryFun` / `mkUncurryFun` 的定义

English:
definition mkUncurryFun
  signature: (n : Nat) (f : Expr)
  body: do
  if n <= 1 then
    return f
  forallBoundedTelescope (← inferType f) n fun xs _ => do
    let xProdName : String ← xs.foldlM (init:="") fun n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl (.mkSimple xProdName) default xProdType fun xProd => do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta

中文:
定义 mkUncurryFun
  签名: (n : 自然数) (f : Expr)
  定义体: do
  if n <= 1 then
    return f
  forallBoundedTelescope (← inferType f) n fun xs _ => do
    let xProdName : String ← xs.foldlM (init:="") fun n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl (.mkSimple xProdName) default xProdType fun xProd => do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta
-/
def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n <= 1 then
    return f
  forallBoundedTelescope (← inferType f) n fun xs _ => do
    let xProdName : String ← xs.foldlM (init:="") fun n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl (.mkSimple xProdName) default xProdType fun xProd => do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta


/--
Definition of `etaExpand1` / `etaExpand1` 的定义

English:
definition etaExpand1
  signature: (f : Expr)
  body: do
  let f := f.eta
  if f.isLambda then
    return f
  else
    withDefault do forallBoundedTelescope (← inferType f) (.some 1) fun xs _ => do
      mkLambdaFVars xs (mkAppN f xs)

中文:
定义 etaExpand1
  签名: (f : Expr)
  定义体: do
  let f := f.eta
  if f.isLambda then
    return f
  else
    withDefault do forallBoundedTelescope (← inferType f) (.some 1) fun xs _ => do
      mkLambdaFVars xs (mkAppN f xs)
-/
def etaExpand1 (f : Expr) : MetaM Expr := do
  let f := f.eta
  if f.isLambda then
    return f
  else
    withDefault do forallBoundedTelescope (← inferType f) (.some 1) fun xs _ => do
      mkLambdaFVars xs (mkAppN f xs)

/--
Definition of `betaThroughLetAux` / `betaThroughLetAux` 的定义

English:
definition betaThroughLetAux
  signature: (f : Expr) (args : List Expr)
  body: match f, args with
  | f, [] => f
  | .lam _ _ b _, a :: as => (betaThroughLetAux (b.instantiate1 a) as)
  | .letE n t v b nondep, args => .letE n t v (betaThroughLetAux b args) nondep
  | .mdata _ b, args => betaThroughLetAux b args
  | f, args => mkAppN f args.toArray

中文:
定义 betaThroughLetAux
  签名: (f : Expr) (args : 列表 Expr)
  定义体: match f, args with
  | f, [] => f
  | .lam _ _ b _, a :: as => (betaThroughLetAux (b.instantiate1 a) as)
  | .letE n t v b nondep, args => .letE n t v (betaThroughLetAux b args) nondep
  | .mdata _ b, args => betaThroughLetAux b args
  | f, args => mkAppN f args.toArray
-/
private def betaThroughLetAux (f : Expr) (args : List Expr) : Expr :=
  match f, args with
  | f, [] => f
  | .lam _ _ b _, a :: as => (betaThroughLetAux (b.instantiate1 a) as)
  | .letE n t v b nondep, args => .letE n t v (betaThroughLetAux b args) nondep
  | .mdata _ b, args => betaThroughLetAux b args
  | f, args => mkAppN f args.toArray

/--
Definition of `betaThroughLet` / `betaThroughLet` 的定义

English:
definition betaThroughLet
  signature: (f : Expr) (args : Array Expr)
  body: betaThroughLetAux f args.toList

中文:
定义 betaThroughLet
  签名: (f : Expr) (args : 数组 Expr)
  定义体: betaThroughLetAux f args.toList

Depends on / 依赖: IsScottHausdorff, IsScottHausdorff.mk, args.toList, betaThroughLetAux, scottHausdorff, toList
-/
def betaThroughLet (f : Expr) (args : Array Expr) : Expr :=
  betaThroughLetAux f args.toList

/--
Definition of `headBetaThroughLet` / `headBetaThroughLet` 的定义

English:
definition headBetaThroughLet
  signature: (e : Expr)
  body: let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaThroughLet f e.getAppArgs else e

中文:
定义 headBetaThroughLet
  签名: (e : Expr)
  定义体: let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaThroughLet f e.getAppArgs else e

Depends on / 依赖: betaThroughLet, e.getAppArgs, e.getAppFn, f.isHeadBetaTargetFn, getAppArgs, getAppFn, isHeadBetaTargetFn
-/
def headBetaThroughLet (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaThroughLet f e.getAppArgs else e


end Meta.FunProp

end Mathlib
