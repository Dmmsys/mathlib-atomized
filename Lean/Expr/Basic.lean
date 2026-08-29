/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, Edward Ayers, Arthur Paulino, Thomas R. Murrills
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Meta.AppBuilder
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Transform
public import Lean.Structure

/-!
# Additional operations on Expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics.
-/

public section

namespace Lean

namespace BinderInfo

/-! ### Declarations about `BinderInfo` -/

/--
Definition of `brackets` / `brackets` 的定义

English:
definition brackets
  signature: : BinderInfo -> String × String

中文:
定义 brackets
  签名: : BinderInfo -> String × String
-/
def brackets : BinderInfo -> String × String
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("{{", "}}")
  | BinderInfo.instImplicit => ("[", "]")
  | _ => ("(", ")")

end BinderInfo

namespace Name

/-! ### Declarations about `name` -/

/--
Definition of `mapPrefix` / `mapPrefix` 的定义

English:
definition mapPrefix
  signature: (f : Name -> Option Name) (n : Name)
  body: Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i

中文:
定义 mapPrefix
  签名: (f : Name -> Option Name) (n : Name)
  定义体: Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i
-/
@[specialize] def mapPrefix (f : Name -> Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i

/--
Definition of `fromComponents` / `fromComponents` 的定义

English:
definition fromComponents
  signature: : List Name -> Name
  body: go .anonymous where
  /-- Auxiliary for `Name.fromComponents` -/
  go : Name -> List Name -> Name
  | n, [] => n
  | n, s :: rest => go (s.updatePrefix n) rest

中文:
定义 fromComponents
  签名: : List Name -> Name
  定义体: go .anonymous where
  /-- Auxiliary for `Name.fromComponents` -/
  go : Name -> List Name -> Name
  | n, [] => n
  | n, s :: rest => go (s.updatePrefix n) rest

Depends on / 依赖: anonymous
-/
def fromComponents : List Name -> Name := go .anonymous where
  /-- Auxiliary for `Name.fromComponents` -/
  go : Name -> List Name -> Name
  | n, [] => n
  | n, s :: rest => go (s.updatePrefix n) rest

/--
Definition of `updateLast` / `updateLast` 的定义

English:
definition updateLast
  signature: (f : String -> String)

中文:
定义 updateLast
  签名: (f : String -> String)
-/
def updateLast (f : String -> String) : Name -> Name
  | .str n s => .str n (f s)
  | n => n

/--
Definition of `lastComponentAsString` / `lastComponentAsString` 的定义

English:
definition lastComponentAsString
  signature: : Name -> String

中文:
定义 lastComponentAsString
  签名: : Name -> String
-/
def lastComponentAsString : Name -> String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

/--
Definition of `splitAt` / `splitAt` 的定义

English:
definition splitAt
  signature: (nm : Name) (n : Nat)
  body: let (nm2, nm1) := nm.componentsRev.splitAt n
  (.fromComponents <| nm1.reverse, .fromComponents <| nm2.reverse)

中文:
定义 splitAt
  签名: (nm : Name) (n : 自然数)
  定义体: let (nm2, nm1) := nm.componentsRev.splitAt n
  (.fromComponents <| nm1.reverse, .fromComponents <| nm2.reverse)

Depends on / 依赖: componentsRev, fromComponents, nm.componentsRev.splitAt, nm1.reverse, nm2.reverse, reverse, splitAt
-/
def splitAt (nm : Name) (n : Nat) : Name × Name :=
  let (nm2, nm1) := nm.componentsRev.splitAt n
  (.fromComponents <| nm1.reverse, .fromComponents <| nm2.reverse)

/--
Definition of `isPrefixOf?` / `isPrefixOf?` 的定义

English:
definition isPrefixOf?
  signature: (pre nm : Name)
  body: if pre == nm then
    some anonymous
  else match nm with
  | anonymous => none
  | num p' a => (isPrefixOf? pre p').map (·.num a)
  | str p' s => (isPrefixOf? pre p').map (·.str s)

中文:
定义 isPrefixOf?
  签名: (pre nm : Name)
  定义体: if pre == nm then
    some anonymous
  else match nm with
  | anonymous => none
  | num p' a => (isPrefixOf? pre p').map (·.num a)
  | str p' s => (isPrefixOf? pre p').map (·.str s)

Depends on / 依赖: anonymous, isPrefixOf
-/
def isPrefixOf? (pre nm : Name) : Option Name :=
  if pre == nm then
    some anonymous
  else match nm with
  | anonymous => none
  | num p' a => (isPrefixOf? pre p').map (·.num a)
  | str p' s => (isPrefixOf? pre p').map (·.str s)

open Meta

-- from Lean.Server.Completion
/--
Definition of `isBlackListed` / `isBlackListed` 的定义

English:
definition isBlackListed
  signature: {m} [Monad m] [MonadEnv m] (declName : Name)
  body: do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
pure declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
 isRec declName isMat

中文:
定义 isBlackListed
  签名: {m} [Monad m] [MonadEnv m] (declName : Name)
  定义体: do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
pure declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
 isRec declName isMat
-/
def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
pure declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
 isRec declName isMatcher declName

end Name

namespace ConstantInfo

/--
Definition of `isDef` / `isDef` 的定义

English:
definition isDef
  signature: : ConstantInfo -> Bool

中文:
定义 isDef
  签名: : ConstantInfo -> 布尔
-/
def isDef : ConstantInfo -> Bool
  | defnInfo _ => true
  | _ => false

/--
Definition of `isThm` / `isThm` 的定义

English:
definition isThm
  signature: : ConstantInfo -> Bool

中文:
定义 isThm
  签名: : ConstantInfo -> 布尔
-/
def isThm : ConstantInfo -> Bool
  | thmInfo _ => true
  | _ => false

/--
Definition of `updateConstantVal` / `updateConstantVal` 的定义

English:
definition updateConstantVal
  signature: : ConstantInfo -> ConstantVal -> ConstantInfo

中文:
定义 updateConstantVal
  签名: : ConstantInfo -> ConstantVal -> ConstantInfo
-/
def updateConstantVal : ConstantInfo -> ConstantVal -> ConstantInfo
  | defnInfo info, v => defnInfo {info with toConstantVal := v}
  | axiomInfo info, v => axiomInfo {info with toConstantVal := v}
  | thmInfo info, v => thmInfo {info with toConstantVal := v}
  | opaqueInfo info, v => opaqueInfo {info with toConstantVal := v}
  | quotInfo info, v => quotInfo {info with toConstantVal := v}
  | inductInfo info, v => inductInfo {info with toConstantVal := v}
  | ctorInfo info, v => ctorInfo {info with toConstantVal := v}
  | recInfo info, v => recInfo {info with toConstantVal := v}

/--
Definition of `updateName` / `updateName` 的定义

English:
definition updateName
  signature: (c : ConstantInfo) (name : Name)
  body: c.updateConstantVal {c.toConstantVal with name}

中文:
定义 updateName
  签名: (c : ConstantInfo) (name : Name)
  定义体: c.updateConstantVal {c.toConstantVal with name}

Depends on / 依赖: c.toConstantVal, c.updateConstantVal, toConstantVal, updateConstantVal
-/
def updateName (c : ConstantInfo) (name : Name) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with name}

/--
Definition of `updateType` / `updateType` 的定义

English:
definition updateType
  signature: (c : ConstantInfo) (type : Expr)
  body: c.updateConstantVal {c.toConstantVal with type}

中文:
定义 updateType
  签名: (c : ConstantInfo) (type : Expr)
  定义体: c.updateConstantVal {c.toConstantVal with type}

Depends on / 依赖: c.toConstantVal, c.updateConstantVal, toConstantVal, updateConstantVal
-/
def updateType (c : ConstantInfo) (type : Expr) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with type}

/--
Definition of `updateLevelParams` / `updateLevelParams` 的定义

English:
definition updateLevelParams
  signature: (c : ConstantInfo) (levelParams : List Name)
  body: c.updateConstantVal {c.toConstantVal with levelParams}

中文:
定义 updateLevelParams
  签名: (c : ConstantInfo) (levelParams : List Name)
  定义体: c.updateConstantVal {c.toConstantVal with levelParams}

Depends on / 依赖: c.toConstantVal, c.updateConstantVal, levelParams, toConstantVal, updateConstantVal
-/
def updateLevelParams (c : ConstantInfo) (levelParams : List Name) :
    ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with levelParams}

/--
Definition of `updateAll` / `updateAll` 的定义

English:
definition updateAll
  signature: : ConstantInfo -> List Name -> ConstantInfo

中文:
定义 updateAll
  签名: : ConstantInfo -> List Name -> ConstantInfo
-/
def updateAll : ConstantInfo -> List Name -> ConstantInfo
  | .defnInfo info, all => .defnInfo {info with all}
  | .thmInfo info, all => .thmInfo {info with all}
  | .opaqueInfo info, all => .opaqueInfo {info with all}
  | .inductInfo info, all => .inductInfo {info with all}
  | ci, _ => ci

/--
Definition of `updateValue` / `updateValue` 的定义

English:
definition updateValue
  signature: : ConstantInfo -> Expr -> ConstantInfo

中文:
定义 updateValue
  签名: : ConstantInfo -> Expr -> ConstantInfo
-/
def updateValue : ConstantInfo -> Expr -> ConstantInfo
  | defnInfo info, v => defnInfo {info with value := v}
  | thmInfo info, v => thmInfo {info with value := v}
  | opaqueInfo info, v => opaqueInfo {info with value := v}
  | d, _ => d

/--
Definition of `toDeclaration!` / `toDeclaration!` 的定义

English:
definition toDeclaration!
  signature: : ConstantInfo -> Declaration

中文:
定义 toDeclaration!
  签名: : ConstantInfo -> Declaration
-/
def toDeclaration! : ConstantInfo -> Declaration
  | defnInfo info => Declaration.defnDecl info
  | thmInfo info => Declaration.thmDecl info
  | axiomInfo info => Declaration.axiomDecl info
  | opaqueInfo info => Declaration.opaqueDecl info
  | quotInfo _ => panic! "toDeclaration for quotInfo not implemented"
  | inductInfo _ => panic! "toDeclaration for inductInfo not implemented"
  | ctorInfo _ => panic! "toDeclaration for ctorInfo not implemented"
  | recInfo _ => panic! "toDeclaration for recInfo not implemented"

end ConstantInfo

open Meta

/--
Definition of `mkConst'` / `mkConst'` 的定义

English:
definition mkConst'
  signature: (constName : Name)
  body: do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)

中文:
定义 mkConst'
  签名: (constName : Name)
  定义体: do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)
-/
def mkConst' (constName : Name) : MetaM Expr := do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)

namespace Expr


/--
Definition of `bvarIdx?` / `bvarIdx?` 的定义

English:
definition bvarIdx?
  signature: : Expr -> Option Nat

中文:
定义 bvarIdx?
  签名: : Expr -> Option 自然数
-/
def bvarIdx? : Expr -> Option Nat
  | bvar idx => some idx
  | _ => none

/--
Definition of `getAppAppsAux` / `getAppAppsAux` 的定义

English:
definition getAppAppsAux
  signature: : Expr -> Array Expr -> Nat -> Array Expr

中文:
定义 getAppAppsAux
  签名: : Expr -> Array Expr -> 自然数 -> Array Expr
-/
private def getAppAppsAux : Expr -> Array Expr -> Nat -> Array Expr
  | .app f a, as, i => getAppAppsAux f (as.set! i (.app f a)) (i-1)
  | _, as, _ => as

/-- Given `f a b c`, return `#[f a, f a b, f a b c]`.
Each entry in the array is an `Expr.app`,
and this array has the same length as the one returned by `Lean.Expr.getAppArgs`. -/
@[inline]
/--
Definition of `getAppApps` / `getAppApps` 的定义

English:
definition getAppApps
  signature: (e : Expr)
  body: let dummy := mkSort .zero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (.replicate nargs dummy) (nargs-1)

中文:
定义 getAppApps
  签名: (e : Expr)
  定义体: let dummy := mkSort .zero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (.replicate nargs dummy) (nargs-1)

Depends on / 依赖: e.getAppNumArgs, getAppAppsAux, getAppNumArgs, mkSort, replicate
-/
def getAppApps (e : Expr) : Array Expr :=
  let dummy := mkSort .zero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (.replicate nargs dummy) (nargs-1)

/--
Definition of `eraseProofs` / `eraseProofs` 的定义

English:
definition eraseProofs
  signature: (e : Expr)
  body: Meta.transform (skipConstInApp := true) e
    (pre := fun e => do
      if (← Meta.isProof e) then
        return .continue (← mkSorry (← inferType e) true)
      else
        return .continue)

中文:
定义 eraseProofs
  签名: (e : Expr)
  定义体: Meta.transform (skipConstInApp := true) e
    (pre := fun e => do
      if (← Meta.isProof e) then
        return .continue (← mkSorry (← inferType e) true)
      else
        return .continue)

Depends on / 依赖: Meta.isProof, Meta.transform, continue, inferType, isProof, mkSorry, return, skipConstInApp, transform
-/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform (skipConstInApp := true) e
    (pre := fun e => do
      if (← Meta.isProof e) then
        return .continue (← mkSorry (← inferType e) true)
      else
        return .continue)

/--
Definition of `type?` / `type?` 的定义

English:
definition type?
  signature: : Expr -> Option Level

中文:
定义 type?
  签名: : Expr -> Option Level
-/
def type? : Expr -> Option Level
  | .sort u => u.dec
  | _ => none

/-- `isConstantApplication e` checks whether `e` is syntactically an application of the form
`(fun x₁ ⋯ xₙ => H) y₁ ⋯ yₙ` where `H` does not contain the variable `xₙ`. In other words,
it does a syntactic check that the expression does not depend on `yₙ`. -/
@[deprecated "This function was implemented incorrectly" (since := "2026-02-13")]
/--
Definition of `isConstantApplication` / `isConstantApplication` 的定义

English:
definition isConstantApplication
  signature: (e : Expr)
  body: e.isApp && aux e.getAppNumArgs'.pred e.getAppFn' e.getAppNumArgs'

中文:
定义 isConstantApplication
  签名: (e : Expr)
  定义体: e.isApp && aux e.getAppNumArgs'.pred e.getAppFn' e.getAppNumArgs'

Depends on / 依赖: e.getAppFn, e.getAppNumArgs, e.isApp, getAppFn, getAppNumArgs
-/
def isConstantApplication (e : Expr) :=
  e.isApp && aux e.getAppNumArgs'.pred e.getAppFn' e.getAppNumArgs'
where
  /-- `aux depth e n` checks whether the body of the `n`-th lambda of `e` has loose bvar
    `depth - 1`. -/
  aux (depth : Nat) : Expr -> Nat -> Bool
    | .lam _ _ b _, n + 1 => aux depth b n
    | e, 0 => !e.hasLooseBVar (depth - 1)
    | _, _ => false

/--
Definition of `isAppOrForallOfConstP` / `isAppOrForallOfConstP` 的定义

English:
definition isAppOrForallOfConstP
  signature: (p : Name -> Bool) (type : Expr)
  body: match type.cleanupAnnotations.getAppFn' with
  | .const n _ => p n
  | .forallE _ _ body _ => isAppOrForallOfConstP p body
  | _ => false

中文:
定义 isAppOrForallOfConstP
  签名: (p : Name -> 布尔) (type : Expr)
  定义体: match type.cleanupAnnotations.getAppFn' with
  | .const n _ => p n
  | .forallE _ _ body _ => isAppOrForallOfConstP p body
  | _ => false
-/
@[inline] partial def isAppOrForallOfConstP (p : Name -> Bool) (type : Expr) : Bool :=
  match type.cleanupAnnotations.getAppFn' with
  | .const n _ => p n
  | .forallE _ _ body _ => isAppOrForallOfConstP p body
  | _ => false

/--
Definition of `isAppOrForallOfConst` / `isAppOrForallOfConst` 的定义

English:
definition isAppOrForallOfConst
  signature: (declName : Name) (type : Expr)
  body: isAppOrForallOfConstP (· == declName) type

中文:
定义 isAppOrForallOfConst
  签名: (declName : Name) (type : Expr)
  定义体: isAppOrForallOfConstP (· == declName) type
-/
@[inline] partial def isAppOrForallOfConst (declName : Name) (type : Expr) : Bool :=
  isAppOrForallOfConstP (· == declName) type

/--
Definition of `getUnusedForallInstanceBinderIdxsWhere` / `getUnusedForallInstanceBinderIdxsWhere` 的定义

English:
definition getUnusedForallInstanceBinderIdxsWhere
  signature: (p : Expr -> Bool) (e : Expr)
  body: go e 0 #[]

中文:
定义 getUnusedForallInstanceBinderIdxsWhere
  签名: (p : Expr -> 布尔) (e : Expr)
  定义体: go e 0 #[]
-/
partial def getUnusedForallInstanceBinderIdxsWhere (p : Expr -> Bool) (e : Expr) :
    Array Nat :=
  go e 0 #[]
where
  /-- Inspects `body`, and if it is a `.forallE` of an instance with type `type` such that `p type`
  is `true` and the remainder of the type does not depend on it, pushes the `current` index onto
  the accumulated array. -/
  go (body : Expr) (current : Nat) (acc : Array Nat) : Array Nat :=
    match body.cleanupAnnotations with
| .forallE _ type body bi => go body (current+1)
      if bi.isInstImplicit && p type && !(body.hasLooseBVar 0) then
        acc.push current
      else
        acc
    /- See through `letE`, and just as in the interpretation of a bound provided to
    `forallBoundedTelescope`, do not increment the number of binders we've counted. -/
    | .letE _ _ _ body _ => go body current acc
    | _ => acc

/--
Definition of `hasInstanceBinderOf` / `hasInstanceBinderOf` 的定义

English:
definition hasInstanceBinderOf
  signature: (p : Expr -> Bool) (e : Expr)
  body: match e.cleanupAnnotations with
  | .forallE _ type body bi => (bi.isInstImplicit && p type) || hasInstanceBinderOf p body
  | .letE _ _ _ body _ => hasInstanceBinderOf p body
  | _ => false

中文:
定义 hasInstanceBinderOf
  签名: (p : Expr -> 布尔) (e : Expr)
  定义体: match e.cleanupAnnotations with
  | .forallE _ type body bi => (bi.isInstImplicit && p type) || hasInstanceBinderOf p body
  | .letE _ _ _ body _ => hasInstanceBinderOf p body
  | _ => false
-/
partial def hasInstanceBinderOf (p : Expr -> Bool) (e : Expr) : Bool :=
  match e.cleanupAnnotations with
  | .forallE _ type body bi => (bi.isInstImplicit && p type) || hasInstanceBinderOf p body
  | .letE _ _ _ body _ => hasInstanceBinderOf p body
  | _ => false

/--
Definition of `letDepth` / `letDepth` 的定义

English:
definition letDepth
  signature: : Expr -> Nat

中文:
定义 letDepth
  签名: : Expr -> 自然数
-/
def letDepth : Expr -> Nat
  | .letE _ _ _ b _ => b.letDepth + 1
  | _ => 0

open Meta

-- There is a `TacticM` level version of this, but it's useful to have in `MetaM`.
/--
Definition of `ensureHasNoMVars` / `ensureHasNoMVars` 的定义

English:
definition ensureHasNoMVars
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

中文:
定义 ensureHasNoMVars
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"
-/
def ensureHasNoMVars (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (α : Expr) (n : Nat)
  body: do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]

中文:
定义 ofNat
  签名: (α : Expr) (n : 自然数)
  定义体: do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]
-/
def ofNat (α : Expr) (n : Nat) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]

/--
Definition of `ofInt` / `ofInt` 的定义

English:
definition ofInt
  signature: (α : Expr)

中文:
定义 ofInt
  签名: (α : Expr)
-/
def ofInt (α : Expr) : Int -> MetaM Expr
  | Int.ofNat n => Expr.ofNat α n
  | Int.negSucc n => do mkAppM ``Neg.neg #[← Expr.ofNat α (n + 1)]

section recognizers

/--
Definition of `numeral?` / `numeral?` 的定义

English:
definition numeral?
  signature: (e : Expr)
  body: if let some n := e.rawNatLit? then n
  else
    let e := e.consumeMData -- `OfNat` numerals may have `no_index` around them from `ofNat()`
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? 

中文:
定义 numeral?
  签名: (e : Expr)
  定义体: if let some n := e.rawNatLit? then n
  else
    let e := e.consumeMData -- `OfNat` numerals may have `no_index` around them from `ofNat()`
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? 
-/
partial def numeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then n
  else
    let e := e.consumeMData -- `OfNat` numerals may have `no_index` around them from `ofNat()`
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

/--
Definition of `zero?` / `zero?` 的定义

English:
definition zero?
  signature: (e : Expr)
  body: match e.numeral? with
  | some 0 => true
  | _ => false

中文:
定义 zero?
  签名: (e : Expr)
  定义体: match e.numeral? with
  | some 0 => true
  | _ => false

Depends on / 依赖: e.numeral, numeral
-/
def zero? (e : Expr) : Bool :=
  match e.numeral? with
  | some 0 => true
  | _ => false

/--
Definition of `ne?'` / `ne?'` 的定义

English:
definition ne?'
  signature: (e : Expr)
  body: e.ne? > (e.not? >>= Expr.eq?)

中文:
定义 ne?'
  签名: (e : Expr)
  定义体: e.ne? > (e.not? >>= Expr.eq?)

Depends on / 依赖: Expr.eq, e.ne, e.not
-/
def ne?' (e : Expr) : Option (Expr × Expr × Expr) :=
e.ne? > (e.not? >>= Expr.eq?)

/--
Definition of `le?` / `le?` 的定义

English:
definition le?
  signature: (p : Expr)
  body: do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)

中文:
定义 le?
  签名: (p : Expr)
  定义体: do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)
-/
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)

/--
Definition of `lt?` / `lt?` 的定义

English:
definition lt?
  signature: (p : Expr)
  body: do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)

中文:
定义 lt?
  签名: (p : Expr)
  定义体: do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)
-/
@[inline] def lt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)

/--
Definition of `sides?` / `sides?` 的定义

English:
definition sides?
  signature: (ty : Expr)
  body: if let some (lhs, rhs) := ty.iff? then
    some (.sort .zero, lhs, .sort .zero, rhs)
  else if let some (ty, lhs, rhs) := ty.eq? then
    some (ty, lhs, ty, rhs)
  else
    ty.heq?

中文:
定义 sides?
  签名: (ty : Expr)
  定义体: if let some (lhs, rhs) := ty.iff? then
    some (.sort .zero, lhs, .sort .zero, rhs)
  else if let some (ty, lhs, rhs) := ty.eq? then
    some (ty, lhs, ty, rhs)
  else
    ty.heq?

Depends on / 依赖: ty.eq, ty.heq, ty.iff
-/
def sides? (ty : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if let some (lhs, rhs) := ty.iff? then
    some (.sort .zero, lhs, .sort .zero, rhs)
  else if let some (ty, lhs, rhs) := ty.eq? then
    some (ty, lhs, ty, rhs)
  else
    ty.heq?

/--
Definition of `isSorryAx` / `isSorryAx` 的定义

English:
definition isSorryAx
  signature: : Expr -> Bool

中文:
定义 isSorryAx
  签名: : Expr -> 布尔
-/
def isSorryAx : Expr -> Bool
  | .app (.app f _ ) _ => f.isConstOf ``sorryAx
  | _ => false

end recognizers

universe u

/--
Definition of `modifyAppArgM` / `modifyAppArgM` 的定义

English:
definition modifyAppArgM
  signature: {M : Type -> Type u} [Functor M] [Pure M]

中文:
定义 modifyAppArgM
  签名: {M : Type -> 类型u} [Functor M] [Pure M]
-/
def modifyAppArgM {M : Type -> Type u} [Functor M] [Pure M]
    (modifier : Expr -> M Expr) : Expr -> M Expr
| app f a => mkApp f < > modifier a
  | e => pure e

/--
Definition of `modifyRevArg` / `modifyRevArg` 的定义

English:
definition modifyRevArg
  signature: (modifier : Expr -> Expr)

中文:
定义 modifyRevArg
  签名: (modifier : Expr -> Expr)
-/
def modifyRevArg (modifier : Expr -> Expr) : Nat -> Expr -> Expr
  | 0, (.app f x) => .app f (modifier x)
  | (i+1), (.app f x) => .app (modifyRevArg modifier i f) x
  | _, e => e

/--
Definition of `modifyArg` / `modifyArg` 的定义

English:
definition modifyArg
  signature: (modifier : Expr -> Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs)
  body: modifyRevArg modifier (n - i - 1) e

中文:
定义 modifyArg
  签名: (modifier : Expr -> Expr) (e : Expr) (i : 自然数) (n := e.getAppNumArgs)
  定义体: modifyRevArg modifier (n - i - 1) e

Depends on / 依赖: e.getAppNumArgs, getAppNumArgs
-/
def modifyArg (modifier : Expr -> Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e

/--
Definition of `setArg` / `setArg` 的定义

English:
definition setArg
  signature: (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs)
  body: e.modifyArg (fun _ => x) i n

中文:
定义 setArg
  签名: (e : Expr) (i : 自然数) (x : Expr) (n := e.getAppNumArgs)
  定义体: e.modifyArg (fun _ => x) i n

Depends on / 依赖: e.getAppNumArgs, getAppNumArgs
-/
def setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modifyArg (fun _ => x) i n

/--
Definition of `getRevArg?` / `getRevArg?` 的定义

English:
definition getRevArg?
  signature: : Expr -> Nat -> Option Expr

中文:
定义 getRevArg?
  签名: : Expr -> 自然数 -> Option Expr
-/
def getRevArg? : Expr -> Nat -> Option Expr
  | app _ a, 0 => a
  | app f _, i+1 => getRevArg! f i
  | _, _ => none

/--
Definition of `getArg?` / `getArg?` 的定义

English:
definition getArg?
  signature: (e : Expr) (i : Nat) (n := e.getAppNumArgs)
  body: getRevArg? e (n - i - 1)

中文:
定义 getArg?
  签名: (e : Expr) (i : 自然数) (n := e.getAppNumArgs)
  定义体: getRevArg? e (n - i - 1)

Depends on / 依赖: e.getAppNumArgs, getAppNumArgs
-/
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Option Expr :=
  getRevArg? e (n - i - 1)

/--
Definition of `modifyArgM` / `modifyArgM` 的定义

English:
definition modifyArgM
  signature: {M : Type -> Type u} [Monad M] (modifier : Expr -> M Expr)
  body: do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ => a) e i n

中文:
定义 modifyArgM
  签名: {M : Type -> 类型u} [Monad M] (modifier : Expr -> M Expr)
  定义体: do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ => a) e i n

Depends on / 依赖: e.getAppNumArgs, getAppNumArgs
-/
def modifyArgM {M : Type -> Type u} [Monad M] (modifier : Expr -> M Expr)
    (e : Expr) (i : Nat) (n := e.getAppNumArgs) : M Expr := do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ => a) e i n

/--
Definition of `renameBVar` / `renameBVar` 的定义

English:
definition renameBVar
  signature: (e : Expr) (old new : Name)
  body: match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVa

中文:
定义 renameBVar
  签名: (e : Expr) (old new : Name)
  定义体: match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVa

Depends on / 依赖: arg.renameBVar, bd.renameBVar, fn.renameBVar, forallE, renameBVar, ty.renameBVar
-/
def renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | mdata d e' => mdata d (e'.renameBVar old new)
  | e => e

open Lean.Meta in
/--
Definition of `getBinderName` / `getBinderName` 的定义

English:
definition getBinderName
  signature: (e : Expr)
  body: do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none

中文:
定义 getBinderName
  签名: (e : Expr)
  定义体: do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none
-/
def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none

/--
Definition of `mapForallBinderNames` / `mapForallBinderNames` 的定义

English:
definition mapForallBinderNames
  signature: : Expr -> (Name -> Name) -> Expr

中文:
定义 mapForallBinderNames
  签名: : Expr -> (Name -> Name) -> Expr
-/
def mapForallBinderNames : Expr -> (Name -> Name) -> Expr
  | .forallE n d b bi, f => .forallE (f n) d (mapForallBinderNames b f) bi
  | e, _ => e

/--
Definition of `mkDirectProjection` / `mkDirectProjection` 的定义

English:
definition mkDirectProjection
  signature: (e : Expr) (fieldName : Name)
  body: do
  let type ← whnf (← inferType e)
  let .const structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
  let some projName := getProjFnForField? (← getEnv) structName fieldName |
    throwError "{structName} doesn't have field {fieldName}"
  return mkAppN (.const projNa

中文:
定义 mkDirectProjection
  签名: (e : Expr) (fieldName : Name)
  定义体: do
  let type ← whnf (← inferType e)
  let .const structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
  let some projName := getProjFnForField? (← getEnv) structName fieldName |
    throwError "{structName} doesn't have field {fieldName}"
  return mkAppN (.const projNa
-/
def mkDirectProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let type ← whnf (← inferType e)
  let .const structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
  let some projName := getProjFnForField? (← getEnv) structName fieldName |
    throwError "{structName} doesn't have field {fieldName}"
  return mkAppN (.const projName us) (type.getAppArgs.push e)

/--
Definition of `mkProjection` / `mkProjection` 的定义

English:
definition mkProjection
  signature: (e : Expr) (fieldName : Name)
  body: do
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPath

中文:
定义 mkProjection
  签名: (e : Expr) (fieldName : Name)
  定义体: do
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPath
-/
def mkProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPathToBaseStructure? (← getEnv) baseStruct structName).get! do
    let type ← whnf (← inferType e)
    let .const _structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
    e := mkAppN (.const projName us) (type.getAppArgs.push e)
  mkDirectProjection e fieldName

/--
Definition of `reduceProjStruct?` / `reduceProjStruct?` 的定义

English:
definition reduceProjStruct?
  signature: (e : Expr)
  body: do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numPa

中文:
定义 reduceProjStruct?
  签名: (e : Expr)
  定义体: do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numPa
-/
def reduceProjStruct? (e : Expr) : MetaM (Option Expr) := do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
    -- Check that the structure is a constructor expression.
    unless sarg.getAppFn.isConstOf pinfo.ctorName do
      return none
    let sfields := sarg.getAppArgs
    -- The ith projection extracts the ith field of the constructor
    let sidx := pinfo.numParams + pinfo.i
    if hs : sidx < sfields.size then
      return some (sfields[sidx]'hs)
    else
      throwError m!"ill-formed expression, {cname} is the {pinfo.i + 1}-th projection function \
        but {sarg} does not have enough arguments"
  else
    return none

/-- Returns true if `e` contains a name `n` where `p n` is true. -/
@[specialize]
/--
Definition of `containsConst` / `containsConst` 的定义

English:
definition containsConst
  signature: (e : Expr) (p : Name -> Bool)
  body: Option.isSome e.find? fun | .const n _ => p n | _ => false

中文:
定义 containsConst
  签名: (e : Expr) (p : Name -> 布尔)
  定义体: Option.isSome e.find? fun | .const n _ => p n | _ => false

Depends on / 依赖: Option.isSome, e.find, isSome
-/
def containsConst (e : Expr) (p : Name -> Bool) : Bool :=
Option.isSome e.find? fun | .const n _ => p n | _ => false

/--
Definition of `forallNot_of_notExists` / `forallNot_of_notExists` 的定义

English:
definition forallNot_of_notExists
  signature: (ex hNotEx : Expr)
  body: do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  go lvl A p hNotEx

中文:
定义 forallNot_of_notExists
  签名: (ex hNotEx : Expr)
  定义体: do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  go lvl A p hNotEx
-/
partial def forallNot_of_notExists (ex hNotEx : Expr) : MetaM (Expr × Expr) := do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  go lvl A p hNotEx
where
  /-- Given `(hNotEx : Not (@Exists.{lvl} A p))`,
      return a `forall x, Not (p x)` and a proof for it.

      This function handles nested existentials. -/
  go (lvl : Level) (A p hNotEx : Expr) : MetaM (Expr × Expr) := do
    let xn ← mkFreshUserName `x
    withLocalDeclD xn A fun x => do
      let px := p.beta #[x]
      let notPx := mkNot px
      let hAllNotPx := mkApp3 (.const ``forall_not_of_not_exists [lvl]) A p hNotEx
      if let .app (.app (.const ``Exists [lvl']) A') p' := px then
        let hNotPxN ← mkFreshUserName `h
        withLocalDeclD hNotPxN notPx fun hNotPx => do
          let (qx, hQx) ← go lvl' A' p' hNotPx
          let allQx ← mkForallFVars #[x] qx
          let hNotPxImpQx ← mkLambdaFVars #[hNotPx] hQx
          let hAllQx ← mkLambdaFVars #[x] (.app hNotPxImpQx (.app hAllNotPx x))
          return (allQx, hAllQx)
      else
        let allNotPx ← mkForallFVars #[x] notPx
        return (allNotPx, hAllNotPx)

end Expr

/--
Definition of `getFieldsToParents` / `getFieldsToParents` 的定义

English:
definition getFieldsToParents
  signature: (env : Environment) (structName : Name)
  body: .filter fun fieldName => getStructureFields env structName
.isSome isSubobjectField? env structName fieldName

中文:
定义 getFieldsToParents
  签名: (env : Environment) (structName : Name)
  定义体: .filter fun fieldName => getStructureFields env structName
.isSome isSubobjectField? env structName fieldName

Depends on / 依赖: fieldName, filter, getStructureFields, isSome, isSubobjectField, structName
-/
def getFieldsToParents (env : Environment) (structName : Name) : Array Name :=
.filter fun fieldName => getStructureFields env structName
.isSome isSubobjectField? env structName fieldName

end Lean
