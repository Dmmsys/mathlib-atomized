/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Meta.Transform
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util -- shake: keep (???)
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing
import Aesop.BuiltinRules

/-!
# `Encodable` deriving handler

Adds a deriving handler for the `Encodable` class.

The resulting `Encodable` instance should be considered to be opaque.
The specific encoding used is an implementation detail.
-/

public section

namespace Mathlib.Deriving.Encodable
open Lean Parser.Term Elab Deriving Meta


/--
Inductive type `S` / 归纳类型 `S`

English:
inductive S
  parameters: : Type where
  constructors (2):
    - nat: (n : Nat)
    - cons: (a b : S)

中文:
归纳类型 S
  参数: : 类型 where
  构造子 (2 个):
    - nat: (n : 自然数)
    - cons: (a b : S)
-/
private inductive S : Type where
  | nat (n : Nat)
  | cons (a b : S)

/--
Definition of `S.encode` / `S.encode` 的定义

English:
definition S.encode
  signature: : S -> Nat

中文:
定义 S.encode
  签名: : S -> 自然数
-/
private def S.encode : S -> Nat
  | nat n => Nat.pair 0 n
  | cons a b => Nat.pair (S.encode a + 1) (S.encode b)

/--
lemma `nat_unpair_lt_2` / 引理 `nat_unpair_lt_2`

English:
lemma nat_unpair_lt_2
  given: {n : Nat} (h : (Nat.unpair n).1 != 0)
  statement: (Nat.unpair n).2 < n
  proof: by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have := Nat.le_mul_self a
  have := Nat.le_mul_self b
  split <;> lia

中文:
引理 nat_unpair_lt_2
  条件: {n : 自然数} (h : (自然数.unpair n).1 != 0)
  结论: (自然数.unpair n).2 < n
  证明: by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have := Nat.le_mul_self a
  have := Nat.le_mul_self b
  split <;> lia
-/
private lemma nat_unpair_lt_2 {n : Nat} (h : (Nat.unpair n).1 != 0) : (Nat.unpair n).2 < n := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have := Nat.le_mul_self a
  have := Nat.le_mul_self b
  split <;> lia

/--
Definition of `S.decode` / `S.decode` 的定义

English:
definition S.decode
  signature: (n : Nat)
  body: let p := Nat.unpair n
  if h : p.1 = 0 then
    S.nat p.2
  else
    have : p.1 <= n := Nat.unpair_left_le n
    have := Nat.unpair_lt (by lia : 1 <= n)
    have := nat_unpair_lt_2 h
    S.cons (S.decode (p.1 - 1)) (S.decode p.2)

中文:
定义 S.decode
  签名: (n : 自然数)
  定义体: let p := Nat.unpair n
  if h : p.1 = 0 then
    S.nat p.2
  else
    have : p.1 <= n := Nat.unpair_left_le n
    have := Nat.unpair_lt (by lia : 1 <= n)
    have := nat_unpair_lt_2 h
    S.cons (S.decode (p.1 - 1)) (S.decode p.2)
-/
private def S.decode (n : Nat) : S :=
  let p := Nat.unpair n
  if h : p.1 = 0 then
    S.nat p.2
  else
    have : p.1 <= n := Nat.unpair_left_le n
    have := Nat.unpair_lt (by lia : 1 <= n)
    have := nat_unpair_lt_2 h
    S.cons (S.decode (p.1 - 1)) (S.decode p.2)

/--
Definition of `S_equiv` / `S_equiv` 的定义

English:
definition S_equiv
  signature: : S ≃ Nat where
  body: S.encode
  invFun := S.decode
  left_inv s := by
    induction s with
    | nat n =>
      unfold S.encode S.decode
      simp
    | cons a b iha ihb =>
      unfold S.encode S.decode
      simp [iha, ihb]
  right_inv n := by -- The fact it's a right inverse isn't needed for the deriving handler.
    induction n using Nat.strongRecOn with | _ n ih =>
    unfold S.decode
    dsimp only
    split
    next h =>
      unfold S.encode
      rw [← h]; rw [Nat.pair_unpair]
    next h =>
      unfold S.encode
      rw [ih]; rw [ih]; rw [Nat.sub_add_cancel]; rw [Nat.pair_unpair]
      · rwa [Nat.one_le_iff_ne_zero]
      · exact nat_unpair_lt_2 h
      · obtain _ | n' := n
        · exact False.elim (h (by simp))
        · have := Nat.unpair_lt (by lia : 1 <= n' + 1)
          lia

中文:
定义 S_equiv
  签名: : S ≃ 自然数 where
  定义体: S.encode
  invFun := S.decode
  left_inv s := by
    induction s with
    | nat n =>
      unfold S.encode S.decode
      simp
    | cons a b iha ihb =>
      unfold S.encode S.decode
      simp [iha, ihb]
  right_inv n := by -- The fact it's a right inverse isn't needed for the deriving handler.
    induction n using Nat.strongRecOn with | _ n ih =>
    unfold S.decode
    dsimp only
    split
    next h =>
      unfold S.encode
      rw [← h]; rw [Nat.pair_unpair]
    next h =>
      unfold S.encode
      rw [ih]; rw [ih]; rw [Nat.sub_add_cancel]; rw [Nat.pair_unpair]
      · rwa [Nat.one_le_iff_ne_zero]
      · exact nat_unpair_lt_2 h
      · obtain _ | n' := n
        · exact False.elim (h (by simp))
        · have := Nat.unpair_lt (by lia : 1 <= n' + 1)
          lia
-/
private def S_equiv : S ≃ Nat where
  toFun := S.encode
  invFun := S.decode
  left_inv s := by
    induction s with
    | nat n =>
      unfold S.encode S.decode
      simp
    | cons a b iha ihb =>
      unfold S.encode S.decode
      simp [iha, ihb]
  right_inv n := by -- The fact it's a right inverse isn't needed for the deriving handler.
    induction n using Nat.strongRecOn with | _ n ih =>
    unfold S.decode
    dsimp only
    split
    next h =>
      unfold S.encode
      rw [← h]; rw [Nat.pair_unpair]
    next h =>
      unfold S.encode
      rw [ih]; rw [ih]; rw [Nat.sub_add_cancel]; rw [Nat.pair_unpair]
      · rwa [Nat.one_le_iff_ne_zero]
      · exact nat_unpair_lt_2 h
      · obtain _ | n' := n
        · exact False.elim (h (by simp))
        · have := Nat.unpair_lt (by lia : 1 <= n' + 1)
          lia

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Encodable S
  body: Encodable.ofEquiv Nat S_equiv

public meta section

中文:
实例 :
  签名: 可编码 S
  定义体: Encodable.ofEquiv Nat S_equiv

public meta section
-/
private instance : Encodable S := Encodable.ofEquiv Nat S_equiv

public meta section

/-!
### Implementation
-/


/--
Definition of `mkToSMatch` / `mkToSMatch` 的定义

English:
definition mkToSMatch
  signature: (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal)
  body: do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)

中文:
定义 mkToSMatch
  签名: (ctx : Deriving.余ntext) (header : Header) (indVal : InductiveVal)
  定义体: do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
-/
private def mkToSMatch (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal)
    (toSNames : Array Name) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
alts := alts.push ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        let mut ctorArgs := #[]
        let mut rhsArgs : Array Term := #[]
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        for _ in [:ctorInfo.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          let x := xs[ctorInfo.numParams + i]!
          let xTy ← inferType x
.map (toSNames[·]!) let recName? := ctx.typeInfos.findIdx? (xTy.isAppOf ·.name)
rhsArgs := rhsArgs.push ←
            if let some recName := recName? then
              `($(mkIdent recName) $a)
            else
              ``(S.nat (Encodable.encode $a))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let rhs' : Term ← rhsArgs.foldrM (init := ← ``(S.nat 0)) fun arg acc => ``(S.cons $arg $acc)
        let rhs : Term ← ``(S.cons (S.nat $(quote ctorInfo.cidx)) $rhs')
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
    return alts

/--
Definition of `mkToSFuns` / `mkToSFuns` 的定义

English:
definition mkToSFuns
  signature: (ctx : Deriving.Context) (toSFunNames : Array Name)
  body: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toNatFnName := toSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkToSMatch ctx header indVal toSFunNames
res := res.push ← `(

中文:
定义 mkToSFuns
  签名: (ctx : Deriving.余ntext) (toSFunNames : 数组 Name)
  定义体: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toNatFnName := toSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkToSMatch ctx header indVal toSFunNames
res := res.push ← `(
-/
private def mkToSFuns (ctx : Deriving.Context) (toSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toNatFnName := toSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkToSMatch ctx header indVal toSFunNames
res := res.push ← `(
private def (mkIdent toNatFnName):ident header.binders:bracketedBinder* :
 (mkCIdent ``S) := body:term
      )
  `(command| mutual $[$res:command]* end)


/--
Definition of `mkFromSMatch` / `mkFromSMatch` 的定义

English:
definition mkFromSMatch
  signature: (ctx : Deriving.Context) (indVal : InductiveVal)
  body: do
  let alts ← mkAlts
  `(fun $alts:matchAlt*)

中文:
定义 mkFromSMatch
  签名: (ctx : Deriving.余ntext) (indVal : InductiveVal)
  定义体: do
  let alts ← mkAlts
  `(fun $alts:matchAlt*)
-/
private def mkFromSMatch (ctx : Deriving.Context) (indVal : InductiveVal)
    (fromSNames : Array Name) : TermElabM Term := do
  let alts ← mkAlts
  `(fun $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
alts := alts.push ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patternArgs : Array Term := #[]
        let mut discrs : Array (TSyntax ``Lean.Parser.Term.matchDiscr) := #[]
        let mut ctorArgs : Array Term := #[]
        let mut patternArgs2 : Array Term := #[]
        let mut patternArgs3 : Array Term := #[]
        for _ in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          let x := xs[ctorInfo.numParams + i]!
          let xTy ← inferType x
.map (fromSNames[·]!) let recName? := ctx.typeInfos.findIdx? (xTy.isAppOf ·.name)
          if let some recName := recName? then
            patternArgs := patternArgs.push a
discrs := discrs.push ← `(matchDiscr| $(mkIdent recName) $a)
          else
patternArgs := patternArgs.push ← ``(S.nat $a)
discrs := discrs.push ← `(matchDiscr| $(mkCIdent ``Encodable.decode) $a)
          ctorArgs := ctorArgs.push a
patternArgs2 := patternArgs2.push ← ``(some $a)
patternArgs3 := patternArgs3.push ← `(_)
        let pattern ← patternArgs.foldrM (init := ← ``(S.nat 0)) fun arg acc => ``(S.cons $arg $acc)
        let pattern ← ``(S.cons (S.nat $(quote ctorInfo.cidx)) $pattern)
        -- Note: this is where we could try to handle indexed types.
        -- The idea would be to use DecidableEq to test the computed index against the expected
        -- index and then rewrite.
        let res ← ``(some <| @$(mkIdent ctorName):ident $ctorArgs:term*)
        if discrs.isEmpty then
          `(matchAltExpr| | $pattern:term => $res)
        else
          let rhs : Term ← `(
match [$discrs],* with
| [$patternArgs2],* => res
| [$patternArgs3],* => none
            )
          `(matchAltExpr| | $pattern:term => $rhs)
alts := alts.push ← `(matchAltExpr| | _ => none)
    return alts

/--
Definition of `mkFromSFuns` / `mkFromSFuns` 的定义

English:
definition mkFromSFuns
  signature: (ctx : Deriving.Context) (fromSFunNames : Array Name)
  body: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:fromSFunNames.size] do
    let fromNatFnName := fromSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkFromSMatch ctx indVal fromSFunNames
    -- Last binder is for the target
    let binders := header.binders[0:header.binders.size - 1]
res := res.push ← `(

中文:
定义 mkFromSFuns
  签名: (ctx : Deriving.余ntext) (fromSFunNames : 数组 Name)
  定义体: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:fromSFunNames.size] do
    let fromNatFnName := fromSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkFromSMatch ctx indVal fromSFunNames
    -- Last binder is for the target
    let binders := header.binders[0:header.binders.size - 1]
res := res.push ← `(
-/
private def mkFromSFuns (ctx : Deriving.Context) (fromSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:fromSFunNames.size] do
    let fromNatFnName := fromSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkFromSMatch ctx indVal fromSFunNames
    -- Last binder is for the target
    let binders := header.binders[0:header.binders.size - 1]
res := res.push ← `(
private def (mkIdent fromNatFnName):ident binders:bracketedBinder* :
 (mkCIdent ``S) -> Option header.targetType := body:term
      )
  `(command| mutual $[$res:command]* end)

/-!
Constructing the proofs that the `fromS` functions are left inverses of the `toS` functions.
-/

/--
Definition of `mkInjThms` / `mkInjThms` 的定义

English:
definition mkInjThms
  signature: (ctx : Deriving.Context) (toSFunNames fromSFunNames : Array Name)
  body: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toSFunName := toSFunNames[i]!
    let fromSFunName := fromSFunNames[i]!
    let injThmName := ctx.auxFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let enc := mkIdent toSFunName
    let dec := mkIdent fromSFunName
    let t := mkIdent header.targetNames[0]!
    let lemmas : TSyntaxArray ``Parser.Tactic.simpLemma ← ctx.auxFunNames.mapM fun i =>
      `(Parser.Tactic.simpLemma| $(mkIdent i):term)
    let tactic : Term ← `(by
cases t:ident
        <;> (unfold $(mkIdent toSFunName):ident $(mkIdent fromSFunName):ident;
              simp only [Encodable.encodek, $lemmas,*]; try rfl)
      )
res := res.push ← `(

中文:
定义 mkInjThms
  签名: (ctx : Deriving.余ntext) (toSFunNames fromSFunNames : 数组 Name)
  定义体: do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toSFunName := toSFunNames[i]!
    let fromSFunName := fromSFunNames[i]!
    let injThmName := ctx.auxFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let enc := mkIdent toSFunName
    let dec := mkIdent fromSFunName
    let t := mkIdent header.targetNames[0]!
    let lemmas : TSyntaxArray ``Parser.Tactic.simpLemma ← ctx.auxFunNames.mapM fun i =>
      `(Parser.Tactic.simpLemma| $(mkIdent i):term)
    let tactic : Term ← `(by
cases t:ident
        <;> (unfold $(mkIdent toSFunName):ident $(mkIdent fromSFunName):ident;
              simp only [Encodable.encodek, $lemmas,*]; try rfl)
      )
res := res.push ← `(
-/
private def mkInjThms (ctx : Deriving.Context) (toSFunNames fromSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toSFunName := toSFunNames[i]!
    let fromSFunName := fromSFunNames[i]!
    let injThmName := ctx.auxFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let enc := mkIdent toSFunName
    let dec := mkIdent fromSFunName
    let t := mkIdent header.targetNames[0]!
    let lemmas : TSyntaxArray ``Parser.Tactic.simpLemma ← ctx.auxFunNames.mapM fun i =>
      `(Parser.Tactic.simpLemma| $(mkIdent i):term)
    let tactic : Term ← `(by
cases t:ident
        <;> (unfold $(mkIdent toSFunName):ident $(mkIdent fromSFunName):ident;
              simp only [Encodable.encodek, $lemmas,*]; try rfl)
      )
res := res.push ← `(
private theorem (mkIdent injThmName):ident header.binders:bracketedBinder* :
 dec ($enc $t) = some t := tactic
      )
  `(command| mutual $[$res:command]* end)

/-!
Assembling the `Encodable` instances.
-/

open TSyntax.Compat in
/--
Definition of `mkEncodableInstanceCmds` / `mkEncodableInstanceCmds` 的定义

English:
definition mkEncodableInstanceCmds
  signature: (ctx : Deriving.Context) (typeNames : Array Name)
  body: do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkInstImplicitBinders ``Encodable indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``Encodable) $indType)
      let encode := mkIdent toSFunNames[i]!
      let decode := mkIdent fromSFunNames[i]!
      let kencode := mkIdent auxFunName
      let instCmd ← `(

中文:
定义 mkEncodableInstanceCmds
  签名: (ctx : Deriving.余ntext) (typeNames : 数组 Name)
  定义体: do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkInstImplicitBinders ``Encodable indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``Encodable) $indType)
      let encode := mkIdent toSFunNames[i]!
      let decode := mkIdent fromSFunNames[i]!
      let kencode := mkIdent auxFunName
      let instCmd ← `(
-/
private def mkEncodableInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name)
    (toSFunNames fromSFunNames : Array Name) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkInstImplicitBinders ``Encodable indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``Encodable) $indType)
      let encode := mkIdent toSFunNames[i]!
      let decode := mkIdent fromSFunNames[i]!
      let kencode := mkIdent auxFunName
      let instCmd ← `(
/--
Instance `binders` / 实例 `binders`

English:
instance binders:implicitBinder*
  signature: : type
  body: (mkCIdent ``Encodable.ofLeftInjection) encode decode kencode
        )
      instances := instances.push instCmd
  return instances

中文:
实例 binders:implicitBinder*
  签名: : type
  定义体: (mkCIdent ``Encodable.ofLeftInjection) encode decode kencode
        )
      instances := instances.push instCmd
  return instances

Depends on / 依赖: Encodable, Encodable.ofLeftInjection, decode, encode, instCmd, instances, instances.push, kencode, mkCIdent, ofLeftInjection, return
-/
instance binders:implicitBinder* : type :=
 (mkCIdent ``Encodable.ofLeftInjection) encode decode kencode
        )
      instances := instances.push instCmd
  return instances

/--
Definition of `mkEncodableCmds` / `mkEncodableCmds` 的定义

English:
definition mkEncodableCmds
  signature: (indVal : InductiveVal) (declNames : Array Name)
  body: do
  let ctx ← mkContext ``Encodable "encodable" indVal.name
  let toSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_toS")
  let fromSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_fromS")
  let cmds :=
    #[← mkToSFuns ctx toSFunNames,
      ← mkFromSFuns ctx fromSFunNames,
      ← mkInjThms ctx toSFunNames fromSFunNames]
    ++ (← mkEncodableInstanceCmds ctx declNames toSFunNames fromSFunNames)
  trace[Mathlib.Deriving.encodable] "\n{cmds}"
  return cmds

中文:
定义 mkEncodableCmds
  签名: (indVal : InductiveVal) (declNames : 数组 Name)
  定义体: do
  let ctx ← mkContext ``Encodable "encodable" indVal.name
  let toSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_toS")
  let fromSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_fromS")
  let cmds :=
    #[← mkToSFuns ctx toSFunNames,
      ← mkFromSFuns ctx fromSFunNames,
      ← mkInjThms ctx toSFunNames fromSFunNames]
    ++ (← mkEncodableInstanceCmds ctx declNames toSFunNames fromSFunNames)
  trace[Mathlib.Deriving.encodable] "\n{cmds}"
  return cmds
-/
private def mkEncodableCmds (indVal : InductiveVal) (declNames : Array Name) :
    TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Encodable "encodable" indVal.name
  let toSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_toS")
  let fromSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
mkFreshUserName .str n' (s ++ "_fromS")
  let cmds :=
    #[← mkToSFuns ctx toSFunNames,
      ← mkFromSFuns ctx fromSFunNames,
      ← mkInjThms ctx toSFunNames fromSFunNames]
    ++ (← mkEncodableInstanceCmds ctx declNames toSFunNames fromSFunNames)
  trace[Mathlib.Deriving.encodable] "\n{cmds}"
  return cmds

open Command

/--
Definition of `mkEncodableInstance` / `mkEncodableInstance` 的定义

English:
definition mkEncodableInstance
  signature: (declNames : Array Name)
  body: do
  let mut seen : NameSet := {}
  let mut toVisit : Array InductiveVal := #[]
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isNested || indVal.isReflexive || indVal.numIndices != 0 then
      return false -- not supported yet
    seen := seen.append (NameSet.ofList indVal.all)
    toVisit := toVisit.push indVal
  for indVal in toVisit do
let cmds ← liftTermElabM mkEncodableCmds indVal (declNames.filter indVal.all.contains)
    withEnableInfoTree false do
elabCommand mkNullNode cmds
  return true

中文:
定义 mkEncodableInstance
  签名: (declNames : 数组 Name)
  定义体: do
  let mut seen : NameSet := {}
  let mut toVisit : Array InductiveVal := #[]
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isNested || indVal.isReflexive || indVal.numIndices != 0 then
      return false -- not supported yet
    seen := seen.append (NameSet.ofList indVal.all)
    toVisit := toVisit.push indVal
  for indVal in toVisit do
let cmds ← liftTermElabM mkEncodableCmds indVal (declNames.filter indVal.all.contains)
    withEnableInfoTree false do
elabCommand mkNullNode cmds
  return true

Depends on / 依赖: T0Space, t0Space
-/
def mkEncodableInstance (declNames : Array Name) : CommandElabM Bool := do
  let mut seen : NameSet := {}
  let mut toVisit : Array InductiveVal := #[]
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isNested || indVal.isReflexive || indVal.numIndices != 0 then
      return false -- not supported yet
    seen := seen.append (NameSet.ofList indVal.all)
    toVisit := toVisit.push indVal
  for indVal in toVisit do
let cmds ← liftTermElabM mkEncodableCmds indVal (declNames.filter indVal.all.contains)
    withEnableInfoTree false do
elabCommand mkNullNode cmds
  return true

initialize
  registerDerivingHandler ``Encodable mkEncodableInstance
  registerTraceClass `Mathlib.Deriving.Encodable

end

end Mathlib.Deriving.Encodable
