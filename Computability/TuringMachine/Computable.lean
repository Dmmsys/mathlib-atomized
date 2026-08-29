/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in `StackTuringMachine.lean`), a definition of when a TM gives
a certain output (in a certain time), and the definition of computability (in polynomial time or
any time function) of a function between two types that have an encoding (as in `Encoding.lean`).

## Main theorems

- `idComputableInPolyTime` : a TM + a proof it computes the identity on a type in polytime.
- `idComputable` : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type `Stmt`); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, and so on).
However, as functions only contain a finite number of executions and each one is executed at most
once, this execution time is up to multiplication by a constant the amount of fundamental steps.
-/

@[expose] public section



open Computability StateTransition


namespace Turing

/--
Definition of `FinTM2` / `FinTM2` 的定义

English:
structure FinTM2
  parameters: where
  axioms and operations (12):
    - {K : Type} [kDecidableEq : DecidableEq K]
    - [kFin : Fintype K]
    - (k₀(k₁) : K)
    - (Γ : K -> Type)
    - (Λ : Type)
    - (main : Λ)
    - [ΛFin : Fintype Λ]
    - (σ : Type)
    - (initialState : σ)
    - [σFin : Fintype σ]
    - [Γk₀Fin : Fintype (Γ k₀)]
    - (m : Λ -> Turing.TM2.Stmt Γ Λ σ)

中文:
结构 FinTM2
  参数: where
  公理与运算 (12 个):
    - {K : 类型} [kDecidableEq : DecidableEq K]
    - [kFin : 有限类型 K]
    - (k₀(k₁) : K)
    - (Γ : K -> 类型)
    - (Λ : 类型)
    - (main : Λ)
    - [ΛFin : 有限类型 Λ]
    - (σ : 类型)
    - (initialState : σ)
    - [σFin : 有限类型 σ]
    - [Γk₀Fin : 有限类型 (Γ k₀)]
    - (m : Λ -> Turing.TM2.Stmt Γ Λ σ)
-/
structure FinTM2 where
  /-- index type of stacks -/
  {K : Type} [kDecidableEq : DecidableEq K]
  /-- A TM2 machine has finitely many stacks. -/
  [kFin : Fintype K]
  /-- input resp. output stack -/
  (k₀ k₁ : K)
  /-- type of stack elements -/
  (Γ : K -> Type)
  /-- type of function labels -/
  (Λ : Type)
  /-- a main function: the initial function that is executed, given by its label -/
  (main : Λ)
  /-- A TM2 machine has finitely many function labels. -/
  [ΛFin : Fintype Λ]
  /-- type of states of the machine -/
  (σ : Type)
  /-- the initial state of the machine -/
  (initialState : σ)
  /-- a TM2 machine has finitely many internal states. -/
  [σFin : Fintype σ]
  /-- Each internal stack is finite. -/
  [Γk₀Fin : Fintype (Γ k₀)]
  /-- the program itself, i.e. one function for every function label -/
  (m : Λ -> Turing.TM2.Stmt Γ Λ σ)

attribute [nolint docBlame] FinTM2.kDecidableEq

namespace FinTM2

section

variable (tm : FinTM2)

/--
Instance `decidableEqK` / 实例 `decidableEqK`

English:
instance decidableEqK
  signature: : DecidableEq tm.K
  body: tm.kDecidableEq

中文:
实例 decidableEqK
  签名: : DecidableEq tm.K
  定义体: tm.kDecidableEq

Depends on / 依赖: kDecidableEq, tm.kDecidableEq
-/
instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq

/--
Instance `inhabitedσ` / 实例 `inhabitedσ`

English:
instance inhabitedσ
  signature: : Inhabited tm.σ
  body: ⟨tm.initialState⟩

中文:
实例 inhabitedσ
  签名: : 可居 tm.σ
  定义体: ⟨tm.initialState⟩

Depends on / 依赖: initialState, tm.initialState
-/
instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/--
Definition of `Stmt` / `Stmt` 的定义

English:
definition Stmt
  signature: : Type
  body: Turing.TM2.Stmt tm.Γ tm.Λ tm.σ

中文:
定义 Stmt
  签名: : 类型
  定义体: Turing.TM2.Stmt tm.Γ tm.Λ tm.σ

Depends on / 依赖: Turing, Turing.TM2.Stmt
-/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ

/--
Instance `inhabitedStmt` / 实例 `inhabitedStmt`

English:
instance inhabitedStmt
  signature: : Inhabited (Stmt tm)
  body: inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

中文:
实例 inhabitedStmt
  签名: : 可居 (Stmt tm)
  定义体: inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

Depends on / 依赖: Inhabited, Turing, Turing.TM2.Stmt
-/
instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

/--
Definition of `Cfg` / `Cfg` 的定义

English:
definition Cfg
  signature: : Type
  body: Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

中文:
定义 Cfg
  签名: : 类型
  定义体: Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

Depends on / 依赖: Turing, Turing.TM2.Cfg
-/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

/--
Instance `inhabitedCfg` / 实例 `inhabitedCfg`

English:
instance inhabitedCfg
  signature: : Inhabited (Cfg tm)
  body: Turing.TM2.Cfg.inhabited _ _ _

中文:
实例 inhabitedCfg
  签名: : 可居 (Cfg tm)
  定义体: Turing.TM2.Cfg.inhabited _ _ _

Depends on / 依赖: Turing, Turing.TM2.Cfg.inhabited, inhabited
-/
instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
/--
Definition of `step` / `step` 的定义

English:
definition step
  signature: : tm.Cfg -> Option tm.Cfg
  body: Turing.TM2.step tm.m

中文:
定义 step
  签名: : tm.Cfg -> 选项类型 tm.Cfg
  定义体: Turing.TM2.step tm.m

Depends on / 依赖: Turing, Turing.TM2.step, tm.m
-/
def step : tm.Cfg -> Option tm.Cfg :=
  Turing.TM2.step tm.m

end

end FinTM2

/--
Definition of `initList` / `initList` 的定义

English:
definition initList
  signature: (tm : FinTM2) (s : List (tm.Γ tm.k₀))
  body: Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []

中文:
定义 initList
  签名: (tm : FinTM2) (s : 列表 (tm.Γ tm.k₀))
  定义体: Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []

Depends on / 依赖: Option.some, tm.main
-/
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []

/--
Definition of `haltList` / `haltList` 的定义

English:
definition haltList
  signature: (tm : FinTM2) (s : List (tm.Γ tm.k₁))
  body: Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []

@[deprecated (since := "2026-03-06")] protected alias EvalsTo :=
  StateTransition.EvalsTo
@[deprecated (since := "2026-03-06")] protected alias EvalsToInTime :=
  StateTransition.EvalsToInTime

中文:
定义 haltList
  签名: (tm : FinTM2) (s : 列表 (tm.Γ tm.k₁))
  定义体: Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []

@[deprecated (since := "2026-03-06")] protected alias EvalsTo :=
  StateTransition.EvalsTo
@[deprecated (since := "2026-03-06")] protected alias EvalsToInTime :=
  StateTransition.EvalsToInTime

Depends on / 依赖: Option.none
-/
def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []

@[deprecated (since := "2026-03-06")] protected alias EvalsTo :=
  StateTransition.EvalsTo
@[deprecated (since := "2026-03-06")] protected alias EvalsToInTime :=
  StateTransition.EvalsToInTime

/--
Definition of `TM2Outputs` / `TM2Outputs` 的定义

English:
definition TM2Outputs
  signature: (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
  body: EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

中文:
定义 TM2Outputs
  签名: (tm : FinTM2) (l : 列表 (tm.Γ tm.k₀)) (l' : 选项类型 (列表 (tm.Γ tm.k₁)))
  定义体: EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

Depends on / 依赖: EvalsTo, Option.map, haltList, initList, tm.step
-/
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/--
Definition of `TM2OutputsInTime` / `TM2OutputsInTime` 的定义

English:
definition TM2OutputsInTime
  signature: (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
  body: EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

中文:
定义 TM2OutputsInTime
  签名: (tm : FinTM2) (l : 列表 (tm.Γ tm.k₀)) (l' : 选项类型 (列表 (tm.Γ tm.k₁)))
  定义体: EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

Depends on / 依赖: EvalsToInTime, Option.map, haltList, initList, tm.step
-/
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : Nat) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/--
Definition of `TM2OutputsInTime.toTM2Outputs` / `TM2OutputsInTime.toTM2Outputs` 的定义

English:
definition TM2OutputsInTime.toTM2Outputs
  signature: {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
  body: h.toEvalsTo

中文:
定义 TM2OutputsInTime.toTM2Outputs
  签名: {tm : FinTM2} {l : 列表 (tm.Γ tm.k₀)}
  定义体: h.toEvalsTo

Depends on / 依赖: h.toEvalsTo, toEvalsTo
-/
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : Nat} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo

/--
Definition of `TM2ComputableAux` / `TM2ComputableAux` 的定义

English:
structure TM2ComputableAux
  parameters: (Γ₀ Γ₁ : Type)
  axioms and operations (3):
    - tm : FinTM2
    - inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
    - outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

中文:
结构 TM2ComputableAux
  参数: (Γ₀ Γ₁ : 类型)
  公理与运算 (3 个):
    - tm : FinTM2
    - inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
    - outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁
-/
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  /-- the underlying bundled TM2 -/
  tm : FinTM2
  /-- the input alphabet is equivalent to `Γ₀` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  /-- the output alphabet is equivalent to `Γ₁` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/--
Definition of `TM2Computable` / `TM2Computable` 的定义

English:
structure TM2Computable
  parameters: {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ) (f : α -> β)
  axioms and operations (1):
    - outputsFun : forall a, TM2Outputs tm (List.map inputAlphabet.invFun (ea a)) (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))

中文:
结构 TM2Computable
  参数: {α β αΓ βΓ : 类型} (ea : α -> 列表 αΓ) (eb : β -> 列表 βΓ) (f : α -> β)
  公理与运算 (1 个):
    - outputsFun : 对任意 a, TM2Outputs tm (列表.map inputAlphabet.invFun (ea a)) (选项类型.some ((列表.map outputAlphabet.invFun) (eb (f a))))
-/
structure TM2Computable {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ) (f : α -> β) extends
  TM2ComputableAux αΓ βΓ where
  /-- a proof this machine outputs `f` -/
  outputsFun :
    forall a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))

/--
Definition of `TM2ComputableInTime` / `TM2ComputableInTime` 的定义

English:
structure TM2ComputableInTime
  parameters: {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ)
  extends: TM2ComputableAux αΓ βΓ
  axioms and operations (2):
    - time : Nat -> Nat
    - outputsFun : forall a, TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a)) (Option.some ((List.map outputAlphabet.invFun) (eb (f a)))) (time (ea a).length)

中文:
结构 TM2ComputableInTime
  参数: {α β αΓ βΓ : 类型} (ea : α -> 列表 αΓ) (eb : β -> 列表 βΓ)
  继承: TM2ComputableAux αΓ βΓ
  公理与运算 (2 个):
    - time : 自然数 -> 自然数
    - outputsFun : 对任意 a, TM2OutputsInTime tm (列表.map inputAlphabet.invFun (ea a)) (选项类型.some ((列表.map outputAlphabet.invFun) (eb (f a)))) (time (ea a).length)
-/
structure TM2ComputableInTime {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ)
  (f : α -> β) extends TM2ComputableAux αΓ βΓ where
  /-- a time function -/
  time : Nat -> Nat
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    forall a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time (ea a).length)

/--
Definition of `TM2ComputableInPolyTime` / `TM2ComputableInPolyTime` 的定义

English:
structure TM2ComputableInPolyTime
  parameters: {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ)
  extends: TM2ComputableAux αΓ βΓ
  axioms and operations (2):
    - time : Polynomial Nat
    - outputsFun : forall a, TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a)) (Option.some ((List.map outputAlphabet.invFun) (eb (f a)))) (time.eval (ea a).length)

中文:
结构 TM2ComputableInPolyTime
  参数: {α β αΓ βΓ : 类型} (ea : α -> 列表 αΓ) (eb : β -> 列表 βΓ)
  继承: TM2ComputableAux αΓ βΓ
  公理与运算 (2 个):
    - time : 多项式 自然数
    - outputsFun : 对任意 a, TM2OutputsInTime tm (列表.map inputAlphabet.invFun (ea a)) (选项类型.some ((列表.map outputAlphabet.invFun) (eb (f a)))) (time.eval (ea a).length)
-/
structure TM2ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ)
  (f : α -> β) extends TM2ComputableAux αΓ βΓ where
  /-- a polynomial time function -/
  time : Polynomial Nat
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    forall a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time.eval (ea a).length)

/--
Definition of `TM2ComputableInTime.toTM2Computable` / `TM2ComputableInTime.toTM2Computable` 的定义

English:
definition TM2ComputableInTime.toTM2Computable
  signature: {α β αΓ βΓ : Type} {ea : α -> List αΓ} {eb : β -> List βΓ}
  body: ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩

中文:
定义 TM2ComputableInTime.toTM2Computable
  签名: {α β αΓ βΓ : 类型} {ea : α -> 列表 αΓ} {eb : β -> 列表 βΓ}
  定义体: ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩

Depends on / 依赖: TM2OutputsInTime, TM2OutputsInTime.toTM2Outputs, h.outputsFun, h.toTM2ComputableAux, outputsFun, toTM2ComputableAux, toTM2Outputs
-/
def TM2ComputableInTime.toTM2Computable {α β αΓ βΓ : Type} {ea : α -> List αΓ} {eb : β -> List βΓ}
    {f : α -> β} (h : TM2ComputableInTime ea eb f) : TM2Computable ea eb f :=
  ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩

/--
Definition of `TM2ComputableInPolyTime.toTM2ComputableInTime` / `TM2ComputableInPolyTime.toTM2ComputableInTime` 的定义

English:
definition TM2ComputableInPolyTime.toTM2ComputableInTime
  signature: {α β αΓ βΓ : Type} {ea : α -> List αΓ}
  body: ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

中文:
定义 TM2ComputableInPolyTime.toTM2ComputableInTime
  签名: {α β αΓ βΓ : 类型} {ea : α -> 列表 αΓ}
  定义体: ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

Depends on / 依赖: h.outputsFun, h.time.eval, h.toTM2ComputableAux, outputsFun, toTM2ComputableAux
-/
def TM2ComputableInPolyTime.toTM2ComputableInTime {α β αΓ βΓ : Type} {ea : α -> List αΓ}
    {eb : β -> List βΓ} {f : α -> β} (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInTime ea eb f :=
  ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM2.Stmt

/--
Definition of `idComputer` / `idComputer` 的定义

English:
definition idComputer
  signature: (αΓ : Type) [Fintype αΓ]
  body: Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := αΓ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  m _ := halt

中文:
定义 idComputer
  签名: (αΓ : 类型) [有限类型 αΓ]
  定义体: Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := αΓ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  m _ := halt
-/
def idComputer (αΓ : Type) [Fintype αΓ] : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := αΓ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  m _ := halt

/--
Instance `inhabitedFinTM2` / 实例 `inhabitedFinTM2`

English:
instance inhabitedFinTM2
  signature: : Inhabited FinTM2
  body: ⟨idComputer Bool⟩

noncomputable section

中文:
实例 inhabitedFinTM2
  签名: : 可居 FinTM2
  定义体: ⟨idComputer Bool⟩

noncomputable section

Depends on / 依赖: idComputer
-/
instance inhabitedFinTM2 : Inhabited FinTM2 :=
  ⟨idComputer Bool⟩

noncomputable section

/--
Definition of `idComputableInPolyTime` / `idComputableInPolyTime` 的定义

English:
definition idComputableInPolyTime
  signature: {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ)
  body: idComputer αΓ
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

中文:
定义 idComputableInPolyTime
  签名: {α αΓ : 类型} [有限类型 αΓ] (ea : α -> 列表 αΓ)
  定义体: idComputer αΓ
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

Depends on / 依赖: idComputer
-/
def idComputableInPolyTime {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) :
    @TM2ComputableInPolyTime α α αΓ αΓ ea ea id where
  tm := idComputer αΓ
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

/--
Instance `inhabitedTM2ComputableInPolyTime` / 实例 `inhabitedTM2ComputableInPolyTime`

English:
instance inhabitedTM2ComputableInPolyTime
  signature: :
  body: ⟨idComputableInPolyTime encodeBool⟩

中文:
实例 inhabitedTM2ComputableInPolyTime
  签名: :
  定义体: ⟨idComputableInPolyTime encodeBool⟩

Depends on / 依赖: encodeBool, idComputableInPolyTime
-/
instance inhabitedTM2ComputableInPolyTime :
    Inhabited (TM2ComputableInPolyTime encodeBool encodeBool id) :=
  ⟨idComputableInPolyTime encodeBool⟩

/--
Instance `inhabitedTM2OutputsInTime` / 实例 `inhabitedTM2OutputsInTime`

English:
instance inhabitedTM2OutputsInTime
  signature: :
  body: ⟨(idComputableInPolyTime encodeBool).outputsFun false⟩

中文:
实例 inhabitedTM2OutputsInTime
  签名: :
  定义体: ⟨(idComputableInPolyTime encodeBool).outputsFun false⟩

Depends on / 依赖: encodeBool, idComputableInPolyTime, outputsFun
-/
instance inhabitedTM2OutputsInTime :
    Inhabited
      (TM2OutputsInTime (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
  ⟨(idComputableInPolyTime encodeBool).outputsFun false⟩

/--
Instance `inhabitedTM2Outputs` / 实例 `inhabitedTM2Outputs`

English:
instance inhabitedTM2Outputs
  signature: :
  body: ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩

中文:
实例 inhabitedTM2Outputs
  签名: :
  定义体: ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩

Depends on / 依赖: TM2OutputsInTime, TM2OutputsInTime.toTM2Outputs, Turing, Turing.inhabitedTM2OutputsInTime.default, inhabitedTM2OutputsInTime, toTM2Outputs
-/
instance inhabitedTM2Outputs :
    Inhabited
      (TM2Outputs (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩

/--
Instance `inhabitedEvalsToInTime` / 实例 `inhabitedEvalsToInTime`

English:
instance inhabitedEvalsToInTime
  signature: :
  body: ⟨EvalsToInTime.refl _ _⟩

中文:
实例 inhabitedEvalsToInTime
  签名: :
  定义体: ⟨EvalsToInTime.refl _ _⟩

Depends on / 依赖: EvalsToInTime, EvalsToInTime.refl
-/
instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩

/--
Instance `inhabitedTM2EvalsTo` / 实例 `inhabitedTM2EvalsTo`

English:
instance inhabitedTM2EvalsTo
  signature: : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩))
  body: ⟨EvalsTo.refl _ _⟩

中文:
实例 inhabitedTM2EvalsTo
  签名: : 可居 (EvalsTo (fun _ : 单元 => some ⟨⟩) ⟨⟩ (some ⟨⟩))
  定义体: ⟨EvalsTo.refl _ _⟩

Depends on / 依赖: EvalsTo, EvalsTo.refl
-/
instance inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩

/--
Definition of `idComputableInTime` / `idComputableInTime` 的定义

English:
definition idComputableInTime
  signature: {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ)
  body: TM2ComputableInPolyTime.toTM2ComputableInTime idComputableInPolyTime ea

中文:
定义 idComputableInTime
  签名: {α αΓ : 类型} [有限类型 αΓ] (ea : α -> 列表 αΓ)
  定义体: TM2ComputableInPolyTime.toTM2ComputableInTime idComputableInPolyTime ea

Depends on / 依赖: TM2ComputableInPolyTime, TM2ComputableInPolyTime.toTM2ComputableInTime, idComputableInPolyTime, toTM2ComputableInTime
-/
def idComputableInTime {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) :
    @TM2ComputableInTime α α αΓ αΓ ea ea id :=
TM2ComputableInPolyTime.toTM2ComputableInTime idComputableInPolyTime ea

/--
Instance `inhabitedTM2ComputableInTime` / 实例 `inhabitedTM2ComputableInTime`

English:
instance inhabitedTM2ComputableInTime
  signature: :
  body: ⟨idComputableInTime encodeBool⟩

中文:
实例 inhabitedTM2ComputableInTime
  签名: :
  定义体: ⟨idComputableInTime encodeBool⟩

Depends on / 依赖: encodeBool, idComputableInTime
-/
instance inhabitedTM2ComputableInTime :
    Inhabited (TM2ComputableInTime encodeBool encodeBool id) :=
  ⟨idComputableInTime encodeBool⟩

/--
Definition of `idComputable` / `idComputable` 的定义

English:
definition idComputable
  signature: {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ)
  body: TM2ComputableInTime.toTM2Computable idComputableInTime ea

中文:
定义 idComputable
  签名: {α αΓ : 类型} [有限类型 αΓ] (ea : α -> 列表 αΓ)
  定义体: TM2ComputableInTime.toTM2Computable idComputableInTime ea

Depends on / 依赖: TM2ComputableInTime, TM2ComputableInTime.toTM2Computable, idComputableInTime, toTM2Computable
-/
def idComputable {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) :
    @TM2Computable α α αΓ αΓ ea ea id :=
TM2ComputableInTime.toTM2Computable idComputableInTime ea

/--
Instance `inhabitedTM2Computable` / 实例 `inhabitedTM2Computable`

English:
instance inhabitedTM2Computable
  signature: :
  body: ⟨idComputable encodeBool⟩

中文:
实例 inhabitedTM2Computable
  签名: :
  定义体: ⟨idComputable encodeBool⟩

Depends on / 依赖: encodeBool, idComputable
-/
instance inhabitedTM2Computable :
    Inhabited (TM2Computable encodeBool encodeBool id) :=
  ⟨idComputable encodeBool⟩

/--
Instance `inhabitedTM2ComputableAux` / 实例 `inhabitedTM2ComputableAux`

English:
instance inhabitedTM2ComputableAux
  signature: : Inhabited (TM2ComputableAux Bool Bool)
  body: ⟨(default : TM2Computable encodeBool encodeBool id).toTM2ComputableAux⟩

中文:
实例 inhabitedTM2ComputableAux
  签名: : 可居 (TM2ComputableAux 布尔值 布尔值)
  定义体: ⟨(default : TM2Computable encodeBool encodeBool id).toTM2ComputableAux⟩

Depends on / 依赖: TM2Computable, encodeBool, toTM2ComputableAux
-/
instance inhabitedTM2ComputableAux : Inhabited (TM2ComputableAux Bool Bool) :=
  ⟨(default : TM2Computable encodeBool encodeBool id).toTM2ComputableAux⟩

/--
For any two polynomial time Multi-tape Turing Machines,
there exists another polynomial time multi-tape Turing Machine that composes their operations.
This machine can work by simply having one tape for each tape in both of the composed TMs.
It first carries out the operations of the first TM on the tapes associated with the first TM,
then copies the output tape of the first TM to the input tape of the second TM,
then runs the second TM.
-/
proof_wanted TM2ComputableInPolyTime.comp
    {α β γ αΓ βΓ γΓ : Type} {eα : α -> List αΓ} {eβ : β -> List βΓ}
    {eγ : γ -> List γΓ} {f : α -> β} {g : β -> γ} (h1 : TM2ComputableInPolyTime eα eβ f)
    (h2 : TM2ComputableInPolyTime eβ eγ g) :
  Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))

end

end Turing
