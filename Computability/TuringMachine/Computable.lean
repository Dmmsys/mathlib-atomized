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
- `idComputable`           : a TM + a proof it computes the identity on a type.

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

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `Turing.TM2` in `StackTuringMachine.lean`), with an input and output stack,
a main function, an initial state and some finiteness guarantees. -/
/-
**Turing.FinTM2** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：Type 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled TM2 (an equivalent of the classical Turing machine, defined starting f
rom
the namespace `Turing.TM2` in `StackTuringMachine.lean`), with an input and outp
ut stack,
a main function, an initial state and some finiteness guarantees.
-/
structure FinTM2 where
  /-- index type of stacks -/
  {K : Type} [kDecidableEq : DecidableEq K]
  /-- A TM2 machine has finitely many stacks. -/
  [kFin : Fintype K]
  /-- input resp. output stack -/
  (k₀ k₁ : K)
  /-- type of stack elements -/
  (Γ : K → Type)
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
  (m : Λ → Turing.TM2.Stmt Γ Λ σ)

attribute [nolint docBlame] FinTM2.kDecidableEq

namespace FinTM2

section

variable (tm : FinTM2)

/-
**Turing.FinTM2.decidableEqK** 是 Mathlib 中的一个实例，位于命名空间 `Turing.FinTM2`。
形式化陈述：decidableEqK : DecidableEq tm.K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq
/-
**Turing.FinTM2.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Turing.FinTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/-- The type of statements (functions) corresponding to this TM. -/
/-
**Turing.FinTM2.Stmt** 是 Mathlib 中的一个定义，位于命名空间 `Turing.FinTM2`。
形式化陈述：Stmt : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of statements (functions) corresponding to this TM.
-/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
/-
**Turing.FinTM2.inhabitedStmt** 是 Mathlib 中的一个实例，位于命名空间 `Turing.FinTM2`。
形式化陈述：inhabitedStmt : Inhabited (Stmt tm)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

/-- The type of configurations (functions) corresponding to this TM. -/
/-
**Turing.FinTM2.Cfg** 是 Mathlib 中的一个定义，位于命名空间 `Turing.FinTM2`。
形式化陈述：Cfg : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of configurations (functions) corresponding to this TM.
-/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ
/-
**Turing.FinTM2.inhabitedCfg** 是 Mathlib 中的一个实例，位于命名空间 `Turing.FinTM2`。
形式化陈述：inhabitedCfg : Inhabited (Cfg tm)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
/-
**Turing.FinTM2.step** 是 Mathlib 中的一个定义，位于命名空间 `Turing.FinTM2`。
形式化陈述：step : tm.Cfg -> Option tm.Cfg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The step function corresponding to this TM.
-/
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m

end

end FinTM2

/-- The initial configuration corresponding to a list in the input alphabet. -/
/-
**Turing.initList** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where l
参数：tm : FinTM2；s : List (tm.Γ tm.k₀)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial configuration corresponding to a list in the input alphabet.
-/
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []

/-- The final configuration corresponding to a list in the output alphabet. -/
/-
**Turing.haltList** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where l
参数：tm : FinTM2；s : List (tm.Γ tm.k₁)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The final configuration corresponding to a list in the output alphabet.
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

/-- A proof of tm outputting l' when given l. -/
/-
**Turing.TM2Outputs** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ 
tm.k₁)))
参数：tm : FinTM2；l : List (tm.Γ tm.k₀)；l' : Option (List (tm.Γ tm.k₁))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof of tm outputting l' when given l.
-/
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
/-
**Turing.TM2OutputsInTime** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List 
(tm.Γ tm.k₁))) (m : Nat)
参数：tm : FinTM2；l : List (tm.Γ tm.k₀)；l' : Option (List (tm.Γ tm.k₁))；m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof of tm outputting l' when given l in at most m steps.
-/
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
/-
**Turing.TM2OutputsInTime.toTM2Outputs** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2Outp
utsInTime`。
形式化陈述：{tm : Turing.FinTM2} →   {l : List (tm.Γ tm.k₀)} →     {l' : Option (List 
(tm.Γ tm.k₁))} → {m : ℕ} → Turing.TM2OutputsInTime tm l l' m → Turing.TM2Outputs
 tm l l'
参数：tm.Γ tm.k₀；List (tm.Γ tm.k₁)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map, forgetting the upper bound on the number of steps.
-/
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo

/-- A (bundled TM2) Turing machine
with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`. -/
/-
**Turing.TM2ComputableAux** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：Type → Type → Type 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (bundled TM2) Turing machine
with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`.
-/
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  /-- the underlying bundled TM2 -/
  tm : FinTM2
  /-- the input alphabet is equivalent to `Γ₀` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  /-- the output alphabet is equivalent to `Γ₁` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/-- A Turing machine + a proof it outputs `f`. -/
/-
**Turing.TM2Computable** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：{α β αΓ βΓ : Type} → (α → List αΓ) → (β → List βΓ) → (α → β) → Type 1
参数：α → List αΓ；β → List βΓ；α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Turing machine + a proof it outputs `f`.
-/
structure TM2Computable {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) extends
  TM2ComputableAux αΓ βΓ where
  /-- a proof this machine outputs `f` -/
  outputsFun :
    ∀ a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
/-
**Turing.TM2ComputableInTime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：{α β αΓ βΓ : Type} → (α → List αΓ) → (β → List βΓ) → (α → β) → Type 1
参数：α → List αΓ；β → List βΓ；α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps.
-/
structure TM2ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time (ea a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
/-
**Turing.TM2ComputableInPolyTime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：{α β αΓ βΓ : Type} → (α → List αΓ) → (β → List βΓ) → (α → β) → Type 1
参数：α → List αΓ；β → List βΓ；α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps.
-/
structure TM2ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time.eval (ea a).length)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
/-
**Turing.TM2ComputableInTime.toTM2Computable** 是 Mathlib 中的一个定义，位于命名空间 `Turing.T
M2ComputableInTime`。
形式化陈述：{α β αΓ βΓ : Type} →   {ea : α → List αΓ} →     {eb : β → List βΓ} → {f : 
α → β} → Turing.TM2ComputableInTime ea eb f → Turing.TM2Computable ea eb f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A forgetful map, forgetting the time bound on the number of steps.
-/
def TM2ComputableInTime.toTM2Computable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInTime ea eb f) : TM2Computable ea eb f :=
  ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
/-
**Turing.TM2ComputableInPolyTime.toTM2ComputableInTime** 是 Mathlib 中的一个定义，位于命名空间
 `Turing.TM2ComputableInPolyTime`。
形式化陈述：{α β αΓ βΓ : Type} →   {ea : α → List αΓ} →     {eb : β → List βΓ} → {f : 
α → β} → Turing.TM2ComputableInPolyTime ea eb f → Turing.TM2ComputableInTime ea 
eb f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A forgetful map, forgetting that the time function is polynomial.
-/
def TM2ComputableInPolyTime.toTM2ComputableInTime {α β αΓ βΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInTime ea eb f :=
  ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
/-
**Turing.idComputer** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：idComputer (αΓ : Type) [Fintype αΓ] : FinTM2 where K
参数：αΓ : Type。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Turing machine computing the identity on α.
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
/-
**Turing.inhabitedFinTM2** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedFinTM2 : Inhabited FinTM2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedFinTM2 : Inhabited FinTM2 :=
  ⟨idComputer Bool⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
/-
**Turing.idComputableInPolyTime** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：idComputableInPolyTime {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) : @T
M2ComputableInPolyTime α α αΓ αΓ ea ea id where tm
参数：ea : α -> List αΓ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof that the identity map on α is computable in polytime.
-/
def idComputableInPolyTime {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2ComputableInPolyTime α α αΓ αΓ ea ea id where
  tm := idComputer αΓ
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }
/-
**Turing.inhabitedTM2ComputableInPolyTime** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2ComputableInPolyTime : Inhabited (TM2ComputableInPolyTime enco
deBool encodeBool id)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2ComputableInPolyTime :
    Inhabited (TM2ComputableInPolyTime encodeBool encodeBool id) :=
  ⟨idComputableInPolyTime encodeBool⟩
/-
**Turing.inhabitedTM2OutputsInTime** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2OutputsInTime : Inhabited (TM2OutputsInTime (idComputer Bool) 
(List.map (Equiv.cast rfl).invFun [false]) (some (List.map (Equiv.cast rfl).invF
un [false])) (Polynomial.eval 1 1))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2OutputsInTime :
    Inhabited
      (TM2OutputsInTime (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
  ⟨(idComputableInPolyTime encodeBool).outputsFun false⟩
/-
**Turing.inhabitedTM2Outputs** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2Outputs : Inhabited (TM2Outputs (idComputer Bool) (List.map (E
quiv.cast rfl).invFun [false]) (some (List.map (Equiv.cast rfl).invFun [false]))
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2Outputs :
    Inhabited
      (TM2Outputs (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩
/-
**Turing.inhabitedEvalsToInTime** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedEvalsToInTime : Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩
) ⟨⟩ (some ⟨⟩) 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩
/-
**Turing.inhabitedTM2EvalsTo** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (som
e ⟨⟩))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
/-
**Turing.idComputableInTime** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：idComputableInTime {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) : @TM2Co
mputableInTime α α αΓ αΓ ea ea id
参数：ea : α -> List αΓ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof that the identity map on α is computable in time.
-/
def idComputableInTime {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2ComputableInTime α α αΓ αΓ ea ea id :=
  TM2ComputableInPolyTime.toTM2ComputableInTime <| idComputableInPolyTime ea
/-
**Turing.inhabitedTM2ComputableInTime** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2ComputableInTime : Inhabited (TM2ComputableInTime encodeBool e
ncodeBool id)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2ComputableInTime :
    Inhabited (TM2ComputableInTime encodeBool encodeBool id) :=
  ⟨idComputableInTime encodeBool⟩

/-- A proof that the identity map on α is computable. -/
/-
**Turing.idComputable** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：idComputable {α αΓ : Type} [Fintype αΓ] (ea : α -> List αΓ) : @TM2Computab
le α α αΓ αΓ ea ea id
参数：ea : α -> List αΓ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof that the identity map on α is computable.
-/
def idComputable {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2Computable α α αΓ αΓ ea ea id :=
  TM2ComputableInTime.toTM2Computable <| idComputableInTime ea
/-
**Turing.inhabitedTM2Computable** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2Computable : Inhabited (TM2Computable encodeBool encodeBool id
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTM2Computable :
    Inhabited (TM2Computable encodeBool encodeBool id) :=
  ⟨idComputable encodeBool⟩
/-
**Turing.inhabitedTM2ComputableAux** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
形式化陈述：inhabitedTM2ComputableAux : Inhabited (TM2ComputableAux Bool Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime eα eβ f)
    (h2 : TM2ComputableInPolyTime eβ eγ g) :
  Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))

end

end Turing

