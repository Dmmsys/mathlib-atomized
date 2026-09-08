/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.Data.Fintype.Pi

/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occurring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the probability over
the entire sample space when `s = Set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `ProbabilityTheory.uniformOn`: given a set `s`, `uniformOn s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure-theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allows us to describe this by abusing the definitional equality of sets and predicates by simply
writing `uniformOn s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/

@[expose] public section


noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {s : Set Ω}

/-- Given a set `s`, `uniformOn s` is the uniform measure on `s`, defined as the counting measure
conditioned by `s`. One should think of `uniformOn s t` as the proportion of `s` that is contained
in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`ProbabilityTheory.uniformOn_isProbabilityMeasure`. -/
/-
**ProbabilityTheory.uniformOn** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：uniformOn (s : Set Ω) : Measure Ω
参数：s : Set Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `s`, `uniformOn s` is the uniform measure on `s`, defined as the cou
nting measure
conditioned by `s`. One should think of `uniformOn s t` as the proportion of `s`
 that is contained
in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`ProbabilityTheory.uniformOn_isProbabilityMeasure`.
-/
def uniformOn (s : Set Ω) : Measure Ω :=
  Measure.count[|s]
deriving IsZeroOrProbabilityMeasure

@[simp]
/-
**ProbabilityTheory.uniformOn_empty_meas** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：uniformOn_empty_meas : (uniformOn ∅ : Measure Ω) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_empty`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (
μ : MeasureTheory.Measure Ω), μ[|∅] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOn_empty_meas : (uniformOn ∅ : Measure Ω) = 0 := by simp [uniformOn]
/-
**ProbabilityTheory.uniformOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：uniformOn_empty {s : Set Ω} : uniformOn s ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOn_empty {s : Set Ω} : uniformOn s ∅ = 0 := by simp

/-- See `uniformOn_eq_zero` for a version assuming `MeasurableSingletonClass Ω` instead of
`MeasurableSet s`. -/
/-
**ProbabilityTheory.uniformOn_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {s : Set Ω},   MeasurableSet s
 → (ProbabilityTheory.uniformOn s = 0 ↔ s.Infinite ∨ s = ∅)
参数：ProbabilityTheory.uniformOn s = 0 ↔ s.Infinite ∨ s = ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See `uniformOn_eq_zero` for a version assuming `MeasurableSingletonClass Ω` inst
ead of
`MeasurableSet s`.
-/
@[simp] lemma uniformOn_eq_zero' (hs : MeasurableSet s) : uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by
  simp [uniformOn, hs]

/-- See `uniformOn_eq_zero'` for a version assuming `MeasurableSet s` instead of
`MeasurableSingletonClass Ω`. -/
/-
**ProbabilityTheory.uniformOn_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {s : Set Ω} [MeasurableSinglet
onClass Ω],   ProbabilityTheory.uniformOn s = 0 ↔ s.Infinite ∨ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See `uniformOn_eq_zero'` for a version assuming `MeasurableSet s` instead of
`MeasurableSingletonClass Ω`.
-/
@[simp] lemma uniformOn_eq_zero [MeasurableSingletonClass Ω] :
    uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by simp [uniformOn]
/-
**ProbabilityTheory.finite_of_uniformOn_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：finite_of_uniformOn_ne_zero {s t : Set Ω} (h : uniformOn s t != 0) : s.Fin
ite
参数：h : uniformOn s t != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply_infinite`：count_apply_infinite (hs : s
.Infinite) : count s = ∞
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem finite_of_uniformOn_ne_zero {s t : Set Ω} (h : uniformOn s t ≠ 0) : s.Finite := by
  by_contra hs'
  simp [uniformOn, cond, Measure.count_apply_infinite hs'] at h
/-
**ProbabilityTheory.uniformOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：uniformOn_univ [Fintype Ω] {s : Set Ω} : uniformOn Set.univ s = Measure.co
unt s / Fintype.card Ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.count_univ`：count_univ : count (univ : Set α) = EN
at.card α
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOn_univ [Fintype Ω] {s : Set Ω} :
    uniformOn Set.univ s = Measure.count s / Fintype.card Ω := by
  simp [uniformOn, cond_apply, ← ENNReal.div_eq_inv_mul]
/-
**ProbabilityTheory.isProbabilityMeasure_uniformOn'** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory`。
形式化陈述：isProbabilityMeasure_uniformOn' {s : Set Ω} (hs_fin : s.Finite) (hs_nonemp
ty : s.Nonempty) (hs_meas : MeasurableSet s) : IsProbabilityMeasure (uniformOn s
)
参数：hs_fin : s.Finite；hs_nonempty : s.Nonempty；hs_meas : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.cond_isProbabilityMeasure_of_finite`：cond_isProbabilit
yMeasure_of_finite (hcs : μ s != 0) (hs : μ s != ∞) : IsProbabilityMeasure μ[|s]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.count_ne_zero_iff`：count_ne_zero_iff : count s != 
0 ↔ s.Nonempty
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.count_apply_lt_top'`：count_apply_lt_top' (s_mble :
 MeasurableSet s) : count s < ∞ ↔ s.Finite
-/
theorem isProbabilityMeasure_uniformOn' {s : Set Ω}
    (hs_fin : s.Finite) (hs_nonempty : s.Nonempty) (hs_meas : MeasurableSet s) :
    IsProbabilityMeasure (uniformOn s) := by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top' hs_meas).2 hs_fin |>.ne
/-
**ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ** 是 Mathlib 中的一个实例，位
于命名空间 `ProbabilityTheory`。
形式化陈述：instIsProbabilityMeasure_uniformOn_univ [Finite Ω] [Nonempty Ω] : IsProbab
ilityMeasure (uniformOn (.univ : Set Ω))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.isProbabilityMeasure_uniformOn'`：isProbabilityMeasure_
uniformOn' {s : Set Ω} (hs_fin : s.Finite) (hs_nonempty : s.Nonempty) (hs_meas :
 MeasurableSet s) : IsProbabilityMeasur…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
instance instIsProbabilityMeasure_uniformOn_univ [Finite Ω] [Nonempty Ω] :
    IsProbabilityMeasure (uniformOn (.univ : Set Ω)) :=
  isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ
/-
**ProbabilityTheory.uniformOn_apply_finset'** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：uniformOn_apply_finset' {Ω : Type*} [DecidableEq Ω] {_ : MeasurableSpace Ω
} {s t : Finset Ω} (hs : MeasurableSet (s : Set Ω)) (ht : MeasurableSet (t : Set
 Ω)) : uniformOn (s : Set Ω) (t : Set Ω) = #(s inter t) / #s
参数：hs : MeasurableSet (s : Set Ω)；ht : MeasurableSet (t : Set Ω)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MeasureTheory.Measure.count_apply_finset'`：count_apply_finset' {s : Fins
et α} (hs : MeasurableSet (s : Set α)) : count (↑s : Set α) = #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma uniformOn_apply_finset' {Ω : Type*} [DecidableEq Ω] {_ : MeasurableSpace Ω} {s t : Finset Ω}
    (hs : MeasurableSet (s : Set Ω)) (ht : MeasurableSet (t : Set Ω)) :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s := by
  rw [uniformOn, cond_apply hs, Measure.count_apply_finset' hs, ← coe_inter,
    Measure.count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.inter ht

variable [MeasurableSingletonClass Ω]
/-
**ProbabilityTheory.uniformOn_apply_finset** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：uniformOn_apply_finset [DecidableEq Ω] {s t : Finset Ω} : uniformOn (s : S
et Ω) (t : Set Ω) = #(s inter t) / #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.uniformOn_apply_finset'`：uniformOn_apply_finset' {Ω : 
Type*} [DecidableEq Ω] {_ : MeasurableSpace Ω} {s t : Finset Ω} (hs : Measurable
Set (s : Set Ω)) (ht : Measurab…
· 使用定理 `Finset.measurableSet`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] (s : Finset α), MeasurableSet ↑s
-/
lemma uniformOn_apply_finset [DecidableEq Ω] {s t : Finset Ω} :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s :=
  uniformOn_apply_finset' s.measurableSet t.measurableSet
/-
**ProbabilityTheory.isProbabilityMeasure_uniformOn** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：isProbabilityMeasure_uniformOn {s : Set Ω} (hs : s.Finite) (hs' : s.Nonemp
ty) : IsProbabilityMeasure (uniformOn s)
参数：hs : s.Finite；hs' : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.cond_isProbabilityMeasure_of_finite`：cond_isProbabilit
yMeasure_of_finite (hcs : μ s != 0) (hs : μ s != ∞) : IsProbabilityMeasure μ[|s]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.count_ne_zero_iff`：count_ne_zero_iff : count s != 
0 ↔ s.Nonempty
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.count_apply_lt_top`：count_apply_lt_top [Measurable
SingletonClass α] : count s < ∞ ↔ s.Finite
-/
theorem isProbabilityMeasure_uniformOn {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (uniformOn s) := by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

@[deprecated (since := "2026-01-26")]
alias uniformOn_isProbabilityMeasure := isProbabilityMeasure_uniformOn
/-
**ProbabilityTheory.uniformOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：uniformOn_singleton (ω : Ω) (t : Set Ω) [Decidable (ω in t)] : uniformOn {
ω} t = if ω in t then 1 else 0
参数：ω : Ω；t : Set Ω；ω in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `MeasureTheory.Measure.count_singleton`：count_singleton [MeasurableSingle
tonClass α] (a : α) : count ({a} : Set α) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem uniformOn_singleton (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)] :
    uniformOn {ω} t = if ω ∈ t then 1 else 0 := by
  rw [uniformOn, cond_apply (measurableSet_singleton ω), Measure.count_singleton, inv_one,
    one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = {ω}), Measure.count_singleton]
  · simpa

variable {s t u : Set Ω}
/-
**ProbabilityTheory.uniformOn_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：uniformOn_inter_self (hs : s.Finite) : uniformOn s (s inter t) = uniformOn
 s t
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_inter_self`：cond_inter_self (hms : MeasurableSet 
s) (t : Set Ω) (μ : Measure Ω) : μ[s inter t | s] = μ[t | s]
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
-/
theorem uniformOn_inter_self (hs : s.Finite) : uniformOn s (s ∩ t) = uniformOn s t := by
  rw [uniformOn, cond_inter_self hs.measurableSet]
/-
**ProbabilityTheory.uniformOn_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：uniformOn_self (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s s = 1
参数：hs : s.Finite；hs' : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `MeasureTheory.Measure.count_ne_zero_iff`：count_ne_zero_iff : count s != 
0 ↔ s.Nonempty
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.count_apply_lt_top`：count_apply_lt_top [Measurable
SingletonClass α] : count s < ∞ ↔ s.Finite
-/
theorem uniformOn_self (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s s = 1 := by
  rw [uniformOn, cond_apply hs.measurableSet, Set.inter_self, ENNReal.inv_mul_cancel]
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne
/-
**ProbabilityTheory.uniformOn_eq_one_of** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：uniformOn_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s subseteq t)
 : uniformOn s t = 1
参数：hs : s.Finite；hs' : s.Nonempty；ht : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.isProbabilityMeasure_uniformOn`：isProbabilityMeasure_u
niformOn {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) : IsProbabilityMeasure (
uniformOn s)
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `ProbabilityTheory.instIsZeroOrProbabilityMeasureUniformOn`：∀ {Ω : Type u
_1} [inst : MeasurableSpace Ω] (s : Set Ω),   MeasureTheory.IsZeroOrProbabilityM
easure (ProbabilityTheory.uniformOn s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.uniformOn_self`：uniformOn_self (hs : s.Finite) (hs' : 
s.Nonempty) : uniformOn s s = 1
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem uniformOn_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s ⊆ t) :
    uniformOn s t = 1 := by
  have := isProbabilityMeasure_uniformOn hs hs'
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt, ← uniformOn_self hs hs']
  exact measure_mono ht
/-
**ProbabilityTheory.pred_true_of_uniformOn_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：pred_true_of_uniformOn_eq_one (h : uniformOn s t = 1) : s subseteq t
参数：h : uniformOn s t = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.finite_of_uniformOn_ne_zero`：finite_of_uniformOn_ne_ze
ro {s t : Set Ω} (h : uniformOn s t != 0) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.eq_inv_of_mul_eq_one_left`：∀ {a b : ENNReal}, a * b = 1 → a = b⁻
¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.toFinset_inj`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {h
t : t.Finite}, hs.toFinset = ht.toFinset ↔ s = t
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `MeasureTheory.Measure.count_apply_finite`：count_apply_finite [Measurable
SingletonClass α] (s : Set α) (hs : s.Finite) : count s = #hs.toFinset
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pred_true_of_uniformOn_eq_one (h : uniformOn s t = 1) : s ⊆ t := by
  have hsf := finite_of_uniformOn_ne_zero (by rw [h]; exact one_ne_zero)
  rw [uniformOn, cond_apply hsf.measurableSet, mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv, Measure.count_apply_finite _ hsf, Measure.count_apply_finite _ (hsf.inter_of_left _),
    Nat.cast_inj] at h
  suffices s ∩ t = s by exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono s.inter_subset_left) h.ge
/-
**ProbabilityTheory.uniformOn_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：uniformOn_eq_zero_iff (hs : s.Finite) : uniformOn s t = 0 ↔ s inter t = ∅
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `MeasureTheory.Measure.count_apply_finite`：count_apply_finite [Measurable
SingletonClass α] (s : Set α) (hs : s.Finite) : count s = #hs.toFinset
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_infinite`：not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniformOn_eq_zero_iff (hs : s.Finite) : uniformOn s t = 0 ↔ s ∩ t = ∅ := by
  simp [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]
/-
**ProbabilityTheory.uniformOn_of_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：uniformOn_of_univ (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s Set.uni
v = 1
参数：hs : s.Finite；hs' : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.uniformOn_eq_one_of`：uniformOn_eq_one_of (hs : s.Finit
e) (hs' : s.Nonempty) (ht : s subseteq t) : uniformOn s t = 1
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem uniformOn_of_univ (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s Set.univ = 1 :=
  uniformOn_eq_one_of hs hs' s.subset_univ
/-
**ProbabilityTheory.uniformOn_inter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：uniformOn_inter (hs : s.Finite) : uniformOn s (t inter u) = uniformOn (s i
nter t) u * uniformOn s t
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn_empty_meas`：uniformOn_empty_meas : (uniformO
n ∅ : Measure Ω) = 0
· 使用定理 `MeasureTheory.Measure.coe_zero`：coe_zero {_m : MeasurableSpace α} : ⇑(0 
: Measure α) = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ProbabilityTheory.uniformOn_eq_zero_iff`：uniformOn_eq_zero_iff (hs : s.F
inite) : uniformOn s t = 0 ↔ s inter t = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `MeasureTheory.Measure.count_eq_zero_iff`：count_eq_zero_iff : count s = 0
 ↔ s = ∅ where mp h
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.count_apply_lt_top`：count_apply_lt_top [Measurable
SingletonClass α] : count s < ∞ ↔ s.Finite
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem uniformOn_inter (hs : s.Finite) :
    uniformOn s (t ∩ u) = uniformOn (s ∩ t) u * uniformOn s t := by
  by_cases hst : s ∩ t = ∅
  · rw [hst, uniformOn_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      uniformOn_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [uniformOn, uniformOn, cond_apply hs.measurableSet, cond_apply hs.measurableSet,
    cond_apply (hs.inter_of_left _).measurableSet, mul_comm _ (Measure.count (s ∩ t)),
    ← mul_assoc, mul_comm _ (Measure.count (s ∩ t)), ← mul_assoc, ENNReal.mul_inv_cancel, one_mul,
    mul_comm, Set.inter_assoc]
  · rwa [← Measure.count_eq_zero_iff] at hst
  · exact (Measure.count_apply_lt_top.2 <| hs.inter_of_left _).ne
/-
**ProbabilityTheory.uniformOn_inter'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：uniformOn_inter' (hs : s.Finite) : uniformOn s (t inter u) = uniformOn (s 
inter u) t * uniformOn s u
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ProbabilityTheory.uniformOn_inter`：uniformOn_inter (hs : s.Finite) : uni
formOn s (t inter u) = uniformOn (s inter t) u * uniformOn s t
-/
theorem uniformOn_inter' (hs : s.Finite) :
    uniformOn s (t ∩ u) = uniformOn (s ∩ u) t * uniformOn s u := by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs
/-
**ProbabilityTheory.uniformOn_union** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：uniformOn_union (hs : s.Finite) (htu : Disjoint t u) : uniformOn s (t unio
n u) = uniformOn s t + uniformOn s u
参数：hs : s.Finite；htu : Disjoint t u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem uniformOn_union (hs : s.Finite) (htu : Disjoint t u) :
    uniformOn s (t ∪ u) = uniformOn s t + uniformOn s u := by
  rw [uniformOn, cond_apply hs.measurableSet, cond_apply hs.measurableSet,
    cond_apply hs.measurableSet, Set.inter_union_distrib_left, measure_union, mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]
/-
**ProbabilityTheory.uniformOn_compl** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：uniformOn_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) : uniformOn
 s t + uniformOn s tᶜ = 1
参数：t : Set Ω；hs : s.Finite；hs' : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.uniformOn_union`：uniformOn_union (hs : s.Finite) (htu 
: Disjoint t u) : uniformOn s (t union u) = uniformOn s t + uniformOn s u
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.isProbabilityMeasure_uniformOn`：isProbabilityMeasure_u
niformOn {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) : IsProbabilityMeasure (
uniformOn s)
-/
theorem uniformOn_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) :
    uniformOn s t + uniformOn s tᶜ = 1 := by
  rw [← uniformOn_union hs disjoint_compl_right, Set.union_compl_self,
    (isProbabilityMeasure_uniformOn hs hs').measure_univ]
/-
**ProbabilityTheory.uniformOn_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：uniformOn_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s
 t) : uniformOn s u * uniformOn (s union t) s + uniformOn t u * uniformOn (s uni
on t) t = uniformOn (s union t) u
参数：hs : s.Finite；ht : t.Finite；hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.uniformOn_empty_meas`：uniformOn_empty_meas : (uniformO
n ∅ : Measure Ω) = 0
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `ProbabilityTheory.uniformOn_self`：uniformOn_self (hs : s.Finite) (hs' : 
s.Nonempty) : uniformOn s s = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `ProbabilityTheory.uniformOn.eq_1`：∀ {Ω : Type u_1} [inst : MeasurableSpa
ce Ω] (s : Set Ω), ProbabilityTheory.uniformOn s = MeasureTheory.Measure.count[|
s]
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.union_inter_cancel_left`：union_inter_cancel_left {s t : Set α} : (s 
union t) inter s = s
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `MeasureTheory.Measure.count_ne_zero`：∀ {α : Type u_1} [inst : Measurable
Space α] {s : Set α}, s.Nonempty → MeasureTheory.Measure.count s ≠ 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 40 条，此处仅展示前 30 条）
-/
theorem uniformOn_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    uniformOn s u * uniformOn (s ∪ t) s + uniformOn t u * uniformOn (s ∪ t) t =
      uniformOn (s ∪ t) u := by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [uniformOn_self ht ht']
  · simp [uniformOn_self hs hs']
  rw [uniformOn, uniformOn, uniformOn, cond_apply hs.measurableSet,
    cond_apply ht.measurableSet, cond_apply (hs.union ht).measurableSet,
    cond_apply (hs.union ht).measurableSet, cond_apply (hs.union ht).measurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right,
      mul_comm (Measure.count (s ∪ t))⁻¹, mul_comm (Measure.count (s ∪ t))⁻¹, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Measure.count s), mul_comm _ (Measure.count t), ← mul_assoc,
      ← mul_assoc]
  rw [ENNReal.mul_inv_cancel, ENNReal.mul_inv_cancel, one_mul, one_mul, ← add_mul, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts [hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).measurableSet,
    Measure.count_ne_zero ht', (Measure.count_apply_lt_top.2 ht).ne, Measure.count_ne_zero hs',
    (Measure.count_apply_lt_top.2 hs).ne]

/-- A version of the law of total probability for counting probabilities. -/
/-
**ProbabilityTheory.uniformOn_add_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：uniformOn_add_compl_eq (u t : Set Ω) (hs : s.Finite) : uniformOn (s inter 
u) t * uniformOn s u + uniformOn (s inter uᶜ) t * uniformOn s uᶜ = uniformOn s t
参数：u t : Set Ω；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.uniformOn_disjoint_union`：uniformOn_disjoint_union (hs
 : s.Finite) (ht : t.Finite) (hst : Disjoint s t) : uniformOn s u * uniformOn (s
 union t) s + uniformOn t u * un…
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.uniformOn_inter_self`：uniformOn_inter_self (hs : s.Fin
ite) : uniformOn s (s inter t) = uniformOn s t

--- 原说明 ---
A version of the law of total probability for counting probabilities.
-/
theorem uniformOn_add_compl_eq (u t : Set Ω) (hs : s.Finite) :
    uniformOn (s ∩ u) t * uniformOn s u + uniformOn (s ∩ uᶜ) t * uniformOn s uᶜ =
      uniformOn s t := by
  conv_rhs =>
    rw [(by simp : s = s ∩ u ∪ s ∩ uᶜ),
      ← uniformOn_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [uniformOn_inter_self hs]

variable {ι : Type*} [Fintype ι]

/-- The uniform measure on a product of sets is the product of the uniform measures. -/
/-
**ProbabilityTheory.uniformOn_pi** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：uniformOn_pi [Finite Ω] {f : ι -> Set Ω} : uniformOn (Set.univ.pi f) = Mea
sure.pi fun i => uniformOn (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `ProbabilityTheory.instIsZeroOrProbabilityMeasureUniformOn`：∀ {Ω : Type u
_1} [inst : MeasurableSpace Ω] (s : Set Ω),   MeasureTheory.IsZeroOrProbabilityM
easure (ProbabilityTheory.uniformOn s)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.uniformOn_apply_finset`：uniformOn_apply_finset [Decida
bleEq Ω] {s t : Finset Ω} : uniformOn (s : Set Ω) (t : Set Ω) = #(s inter t) / #
s
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `ENNReal.prod_div_distrib_of_ne_top`：prod_div_distrib_of_ne_top (hg : for
all i in s, g i != ∞) : (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i in s, g i
)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The uniform measure on a product of sets is the product of the uniform measures.
-/
lemma uniformOn_pi [Finite Ω] {f : ι → Set Ω} :
    uniformOn (Set.univ.pi f) = Measure.pi fun i ↦ uniformOn (f i) := by
  refine (MeasureTheory.Measure.pi_eq fun t ht ↦ ?_).symm
  lift f to ι → Finset Ω using by simp [Set.toFinite]
  lift t to ι → Finset Ω using by simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne_top]

end ProbabilityTheory

