/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.TietzeExtension

/-!
# Finite measures

This file defines the type of finite measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of finite measures is equipped with the topology of weak convergence
of measures. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

## Main definitions

The main definitions are
* `MeasureTheory.FiniteMeasure Ω`: The type of finite measures on `Ω` with the topology of weak
  convergence of measures.
* `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`:
  Interpret a finite measure as a continuous linear functional on the space of
  bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
  topology of weak convergence.
* `MeasureTheory.FiniteMeasure.map`: The push-forward `f* μ` of a finite measure `μ` on `Ω`
  along a measurable function `f : Ω → Ω'`.
* `MeasureTheory.FiniteMeasure.mapCLM`: The push-forward along a given continuous `f : Ω → Ω'`
  as a continuous linear map `f* : FiniteMeasure Ω →L[ℝ≥0] FiniteMeasure Ω'`.

## Main results

* Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
  bounded continuous nonnegative functions on `Ω` via integration:
  `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`
* `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
  measures is characterized by the convergence of integrals of all bounded continuous functions.
  This shows that the chosen definition of topology coincides with the common textbook definition
  of weak convergence of measures. A similar characterization by the convergence of integrals (in
  the `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative functions is
  `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of finite measures `f* : FiniteMeasure Ω → FiniteMeasure Ω'` is continuous.
* `MeasureTheory.FiniteMeasure.t2Space`: The topology of weak convergence of finite Borel measures
  is Hausdorff on spaces where indicators of closed sets have continuous decreasing approximating
  sequences (in particular on any pseudo-metrizable spaces).

## Implementation notes

The topology of weak convergence of finite Borel measures is defined using a mapping from
`MeasureTheory.FiniteMeasure Ω` to `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The implementation of `MeasureTheory.FiniteMeasure Ω` and is directly as a subtype of
`MeasureTheory.Measure Ω`, and the coercion to a function is the composition `ENNReal.toNNReal`
and the coercion to function of `MeasureTheory.Measure Ω`. Another alternative would have been to
use a bijection with `MeasureTheory.VectorMeasure Ω ℝ≥0` as an intermediate step. Some
considerations:
* Potential advantages of using the `NNReal`-valued vector measure alternative:
  * The coercion to function would avoid need to compose with `ENNReal.toNNReal`, the
    `NNReal`-valued API could be more directly available.
* Potential drawbacks of the vector measure alternative:
  * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
    have measure 0.
  * No integration theory directly. E.g., the topology definition requires
    `MeasureTheory.lintegral` w.r.t. a coercion to `MeasureTheory.Measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure

-/

@[expose] public section


noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Function

namespace MeasureTheory

namespace FiniteMeasure

section FiniteMeasure

/-! ### Finite measures

In this section we define the `Type` of `MeasureTheory.FiniteMeasure Ω`, when `Ω` is a measurable
space. Finite measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.FiniteMeasure Ω` is equipped with
the topology of weak convergence of measures. This is implemented by defining a pairing of finite
measures `μ` on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration,
and using the associated weak topology (essentially the weak-star topology on the dual of
`Ω →ᵇ ℝ≥0`).
-/


variable {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
/-
**MeasureTheory.FiniteMeasure._root_.MeasureTheory.FiniteMeasure** 是 Mathlib 中的一
个定义，位于命名空间 `MeasureTheory.FiniteMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite measures are defined as the subtype of measures that have the property of
 being finite
measures (i.e., their total mass is finite).
-/
def _root_.MeasureTheory.FiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsFiniteMeasure μ }

/-- Coercion from `MeasureTheory.FiniteMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
/-
**MeasureTheory.FiniteMeasure.toMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：toMeasure : FiniteMeasure Ω -> Measure Ω
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `MeasureTheory.FiniteMeasure Ω` to `MeasureTheory.Measure Ω`.
-/
def toMeasure : FiniteMeasure Ω → Measure Ω := Subtype.val

/-- A finite measure can be interpreted as a measure. -/
/-
**MeasureTheory.FiniteMeasure.instCoe** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.F
initeMeasure`。
形式化陈述：instCoe : Coe (FiniteMeasure Ω) (MeasureTheory.Measure Ω)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite measure can be interpreted as a measure.
-/
instance instCoe : Coe (FiniteMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }
/-
**MeasureTheory.FiniteMeasure.isFiniteMeasure** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory.FiniteMeasure`。
形式化陈述：isFiniteMeasure (μ : FiniteMeasure Ω) : IsFiniteMeasure (μ : Measure Ω)
参数：μ : FiniteMeasure Ω。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance isFiniteMeasure (μ : FiniteMeasure Ω) : IsFiniteMeasure (μ : Measure Ω) := μ.prop

@[simp]
/-
**MeasureTheory.FiniteMeasure.val_eq_toMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.FiniteMeasure`。
形式化陈述：val_eq_toMeasure (ν : FiniteMeasure Ω) : ν.val = (ν : Measure Ω)
参数：ν : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_toMeasure (ν : FiniteMeasure Ω) : ν.val = (ν : Measure Ω) := rfl
/-
**MeasureTheory.FiniteMeasure.toMeasure_injective** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FiniteMeasure`。
形式化陈述：toMeasure_injective : Function.Injective ((↑) : FiniteMeasure Ω -> Measure
 Ω)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem toMeasure_injective : Function.Injective ((↑) : FiniteMeasure Ω → Measure Ω) :=
  Subtype.coe_injective
/-
**MeasureTheory.FiniteMeasure.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.FiniteMeasure`。
形式化陈述：instFunLike : FunLike (FiniteMeasure Ω) (Set Ω) Real>=0 where coe μ s
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (FiniteMeasure Ω) (Set Ω) ℝ≥0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
  coe_injective μ ν h := toMeasure_injective <| Measure.ext fun s _ ↦ by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s
/-
**MeasureTheory.FiniteMeasure.coeFn_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：coeFn_def (μ : FiniteMeasure Ω) : μ = fun s => ((μ : Measure Ω) s).toNNRea
l
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFn_def (μ : FiniteMeasure Ω) : μ = fun s ↦ ((μ : Measure Ω) s).toNNReal := rfl
/-
**MeasureTheory.FiniteMeasure.coeFn_mk** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：coeFn_mk (μ : Measure Ω) (hμ) : DFunLike.coe (F
参数：μ : Measure Ω；hμ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := FiniteMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ (μ s).toNNReal := rfl

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) : DFunLike.coe (F
参数：μ : Measure Ω；hμ；s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := FiniteMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl
/-
**MeasureTheory.FiniteMeasure.toMeasure_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) 
(h : MeasureTheory.IsFiniteMeasure μ),   ↑⟨μ, h⟩ = μ
参数：μ : MeasureTheory.Measure Ω；h : MeasureTheory.IsFiniteMeasure μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_mk (μ : Measure Ω) (h : IsFiniteMeasure μ) :
    FiniteMeasure.toMeasure (⟨μ, h⟩ : FiniteMeasure Ω) = μ := rfl
/-
**MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.FiniteMeasu
re Ω} {s : Set Ω}, (↑μ).real s = ↑(μ s)
参数：↑μ；μ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma measureReal_eq_coe_coeFn {μ : FiniteMeasure Ω} {s : Set Ω} :
    (μ : Measure Ω).real s = μ s := rfl

@[simp]
/-
**MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：ennreal_coeFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s 
: Real>=0∞) = (ν : Measure Ω) s
参数：ν : FiniteMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) :
    (ν s : ℝ≥0∞) = (ν : Measure Ω) s :=
  ENNReal.coe_toNNReal (measure_lt_top (↑ν) s).ne

@[simp]
/-
**MeasureTheory.FiniteMeasure.null_iff_toMeasure_null** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.FiniteMeasure`。
形式化陈述：null_iff_toMeasure_null (ν : FiniteMeasure Ω) (s : Set Ω) : ν s = 0 ↔ (ν :
 Measure Ω) s = 0
参数：ν : FiniteMeasure Ω；s : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
-/
theorem null_iff_toMeasure_null (ν : FiniteMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h ↦ by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h ↦ congrArg ENNReal.toNNReal h⟩

@[mono, gcongr]
/-
**MeasureTheory.FiniteMeasure.apply_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.FiniteMeasure`。
形式化陈述：apply_mono (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ 
s₁ <= μ s₂
参数：μ : FiniteMeasure Ω；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
-/
theorem apply_mono (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ :=
  ENNReal.toNNReal_mono (measure_ne_top _ s₂) ((μ : Measure Ω).mono h)
/-
**MeasureTheory.FiniteMeasure.apply_union_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：apply_union_le (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ union s₂) <= 
μ s₁ + μ s₂
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `ENNReal.Finiteness.add_ne_top`：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b 
≠ ⊤
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_add`：toNNReal_add {r₁ r₂ : Real>=0∞} (h₁ : r₁ != ∞) (h₂
 : r₂ != ∞) : (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal
· 使用引理 `MeasureTheory.FiniteMeasure.coeFn_def`：coeFn_def (μ : FiniteMeasure Ω) :
 μ = fun s => ((μ : Measure Ω) s).toNNReal
-/
theorem apply_union_le (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ := by
  have := measure_union_le (μ := (μ : Measure Ω)) s₁ s₂
  apply (ENNReal.toNNReal_mono (by finiteness) this).trans_eq
  rw [ENNReal.toNNReal_add (by finiteness) (by finiteness), coeFn_def]
/-
**MeasureTheory.FiniteMeasure.mono_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：mono_null (μ : FiniteMeasure Ω) (h : s subseteq t) (ht : μ t = 0) : μ s = 
0
参数：μ : FiniteMeasure Ω；h : s subseteq t；ht : μ t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `MeasureTheory.FiniteMeasure.apply_mono`：apply_mono (μ : FiniteMeasure Ω)
 {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂
-/
theorem mono_null (μ : FiniteMeasure Ω) (h : s ⊆ t) (ht : μ t = 0) : μ s = 0 :=
  eq_bot_mono (apply_mono μ h) ht
/-
**MeasureTheory.FiniteMeasure.pos_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：pos_mono (μ : FiniteMeasure Ω) (h : s subseteq t) (hs : 0 < μ s) : 0 < μ t
参数：μ : FiniteMeasure Ω；h : s subseteq t；hs : 0 < μ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.FiniteMeasure.apply_mono`：apply_mono (μ : FiniteMeasure Ω)
 {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂
-/
lemma pos_mono (μ : FiniteMeasure Ω) (h : s ⊆ t) (hs : 0 < μ s) :
    0 < μ t := hs.trans_le <| μ.apply_mono h

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_measure_iUnion_accumulate** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {ι : Type u_2} [inst_1 : Preor
der ι] [Filter.atTop.IsCountablyGenerated]   {μ : MeasureTheory.FiniteMeasure Ω}
 {f : ι → Set Ω},   Filter.Tendsto (fun i => μ (Set.accumulate f i)) Filter.atTo
p (nhds (μ (⋃ i, f i)))
参数：fun i => μ (Set.accumulate f i)；nhds (μ (⋃ i, f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_accumulate`：tendsto_measure_iUnion_
accumulate {α ι : Type*} [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] 
{_ : MeasurableSpace α} {μ : Measure …

--- 原说明 ---
Continuity from below: the measure of the union of a sequence of (not necessaril
y measurable)
sets is the limit of the measures of the partial unions.
-/
protected lemma tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : FiniteMeasure Ω} {f : ι → Set Ω} :
    Tendsto (fun i ↦ μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure) (ι := ι)

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `NNReal` of
`(μ : measure Ω) univ`. -/
/-
**MeasureTheory.FiniteMeasure.mass** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Fini
teMeasure`。
形式化陈述：mass (μ : FiniteMeasure Ω) : Real>=0
参数：μ : FiniteMeasure Ω。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `NNReal`
 of
`(μ : measure Ω) univ`.
-/
def mass (μ : FiniteMeasure Ω) : ℝ≥0 := μ univ
/-
**MeasureTheory.FiniteMeasure.apply_le_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.FiniteMeasu
re Ω) (s : Set Ω), μ s ≤ μ.mass
参数：μ : MeasureTheory.FiniteMeasure Ω；s : Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.apply_mono`：apply_mono (μ : FiniteMeasure Ω)
 {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
@[simp] theorem apply_le_mass (μ : FiniteMeasure Ω) (s : Set Ω) : μ s ≤ μ.mass := by
  simpa using! apply_mono μ (subset_univ s)

@[simp]
/-
**MeasureTheory.FiniteMeasure.ennreal_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：ennreal_mass {μ : FiniteMeasure Ω} : (μ.mass : Real>=0∞) = (μ : Measure Ω)
 univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
-/
theorem ennreal_mass {μ : FiniteMeasure Ω} : (μ.mass : ℝ≥0∞) = (μ : Measure Ω) univ :=
  ennreal_coeFn_eq_coeFn_toMeasure μ Set.univ
/-
**MeasureTheory.FiniteMeasure.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：instZero : Zero (FiniteMeasure Ω) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (FiniteMeasure Ω) where zero := ⟨0, MeasureTheory.isFiniteMeasureZero⟩
/-
**MeasureTheory.FiniteMeasure.coeFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω], ⇑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coeFn_zero : ⇑(0 : FiniteMeasure Ω) = 0 := rfl

@[simp]
/-
**MeasureTheory.FiniteMeasure.zero_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：zero_mass : (0 : FiniteMeasure Ω).mass = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_mass : (0 : FiniteMeasure Ω).mass = 0 := rfl

@[simp]
/-
**MeasureTheory.FiniteMeasure.mass_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：mass_zero_iff (μ : FiniteMeasure Ω) : μ.mass = 0 ↔ μ = 0
参数：μ : FiniteMeasure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.toMeasure_injective`：toMeasure_injective : F
unction.Injective ((↑) : FiniteMeasure Ω -> Measure Ω)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_mass`：ennreal_mass {μ : FiniteMeasur
e Ω} : (μ.mass : Real>=0∞) = (μ : Measure Ω) univ
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mass_zero_iff (μ : FiniteMeasure Ω) : μ.mass = 0 ↔ μ = 0 := by
  refine ⟨fun μ_mass => ?_, fun hμ => by simp only [hμ, zero_mass]⟩
  apply toMeasure_injective
  apply Measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, ENNReal.coe_eq_zero]
/-
**MeasureTheory.FiniteMeasure.mass_nonzero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.FiniteMeasure`。
形式化陈述：mass_nonzero_iff (μ : FiniteMeasure Ω) : μ.mass != 0 ↔ μ != 0
参数：μ : FiniteMeasure Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `MeasureTheory.FiniteMeasure.mass_zero_iff`：mass_zero_iff (μ : FiniteMeas
ure Ω) : μ.mass = 0 ↔ μ = 0
-/
theorem mass_nonzero_iff (μ : FiniteMeasure Ω) : μ.mass ≠ 0 ↔ μ ≠ 0 :=
  not_iff_not.mpr <| FiniteMeasure.mass_zero_iff μ

@[ext]
/-
**MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：eq_of_forall_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Se
t Ω, MeasurableSet s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν
参数：μ ν : FiniteMeasure Ω；h : forall s : Set Ω, MeasurableSet s -> (μ : Measure Ω
) s = (ν : Measure Ω) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
-/
theorem eq_of_forall_toMeasure_apply_eq (μ ν : FiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply Subtype.ext
  ext1 s s_mble
  exact h s s_mble
/-
**MeasureTheory.FiniteMeasure.eq_of_forall_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.FiniteMeasure`。
形式化陈述：eq_of_forall_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, Measu
rableSet s -> μ s = ν s) : μ = ν
参数：μ ν : FiniteMeasure Ω；h : forall s : Set Ω, MeasurableSet s -> μ s = ν s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem eq_of_forall_apply_eq (μ ν : FiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (h s s_mble)
/-
**MeasureTheory.FiniteMeasure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：instInhabited : Inhabited (FiniteMeasure Ω)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (FiniteMeasure Ω) := ⟨0⟩
/-
**MeasureTheory.FiniteMeasure.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.F
initeMeasure`。
形式化陈述：instAdd : Add (FiniteMeasure Ω) where add μ ν
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (FiniteMeasure Ω) where add μ ν := ⟨μ + ν, MeasureTheory.isFiniteMeasureAdd⟩

variable {R : Type*} [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞]
  [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
/-
**MeasureTheory.FiniteMeasure.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：instSMul : SMul R (FiniteMeasure Ω) where smul (c : R) μ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul R (FiniteMeasure Ω) where
  smul (c : R) μ := ⟨c • (μ : Measure Ω), MeasureTheory.isFiniteMeasureSMulOfNNRealTower⟩

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.toMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：toMeasure_zero : ((↑) : FiniteMeasure Ω -> Measure Ω) 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMeasure_zero : ((↑) : FiniteMeasure Ω → Measure Ω) 0 = 0 := rfl

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.toMeasure_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：toMeasure_add (μ ν : FiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω)
参数：μ ν : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMeasure_add (μ ν : FiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω) := rfl

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.toMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：toMeasure_smul (c : R) (μ : FiniteMeasure Ω) : ↑(c • μ) = c • (μ : Measure
 Ω)
参数：c : R；μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMeasure_smul (c : R) (μ : FiniteMeasure Ω) : ↑(c • μ) = c • (μ : Measure Ω) :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.coeFn_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：coeFn_add (μ ν : FiniteMeasure Ω) : (⇑(μ + ν) : Set Ω -> Real>=0) = (⇑μ + 
⇑ν : Set Ω -> Real>=0)
参数：μ ν : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
-/
theorem coeFn_add (μ ν : FiniteMeasure Ω) : (⇑(μ + ν) : Set Ω → ℝ≥0) = (⇑μ + ⇑ν : Set Ω → ℝ≥0) := by
  funext
  simp only [Pi.add_apply, ← ENNReal.coe_inj, ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_add]
  norm_cast

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.coeFn_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.FiniteMeasure`。
形式化陈述：coeFn_smul [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω)
 : (⇑(c • μ) : Set Ω -> Real>=0) = c • (⇑μ : Set Ω -> Real>=0)
参数：c : R；μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `ENNReal.coe_smul`：coe_smul {R} (r : R) (s : Real>=0) [SMul R Real>=0] [S
Mul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0] [IsScalarTower R Real>=0 Real>
=0∞] :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeFn_smul [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) :
    (⇑(c • μ) : Set Ω → ℝ≥0) = c • (⇑μ : Set Ω → ℝ≥0) := by
  funext; simp [← ENNReal.coe_inj, ENNReal.coe_smul]
/-
**MeasureTheory.FiniteMeasure.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory.FiniteMeasure`。
形式化陈述：instAddCommMonoid : AddCommMonoid (FiniteMeasure Ω)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (FiniteMeasure Ω) := fast_instance%
  toMeasure_injective.addCommMonoid _ toMeasure_zero toMeasure_add fun _ _ ↦ toMeasure_smul _ _

/-- Coercion is an `AddMonoidHom`. -/
@[simps]
/-
**MeasureTheory.FiniteMeasure.toMeasureAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `M
easureTheory.FiniteMeasure`。
形式化陈述：toMeasureAddMonoidHom : FiniteMeasure Ω ->+ Measure Ω where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.toMeasure_zero`：toMeasure_zero : ((↑) : Fini
teMeasure Ω -> Measure Ω) 0 = 0
· 使用定理 `MeasureTheory.FiniteMeasure.toMeasure_add`：toMeasure_add (μ ν : FiniteMe
asure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω)

--- 原说明 ---
Coercion is an `AddMonoidHom`.
-/
def toMeasureAddMonoidHom : FiniteMeasure Ω →+ Measure Ω where
  toFun := (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

@[simp, norm_cast]
/-
**MeasureTheory.FiniteMeasure.toMeasure_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：toMeasure_sum {ι : Type*} {s : Finset ι} {ν : ι -> FiniteMeasure Ω} : ↑(∑ 
i in s, ν i) = ∑ i in s, (ν i : Measure Ω)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toMeasure_sum {ι : Type*} {s : Finset ι} {ν : ι → FiniteMeasure Ω} :
    ↑(∑ i ∈ s, ν i) = ∑ i ∈ s, (ν i : Measure Ω) :=
  map_sum toMeasureAddMonoidHom _ _
/-
**MeasureTheory.FiniteMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.FiniteMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Ω : Type*} [MeasurableSpace Ω] : Module ℝ≥0 (FiniteMeasure Ω) :=
  Function.Injective.module _ toMeasureAddMonoidHom toMeasure_injective toMeasure_smul

@[simp]
/-
**MeasureTheory.FiniteMeasure.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.FiniteMeasure`。
形式化陈述：smul_apply [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω)
 (s : Set Ω) : (c • μ) s = c • μ s
参数：c : R；μ : FiniteMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.coeFn_smul`：coeFn_smul [IsScalarTower R Real
>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω) : (⇑(c • μ) : Set Ω -> Real>=0) = c •
 (⇑μ : Set Ω -> Real>=0)
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
-/
theorem smul_apply [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) :
    (c • μ) s = c • μ s := by
  rw [coeFn_smul, Pi.smul_apply]

/-- Restrict a finite measure μ to a set A. -/
/-
**MeasureTheory.FiniteMeasure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
FiniteMeasure`。
形式化陈述：restrict (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω where val
参数：μ : FiniteMeasure Ω；A : Set Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a finite measure μ to a set A.
-/
def restrict (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω where
  val := (μ : Measure Ω).restrict A
  property := MeasureTheory.isFiniteMeasureRestrict (μ : Measure Ω) A

@[simp]
/-
**MeasureTheory.FiniteMeasure.restrict_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FiniteMeasure`。
形式化陈述：restrict_measure_eq (μ : FiniteMeasure Ω) (A : Set Ω) : (μ.restrict A : Me
asure Ω) = (μ : Measure Ω).restrict A
参数：μ : FiniteMeasure Ω；A : Set Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_measure_eq (μ : FiniteMeasure Ω) (A : Set Ω) :
    (μ.restrict A : Measure Ω) = (μ : Measure Ω).restrict A := rfl
/-
**MeasureTheory.FiniteMeasure.restrict_apply_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.FiniteMeasure`。
形式化陈述：restrict_apply_measure (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω} (s_mb
le : MeasurableSet s) : (μ.restrict A : Measure Ω) s = (μ : Measure Ω) (s inter 
A)
参数：μ : FiniteMeasure Ω；A : Set Ω；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
theorem restrict_apply_measure (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω}
    (s_mble : MeasurableSet s) : (μ.restrict A : Measure Ω) s = (μ : Measure Ω) (s ∩ A) :=
  Measure.restrict_apply s_mble

@[simp]
/-
**MeasureTheory.FiniteMeasure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：restrict_apply (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω} (s_mble : Mea
surableSet s) : (μ.restrict A) s = μ (s inter A)
参数：μ : FiniteMeasure Ω；A : Set Ω；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
theorem restrict_apply (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω} (s_mble : MeasurableSet s) :
    (μ.restrict A) s = μ (s ∩ A) := by
  apply congr_arg ENNReal.toNNReal
  exact Measure.restrict_apply s_mble

@[simp]
/-
**MeasureTheory.FiniteMeasure.restrict_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：restrict_mass (μ : FiniteMeasure Ω) (A : Set Ω) : (μ.restrict A).mass = μ 
A
参数：μ : FiniteMeasure Ω；A : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.restrict_apply`：restrict_apply (μ : FiniteMe
asure Ω) (A : Set Ω) {s : Set Ω} (s_mble : MeasurableSet s) : (μ.restrict A) s =
 μ (s inter A)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_mass (μ : FiniteMeasure Ω) (A : Set Ω) : (μ.restrict A).mass = μ A := by
  simp only [mass, restrict_apply μ A MeasurableSet.univ, univ_inter]
/-
**MeasureTheory.FiniteMeasure.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.FiniteMeasu
re Ω}, μ.restrict Set.univ = μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma restrict_univ {μ : FiniteMeasure Ω} : μ.restrict univ = μ := by
  ext; simp
/-
**MeasureTheory.FiniteMeasure.restrict_union** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：restrict_union {μ : FiniteMeasure Ω} {s t : Set Ω} (h : Disjoint s t) (ht 
: MeasurableSet t) : μ.restrict (s union t) = μ.restrict s + μ.restrict t
参数：h : Disjoint s t；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_union`：restrict_union (h : Disjoint s t) 
(ht : MeasurableSet t) : μ.restrict (s union t) = μ.restrict s + μ.restrict t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_union {μ : FiniteMeasure Ω} {s t : Set Ω} (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  ext u hu
  simp [Measure.restrict_union h ht]
/-
**MeasureTheory.FiniteMeasure.restrict_biUnion_finset** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.FiniteMeasure`。
形式化陈述：restrict_biUnion_finset {ι : Type*} {μ : FiniteMeasure Ω} {T : Finset ι} {
s : ι -> Set Ω} (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : forall i, Meas
urableSet (s i)) : μ.restrict (⋃ i in T, s i) = ∑ i in T, μ.restrict (s i)
参数：hd : (T : Set ι).Pairwise (Disjoint on s)；hm : forall i, MeasurableSet (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.FiniteMeasure.toMeasure_sum`：toMeasure_sum {ι : Type*} {s 
: Finset ι} {ν : ι -> FiniteMeasure Ω} : ↑(∑ i in s, ν i) = ∑ i in s, (ν i : Mea
sure Ω)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.Measure.coe_finsetSum`：coe_finsetSum {_m : MeasurableSpace
 α} (I : Finset ι) (μ : ι -> Measure α) : ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `MeasureTheory.Measure.restrict_biUnion_finset`：restrict_biUnion_finset {
s : ι -> Set α} {T : Finset ι} (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm :
 forall i, MeasurableSet (s i)) : μ…
· 使用定理 `MeasureTheory.Measure.sum_fintype`：sum_fintype [Fintype ι] (μ : ι -> Mea
sure α) : sum μ = ∑ i, μ i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
-/
lemma restrict_biUnion_finset {ι : Type*} {μ : FiniteMeasure Ω} {T : Finset ι}
    {s : ι → Set Ω} (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.restrict (⋃ i ∈ T, s i) = ∑ i ∈ T, μ.restrict (s i) := by
  ext t ht
  simp only [restrict_measure_eq, toMeasure_sum, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.restrict_biUnion_finset hd hm]
  simp only [Measure.sum_fintype, Finset.univ_eq_attach, Measure.coe_finsetSum, Finset.sum_apply]
  conv_rhs => rw [← Finset.sum_attach]

@[simp]
/-
**MeasureTheory.FiniteMeasure.restrict_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.FiniteMeasure`。
形式化陈述：restrict_eq_zero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A = 0 
↔ μ A = 0
参数：μ : FiniteMeasure Ω；A : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_zero_iff`：mass_zero_iff (μ : FiniteMeas
ure Ω) : μ.mass = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.FiniteMeasure.restrict_mass`：restrict_mass (μ : FiniteMeas
ure Ω) (A : Set Ω) : (μ.restrict A).mass = μ A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_eq_zero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A = 0 ↔ μ A = 0 := by
  rw [← mass_zero_iff, restrict_mass]
/-
**MeasureTheory.FiniteMeasure.restrict_nonzero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.FiniteMeasure`。
形式化陈述：restrict_nonzero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A != 0
 ↔ μ A != 0
参数：μ : FiniteMeasure Ω；A : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrict_nonzero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A ≠ 0 ↔ μ A ≠ 0 := by
  simp

/-- The type of finite measures is a measurable space when equipped with the Giry monad. -/
/-
**MeasureTheory.FiniteMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.FiniteMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of finite measures is a measurable space when equipped with the Giry mo
nad.
-/
instance : MeasurableSpace (FiniteMeasure Ω) :=
  inferInstanceAs <| MeasurableSpace (Subtype _)

/-- The set of all finite measures is a measurable set in the Giry monad. -/
/-
**MeasureTheory.FiniteMeasure.measurableSet_isFiniteMeasure** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：measurableSet_isFiniteMeasure : MeasurableSet { μ : Measure Ω | IsFiniteMe
asure μ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.isFiniteMeasure_iff`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} (μ : MeasureTheory.Measure α),   MeasureTheory.IsFiniteMeasure μ ↔ μ Set.un
iv < ⊤
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal

--- 原说明 ---
The set of all finite measures is a measurable set in the Giry monad.
-/
lemma measurableSet_isFiniteMeasure : MeasurableSet { μ : Measure Ω | IsFiniteMeasure μ } := by
  suffices { μ : Measure Ω | IsFiniteMeasure μ } = (fun μ => μ univ) ⁻¹' (Set.Ico 0 ∞) by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ measurableSet_Ico
  ext μ
  simp only [mem_ofPred_eq, mem_preimage, mem_Ico, zero_le, true_and]
  exact isFiniteMeasure_iff μ

/-- The monoidal product is a measurable function from the product of finite measures over
`α` and `β` into the type of finite measures over `α × β`. -/
/-
**MeasureTheory.FiniteMeasure.measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FiniteMeasure`。
形式化陈述：measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] 
: Measurable (fun (μ : FiniteMeasure α × FiniteMeasure β) => μ.1.toMeasure.prod 
μ.2.toMeasure)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Measurable.measure_of_isPiSystem`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} {μ : α → MeasureTheory.Measure β}   
[∀ (a : α), MeasureThe…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ

--- 原说明 ---
The monoidal product is a measurable function from the product of finite measure
s over
`α` and `β` into the type of finite measures over `α × β`.
-/
theorem measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (μ : FiniteMeasure α × FiniteMeasure β)
      ↦ μ.1.toMeasure.prod μ.2.toMeasure) := by
  have Heval {u v} (Hu : MeasurableSet u) (Hv : MeasurableSet v) :
      Measurable fun a : (FiniteMeasure α × FiniteMeasure β) ↦
      a.1.toMeasure u * a.2.toMeasure v :=
    Measurable.mul
      ((Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst))
      ((Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd))
  apply Measurable.measure_of_isPiSystem generateFrom_prod.symm isPiSystem_prod _
  · simp_rw [← Set.univ_prod_univ, Measure.prod_prod, Heval MeasurableSet.univ MeasurableSet.univ]
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ _ Hu _ Hv Heq
  simp_rw [← Heq, Measure.prod_prod, Heval Hu Hv]
/-
**MeasureTheory.FiniteMeasure.apply_iUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.FiniteMeasure`。
形式化陈述：apply_iUnion_le {μ : FiniteMeasure Ω} {f : Nat -> Set Ω} (hf : Summable fu
n n => μ (f n)) : μ (⋃ n, f n) <= ∑' n, μ (f n)
参数：hf : Summable fun n => μ (f n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `ENNReal.coe_tsum`：∀ {α : Type u_1} {f : α → NNReal}, Summable f → ↑(tsum
 f) = ∑' (a : α), ↑(f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instCountableNat`：Countable ℕ
-/
lemma apply_iUnion_le {μ : FiniteMeasure Ω} {f : ℕ → Set Ω}
    (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

variable [TopologicalSpace Ω]

/-- Two finite Borel measures are equal if the integrals of all non-negative bounded continuous
functions with respect to both agree. -/
/-
**MeasureTheory.FiniteMeasure.ext_of_forall_lintegral_eq** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：ext_of_forall_lintegral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : 
FiniteMeasure Ω} (h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
 μ = ν
参数：h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure`：ext_of_fora
ll_lintegral_eq_of_IsFiniteMeasure {Ω : Type*} [MeasurableSpace Ω] [TopologicalS
pace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] {…

--- 原说明 ---
Two finite Borel measures are equal if the integrals of all non-negative bounded
 continuous
functions with respect to both agree.
-/
theorem ext_of_forall_lintegral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {μ ν : FiniteMeasure Ω} (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  apply Subtype.ext
  change (μ : Measure Ω) = (ν : Measure Ω)
  exact ext_of_forall_lintegral_eq_of_IsFiniteMeasure h

/-- Two finite Borel measures are equal if the integrals of all bounded continuous functions with
respect to both agree. -/
/-
**MeasureTheory.FiniteMeasure.ext_of_forall_integral_eq** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.FiniteMeasure`。
形式化陈述：ext_of_forall_integral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : F
initeMeasure Ω} (h : forall (f : Ω ->ᵇ Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν
参数：h : forall (f : Ω ->ᵇ Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.ext_of_forall_lintegral_eq`：ext_of_forall_li
ntegral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : FiniteMeasure Ω} (h : 
forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.toReal_lintegral_coe_eq_integral`：toReal_linte
gral_coe_eq_integral [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) (μ : Measure X
) : (∫⁻ x, (f x : Real>=0∞) ∂μ).toReal = ∫ x, (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `BoundedContinuousFunction.map_bounded'`：∀ {α : Type u} {β : Type v} [ins
t : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (self : BoundedContinuo
usFunction α β), ∃ C, ∀ (x y…

--- 原说明 ---
Two finite Borel measures are equal if the integrals of all bounded continuous f
unctions with
respect to both agree.
-/
theorem ext_of_forall_integral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {μ ν : FiniteMeasure Ω} (h : ∀ (f : Ω →ᵇ ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply ext_of_forall_lintegral_eq
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ, toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `MeasureTheory.FiniteMeasure.testAgainstNN`. -/
/-
**MeasureTheory.FiniteMeasure.testAgainstNN** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.FiniteMeasure`。
形式化陈述：testAgainstNN (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) : Real>=0
参数：μ : FiniteMeasure Ω；f : Ω ->ᵇ Real>=0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuou
s
function is obtained by (Lebesgue) integrating the (test) function against the m
easure.
This is `MeasureTheory.FiniteMeasure.testAgainstNN`.
-/
def testAgainstNN (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) : ℝ≥0 :=
  (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal

@[simp]
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_coe_eq {μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAg
ainstNN f : Real>=0∞) = ∫⁻ ω, f ω ∂(μ : Measure Ω)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
-/
theorem testAgainstNN_coe_eq {μ : FiniteMeasure Ω} {f : Ω →ᵇ ℝ≥0} :
    (μ.testAgainstNN f : ℝ≥0∞) = ∫⁻ ω, f ω ∂(μ : Measure Ω) :=
  ENNReal.coe_toNNReal (f.lintegral_lt_top_of_nnreal _).ne
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_const** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_const (μ : FiniteMeasure Ω) (c : Real>=0) : μ.testAgainstNN 
(BoundedContinuousFunction.const Ω c) = c * μ.mass
参数：μ : FiniteMeasure Ω；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq`：testAgainstNN_coe_eq {
μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω
, f ω ∂(μ : Measure Ω)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_mass`：ennreal_mass {μ : FiniteMeasur
e Ω} : (μ.mass : Real>=0∞) = (μ : Measure Ω) univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem testAgainstNN_const (μ : FiniteMeasure Ω) (c : ℝ≥0) :
    μ.testAgainstNN (BoundedContinuousFunction.const Ω c) = c * μ.mass := by
  simp [← ENNReal.coe_inj]
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_mono** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_mono (μ : FiniteMeasure Ω) {f g : Ω ->ᵇ Real>=0} (f_le_g : (
f : Ω -> Real>=0) <= g) : μ.testAgainstNN f <= μ.testAgainstNN g
参数：μ : FiniteMeasure Ω；f_le_g : (f : Ω -> Real>=0) <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq`：testAgainstNN_coe_eq {
μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω
, f ω ∂(μ : Measure Ω)
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
-/
theorem testAgainstNN_mono (μ : FiniteMeasure Ω) {f g : Ω →ᵇ ℝ≥0} (f_le_g : (f : Ω → ℝ≥0) ≤ g) :
    μ.testAgainstNN f ≤ μ.testAgainstNN g := by
  simp only [← ENNReal.coe_le_coe, testAgainstNN_coe_eq]
  gcongr
  apply f_le_g

@[simp]
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_zero** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_zero (μ : FiniteMeasure Ω) : μ.testAgainstNN 0 = 0
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_const`：testAgainstNN_const (μ 
: FiniteMeasure Ω) (c : Real>=0) : μ.testAgainstNN (BoundedContinuousFunction.co
nst Ω c) = c * μ.mass
-/
theorem testAgainstNN_zero (μ : FiniteMeasure Ω) : μ.testAgainstNN 0 = 0 := by
  simpa only [zero_mul] using! μ.testAgainstNN_const 0

@[simp]
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_one** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_one (μ : FiniteMeasure Ω) : μ.testAgainstNN 1 = μ.mass
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
-/
theorem testAgainstNN_one (μ : FiniteMeasure Ω) : μ.testAgainstNN 1 = μ.mass := by
  simp only [testAgainstNN, coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_one]
  rfl

@[simp]
/-
**MeasureTheory.FiniteMeasure.zero_testAgainstNN_apply** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.FiniteMeasure`。
形式化陈述：zero_testAgainstNN_apply (f : Ω ->ᵇ Real>=0) : (0 : FiniteMeasure Ω).testA
gainstNN f = 0
参数：f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_testAgainstNN_apply (f : Ω →ᵇ ℝ≥0) : (0 : FiniteMeasure Ω).testAgainstNN f = 0 := by
  simp only [testAgainstNN, toMeasure_zero, lintegral_zero_measure, ENNReal.toNNReal_zero]
/-
**MeasureTheory.FiniteMeasure.zero_testAgainstNN** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FiniteMeasure`。
形式化陈述：zero_testAgainstNN : (0 : FiniteMeasure Ω).testAgainstNN = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.zero_testAgainstNN_apply`：zero_testAgainstNN
_apply (f : Ω ->ᵇ Real>=0) : (0 : FiniteMeasure Ω).testAgainstNN f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_testAgainstNN : (0 : FiniteMeasure Ω).testAgainstNN = 0 := by
  funext
  simp only [zero_testAgainstNN_apply, Pi.zero_apply]

@[simp]
/-
**MeasureTheory.FiniteMeasure.smul_testAgainstNN_apply** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.FiniteMeasure`。
形式化陈述：smul_testAgainstNN_apply (c : Real>=0) (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Re
al>=0) : (c • μ).testAgainstNN f = c • μ.testAgainstNN f
参数：c : Real>=0；μ : FiniteMeasure Ω；f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_testAgainstNN_apply (c : ℝ≥0) (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    (c • μ).testAgainstNN f = c • μ.testAgainstNN f := by
  simp only [testAgainstNN, toMeasure_smul, smul_eq_mul, ← ENNReal.smul_toNNReal, ENNReal.smul_def,
    lintegral_smul_measure]

section weak_convergence

variable [OpensMeasurableSpace Ω]

/-
**MeasureTheory.FiniteMeasure.testAgainstNN_add** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_add (μ : FiniteMeasure Ω) (f₁ f₂ : Ω ->ᵇ Real>=0) : μ.testAg
ainstNN (f₁ + f₂) = μ.testAgainstNN f₁ + μ.testAgainstNN f₂
参数：μ : FiniteMeasure Ω；f₁ f₂ : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq`：testAgainstNN_coe_eq {
μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω
, f ω ∂(μ : Measure Ω)
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `BoundedContinuousFunction.measurable_coe_ennreal_comp`：measurable_coe_en
nreal_comp [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) : Measurable fun x => (f
 x : Real>=0∞)
-/
theorem testAgainstNN_add (μ : FiniteMeasure Ω) (f₁ f₂ : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN (f₁ + f₂) = μ.testAgainstNN f₁ + μ.testAgainstNN f₂ := by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_add, ENNReal.coe_add, Pi.add_apply,
    testAgainstNN_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.measurable_coe_ennreal_comp _) _
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_smul** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_smul [IsScalarTower R Real>=0 Real>=0] [PseudoMetricSpace R]
 [Zero R] [IsBoundedSMul R Real>=0] (μ : FiniteMeasure Ω) (c : R) (f : Ω ->ᵇ Rea
l>=0) : μ.testAgainstNN (c • f) = c • μ.testAgainstNN f
参数：μ : FiniteMeasure Ω；c : R；f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq`：testAgainstNN_coe_eq {
μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω
, f ω ∂(μ : Measure Ω)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_smul`：coe_smul {R} (r : R) (s : Real>=0) [SMul R Real>=0] [S
Mul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0] [IsScalarTower R Real>=0 Real>
=0∞] :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `BoundedContinuousFunction.measurable_coe_ennreal_comp`：measurable_coe_en
nreal_comp [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) : Measurable fun x => (f
 x : Real>=0∞)
-/
theorem testAgainstNN_smul [IsScalarTower R ℝ≥0 ℝ≥0] [PseudoMetricSpace R] [Zero R]
    [IsBoundedSMul R ℝ≥0] (μ : FiniteMeasure Ω) (c : R) (f : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN (c • f) = c • μ.testAgainstNN f := by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_smul, testAgainstNN_coe_eq,
    ENNReal.coe_smul]
  simp_rw [← smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ← smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞),
    smul_eq_mul]
  exact lintegral_const_mul (c • (1 : ℝ≥0∞)) f.measurable_coe_ennreal_comp
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz_estimate** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω ->ᵇ Real>=
0) : μ.testAgainstNN f <= μ.testAgainstNN g + nndist f g * μ.mass
参数：μ : FiniteMeasure Ω；f g : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_const`：testAgainstNN_const (μ 
: FiniteMeasure Ω) (c : Real>=0) : μ.testAgainstNN (BoundedContinuousFunction.co
nst Ω c) = c * μ.mass
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq`：testAgainstNN_coe_eq {
μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} : (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω
, f ω ∂(μ : Measure Ω)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `coe_nnreal_ennreal_nndist`：coe_nnreal_ennreal_nndist (x y : α) : ↑(nndis
t x y) = edist x y
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用引理 `NNReal.le_add_nndist`：NNReal.le_add_nndist (a b : Real>=0) : a <= b + nn
dist a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem testAgainstNN_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN f ≤ μ.testAgainstNN g + nndist f g * μ.mass := by
  simp only [← μ.testAgainstNN_const (nndist f g), ← testAgainstNN_add, ← ENNReal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, ENNReal.coe_add, Pi.add_apply,
    coe_nnreal_ennreal_nndist, testAgainstNN_coe_eq]
  apply lintegral_mono
  have le_dist : ∀ ω, dist (f ω) (g ω) ≤ nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro ω
  have le' : f ω ≤ g ω + nndist f g := by
    calc f ω
     _ ≤ g ω + nndist (f ω) (g ω) := NNReal.le_add_nndist (f ω) (g ω)
     _ ≤ g ω + nndist f g := (add_le_add_iff_left (g ω)).mpr (le_dist ω)
  have le : (f ω : ℝ≥0∞) ≤ (g ω : ℝ≥0∞) + nndist f g := by
    simpa only [← ENNReal.coe_add] using (by exact_mod_cast le')
  rwa [coe_nnreal_ennreal_nndist] at le
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_lipschitz (μ : FiniteMeasure Ω) : LipschitzWith μ.mass fun f
 : Ω ->ᵇ Real>=0 => μ.testAgainstNN f
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz_estimate`：testAgains
tNN_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω ->ᵇ Real>=0) : μ.testAgain
stNN f <= μ.testAgainstNN g + nndist f g * μ.mass
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 49 条，此处仅展示前 30 条）
-/
theorem testAgainstNN_lipschitz (μ : FiniteMeasure Ω) :
    LipschitzWith μ.mass fun f : Ω →ᵇ ℝ≥0 ↦ μ.testAgainstNN f := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.testAgainstNN f₁ - μ.testAgainstNN f₂ : ℝ) ≤ μ.mass * dist f₁ f₂ by
    rwa [NNReal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key := μ.testAgainstNN_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₂) ≤ ↑(μ.testAgainstNN f₁) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa [nndist_comm] using NNReal.coe_mono key
  · have key := μ.testAgainstNN_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₁) ≤ ↑(μ.testAgainstNN f₂) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa using NNReal.coe_mono key

/-- Finite measures yield elements of the `WeakDual` of bounded continuous nonnegative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration. -/
/-
**MeasureTheory.FiniteMeasure.toWeakDualBCNN** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：toWeakDualBCNN (μ : FiniteMeasure Ω) : WeakDual Real>=0 (Ω ->ᵇ Real>=0) wh
ere toFun f
参数：μ : FiniteMeasure Ω。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_add`：testAgainstNN_add (μ : Fi
niteMeasure Ω) (f₁ f₂ : Ω ->ᵇ Real>=0) : μ.testAgainstNN (f₁ + f₂) = μ.testAgain
stNN f₁ + μ.testAgainstNN f₂

--- 原说明 ---
Finite measures yield elements of the `WeakDual` of bounded continuous nonnegati
ve
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration.
-/
def toWeakDualBCNN (μ : FiniteMeasure Ω) : WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) where
  toFun f := μ.testAgainstNN f
  map_add' := testAgainstNN_add μ
  map_smul' := testAgainstNN_smul μ
  cont := μ.testAgainstNN_lipschitz.continuous

@[simp]
/-
**MeasureTheory.FiniteMeasure.coe_toWeakDualBCNN** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.FiniteMeasure`。
形式化陈述：coe_toWeakDualBCNN (μ : FiniteMeasure Ω) : ⇑μ.toWeakDualBCNN = μ.testAgain
stNN
参数：μ : FiniteMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
-/
theorem coe_toWeakDualBCNN (μ : FiniteMeasure Ω) : ⇑μ.toWeakDualBCNN = μ.testAgainstNN :=
  rfl

@[simp]
/-
**MeasureTheory.FiniteMeasure.toWeakDualBCNN_apply** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.FiniteMeasure`。
形式化陈述：toWeakDualBCNN_apply (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) : μ.toWeakD
ualBCNN f = (∫⁻ x, f x ∂(μ : Measure Ω)).toNNReal
参数：μ : FiniteMeasure Ω；f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
-/
theorem toWeakDualBCNN_apply (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBCNN f = (∫⁻ x, f x ∂(μ : Measure Ω)).toNNReal := rfl

/-- The topology of weak convergence on `MeasureTheory.FiniteMeasure Ω` is inherited (induced)
from the weak-\* topology on `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)` via the function
`MeasureTheory.FiniteMeasure.toWeakDualBCNN`. -/
/-
**MeasureTheory.FiniteMeasure.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Me
asureTheory.FiniteMeasure`。
形式化陈述：instTopologicalSpace : TopologicalSpace (FiniteMeasure Ω)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of weak convergence on `MeasureTheory.FiniteMeasure Ω` is inherited
 (induced)
from the weak-\* topology on `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)` via the function
`MeasureTheory.FiniteMeasure.toWeakDualBCNN`.
-/
instance instTopologicalSpace : TopologicalSpace (FiniteMeasure Ω) :=
  TopologicalSpace.induced toWeakDualBCNN inferInstance
/-
**MeasureTheory.FiniteMeasure.toWeakDualBCNN_continuous** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.FiniteMeasure`。
形式化陈述：toWeakDualBCNN_continuous : Continuous (@toWeakDualBCNN Ω _ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
-/
theorem toWeakDualBCNN_continuous : Continuous (@toWeakDualBCNN Ω _ _ _) :=
  continuous_induced_dom

/-- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
/-
**MeasureTheory.FiniteMeasure.continuous_testAgainstNN_eval** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：continuous_testAgainstNN_eval (f : Ω ->ᵇ Real>=0) : Continuous fun μ : Fin
iteMeasure Ω => μ.testAgainstNN f
参数：f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y
· 使用定理 `MeasureTheory.FiniteMeasure.toWeakDualBCNN_continuous`：toWeakDualBCNN_co
ntinuous : Continuous (@toWeakDualBCNN Ω _ _ _)

--- 原说明 ---
Integration of (nonnegative bounded continuous) test functions against finite Bo
rel measures
depends continuously on the measure.
-/
theorem continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0) :
    Continuous fun μ : FiniteMeasure Ω ↦ μ.testAgainstNN f := by
  change Continuous ((fun φ : WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) ↦ φ f) ∘ toWeakDualBCNN)
  refine Continuous.comp ?_ (toWeakDualBCNN_continuous (Ω := Ω))
  exact WeakBilin.eval_continuous _ _

/-- The total mass of a finite measure depends continuously on the measure. -/
/-
**MeasureTheory.FiniteMeasure.continuous_mass** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : TopologicalSpace Ω] 
[inst_2 : OpensMeasurableSpace Ω],   Continuous fun μ => μ.mass
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.FiniteMeasure.continuous_testAgainstNN_eval`：continuous_te
stAgainstNN_eval (f : Ω ->ᵇ Real>=0) : Continuous fun μ : FiniteMeasure Ω => μ.t
estAgainstNN f

--- 原说明 ---
The total mass of a finite measure depends continuously on the measure.
-/
@[fun_prop] theorem continuous_mass : Continuous fun μ : FiniteMeasure Ω ↦ μ.mass := by
  simp_rw [← testAgainstNN_one]; exact continuous_testAgainstNN_eval 1

/-- Convergence of finite measures implies the convergence of their total masses. -/
/-
**MeasureTheory.FiniteMeasure._root_.Filter.Tendsto.mass** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.FiniteMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convergence of finite measures implies the convergence of their total masses.
-/
theorem _root_.Filter.Tendsto.mass {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} (h : Tendsto μs F (𝓝 μ)) : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass) :=
  (continuous_mass.tendsto μ).comp h
/-
**MeasureTheory.FiniteMeasure.tendsto_iff_weakDual_tendsto** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_iff_weakDual_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteM
easure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i => (μs i).
toWeakDualBCNN) F (𝓝 μ.toWeakDualBCNN)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
-/
theorem tendsto_iff_weakDual_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i ↦ (μs i).toWeakDualBCNN) F (𝓝 μ.toWeakDualBCNN) :=
  IsInducing.tendsto_nhds_iff ⟨rfl⟩
/-
**MeasureTheory.FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_iff_forall_toWeakDualBCNN_tendsto {γ : Type*} {F : Filter γ} {μs :
 γ -> FiniteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ forall f : Ω
 ->ᵇ Real>=0, Tendsto (fun i => (μs i).toWeakDualBCNN f) F (𝓝 (μ.toWeakDualBCNN 
f))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_weakDual_tendsto`：tendsto_iff_we
akDual_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω} {μ : Finit
eMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ Tendsto (fu…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `tendsto_iff_forall_eval_tendsto_topDualPairing`：tendsto_iff_forall_eval_
tendsto_topDualPairing {l : Filter α} {f : α -> WeakDual 𝕜 E} {x : WeakDual 𝕜 E}
 : Tendsto f l (𝓝 x) ↔ forall y, Ten…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_forall_toWeakDualBCNN_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0, Tendsto (fun i ↦ (μs i).toWeakDualBCNN f) F (𝓝 (μ.toWeakDualBCNN f)) := by
  rw [tendsto_iff_weakDual_tendsto, tendsto_iff_forall_eval_tendsto_topDualPairing]; rfl
/-
**MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : 
γ -> FiniteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ forall f : Ω 
->ᵇ Real>=0, Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto`：t
endsto_iff_forall_toWeakDualBCNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> F
initeMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0, Tendsto (fun i ↦ (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  rw [FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto]; rfl

/-- If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass` for
a formulation stating the weak convergence of measures. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_zero_testAgainstNN_of_tendsto_zero_mass** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_zero_testAgainstNN_of_tendsto_zero_mass {γ : Type*} {F : Filter γ}
 {μs : γ -> FiniteMeasure Ω} (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0))
 (f : Ω ->ᵇ Real>=0) : Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 0)
参数：mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)；f : Ω ->ᵇ Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz_estimate`：testAgains
tNN_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω ->ᵇ Real>=0) : μ.testAgain
stNN f <= μ.testAgainstNN g + nndist f g * μ.mass
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `NNReal.nndist_zero_eq_val'`：NNReal.nndist_zero_eq_val' (z : Real>=0) : n
ndist z 0 = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_zero`：testAgainstNN_zero (μ : 
FiniteMeasure Ω) : μ.testAgainstNN 0 = 0
· 使用定理 `Prod.tendsto_iff`：Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X}
 (p : Y × Z) : Tendsto seq f (𝓝 p) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) 
∧ Tend…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ

--- 原说明 ---
If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `MeasureTheory.FiniteMeasure.tendsto_zero_of_ten
dsto_zero_mass` for
a formulation stating the weak convergence of measures.
-/
theorem tendsto_zero_testAgainstNN_of_tendsto_zero_mass {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 0)) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i ↦ (μs i).testAgainstNN f) F (𝓝 0) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have obs := fun i ↦ (μs i).testAgainstNN_lipschitz_estimate f 0
  simp_rw [testAgainstNN_zero, zero_add] at obs
  simp_rw [show ∀ i, dist ((μs i).testAgainstNN f) 0 = (μs i).testAgainstNN f by
      simp only [dist_nndist, NNReal.nndist_zero_eq_val', imp_true_iff]]
  apply squeeze_zero (fun i ↦ NNReal.coe_nonneg _) obs
  have lim_pair : Tendsto (fun i ↦ (⟨nndist f 0, (μs i).mass⟩ : ℝ × ℝ)) F (𝓝 ⟨nndist f 0, 0⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, (NNReal.continuous_coe.tendsto 0).comp mass_lim⟩
  simpa using! tendsto_mul.comp lim_pair

/-- If the total masses of finite measures tend to zero, then the measures tend to zero. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_zero_of_tendsto_zero_mass {γ : Type*} {F : Filter γ} {μs : γ -> Fi
niteMeasure Ω} (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)) : Tendsto μs 
F (𝓝 0)
参数：mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`：te
ndsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Fin
iteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.zero_testAgainstNN_apply`：zero_testAgainstNN
_apply (f : Ω ->ᵇ Real>=0) : (0 : FiniteMeasure Ω).testAgainstNN f = 0
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_zero_testAgainstNN_of_tendsto_zero_m
ass`：tendsto_zero_testAgainstNN_of_tendsto_zero_mass {γ : Type*} {F : Filter γ} 
{μs : γ -> FiniteMeasure Ω} (mass_lim : Tendsto (fun i => (μs i).…

--- 原说明 ---
If the total masses of finite measures tend to zero, then the measures tend to z
ero.
-/
theorem tendsto_zero_of_tendsto_zero_mass {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 0)) : Tendsto μs F (𝓝 0) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  convert! tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  rw [zero_testAgainstNN_apply]

/-- A characterization of weak convergence in terms of integrals of bounded continuous
nonnegative functions. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ ->
 FiniteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ forall f : Ω ->ᵇ 
Real>=0, Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ x, f x ∂(μ : 
Measure Ω)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto`：t
endsto_iff_forall_toWeakDualBCNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> F
initeMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.FiniteMeasure.toWeakDualBCNN_apply`：toWeakDualBCNN_apply (
μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) : μ.toWeakDualBCNN f = (∫⁻ x, f x ∂(μ :
 Measure Ω)).toNNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A characterization of weak convergence in terms of integrals of bounded continuo
us
nonnegative functions.
-/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0,
        Tendsto (fun i ↦ ∫⁻ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure Ω))) := by
  rw [tendsto_iff_forall_toWeakDualBCNN_tendsto]
  simp_rw [toWeakDualBCNN_apply _ _, ← testAgainstNN_coe_eq, ENNReal.tendsto_coe,
    ENNReal.toNNReal_coe]
/-
**MeasureTheory.FiniteMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.FiniteMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R1Space (FiniteMeasure Ω) := IsInducing.r1Space (f := toWeakDualBCNN) ⟨rfl⟩

end weak_convergence -- section

section Hausdorff

variable [HasOuterApproxClosed Ω] [BorelSpace Ω]

open Function

/-- The mapping `toWeakDualBCNN` from finite Borel measures to the weak dual of `Ω →ᵇ ℝ≥0` is
injective, if in the underlying space `Ω`, indicator functions of closed sets have decreasing
approximations by sequences of continuous functions (in particular if `Ω` is pseudometrizable). -/
/-
**MeasureTheory.FiniteMeasure.injective_toWeakDualBCNN** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.FiniteMeasure`。
形式化陈述：injective_toWeakDualBCNN : Injective (toWeakDualBCNN : FiniteMeasure Ω -> 
WeakDual Real>=0 (Ω ->ᵇ Real>=0))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.FiniteMeasure.ext_of_forall_lintegral_eq`：ext_of_forall_li
ntegral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : FiniteMeasure Ω} (h : 
forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toNNReal_eq_toNNReal_iff'`：toNNReal_eq_toNNReal_iff' {x y : Real
>=0∞} (hx : x != ⊤) (hy : y != ⊤) : x.toNNReal = y.toNNReal ↔ x = y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞

--- 原说明 ---
The mapping `toWeakDualBCNN` from finite Borel measures to the weak dual of `Ω →
ᵇ ℝ≥0` is
injective, if in the underlying space `Ω`, indicator functions of closed sets ha
ve decreasing
approximations by sequences of continuous functions (in particular if `Ω` is pse
udometrizable).
-/
lemma injective_toWeakDualBCNN :
    Injective (toWeakDualBCNN : FiniteMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)) := by
  intro μ ν hμν
  apply ext_of_forall_lintegral_eq
  intro f
  have key := congr_fun (congrArg DFunLike.coe hμν) f
  apply (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp key
  · exact (lintegral_lt_top_of_nnreal μ f).ne
  · exact (lintegral_lt_top_of_nnreal ν f).ne

variable (Ω)
/-
**MeasureTheory.FiniteMeasure.isEmbedding_toWeakDualBCNN** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：isEmbedding_toWeakDualBCNN : IsEmbedding (toWeakDualBCNN : FiniteMeasure Ω
 -> WeakDual Real>=0 (Ω ->ᵇ Real>=0)) where eq_induced
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `MeasureTheory.FiniteMeasure.injective_toWeakDualBCNN`：injective_toWeakDu
alBCNN : Injective (toWeakDualBCNN : FiniteMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ 
Real>=0))
-/
lemma isEmbedding_toWeakDualBCNN :
    IsEmbedding (toWeakDualBCNN : FiniteMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)) where
  eq_induced := rfl
  injective := injective_toWeakDualBCNN

/-- On topological spaces where indicators of closed sets have decreasing approximating sequences of
continuous functions (`HasOuterApproxClosed`), the topology of weak convergence of finite Borel
measures is Hausdorff (`T2Space`). -/
/-
**MeasureTheory.FiniteMeasure.t2Space** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.F
initeMeasure`。
形式化陈述：t2Space : T2Space (FiniteMeasure Ω)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.FiniteMeasure.isEmbedding_toWeakDualBCNN`：isEmbedding_toWe
akDualBCNN : IsEmbedding (toWeakDualBCNN : FiniteMeasure Ω -> WeakDual Real>=0 (
Ω ->ᵇ Real>=0)) where eq_induced

--- 原说明 ---
On topological spaces where indicators of closed sets have decreasing approximat
ing sequences of
continuous functions (`HasOuterApproxClosed`), the topology of weak convergence 
of finite Borel
measures is Hausdorff (`T2Space`).
-/
instance t2Space : T2Space (FiniteMeasure Ω) := (isEmbedding_toWeakDualBCNN Ω).t2Space

end Hausdorff -- section

end FiniteMeasure

-- section
section FiniteMeasureBoundedConvergence

/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/


variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`MeasureTheory.lintegral`) against the finite
measure tend to the integral of the limit.

A related result with more general assumptions is
`MeasureTheory.tendsto_lintegral_nn_filter_of_le_const`.
-/
/-
**MeasureTheory.tendsto_lintegral_nn_of_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded
 by a constant
and tend pointwise to a limit, then their integrals (`MeasureTheory.lintegral`) 
against the finite
measure tend to the integral of the limit.

A related result with more general assumptions is
`MeasureTheory.tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure Ω) {fs : ℕ → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω → ℝ≥0}
    (fs_lim : ∀ ω, Tendsto (fun n ↦ fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n ↦ ∫⁻ ω, fs n ω ∂(μ : Measure Ω)) atTop (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) :=
  tendsto_lintegral_nn_filter_of_le_const μ
    (.of_forall fun n ↦ .of_forall (fs_le_const n))
    (.of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere;
* integration is the pairing against non-negative continuous test functions
  (`MeasureTheory.FiniteMeasure.testAgainstNN`).

A related result using `MeasureTheory.lintegral` for integration is
`MeasureTheory.FiniteMeasure.tendsto_lintegral_nn_filter_of_le_const`.
-/
/-
**MeasureTheory.tendsto_testAgainstNN_filter_of_le_const** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant
 and tend to a
limit, then their integrals against the finite measure tend to the integral of t
he limit.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere;
* integration is the pairing against non-negative continuous test functions
  (`MeasureTheory.FiniteMeasure.testAgainstNN`).

A related result using `MeasureTheory.lintegral` for integration is
`MeasureTheory.FiniteMeasure.tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_testAgainstNN_filter_of_le_const {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μ : FiniteMeasure Ω} {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂(μ : Measure Ω), fs i ω ≤ c) {f : Ω →ᵇ ℝ≥0}
    (fs_lim : ∀ᵐ ω : Ω ∂(μ : Measure Ω), Tendsto (fun i ↦ fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i ↦ μ.testAgainstNN (fs i)) L (𝓝 (μ.testAgainstNN f)) := by
  apply (ENNReal.tendsto_toNNReal (f.lintegral_lt_top_of_nnreal (μ : Measure Ω)).ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const (Ω := Ω) μ fs_le_const fs_lim

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant and
tend pointwise to a limit, then their integrals (`MeasureTheory.FiniteMeasure.testAgainstNN`)
against the finite measure tend to the integral of the limit.

Related results:
* `MeasureTheory.FiniteMeasure.tendsto_testAgainstNN_filter_of_le_const`:
  more general assumptions
* `MeasureTheory.FiniteMeasure.tendsto_lintegral_nn_of_le_const`:
  using `MeasureTheory.lintegral` for integration.
-/
/-
**MeasureTheory.tendsto_testAgainstNN_of_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded
 by a constant and
tend pointwise to a limit, then their integrals (`MeasureTheory.FiniteMeasure.te
stAgainstNN`)
against the finite measure tend to the integral of the limit.

Related results:
* `MeasureTheory.FiniteMeasure.tendsto_testAgainstNN_filter_of_le_const`:
  more general assumptions
* `MeasureTheory.FiniteMeasure.tendsto_lintegral_nn_of_le_const`:
  using `MeasureTheory.lintegral` for integration.
-/
theorem tendsto_testAgainstNN_of_le_const {μ : FiniteMeasure Ω} {fs : ℕ → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω →ᵇ ℝ≥0}
    (fs_lim : ∀ ω, Tendsto (fun n ↦ fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n ↦ μ.testAgainstNN (fs n)) atTop (𝓝 (μ.testAgainstNN f)) :=
  tendsto_testAgainstNN_filter_of_le_const
    (.of_forall fun n ↦ .of_forall (fs_le_const n))
    (.of_forall fs_lim)

end FiniteMeasureBoundedConvergence

-- section
section FiniteMeasureConvergenceByBoundedContinuousFunctions

/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/


variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-
**MeasureTheory.tendsto_of_forall_integral_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_of_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω}
    (h : ∀ f : Ω →ᵇ ℝ,
          Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω)))) :
    Tendsto μs F (𝓝 μ) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  apply (ENNReal.tendsto_toReal_iff (fi := F)
      (fun i ↦ (f.lintegral_lt_top_of_nnreal (μs i)).ne) (f.lintegral_lt_top_of_nnreal μ).ne).mp
  have lip : LipschitzWith 1 ((↑) : ℝ≥0 → ℝ) := NNReal.isometry_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with _def_f₀
  have f₀_eq : ⇑f₀ = ((↑) : ℝ≥0 → ℝ) ∘ ⇑f := rfl
  have f₀_nn : 0 ≤ ⇑f₀ := fun _ ↦ by
    simp only [f₀_eq, Pi.zero_apply, Function.comp_apply, NNReal.zero_le_coe]
  have f₀_ae_nn : 0 ≤ᵐ[(μ : Measure Ω)] ⇑f₀ := .of_forall f₀_nn
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : Measure Ω)] ⇑f₀ := fun i ↦ .of_forall f₀_nn
  have aux :=
    integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.aestronglyMeasurable
  have auxs := fun i ↦
    integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.aestronglyMeasurable
  simp_rw [f₀_eq, Function.comp_apply, ENNReal.ofReal_coe_nnreal] at aux auxs
  simpa only [← aux, ← auxs] using! h f₀

/-- A characterization of weak convergence in terms of integrals of bounded continuous
real-valued functions. -/
/-
**MeasureTheory.tendsto_iff_forall_integral_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A characterization of weak convergence in terms of integrals of bounded continuo
us
real-valued functions.
-/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ,
        Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  refine ⟨?_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  set f_pos := f.nnrealPart with _def_f_pos
  set f_neg := (-f).nnrealPart with _def_f_neg
  have tends_pos := (ENNReal.tendsto_toReal (f_pos.lintegral_lt_top_of_nnreal μ).ne).comp (h f_pos)
  have tends_neg := (ENNReal.tendsto_toReal (f_neg.lintegral_lt_top_of_nnreal μ).ne).comp (h f_neg)
  have aux :
    ∀ g : Ω →ᵇ ℝ≥0,
      (ENNReal.toReal ∘ fun i : γ ↦ ∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)) =
        fun i : γ ↦ (∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)).toReal :=
    fun _ ↦ rfl
  simp_rw [aux, BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at tends_pos tends_neg
  exact Tendsto.sub tends_pos tends_neg

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.tendsto_iff_forall_integral_rclike_tendsto** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f ↦ ?_, fun h f ↦ ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · exact (RCLike.continuous_ofReal.tendsto _).comp (h (f.comp RCLike.re RCLike.lipschitzWith_re))
    · exact (Tendsto.comp (RCLike.continuous_ofReal.tendsto _)
        (h (f.comp RCLike.im RCLike.lipschitzWith_im))).mul_const _
  · specialize h ((RCLike.ofRealAm (K := 𝕜)).compLeftContinuousBounded ℝ
      RCLike.lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, RCLike.ofRealAm_coe,
      integral_ofReal] at h
    exact tendsto_ofReal_iff'.mp h
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousAdd (FiniteMeasure Ω) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p ↦ ?_)⟩
  apply tendsto_iff_forall_lintegral_tendsto.2 (fun g ↦ ?_)
  have A : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) ↦ ∫⁻ x, g x ∂i.1) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.1)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_fst
  have B : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) ↦ ∫⁻ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.add B with q <;> simp
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSMul ℝ≥0 (FiniteMeasure Ω) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p ↦ ?_)⟩
  apply tendsto_iff_forall_integral_tendsto.2 (fun g ↦ ?_)
  have A : Tendsto (fun (i : ℝ≥0 × FiniteMeasure Ω) ↦ i.1) (𝓝 p) (𝓝 (p.1)) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have B : Tendsto (fun (i : ℝ≥0 × FiniteMeasure Ω) ↦ ∫ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_integral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.smul B with q <;> simp

variable {X : Type*} [TopologicalSpace X] {μs : X → FiniteMeasure Ω}

/-- The characterization of weak convergence of finite measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
/-
**MeasureTheory.continuous_iff_forall_continuous_lintegral** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characterization of weak convergence of finite measures by the condition tha
t the
integrals of every continuous bounded nonnegative function are continuous.
-/
lemma continuous_iff_forall_continuous_lintegral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ≥0, Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

/-- The characterization of weak convergence of finite measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
/-
**MeasureTheory.continuous_iff_forall_continuous_integral** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characterization of weak convergence of finite measures by the usual (defini
ng)
condition that the integrals of every continuous bounded function are continuous
.
-/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ, Continuous fun x ↦ ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

@[fun_prop]
/-
**MeasureTheory.continuous_lintegral_boundedContinuousFunction** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ≥0) : Continuous fun μ : FiniteMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _

@[fun_prop]
/-
**MeasureTheory.continuous_integral_boundedContinuousFunction** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ) : Continuous fun μ : FiniteMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/-- The characterization of weak convergence of finite measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
/-
**MeasureTheory.continuous_iff_forall_continuousMap_continuous_lintegral** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characterization of weak convergence of finite measures by the condition tha
t the
integrals of every continuous bounded nonnegative function are continuous.
-/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ≥0), Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/-- The characterization of weak convergence of finite measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
/-
**MeasureTheory.continuous_iff_forall_continuousMap_continuous_integral** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characterization of weak convergence of finite measures by the usual (defini
ng)
condition that the integrals of every continuous bounded function are continuous
.
-/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ), Continuous fun x ↦ ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {F : Type*}
/-
**MeasureTheory.continuous_lintegral_continuousMap** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_lintegral_continuousMap [FunLike F X ℝ≥0] [ContinuousMapClass F X ℝ≥0] (f : F) :
    Continuous fun μ : FiniteMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩
/-
**MeasureTheory.continuous_integral_continuousMap** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_integral_continuousMap [FunLike F X ℝ] [ContinuousMapClass F X ℝ] (f : F) :
    Continuous fun μ : FiniteMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end FiniteMeasureConvergenceByBoundedContinuousFunctions -- section


section comap

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The pullback of a finite measure under a map.
If `f` is injective and sends each measurable set to a null-measurable set, then for each
measurable set `s` we have `comap f μ s = μ (f '' s)`.
Otherwise, the pullback is defined to be zero. -/
/-
**MeasureTheory.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a finite measure under a map.
If `f` is injective and sends each measurable set to a null-measurable set, then
 for each
measurable set `s` we have `comap f μ s = μ (f '' s)`.
Otherwise, the pullback is defined to be zero.
-/
noncomputable def comap
    (f : Ω → Ω') (μ : FiniteMeasure Ω') : FiniteMeasure Ω :=
  ⟨Measure.comap f μ, by infer_instance⟩
/-
**MeasureTheory.toMeasure_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_comap (f : Ω → Ω') (μ : FiniteMeasure Ω') :
    (μ.comap f).toMeasure = (μ : Measure Ω').comap f := rfl
/-
**MeasureTheory.mass_comap_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mass_comap_le (f : Ω → Ω') (μ : FiniteMeasure Ω') :
    (μ.comap f).mass ≤ μ.mass := by
  simp only [mass, comap, mk_apply, coeFn_def, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  apply (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans (measure_mono (subset_univ _))

variable [TopologicalSpace Ω] [TopologicalSpace Ω'] [BorelSpace Ω] [BorelSpace Ω']
/-
**MeasureTheory._root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasu
re** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure [NormalSpace Ω']
    {f : Ω → Ω'} (hf : IsClosedEmbedding f) :
    ContinuousOn (fun (μ : FiniteMeasure Ω') ↦ μ.comap f) {μ | μ (range f)ᶜ = 0} := by
  intro μ hμ
  simp only [ContinuousWithinAt]
  rw [tendsto_iff_forall_integral_tendsto]
  intro g
  obtain ⟨g', -, hg'⟩ : ∃ g' : Ω' →ᵇ ℝ, ‖g'‖ = ‖g‖ ∧ g' ∘ f = g :=
    exists_extension_norm_eq_of_isClosedEmbedding g hf
  have A x : g x = g' (f x) := by change (⇑g) x = (⇑g' ∘ f) x; simp only [hg']
  simp only [comap, toMeasure_mk, A, ← MeasurableEmbedding.integral_map hf.measurableEmbedding,
    MeasurableEmbedding.map_comap hf.measurableEmbedding]
  have B {ν : FiniteMeasure Ω'} (hν : ν (range f)ᶜ = 0) :
      ∫ y in range f, g' y ∂ν = ∫ y, g' y ∂ν := by
    congr
    simp only [null_iff_toMeasure_null] at hν
    exact Measure.restrict_eq_self_of_ae_mem hν
  rw [B hμ]
  have : Tendsto (fun (ν : FiniteMeasure Ω') ↦ ∫ y, g' y ∂ν) (𝓝[{μ | μ (range f)ᶜ = 0}] μ)
      (𝓝 (∫ (y : Ω'), g' y ∂μ)) := by
    rw [nhdsWithin]
    have A : Tendsto (fun (ν : FiniteMeasure Ω') ↦ ∫ y, g' y ∂ν) (𝓝 μ) (𝓝 (∫ (y : Ω'), g' y ∂μ)) :=
      tendsto_iff_forall_integral_tendsto.1 tendsto_id _
    exact Tendsto.mono_left A inf_le_left
  apply Tendsto.congr' _ this
  filter_upwards [self_mem_nhdsWithin] with ν hν using (B hν).symm

end comap

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The push-forward of a finite measure by a function between measurable spaces. -/
/-
**MeasureTheory.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The push-forward of a finite measure by a function between measurable spaces.
-/
noncomputable def map (ν : FiniteMeasure Ω) (f : Ω → Ω') : FiniteMeasure Ω' :=
  ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isFiniteMeasure_map f⟩
/-
**MeasureTheory.toMeasure_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_map (ν : FiniteMeasure Ω) (f : Ω → Ω') :
    (ν.map f).toMeasure = ν.toMeasure.map f := rfl

/-- Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.FiniteMeasure.map_apply` for the corresponding equality as elements of `ℝ≥0`. -/
/-
**MeasureTheory.map_apply'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.FiniteMeasure.map_apply` for the corresponding equality as elemen
ts of `ℝ≥0`.
-/
lemma map_apply' (ν : FiniteMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble
/-
**MeasureTheory.map_apply_of_aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply_of_aemeasurable (ν : FiniteMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    ν.map f A = ν (f ⁻¹' A) := by
  have key := ν.map_apply' f_aemble A_mble
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr key
/-
**MeasureTheory.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (ν : FiniteMeasure Ω) {f : Ω → Ω'} (f_mble : Measurable f)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    ν.map f A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_mble.aemeasurable A_mble
/-
**MeasureTheory.map_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_add {f : Ω → Ω'} (f_mble : Measurable f) (ν₁ ν₂ : FiniteMeasure Ω) :
    (ν₁ + ν₂).map f = ν₁.map f + ν₂.map f := by ext; simp [*]
/-
**MeasureTheory.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {M : Type v} {α : Type w} {m : MeasurableSpace α} [inst : SMul M α] [Mea
surableConstSMul M α] (c : M)   (μ : MeasureTheory.Measure α) [MeasureTheory.SMu
lInvariantMeasure M α μ],   MeasureTheory.Measure.map (fun x => c • x) μ = μ
参数：c : M；μ : MeasureTheory.Measure α；fun x => c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
-/
@[simp] lemma map_smul {f : Ω → Ω'} (c : ℝ≥0) (ν : FiniteMeasure Ω) :
    (c • ν).map f = c • (ν.map f) := by
  ext s _
  simp [toMeasure_smul]

/-- The push-forward of a finite measure by a function between measurable spaces as a linear map. -/
/-
**MeasureTheory.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The push-forward of a finite measure by a function between measurable spaces as 
a linear map.
-/
noncomputable def mapHom {f : Ω → Ω'} (f_mble : Measurable f) :
    FiniteMeasure Ω →ₗ[ℝ≥0] FiniteMeasure Ω' where
  toFun := fun ν ↦ ν.map f
  map_add' := map_add f_mble
  map_smul' := map_smul
/-
**MeasureTheory.mass_map_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mass_map_le (f : Ω → Ω') (μ : FiniteMeasure Ω) : (μ.map f).mass ≤ μ.mass := by
  simp only [mass, coeFn_def, toMeasure_map, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_mono (subset_univ _)
  · simp [Measure.map_of_not_aemeasurable hf]

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
(weak) convergence of `FiniteMeasure`s on `X` implies (weak) convergence of the push-forwards
of these measures by `f`. -/
/-
**MeasureTheory.tendsto_map_of_tendsto_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, t
hen
(weak) convergence of `FiniteMeasure`s on `X` implies (weak) convergence of the 
push-forwards
of these measures by `f`.
-/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι → FiniteMeasure Ω) (ν : FiniteMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω → Ω'} (f_cont : Continuous f) :
    Tendsto (fun i ↦ (νs i).map f) L (𝓝 (ν.map f)) := by
  rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of finite measures `f* : FiniteMeasure X → FiniteMeasure Y` is continuous
(in the topologies of weak convergence of measures). -/
@[fun_prop]
/-
**MeasureTheory.continuous_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, t
hen
the push-forward of finite measures `f* : FiniteMeasure X → FiniteMeasure Y` is 
continuous
(in the topologies of weak convergence of measures).
-/
lemma continuous_map {f : Ω → Ω'} (f_cont : Continuous f) :
    Continuous (fun ν ↦ FiniteMeasure.map ν f) := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

/-- The push-forward of a finite measure by a continuous function between Borel spaces as
a continuous linear map. -/
/-
**MeasureTheory.mapCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The push-forward of a finite measure by a continuous function between Borel spac
es as
a continuous linear map.
-/
noncomputable def mapCLM {f : Ω → Ω'} (f_cont : Continuous f) :
    FiniteMeasure Ω →L[ℝ≥0] FiniteMeasure Ω' where
  toFun := fun ν ↦ ν.map f
  map_add' := map_add f_cont.measurable
  map_smul' := map_smul
/-
**MeasureTheory.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] [NormalSpace Ω']
    (f : Ω → Ω') (hf : IsClosedEmbedding f) :
    IsEmbedding (fun (μ : FiniteMeasure Ω) ↦ μ.map f) := by
  let M : Set (FiniteMeasure Ω') := {μ | μ (range f)ᶜ = 0}
  have A : IsEmbedding (Subtype.val : M → FiniteMeasure Ω') := IsEmbedding.subtypeVal
  let B : FiniteMeasure Ω ≃ₜ M :=
  { toFun μ := by
      refine ⟨μ.map f, ?_⟩
      simp only [null_iff_toMeasure_null, mem_ofPred_eq, toMeasure_map, M]
      rw [Measure.map_apply hf.continuous.measurable hf.isClosed_range.isOpen_compl.measurableSet]
      simp
    invFun := M.domRestrict (fun μ ↦ μ.comap f)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      rw [← continuousOn_iff_continuous_domRestrict]
      exact hf.continuousOn_comap_finiteMeasure
    left_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_comap, toMeasure_map]
      rw [Measure.comap_apply, Measure.map_apply, preimage_image_eq]
      · exact hf.injective
      · exact hf.continuous.measurable
      · exact hf.measurableEmbedding.measurableSet_image' hs
      · exact hf.injective
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hs
    right_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_map]
      rw [Measure.map_apply hf.continuous.measurable hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ hf.injective, image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        exact (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp (by exact μ.2)
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs }
  exact A.comp B.isEmbedding

end map -- section

end FiniteMeasure -- namespace

end MeasureTheory -- namespace

