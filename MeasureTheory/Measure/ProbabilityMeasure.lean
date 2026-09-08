/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
* the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
  distribution (a.k.a. convergence in law, weak convergence of measures);
* `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
  a finite measure;
* `MeasureTheory.FiniteMeasure.normalize`: Normalize a finite measure to a probability measure
  (returns junk for the zero measure).
* `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
  `μ` on `Ω` along a measurable function `f : Ω → Ω'`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
  probability measures is characterized by the convergence of expected values of all bounded
  continuous random variables. This shows that the chosen definition of topology coincides with
  the common textbook definition of convergence in distribution, i.e., weak convergence of
  measures. A similar characterization by the convergence of expected values (in the
  `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
  measures to a nonzero limit is characterized by the convergence of the probability-normalized
  versions and of the total masses.
* `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
  continuous.
* `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
  Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
  approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
* Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

@[expose] public section


noncomputable section

open Set Filter BoundedContinuousFunction Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/


/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
/-
**MeasureTheory.ProbabilityMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _
参数：Ω : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Probability measures are defined as the subtype of measures that have the proper
ty of being
probability measures (i.e., their total mass is one).
-/
def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-
**MeasureTheory.ProbabilityMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Pro
babilityMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited Ω] : Inhabited (ProbabilityMeasure Ω) :=
  ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

/-- Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
/-
**MeasureTheory.ProbabilityMeasure.toMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.ProbabilityMeasure`。
形式化陈述：toMeasure : ProbabilityMeasure Ω -> Measure Ω
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`.
-/
def toMeasure : ProbabilityMeasure Ω → Measure Ω := Subtype.val

/-- A probability measure can be interpreted as a measure. -/
/-
**MeasureTheory.ProbabilityMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Pro
babilityMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A probability measure can be interpreted as a measure.
-/
instance : Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }
/-
**MeasureTheory.ProbabilityMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Pro
babilityMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω) :=
  μ.prop
/-
**MeasureTheory.ProbabilityMeasure.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) 
(hμ : MeasureTheory.IsProbabilityMeasure μ),   ↑⟨μ, hμ⟩ = μ
参数：μ : MeasureTheory.Measure Ω；hμ : MeasureTheory.IsProbabilityMeasure μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (μ : Measure Ω) (hμ) : toMeasure ⟨μ, hμ⟩ = μ := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.val_eq_to_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.ProbabilityMeasure`。
形式化陈述：val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω)
参数：ν : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω) := rfl
/-
**MeasureTheory.ProbabilityMeasure.toMeasure_injective** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω -> Me
asure Ω)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω → Measure Ω) :=
  Subtype.coe_injective
/-
**MeasureTheory.ProbabilityMeasure.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.ProbabilityMeasure`。
形式化陈述：instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) Real>=0 where coe μ s
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) ℝ≥0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
  coe_injective μ ν h := toMeasure_injective <| Measure.ext fun s _ ↦ by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s
/-
**MeasureTheory.ProbabilityMeasure.coeFn_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.ProbabilityMeasure`。
形式化陈述：coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s => ((μ : Measure Ω) s).to
NNReal
参数：μ : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s ↦ ((μ : Measure Ω) s).toNNReal := rfl
/-
**MeasureTheory.ProbabilityMeasure.coeFn_mk** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.ProbabilityMeasure`。
形式化陈述：coeFn_mk (μ : Measure Ω) (hμ) : DFunLike.coe (F
参数：μ : Measure Ω；hμ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ (μ s).toNNReal := rfl

@[simp, norm_cast]
/-
**MeasureTheory.ProbabilityMeasure.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.ProbabilityMeasure`。
形式化陈述：mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) : DFunLike.coe (F
参数：μ : Measure Ω；hμ；s : Set Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

@[simp, norm_cast]
/-
**MeasureTheory.ProbabilityMeasure.coeFn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.ProbabilityMeasure`。
形式化陈述：coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1
参数：ν : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1 :=
  congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.coeFn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.ProbabilityMeasure`。
形式化陈述：coeFn_empty (ν : ProbabilityMeasure Ω) : ν ∅ = 0
参数：ν : ProbabilityMeasure Ω。
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
theorem coeFn_empty (ν : ProbabilityMeasure Ω) : ν ∅ = 0 := by simp [coeFn_def]
/-
**MeasureTheory.ProbabilityMeasure.coeFn_univ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.ProbabilityMeasure`。
形式化陈述：coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ != 0
参数：ν : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_univ`：coeFn_univ (ν : Probability
Measure Ω) : ν univ = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ ≠ 0 := by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]
/-
**MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (ν : MeasureTheory.Probability
Measure Ω) (s : Set Ω), (↑ν).real s = ↑(ν s)
参数：ν : MeasureTheory.ProbabilityMeasure Ω；s : Set Ω；↑ν；ν s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem measureReal_eq_coe_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν : Measure Ω).real s = ν s := by
  simp [coeFn_def, Measure.real, ENNReal.toReal]
/-
**MeasureTheory.ProbabilityMeasure.toNNReal_measureReal_eq_coeFn** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toNNReal_measureReal_eq_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) : ((ν
 : Measure Ω).real s).toNNReal = ν s
参数：ν : ProbabilityMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn`：∀ {Ω : Type u
_1} [inst : MeasurableSpace Ω] (ν : MeasureTheory.ProbabilityMeasure Ω) (s : Set
 Ω), (↑ν).real s = ↑(ν s)
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_measureReal_eq_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ((ν : Measure Ω).real s).toNNReal = ν s := by
  simp

/-- A probability measure can be interpreted as a finite measure. -/
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω
参数：μ : ProbabilityMeasure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A probability measure can be interpreted as a finite measure.
-/
def toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω := ⟨μ, inferInstance⟩
/-
**MeasureTheory.ProbabilityMeasure.coeFn_toFiniteMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Probability
Measure Ω), ⇑μ.toFiniteMeasure = ⇑μ
参数：μ : MeasureTheory.ProbabilityMeasure Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeFn_toFiniteMeasure (μ : ProbabilityMeasure Ω) : ⇑μ.toFiniteMeasure = μ := rfl
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure_apply** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ.toFiniteM
easure s = μ s
参数：μ : ProbabilityMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) :
    μ.toFiniteMeasure s = μ s := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) : (
ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω)
参数：ν : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω) := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) : (ν.toFini
teMeasure : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0)
参数：ν : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Set Ω → ℝ≥0) = (ν : Set Ω → ℝ≥0) := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure_apply_eq_apply** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) : ν.
toFiniteMeasure s = ν s
参数：ν : ProbabilityMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν.toFiniteMeasure s = ν s := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : 
(ν s : Real>=0∞) = (ν : Measure Ω) s
参数：ν : ProbabilityMeasure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn`：co
eFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) : (ν.toFiniteMeasur
e : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0)
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `MeasureTheory.ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMea
sure`：toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) : (
ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω)
-/
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν s : ℝ≥0∞) = (ν : Measure Ω) s := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.null_iff_toMeasure_null** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：null_iff_toMeasure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) : ν s = 0 ↔
 (ν : Measure Ω) s = 0
参数：ν : ProbabilityMeasure Ω；s : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
-/
theorem null_iff_toMeasure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h ↦ by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h ↦ congrArg ENNReal.toNNReal h⟩

@[gcongr]
/-
**MeasureTheory.ProbabilityMeasure.apply_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.ProbabilityMeasure`。
形式化陈述：apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂)
 : μ s₁ <= μ s₂
参数：μ : ProbabilityMeasure Ω；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn`：co
eFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) : (ν.toFiniteMeasur
e : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0)
· 使用定理 `MeasureTheory.FiniteMeasure.apply_mono`：apply_mono (μ : FiniteMeasure Ω)
 {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂
-/
theorem apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h
/-
**MeasureTheory.ProbabilityMeasure.apply_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.ProbabilityMeasure`。
形式化陈述：apply_union_le (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ union s₂
) <= μ s₁ + μ s₂
参数：μ : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn`：co
eFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) : (ν.toFiniteMeasur
e : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0)
· 使用定理 `MeasureTheory.FiniteMeasure.apply_union_le`：apply_union_le (μ : FiniteMe
asure Ω) {s₁ s₂ : Set Ω} : μ (s₁ union s₂) <= μ s₁ + μ s₂
-/
theorem apply_union_le (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_measure_iUnion_accumulate** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {ι : Type u_2} [inst_1 : Preor
der ι] [Filter.atTop.IsCountablyGenerated]   {μ : MeasureTheory.ProbabilityMeasu
re Ω} {f : ι → Set Ω},   Filter.Tendsto (fun i => μ (Set.accumulate f i)) Filter
.atTop (nhds (μ (⋃ i, f i)))
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
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure Ω} {f : ι → Set Ω} :
    Tendsto (fun i ↦ μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)
/-
**MeasureTheory.ProbabilityMeasure.apply_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Probability
Measure Ω) (s : Set Ω), μ s ≤ 1
参数：μ : MeasureTheory.ProbabilityMeasure Ω；s : Set Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_univ`：coeFn_univ (ν : Probability
Measure Ω) : ν univ = 1
· 使用定理 `MeasureTheory.ProbabilityMeasure.apply_mono`：apply_mono (μ : Probability
Measure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
@[simp] theorem apply_le_one (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ s ≤ 1 := by
  simpa using apply_mono μ (subset_univ s)
/-
**MeasureTheory.ProbabilityMeasure.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.ProbabilityMeasure`。
形式化陈述：nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω
参数：μ : ProbabilityMeasure Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_isProbabilityMeasure`：nonempty_of_isProbabilit
yMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
-/
theorem nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω :=
  nonempty_of_isProbabilityMeasure μ

@[ext]
/-
**MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω) (h : forall s
 : Set Ω, MeasurableSet s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν
参数：μ ν : ProbabilityMeasure Ω；h : forall s : Set Ω, MeasurableSet s -> (μ : Meas
ure Ω) s = (ν : Measure Ω) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ProbabilityMeasure.toMeasure_injective`：toMeasure_injectiv
e : Function.Injective ((↑) : ProbabilityMeasure Ω -> Measure Ω)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
-/
theorem eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble
/-
**MeasureTheory.ProbabilityMeasure.eq_of_forall_apply_eq** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω) (h : forall s : Set Ω, 
MeasurableSet s -> μ s = ν s) : μ = ν
参数：μ ν : ProbabilityMeasure Ω；h : forall s : Set Ω, MeasurableSet s -> μ s = ν s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_
forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω) (h : forall s : Set Ω, Me
asurableSet s -> (μ : Measure Ω) s = (ν : Measure Ω) s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (h s s_mble)

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass =
 1
参数：μ : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_univ`：coeFn_univ (ν : Probability
Measure Ω) : ν univ = 1
-/
theorem mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1 :=
  μ.coeFn_univ

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.ProbabilityMeasure.range_toFiniteMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω],   Set.range MeasureTheory.Pro
babilityMeasure.toFiniteMeasure = {μ | μ.mass = 1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure`：mass_toFiniteMeas
ure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.isProbabilityMeasure_iff_real`：isProbabilityMeasure_iff_re
al {μ : Measure α} : IsProbabilityMeasure μ ↔ μ.real univ = 1
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
-/
@[simp] lemma range_toFiniteMeasure :
    range toFiniteMeasure = {μ : FiniteMeasure Ω | μ.mass = 1} := by
  ext μ
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨fun ⟨ν, hν⟩ ↦ by simp [← hν], fun h ↦ ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! h)⟩, ?_⟩
  ext s hs
  simp
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure_nonzero** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure != 
0
参数：μ : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure`：mass_toFiniteMeas
ure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure ≠ 0 := by
  simp [← FiniteMeasure.mass_nonzero_iff]

/-- The type of probability measures is a measurable space when equipped with the Giry monad. -/
/-
**MeasureTheory.ProbabilityMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Pro
babilityMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of probability measures is a measurable space when equipped with the Gi
ry monad.
-/
instance : MeasurableSpace (ProbabilityMeasure Ω) :=
  inferInstanceAs <| MeasurableSpace (Subtype _)
/-
**MeasureTheory.ProbabilityMeasure.measurableSet_isProbabilityMeasure** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：measurableSet_isProbabilityMeasure : MeasurableSet { μ : Measure Ω | IsPro
babilityMeasure μ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `MeasureTheory.isProbabilityMeasure_iff`：isProbabilityMeasure_iff : IsPro
babilityMeasure μ ↔ μ univ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
-/
lemma measurableSet_isProbabilityMeasure :
    MeasurableSet { μ : Measure Ω | IsProbabilityMeasure μ } := by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

/-- The monoidal product is a measurable function from the product of probability spaces over
`α` and `β` into the type of probability spaces over `α × β`. Lemma 4.1 of [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]. -/
/-
**MeasureTheory.ProbabilityMeasure.measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] 
: Measurable (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β) => μ.1.toMea
sure.prod μ.2.toMeasure)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : α → Mea
sureTheory.Measure β}   [∀ (a : α), MeasureThe…
· 使用定理 `MeasureTheory.Measure.prod.instIsProbabilityMeasure`：∀ {α : Type u_4} {β
 : Type u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheor
y.Measure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
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
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
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

--- 原说明 ---
The monoidal product is a measurable function from the product of probability sp
aces over
`α` and `β` into the type of probability spaces over `α × β`. Lemma 4.1 of [A sy
nthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][
fritz2020].
-/
theorem measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β)
      ↦ μ.1.toMeasure.prod μ.2.toMeasure) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod]
  apply Measurable.mul
  · exact (Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst)
  · exact (Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd)
/-
**MeasureTheory.ProbabilityMeasure.apply_iUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.ProbabilityMeasure`。
形式化陈述：apply_iUnion_le {μ : ProbabilityMeasure Ω} {f : Nat -> Set Ω} (hf : Summab
le fun n => μ (f n)) : μ (⋃ n, f n) <= ∑' n, μ (f n)
参数：hf : Summable fun n => μ (f n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
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
lemma apply_iUnion_le {μ : ProbabilityMeasure Ω} {f : ℕ → Set Ω}
    (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

section convergence_in_distribution

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-
**MeasureTheory.ProbabilityMeasure.testAgainstNN_lipschitz** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) : LipschitzWith 1 fun f
 : Ω ->ᵇ Real>=0 => μ.toFiniteMeasure.testAgainstNN f
参数：μ : ProbabilityMeasure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz`：testAgainstNN_lipsc
hitz (μ : FiniteMeasure Ω) : LipschitzWith μ.mass fun f : Ω ->ᵇ Real>=0 => μ.tes
tAgainstNN f
· 使用定理 `MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure`：mass_toFiniteMeas
ure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1
-/
theorem testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) :
    LipschitzWith 1 fun f : Ω →ᵇ ℝ≥0 ↦ μ.toFiniteMeasure.testAgainstNN f :=
  μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

/-- The topology of weak convergence on `MeasureTheory.ProbabilityMeasure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`. -/
/-
**MeasureTheory.ProbabilityMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Pro
babilityMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of weak convergence on `MeasureTheory.ProbabilityMeasure Ω`. This i
s inherited
(induced) from the topology of weak convergence of finite measures via the inclu
sion
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/
instance : TopologicalSpace (ProbabilityMeasure Ω) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure_continuous : Continuous (toFiniteMeasure : ProbabilityMeas
ure Ω -> FiniteMeasure Ω)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem toFiniteMeasure_continuous :
    Continuous (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  continuous_induced_dom

/-- Probability measures yield elements of the `WeakDual` of bounded continuous nonnegative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration. -/
/-
**MeasureTheory.ProbabilityMeasure.toWeakDualBCNN** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.ProbabilityMeasure`。
形式化陈述：toWeakDualBCNN : ProbabilityMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ Real>=0)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Probability measures yield elements of the `WeakDual` of bounded continuous nonn
egative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration.
-/
def toWeakDualBCNN : ProbabilityMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
  FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.coe_toWeakDualBCNN** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.ProbabilityMeasure`。
形式化陈述：coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) : ⇑μ.toWeakDualBCNN = μ.toFi
niteMeasure.testAgainstNN
参数：μ : ProbabilityMeasure Ω。
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
theorem coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) :
    ⇑μ.toWeakDualBCNN = μ.toFiniteMeasure.testAgainstNN := rfl

@[simp]
/-
**MeasureTheory.ProbabilityMeasure.toWeakDualBCNN_apply** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω ->ᵇ Real>=0) : μ.to
WeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal
参数：μ : ProbabilityMeasure Ω；f : Ω ->ᵇ Real>=0。
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
theorem toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal := rfl
/-
**MeasureTheory.ProbabilityMeasure.toWeakDualBCNN_continuous** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω => μ.t
oWeakDualBCNN
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
· 使用定理 `MeasureTheory.FiniteMeasure.toWeakDualBCNN_continuous`：toWeakDualBCNN_co
ntinuous : Continuous (@toWeakDualBCNN Ω _ _ _)
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous`：toFiniteMea
sure_continuous : Continuous (toFiniteMeasure : ProbabilityMeasure Ω -> FiniteMe
asure Ω)
-/
theorem toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toWeakDualBCNN :=
  FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

/-- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_testAgainstNN_eval** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_testAgainstNN_eval (f : Ω ->ᵇ Real>=0) : Continuous fun μ : Pro
babilityMeasure Ω => μ.toFiniteMeasure.testAgainstNN f
参数：f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.FiniteMeasure.continuous_testAgainstNN_eval`：continuous_te
stAgainstNN_eval (f : Ω ->ᵇ Real>=0) : Continuous fun μ : FiniteMeasure Ω => μ.t
estAgainstNN f
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous`：toFiniteMea
sure_continuous : Continuous (toFiniteMeasure : ProbabilityMeasure Ω -> FiniteMe
asure Ω)

--- 原说明 ---
Integration of (nonnegative bounded continuous) test functions against Borel pro
bability
measures depends continuously on the measure.
-/
theorem continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0) :
    Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toFiniteMeasure.testAgainstNN f :=
  (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

/-- The canonical mapping from probability measures to finite measures is an embedding. -/
/-
**MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：toFiniteMeasure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSp
ace Ω] [OpensMeasurableSpace Ω] : IsEmbedding (toFiniteMeasure : ProbabilityMeas
ure Ω -> FiniteMeasure Ω) where eq_induced
参数：Ω : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The canonical mapping from probability measures to finite measures is an embeddi
ng.
-/
theorem toFiniteMeasure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] :
    IsEmbedding (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) where
  eq_induced := rfl
  injective _μ _ν h := Subtype.ext <| congr_arg FiniteMeasure.toMeasure h
/-
**MeasureTheory.ProbabilityMeasure.R1Space** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.ProbabilityMeasure`。
形式化陈述：R1Space : R1Space (ProbabilityMeasure Ω)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.r1Space`：Topology.IsInducing.r1Space [TopologicalSpa
ce Y] {f : Y -> X} (hf : IsInducing f) : R1Space Y
· 使用定理 `MeasureTheory.FiniteMeasure.instR1Space`：∀ {Ω : Type u_1} [inst : Measur
ableSpace Ω] [inst_1 : TopologicalSpace Ω] [inst_2 : OpensMeasurableSpace Ω],   
R1Space (MeasureTheory.Finite…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding`：toFiniteMe
asure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMea
surableSpace Ω] : IsEmbedding (toFiniteMeasure : P…
-/
instance R1Space : R1Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).r1Space
/-
**MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ) {
μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝 μ₀
) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure)
参数：F : Filter δ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding`：toFiniteMe
asure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMea
surableSpace Ω] : IsEmbedding (toFiniteMeasure : P…
-/
theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
    {μs : δ → ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ₀) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ ->
 ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ forall 
f : Ω ->ᵇ Real>=0, Tendsto (fun i => ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, 
f ω ∂(μ : Measure Ω)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendst
o_nhds`：tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
 {μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} : Tend…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`：tendst
o_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasu
re Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ for…

--- 原说明 ---
The characterization of weak convergence of probability measures by the conditio
n that the
integrals of every continuous bounded nonnegative function converge to the integ
ral of the function
against the limit measure.
-/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0,
        Tendsto (fun i ↦ ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> 
ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ forall f
 : Ω ->ᵇ Real, Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(
μ : Measure Ω)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The characterization of weak convergence of probability measures by the usual (d
efining)
condition that the integrals of every continuous bounded function converge to th
e integral of the
function against the limit measure.
-/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]
/-
**MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike
 𝕜] {F : Filter γ} {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
 Tendsto μs F (𝓝 μ) ↔ forall f : Ω ->ᵇ 𝕜, Tendsto (fun i => ∫ ω, f ω ∂(μs i : Me
asure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω)))
参数：𝕜 : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto`：
tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜] {F
 : Filter γ} {μs : γ -> FiniteMeasure Ω} {μ : FiniteMeasure …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

variable {X : Type*} [TopologicalSpace X] {μs : X → ProbabilityMeasure Ω}

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_lintegral** 
是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_iff_forall_continuous_lintegral : Continuous μs ↔ forall f : Ω 
->ᵇ Real>=0, Continuous fun x => ∫⁻ ω, f ω ∂(μs x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The characterization of weak convergence of probability measures by the conditio
n that the
integrals of every continuous bounded nonnegative function are continuous.
-/
lemma continuous_iff_forall_continuous_lintegral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ≥0, Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integral** 是
 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_iff_forall_continuous_integral : Continuous μs ↔ forall f : Ω -
>ᵇ Real, Continuous fun x => ∫ ω, f ω ∂(μs x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The characterization of weak convergence of probability measures by the usual (d
efining)
condition that the integrals of every continuous bounded function are continuous
.
-/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ, Continuous fun x ↦ ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]
/-
**MeasureTheory.ProbabilityMeasure.continuous_lintegral_boundedContinuousFunctio
n** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensM
easurableSpace X] (f : X ->ᵇ Real>=0) : Continuous fun μ : ProbabilityMeasure X 
=> ∫⁻ x, f x ∂μ
参数：f : X ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_linteg
ral`：continuous_iff_forall_continuous_lintegral : Continuous μs ↔ forall f : Ω -
>ᵇ Real>=0, Continuous fun x => ∫⁻ ω, f ω ∂(μs x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ≥0) : Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _
/-
**MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMe
asurableSpace X] (f : X ->ᵇ Real) : Continuous fun μ : ProbabilityMeasure X => ∫
 x, f x ∂μ
参数：f : X ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integr
al`：continuous_iff_forall_continuous_integral : Continuous μs ↔ forall f : Ω ->ᵇ
 Real, Continuous fun x => ∫ ω, f ω ∂(μs x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ) : Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuousMap_continuou
s_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_iff_forall_continuousMap_continuous_lintegral : Continuous μs ↔
 forall f : C(Ω, Real>=0), Continuous fun x => ∫⁻ ω, f ω ∂(μs x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_linteg
ral`：continuous_iff_forall_continuous_lintegral : Continuous μs ↔ forall f : Ω -
>ᵇ Real>=0, Continuous fun x => ∫⁻ ω, f ω ∂(μs x)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The characterization of weak convergence of probability measures by the conditio
n that the
integrals of every continuous bounded nonnegative function are continuous.
-/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ≥0), Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuousMap_continuou
s_integral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_iff_forall_continuousMap_continuous_integral : Continuous μs ↔ 
forall f : C(Ω, Real), Continuous fun x => ∫ ω, f ω ∂(μs x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integr
al`：continuous_iff_forall_continuous_integral : Continuous μs ↔ forall f : Ω ->ᵇ
 Real, Continuous fun x => ∫ ω, f ω ∂(μs x)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The characterization of weak convergence of probability measures by the usual (d
efining)
condition that the integrals of every continuous bounded function are continuous
.
-/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ), Continuous fun x ↦ ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {F : Type*}
/-
**MeasureTheory.ProbabilityMeasure.continuous_lintegral_continuousMap** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_lintegral_continuousMap [FunLike F X Real>=0] [ContinuousMapCla
ss F X Real>=0] (f : F) : Continuous fun μ : ProbabilityMeasure X => ∫⁻ x, f x ∂
μ
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuousMap_con
tinuous_lintegral`：continuous_iff_forall_continuousMap_continuous_lintegral : Co
ntinuous μs ↔ forall f : C(Ω, Real>=0), Continuous fun x => ∫⁻ ω, f ω ∂(μs x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
lemma continuous_lintegral_continuousMap [FunLike F X ℝ≥0] [ContinuousMapClass F X ℝ≥0] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩
/-
**MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：continuous_integral_continuousMap [FunLike F X Real] [ContinuousMapClass F
 X Real] (f : F) : Continuous fun μ : ProbabilityMeasure X => ∫ x, f x ∂μ
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuousMap_con
tinuous_integral`：continuous_iff_forall_continuousMap_continuous_integral : Cont
inuous μs ↔ forall f : C(Ω, Real), Continuous fun x => ∫ ω, f ω ∂(μs x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
lemma continuous_integral_continuousMap [FunLike F X ℝ] [ContinuousMapClass F X ℝ] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end convergence_in_distribution -- section

section Hausdorff

variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
variable (Ω)

/-- On topological spaces where indicators of closed sets have decreasing approximating sequences of
continuous functions (`HasOuterApproxClosed`), the topology of convergence in distribution of Borel
probability measures is Hausdorff (`T2Space`). -/
/-
**MeasureTheory.ProbabilityMeasure.t2Space** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.ProbabilityMeasure`。
形式化陈述：t2Space : T2Space (ProbabilityMeasure Ω)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding`：toFiniteMe
asure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMea
surableSpace Ω] : IsEmbedding (toFiniteMeasure : P…

--- 原说明 ---
On topological spaces where indicators of closed sets have decreasing approximat
ing sequences of
continuous functions (`HasOuterApproxClosed`), the topology of convergence in di
stribution of Borel
probability measures is Hausdorff (`T2Space`).
-/
instance t2Space : T2Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).t2Space

end Hausdorff -- section

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section NormalizeFiniteMeasure

/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace FiniteMeasure

variable {Ω : Type*} [Nonempty Ω] {m0 : MeasurableSpace Ω} (μ : FiniteMeasure Ω)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
/-
**MeasureTheory.FiniteMeasure.normalize** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：normalize : ProbabilityMeasure Ω
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normalize a finite measure so that it becomes a probability measure, i.e., divid
e by the
total mass.
-/
def normalize : ProbabilityMeasure Ω :=
  if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
          ENNReal.coe_inv zero, ennreal_mass]
        rw [← Ne, ← ENNReal.coe_ne_zero, ennreal_mass] at zero
        exact ENNReal.inv_mul_cancel zero μ.prop.measure_univ_lt_top.ne }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：self_eq_mass_mul_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s
参数：s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
-/
theorem self_eq_mass_mul_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s := by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass ≠ 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [mul_inv_cancel_left₀ mass_nonzero, coeFn_def]
/-
**MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_apply_eq`：eq_of_forall_apply_eq
 (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSet s -> μ s = ν s) : 
μ = ν
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize`：self_eq_mass_mul
_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s
· 使用定理 `MeasureTheory.FiniteMeasure.smul_apply`：smul_apply [IsScalarTower R Real
>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn`：co
eFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) : (ν.toFiniteMeasur
e : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0)
-/
theorem self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure := by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s, smul_apply, smul_eq_mul,
    ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]
/-
**MeasureTheory.FiniteMeasure.normalize_eq_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.FiniteMeasure`。
形式化陈述：normalize_eq_of_nonzero (nonzero : μ != 0) (s : Set Ω) : μ.normalize s = μ
.mass⁻¹ * μ s
参数：nonzero : μ != 0；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize`：self_eq_mass_mul
_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : Set Ω) : μ.normalize s = μ.mass⁻¹ * μ s := by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]
/-
**MeasureTheory.FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ != 0) : μ.normalize.toF
initeMeasure = μ.mass⁻¹ • μ
参数：nonzero : μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize`：self_eq_mass_sm
ul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ ≠ 0) :
    μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ := by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, smul_eq_mul, inv_mul_cancel₀, Ne,
    not_false_iff, one_smul]
/-
**MeasureTheory.FiniteMeasure.toMeasure_normalize_eq_of_nonzero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：toMeasure_normalize_eq_of_nonzero (nonzero : μ != 0) : (μ.normalize : Meas
ure Ω) = μ.mass⁻¹ • μ
参数：nonzero : μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `MeasureTheory.FiniteMeasure.normalize_eq_of_nonzero`：normalize_eq_of_non
zero (nonzero : μ != 0) (s : Set Ω) : μ.normalize s = μ.mass⁻¹ * μ s
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `MeasureTheory.Measure.coe_nnreal_smul_apply`：coe_nnreal_smul_apply {_m :
 MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) : (c • μ) s = c * 
μ s
-/
theorem toMeasure_normalize_eq_of_nonzero (nonzero : μ ≠ 0) :
    (μ.normalize : Measure Ω) = μ.mass⁻¹ • μ := by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s, μ.normalize_eq_of_nonzero nonzero s,
    ENNReal.coe_mul, ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _

@[simp]
/-
**MeasureTheory.FiniteMeasure._root_.ProbabilityMeasure.toFiniteMeasure_normaliz
e_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self {m0 : MeasurableSpace Ω}
    (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.normalize = μ := by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]

/-- Averaging with respect to a finite measure is the same as integrating against
`MeasureTheory.FiniteMeasure.normalize`. -/
/-
**MeasureTheory.FiniteMeasure.average_eq_integral_normalize** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSp
ace Real E] (nonzero : μ != 0) (f : Ω -> E) : average (μ : Measure Ω) f = ∫ ω, f
 ω ∂(μ.normalize : Measure Ω)
参数：nonzero : μ != 0；f : Ω -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.toMeasure_normalize_eq_of_nonzero`：toMeasure
_normalize_eq_of_nonzero (nonzero : μ != 0) : (μ.normalize : Measure Ω) = μ.mass
⁻¹ • μ
· 使用定理 `MeasureTheory.average.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (μ : Mea
sureTheory.Measu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_mass`：ennreal_mass {μ : FiniteMeasur
e Ω} : (μ.mass : Real>=0∞) = (μ : Measure Ω) univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Averaging with respect to a finite measure is the same as integrating against
`MeasureTheory.FiniteMeasure.normalize`.
-/
theorem average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (nonzero : μ ≠ 0) (f : Ω → E) :
    average (μ : Measure Ω) f = ∫ ω, f ω ∂(μ.normalize : Measure Ω) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero, average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]

variable [TopologicalSpace Ω]
/-
**MeasureTheory.FiniteMeasure.testAgainstNN_eq_mass_mul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.FiniteMeasure`。
形式化陈述：testAgainstNN_eq_mass_mul (f : Ω ->ᵇ Real>=0) : μ.testAgainstNN f = μ.mass
 * μ.normalize.toFiniteMeasure.testAgainstNN f
参数：f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize`：self_eq_mass_sm
ul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure
· 使用定理 `MeasureTheory.FiniteMeasure.smul_testAgainstNN_apply`：smul_testAgainstNN
_apply (c : Real>=0) (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) : (c • μ).testAga
instNN f = c • μ.testAgainstNN f
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem testAgainstNN_eq_mass_mul (f : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN f = μ.mass * μ.normalize.toFiniteMeasure.testAgainstNN f := by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f, smul_eq_mul]
/-
**MeasureTheory.FiniteMeasure.normalize_testAgainstNN** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.FiniteMeasure`。
形式化陈述：normalize_testAgainstNN (nonzero : μ != 0) (f : Ω ->ᵇ Real>=0) : μ.normali
ze.toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f
参数：nonzero : μ != 0；f : Ω ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_eq_mass_mul`：testAgainstNN_eq_
mass_mul (f : Ω ->ᵇ Real>=0) : μ.testAgainstNN f = μ.mass * μ.normalize.toFinite
Measure.testAgainstNN f
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalize_testAgainstNN (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    μ.normalize.toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f := by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]

variable [OpensMeasurableSpace Ω]
variable {μ}
/-
**MeasureTheory.FiniteMeasure.tendsto_testAgainstNN_of_tendsto_normalize_testAga
instNN_of_tendsto_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {
γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω} (μs_lim : Tendsto (fun i =
> (μs i).normalize) F (𝓝 μ.normalize)) (mass_lim : Tendsto (fun i => (μs i).mass
) F (𝓝 μ.mass)) (f : Ω ->ᵇ Real>=0) : Tendsto (fun i => (μs i).testAgainstNN f) 
F (𝓝 (μ.testAgainstNN f))
参数：μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize)；mass_lim : Ten
dsto (fun i => (μs i).mass) F (𝓝 μ.mass)；f : Ω ->ᵇ Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.FiniteMeasure.mass_zero_iff`：mass_zero_iff (μ : FiniteMeas
ure Ω) : μ.mass = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.FiniteMeasure.zero_testAgainstNN_apply`：zero_testAgainstNN
_apply (f : Ω ->ᵇ Real>=0) : (0 : FiniteMeasure Ω).testAgainstNN f = 0
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_zero_testAgainstNN_of_tendsto_zero_m
ass`：tendsto_zero_testAgainstNN_of_tendsto_zero_mass {γ : Type*} {F : Filter γ} 
{μs : γ -> FiniteMeasure Ω} (mass_lim : Tendsto (fun i => (μs i).…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.FiniteMeasure.testAgainstNN_eq_mass_mul`：testAgainstNN_eq_
mass_mul (f : Ω ->ᵇ Real>=0) : μ.testAgainstNN f = μ.mass * μ.normalize.toFinite
Measure.testAgainstNN f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.tendsto_iff`：Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X}
 (p : Y × Z) : Tendsto seq f (𝓝 p) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) 
∧ Tend…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`：te
ndsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Fin
iteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔…
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendst
o_nhds`：tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
 {μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} : Tend…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
-/
theorem tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*}
    {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass)) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i ↦ (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass] at mass_lim ⊢
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i ↦ (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at μs_lim
  rw [tendsto_iff_forall_testAgainstNN_tendsto] at μs_lim
  have lim_pair :
    Tendsto (fun i ↦ (⟨(μs i).mass, (μs i).normalize.toFiniteMeasure.testAgainstNN f⟩ : ℝ≥0 × ℝ≥0))
      F (𝓝 ⟨μ.mass, μ.normalize.toFiniteMeasure.testAgainstNN f⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩
  exact tendsto_mul.comp lim_pair
/-
**MeasureTheory.FiniteMeasure.tendsto_normalize_testAgainstNN_of_tendsto** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ} {μs 
: γ -> FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ != 0) (f : Ω 
->ᵇ Real>=0) : Tendsto (fun i => (μs i).normalize.toFiniteMeasure.testAgainstNN 
f) F (𝓝 (μ.normalize.toFiniteMeasure.testAgainstNN f))
参数：μs_lim : Tendsto μs F (𝓝 μ)；nonzero : μ != 0；f : Ω ->ᵇ Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mass`：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1
 : TopologicalSpace Ω] [inst_2 : OpensMeasurableSpace Ω]   {γ : Type u_3} {F : F
ilter γ} …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_nonzero_iff`：mass_nonzero_iff (μ : Fini
teMeasure Ω) : μ.mass != 0 ↔ μ != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.FiniteMeasure.normalize_testAgainstNN`：normalize_testAgain
stNN (nonzero : μ != 0) (f : Ω ->ᵇ Real>=0) : μ.normalize.toFiniteMeasure.testAg
ainstNN f = μ.mass⁻¹ * μ.testAgainstNN f
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Prod.tendsto_iff`：Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X}
 (p : Y × Z) : Tendsto seq f (𝓝 p) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) 
∧ Tend…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `continuousOn_inv₀`：continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀)
 {0}ᶜ
· 使用定理 `NNReal.instContinuousInv₀`：ContinuousInv₀ NNReal
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`：te
ndsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Fin
iteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔…
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
-/
theorem tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i ↦ (μs i).normalize.toFiniteMeasure.testAgainstNN f) F
      (𝓝 (μ.normalize.toFiniteMeasure.testAgainstNN f)) := by
  have lim_mass := μs_lim.mass
  have aux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : ∀ᶠ i in F, μs i ≠ 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : ∀ᶠ i in F,
      (μs i).normalize.toFiniteMeasure.testAgainstNN f =
        (μs i).mass⁻¹ * (μs i).testAgainstNN f := by
    filter_upwards [eventually_iff.mp eventually_nonzero]
    intro i hi
    apply normalize_testAgainstNN _ hi
  simp_rw [tendsto_congr' eve, μ.normalize_testAgainstNN nonzero]
  have lim_pair :
    Tendsto (fun i ↦ (⟨(μs i).mass⁻¹, (μs i).testAgainstNN f⟩ : ℝ≥0 × ℝ≥0)) F
      (𝓝 ⟨μ.mass⁻¹, μ.testAgainstNN f⟩) := by
    refine (Prod.tendsto_iff _ _).mpr ⟨?_, ?_⟩
    · exact (continuousOn_inv₀.continuousAt aux).tendsto.comp lim_mass
    · exact tendsto_iff_forall_testAgainstNN_tendsto.mp μs_lim f
  exact tendsto_mul.comp lim_pair

/-- If the normalized versions of finite measures converge weakly and their total masses
also converge, then the finite measures themselves converge weakly. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tend
sto_mass** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*} {F 
: Filter γ} {μs : γ -> FiniteMeasure Ω} (μs_lim : Tendsto (fun i => (μs i).norma
lize) F (𝓝 μ.normalize)) (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass)
) : Tendsto μs F (𝓝 μ)
参数：μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize)；mass_lim : Ten
dsto (fun i => (μs i).mass) F (𝓝 μ.mass)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`：te
ndsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Fin
iteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_testAgainstNN_of_tendsto_normalize_t
estAgainstNN_of_tendsto_mass`：tendsto_testAgainstNN_of_tendsto_normalize_testAga
instNN_of_tendsto_mass {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω} (μ
s_lim : Te…

--- 原说明 ---
If the normalized versions of finite measures converge weakly and their total ma
sses
also converge, then the finite measures themselves converge weakly.
-/
theorem tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass)) : Tendsto μs F (𝓝 μ) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f ↦
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f

/-- If finite measures themselves converge weakly to a nonzero limit measure, then their
normalized versions also converge weakly. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_normalize_of_tendsto** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_normalize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteM
easure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ != 0) : Tendsto (fun i => (
μs i).normalize) F (𝓝 μ.normalize)
参数：μs_lim : Tendsto μs F (𝓝 μ)；nonzero : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendst
o_nhds`：tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
 {μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} : Tend…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`：te
ndsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Fin
iteMeasure Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_normalize_testAgainstNN_of_tendsto`：
tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ ->
 FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ…

--- 原说明 ---
If finite measures themselves converge weakly to a nonzero limit measure, then t
heir
normalized versions also converge weakly.
-/
theorem tendsto_normalize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f ↦ tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
/-
**MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：tendsto_normalize_iff_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Finite
Measure Ω} (nonzero : μ != 0) : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.norma
lize) ∧ Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass) ↔ Tendsto μs F (𝓝 μ)
参数：nonzero : μ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_o
f_tendsto_mass`：tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : 
Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω} (μs_lim : Tendsto (fun i =…
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_normalize_of_tendsto`：tendsto_normal
ize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω} (μs_lim : 
Tendsto μs F (𝓝 μ)) (nonzero : μ != 0) : Tends…
· 使用定理 `Filter.Tendsto.mass`：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1
 : TopologicalSpace Ω] [inst_2 : OpensMeasurableSpace Ω]   {γ : Type u_3} {F : F
ilter γ} …

--- 原说明 ---
The weak convergence of finite measures to a nonzero limit can be characterized 
by the weak
convergence of both their normalized versions (probability measures) and their t
otal masses.
-/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (nonzero : μ ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize) ∧
        Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) := by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩

end FiniteMeasure --namespace

end NormalizeFiniteMeasure -- section

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

namespace ProbabilityMeasure

/-- The push-forward of a probability measure by a measurable function. -/
/-
**MeasureTheory.ProbabilityMeasure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
ProbabilityMeasure`。
形式化陈述：map (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
 : ProbabilityMeasure Ω'
参数：ν : ProbabilityMeasure Ω；f_aemble : AEMeasurable f ν。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The push-forward of a probability measure by a measurable function.
-/
noncomputable def map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν) :
    ProbabilityMeasure Ω' :=
  ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isProbabilityMeasure_map f_aemble⟩
/-
**MeasureTheory.ProbabilityMeasure.toMeasure_map** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {Ω' : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : Meas
urableSpace Ω']   (ν : MeasureTheory.ProbabilityMeasure Ω) {f : Ω → Ω'} (hf : AE
Measurable f ↑ν),   ↑(ν.map hf) = MeasureTheory.Measure.map f ↑ν
参数：ν : MeasureTheory.ProbabilityMeasure Ω；hf : AEMeasurable f ↑ν；ν.map hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (hf : AEMeasurable f ν) :
    (ν.map hf).toMeasure = ν.toMeasure.map f := rfl

/-- Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.ProbabilityMeasure.map_apply` for the corresponding equality as elements of `ℝ≥0`. -/
/-
**MeasureTheory.ProbabilityMeasure.map_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.ProbabilityMeasure`。
形式化陈述：map_apply' (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurab
le f ν) {A : Set Ω'} (A_mble : MeasurableSet A) : (ν.map f_aemble : Measure Ω') 
A = (ν : Measure Ω) (f ⁻¹' A)
参数：ν : ProbabilityMeasure Ω；f_aemble : AEMeasurable f ν；A_mble : MeasurableSet A
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)

--- 原说明 ---
Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.ProbabilityMeasure.map_apply` for the corresponding equality as e
lements of `ℝ≥0`.
-/
lemma map_apply' (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble
/-
**MeasureTheory.ProbabilityMeasure.map_apply_of_aemeasurable** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：map_apply_of_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemb
le : AEMeasurable f ν) {A : Set Ω'} (A_mble : MeasurableSet A) : (ν.map f_aemble
) A = ν (f ⁻¹' A)
参数：ν : ProbabilityMeasure Ω；f_aemble : AEMeasurable f ν；A_mble : MeasurableSet A
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toNNReal_eq_toNNReal_iff'`：toNNReal_eq_toNNReal_iff' {x y : Real
>=0∞} (hx : x != ⊤) (hy : y != ⊤) : x.toNNReal = y.toNNReal ↔ x = y
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用引理 `MeasureTheory.ProbabilityMeasure.map_apply'`：map_apply' (ν : Probability
Measure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν) {A : Set Ω'} (A_mble : Me
asurableSet A) : (ν.map f_aemble …
-/
lemma map_apply_of_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (f_aemble : AEMeasurable f ν) {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) := by
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr <|
    ν.map_apply' f_aemble A_mble
/-
**MeasureTheory.ProbabilityMeasure.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.ProbabilityMeasure`。
形式化陈述：map_apply (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurabl
e f ν) {A : Set Ω'} (A_mble : MeasurableSet A) : (ν.map f_aemble) A = ν (f ⁻¹' A
)
参数：ν : ProbabilityMeasure Ω；f_aemble : AEMeasurable f ν；A_mble : MeasurableSet A
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.ProbabilityMeasure.map_apply_of_aemeasurable`：map_apply_of
_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable 
f ν) {A : Set Ω'} (A_mble : MeasurableSet A) : (…
-/
lemma map_apply (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_aemble A_mble

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
convergence (in distribution) of `ProbabilityMeasure`s on `X` implies convergence (in
distribution) of the push-forwards of these measures by `f`. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι} (νs : ι ->
 ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν)) {f 
: Ω -> Ω'} (f_cont : Continuous f) : Tendsto (fun i => (νs i).map f_cont.measura
ble.aemeasurable) L (𝓝 (ν.map f_cont.measurable.aemeasurable))
参数：νs : ι -> ProbabilityMeasure Ω；ν : ProbabilityMeasure Ω；lim : Tendsto νs L (𝓝
 ν)；f_cont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`：t
endsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Probab
ilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f

--- 原说明 ---
If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, t
hen
convergence (in distribution) of `ProbabilityMeasure`s on `X` implies convergenc
e (in
distribution) of the push-forwards of these measures by `f`.
-/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι → ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω → Ω'} (f_cont : Continuous f) :
    Tendsto (fun i ↦ (νs i).map f_cont.measurable.aemeasurable) L
      (𝓝 (ν.map f_cont.measurable.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of probability measures `f* : ProbabilityMeasure X → ProbabilityMeasure Y`
is continuous (in the topologies of convergence in distribution). -/
/-
**MeasureTheory.ProbabilityMeasure.continuous_map** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.ProbabilityMeasure`。
形式化陈述：continuous_map {f : Ω -> Ω'} (f_cont : Continuous f) : Continuous (fun ν =
> ProbabilityMeasure.map ν f_cont.measurable.aemeasurable)
参数：f_cont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`：t
endsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι} (νs : ι -> Probab
ilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto ν…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, t
hen
the push-forward of probability measures `f* : ProbabilityMeasure X → Probabilit
yMeasure Y`
is continuous (in the topologies of convergence in distribution).
-/
lemma continuous_map {f : Ω → Ω'} (f_cont : Continuous f) :
    Continuous (fun ν ↦ ProbabilityMeasure.map ν f_cont.measurable.aemeasurable) := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

end ProbabilityMeasure -- namespace

end map -- section

section join_bind

/-
**MeasureTheory.isProbabilityMeasure_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：isProbabilityMeasure_join {α : Type*} [MeasurableSpace α] {m : Measure (Me
asure α)} [IsProbabilityMeasure m] (hm : forallᵐ μ ∂m, IsProbabilityMeasure μ) :
 IsProbabilityMeasure (m.join)
参数：Measure α；hm : forallᵐ μ ∂m, IsProbabilityMeasure μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MeasureTheory.lintegral_eq_const`：lintegral_eq_const [IsProbabilityMeasu
re μ] {f : α -> Real>=0∞} {c : Real>=0∞} (hf : forallᵐ x ∂μ, f x = c) : ∫⁻ x, f 
x ∂μ = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isProbabilityMeasure_join {α : Type*} [MeasurableSpace α] {m : Measure (Measure α)}
    [IsProbabilityMeasure m] (hm : ∀ᵐ μ ∂m, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm
/-
**MeasureTheory.isProbabilityMeasure_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：isProbabilityMeasure_bind {α : Type*} {β : Type*} [MeasurableSpace α] [Mea
surableSpace β] {m : Measure α} [IsProbabilityMeasure m] {f : α -> Measure β} (h
f₀ : AEMeasurable f m) (hf₁ : forallᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProb
abilityMeasure (m.bind f)
参数：hf₀ : AEMeasurable f m；hf₁ : forallᵐ μ ∂m, IsProbabilityMeasure (f μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MeasureTheory.lintegral_eq_const`：lintegral_eq_const [IsProbabilityMeasu
re μ] {f : α -> Real>=0∞} {c : Real>=0∞} (hf : forallᵐ x ∂μ, f x = c) : ∫⁻ x, f 
x ∂μ = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isProbabilityMeasure_bind {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β} (hf₀ : AEMeasurable f m)
    (hf₁ : ∀ᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

end join_bind

end MeasureTheory -- namespace

