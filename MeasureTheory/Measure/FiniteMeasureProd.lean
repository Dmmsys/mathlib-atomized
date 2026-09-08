/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Products of finite measures and probability measures

This file introduces binary products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.prod`: The product of two finite measures.
* `MeasureTheory.ProbabilityMeasure.prod`: The product of two probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_prod`: the product probability measure depends
continuously on the factors.

-/

@[expose] public section

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section FiniteMeasure_product

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of finite measures. -/
/-
**MeasureTheory.FiniteMeasure.prod** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Fini
teMeasure`。
形式化陈述：prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β)
参数：μ : FiniteMeasure α；ν : FiniteMeasure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary product of finite measures.
-/
noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)
/-
**MeasureTheory.FiniteMeasure.toMeasure_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α) (ν : MeasureTheory.FiniteMea
sure β), ↑(μ.prod ν) = (↑μ).prod ↑ν
参数：μ : MeasureTheory.FiniteMeasure α；ν : MeasureTheory.FiniteMeasure β；μ.prod ν；
↑μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl
/-
**MeasureTheory.FiniteMeasure.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.FiniteMeasure`。
形式化陈述：prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) : μ.prod ν s = ENN
Real.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ)
参数：s : Set (α × β)；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]
/-
**MeasureTheory.FiniteMeasure.prod_apply_symm** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.FiniteMeasure`。
形式化陈述：prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) : μ.prod ν s 
= ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x => ⟨x, y⟩) ⁻¹' s) ∂ν)
参数：s : Set (α × β)；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply_symm`：prod_apply_symm {s : Set (α × β)}
 (hs : MeasurableSet s) : μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]
/-
**MeasureTheory.FiniteMeasure.prod_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α) (ν : MeasureTheory.FiniteMea
sure β) (s : Set α) (t : Set β),   (μ.prod ν) (s ×ˢ t) = μ s * ν t
参数：μ : MeasureTheory.FiniteMeasure α；ν : MeasureTheory.FiniteMeasure β；s : Set α
；t : Set β；μ.prod ν；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]
/-
**MeasureTheory.FiniteMeasure.mass_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α) (ν : MeasureTheory.FiniteMea
sure β), (μ.prod ν).mass = μ.mass * ν.mass
参数：μ : MeasureTheory.FiniteMeasure α；ν : MeasureTheory.FiniteMeasure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
@[simp] lemma mass_prod : (μ.prod ν).mass = μ.mass * ν.mass := by
  simp only [coeFn_def, mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)
/-
**MeasureTheory.FiniteMeasure.zero_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (ν : MeasureTheory.FiniteMeasure β), MeasureTheory.FiniteMeasure
.prod 0 ν = 0
参数：ν : MeasureTheory.FiniteMeasure β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_zero_iff`：mass_zero_iff (μ : FiniteMeas
ure Ω) : μ.mass = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.FiniteMeasure.mass_prod`：∀ {α : Type u_1} [inst : Measurab
leSpace α] {β : Type u_2} [inst_1 : MeasurableSpace β]   (μ : MeasureTheory.Fini
teMeasure α) (ν : MeasureTh…
· 使用定理 `MeasureTheory.FiniteMeasure.zero_mass`：zero_mass : (0 : FiniteMeasure Ω)
.mass = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
@[simp] lemma zero_prod : (0 : FiniteMeasure α).prod ν = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, zero_mul]
/-
**MeasureTheory.FiniteMeasure.prod_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α), μ.prod 0 = 0
参数：μ : MeasureTheory.FiniteMeasure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.FiniteMeasure.mass_zero_iff`：mass_zero_iff (μ : FiniteMeas
ure Ω) : μ.mass = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.FiniteMeasure.mass_prod`：∀ {α : Type u_1} [inst : Measurab
leSpace α] {β : Type u_2} [inst_1 : MeasurableSpace β]   (μ : MeasureTheory.Fini
teMeasure α) (ν : MeasureTh…
· 使用定理 `MeasureTheory.FiniteMeasure.zero_mass`：zero_mass : (0 : FiniteMeasure Ω)
.mass = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma prod_zero : μ.prod (0 : FiniteMeasure β) = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, mul_zero]
/-
**MeasureTheory.FiniteMeasure.map_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α) (ν : MeasureTheory.FiniteMea
sure β), (μ.prod ν).map Prod.fst = ν Set.univ • μ
参数：μ : MeasureTheory.FiniteMeasure α；ν : MeasureTheory.FiniteMeasure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_fst_prod : (μ.prod ν).map Prod.fst = ν univ • μ := by ext; simp
/-
**MeasureTheory.FiniteMeasure.map_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.FiniteMeasure α) (ν : MeasureTheory.FiniteMea
sure β), (μ.prod ν).map Prod.snd = μ Set.univ • ν
参数：μ : MeasureTheory.FiniteMeasure α；ν : MeasureTheory.FiniteMeasure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennreal_co
eFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : Real>=0∞) = (ν
 : Measure Ω) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_snd_prod : (μ.prod ν).map Prod.snd = μ univ • ν := by ext; simp
/-
**MeasureTheory.FiniteMeasure.map_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpa
ce β'] {f : α -> α'} {g : β -> β'} (f_mble : Measurable f) (g_mble : Measurable 
g) : (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g)
参数：f_mble : Measurable f；g_mble : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]
/-
**MeasureTheory.FiniteMeasure.prod_swap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

end FiniteMeasure -- namespace

end FiniteMeasure_product -- section

section ProbabilityMeasure_product

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of probability measures. -/
/-
**MeasureTheory.ProbabilityMeasure.prod** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.ProbabilityMeasure`。
形式化陈述：prod (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : ProbabilityMe
asure (α × β)
参数：μ : ProbabilityMeasure α；ν : ProbabilityMeasure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary product of probability measures.
-/
noncomputable def prod (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbabilityMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, by infer_instance⟩

variable (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
/-
**MeasureTheory.ProbabilityMeasure.toMeasure_prod** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.ProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.ProbabilityMeasure α) (ν : MeasureTheory.Prob
abilityMeasure β), ↑(μ.prod ν) = (↑μ).prod ↑ν
参数：μ : MeasureTheory.ProbabilityMeasure α；ν : MeasureTheory.ProbabilityMeasure β
；μ.prod ν；↑μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl
/-
**MeasureTheory.ProbabilityMeasure.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.ProbabilityMeasure`。
形式化陈述：prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) : μ.prod ν s = ENN
Real.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ)
参数：s : Set (α × β)；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]
/-
**MeasureTheory.ProbabilityMeasure.prod_apply_symm** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.ProbabilityMeasure`。
形式化陈述：prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) : μ.prod ν s 
= ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x => ⟨x, y⟩) ⁻¹' s) ∂ν)
参数：s : Set (α × β)；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply_symm`：prod_apply_symm {s : Set (α × β)}
 (hs : MeasurableSet s) : μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]
/-
**MeasureTheory.ProbabilityMeasure.prod_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.ProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.ProbabilityMeasure α) (ν : MeasureTheory.Prob
abilityMeasure β) (s : Set α) (t : Set β),   (μ.prod ν) (s ×ˢ t) = μ s * ν t
参数：μ : MeasureTheory.ProbabilityMeasure α；ν : MeasureTheory.ProbabilityMeasure β
；s : Set α；t : Set β；μ.prod ν；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]

/-- The first marginal of a product probability measure is the first probability measure. -/
/-
**MeasureTheory.ProbabilityMeasure.map_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.ProbabilityMeasure α) (ν : MeasureTheory.Prob
abilityMeasure β), (μ.prod ν).map ⋯ = μ
参数：μ : MeasureTheory.ProbabilityMeasure α；ν : MeasureTheory.ProbabilityMeasure β
；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The first marginal of a product probability measure is the first probability mea
sure.
-/
@[simp] lemma map_fst_prod : (μ.prod ν).map measurable_fst.aemeasurable = μ := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]

/-- The second marginal of a product probability measure is the second probability measure. -/
/-
**MeasureTheory.ProbabilityMeasure.map_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {β : Type u_2} [inst_1 : Measu
rableSpace β]   (μ : MeasureTheory.ProbabilityMeasure α) (ν : MeasureTheory.Prob
abilityMeasure β), (μ.prod ν).map ⋯ = ν
参数：μ : MeasureTheory.ProbabilityMeasure α；ν : MeasureTheory.ProbabilityMeasure β
；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The second marginal of a product probability measure is the second probability m
easure.
-/
@[simp] lemma map_snd_prod : (μ.prod ν).map measurable_snd.aemeasurable = ν := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]
/-
**MeasureTheory.ProbabilityMeasure.map_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.ProbabilityMeasure`。
形式化陈述：map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpa
ce β'] {f : α -> α'} {g : β -> β'} (f_mble : Measurable f) (g_mble : Measurable 
g) : (μ.map f_mble.aemeasurable).prod (ν.map g_mble.aemeasurable) = (μ.prod ν).m
ap (f_mble.prodMap g_mble).aemeasurable
参数：f_mble : Measurable f；g_mble : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
-/
lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f_mble.aemeasurable).prod (ν.map g_mble.aemeasurable)
      = (μ.prod ν).map (f_mble.prodMap g_mble).aemeasurable := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]
/-
**MeasureTheory.ProbabilityMeasure.prod_swap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.ProbabilityMeasure`。
形式化陈述：prod_swap : (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
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
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_swap : (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

open TopologicalSpace

/-- The map associating to two probability measures their product is a continuous map. -/
@[fun_prop]
/-
**MeasureTheory.ProbabilityMeasure.continuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.ProbabilityMeasure`。
形式化陈述：continuous_prod [TopologicalSpace α] [TopologicalSpace β] [SecondCountable
Topology α] [SecondCountableTopology β] [PseudoMetrizableSpace α] [PseudoMetriza
bleSpace β] [OpensMeasurableSpace α] [OpensMeasurableSpace β] : Continuous (fun 
(μ : ProbabilityMeasure α × ProbabilityMeasure β) => μ.1.prod μ.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.null_iff_toMeasure_null`：null_iff_toMea
sure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) : ν s = 0 ↔ (ν : Measure Ω) s =
 0
· 使用定理 `null_frontier_inter`：null_frontier_inter {μ : Measure α'} {s s' : Set α'
} (h : μ (frontier s) = 0) (h' : μ (frontier s') = 0) : μ (frontier (s inter s')
) = 0
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`：∀ {Ω : Type u_1
} {ι : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : TopologicalSpace Ω] [Secon
dCountableTopology Ω]   [inst_3 : OpensMeasur…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.instFirstCountableTopologyProd`：∀ {α : Type u} [t : Top
ologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [FirstCountableTopol
ogy α]   [FirstCountableTopology β], …
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `MeasureTheory.instPseudoMetrizableSpaceProbabilityMeasureOfSeparableSpac
e`：∀ (X : Type u_2) [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizab
leSpace X]   [TopologicalSpace.SeparableSpace X] [inst_3 : Meas…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `MeasureTheory.exists_null_frontier_thickening`：exists_null_frontier_thic
kening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : Real} (hab : a < b) : exis
ts r in Ioo a b, μ (frontier (Metri…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The map associating to two probability measures their product is a continuous ma
p.
-/
theorem continuous_prod [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology α]
    [SecondCountableTopology β] [PseudoMetrizableSpace α] [PseudoMetrizableSpace β]
    [OpensMeasurableSpace α] [OpensMeasurableSpace β] :
    Continuous (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β) ↦ μ.1.prod μ.2) := by
  refine continuous_iff_continuousAt.2 (fun μ ↦ ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `a ×ˢ b` where `a` and `b` have null frontier. -/
  let S : Set (Set (α × β)) := {t | ∃ (a : Set α) (b : Set β),
    MeasurableSet a ∧ μ.1 (frontier a) = 0 ∧ MeasurableSet b ∧ μ.2 (frontier b) = 0
    ∧ t = a ×ˢ b}
  have : IsPiSystem S := by
    rintro - ⟨a, b, ameas, ha, bmeas, hb, rfl⟩ - ⟨a', b', a'meas, ha', b'meas, hb', rfl⟩ -
    refine ⟨a ∩ a', b ∩ b', ameas.inter a'meas, ?_, bmeas.inter b'meas, ?_, prod_inter_prod⟩
    · rw [null_iff_toMeasure_null] at ha ha' ⊢
      exact null_frontier_inter ha ha'
    · rw [null_iff_toMeasure_null] at hb hb' ⊢
      exact null_frontier_inter hb hb'
  apply this.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, ameas, -, bmeas, -, rfl⟩
    exact ameas.prod bmeas
  · let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
    let : PseudoMetricSpace β := TopologicalSpace.pseudoMetrizableSpacePseudoMetric β
    intro u u_open x xu
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ball x ε ⊆ u := Metric.isOpen_iff.1 u_open x xu
    rcases exists_null_frontier_thickening (μ.1 : Measure α) {x.1} εpos with ⟨r, hr, μr⟩
    rcases exists_null_frontier_thickening (μ.2 : Measure β) {x.2} εpos with ⟨r', hr', μr'⟩
    simp only [thickening_singleton] at μr μr'
    refine ⟨ball x.1 r ×ˢ ball x.2 r', ⟨ball x.1 r, ball x.2 r', measurableSet_ball,
      by simp [coeFn_def, μr], measurableSet_ball, by simp [coeFn_def, μr'], rfl⟩, ?_, ?_⟩
    · exact (isOpen_ball.prod isOpen_ball).mem_nhds (by simp [hr.1, hr'.1])
    · calc ball x.1 r ×ˢ ball x.2 r'
      _ ⊆ ball x.1 ε ×ˢ ball x.2 ε := by gcongr; exacts [hr.2.le, hr'.2.le]
      _ ⊆ _ := by rwa [ball_prod_same]
  · rintro s ⟨a, b, ameas, ha, bmeas, hb, rfl⟩
    simp only [prod_prod]
    apply Filter.Tendsto.mul
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.fst_nhds ha
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.snd_nhds hb

end ProbabilityMeasure -- namespace

end ProbabilityMeasure_product -- section

end MeasureTheory -- namespace

