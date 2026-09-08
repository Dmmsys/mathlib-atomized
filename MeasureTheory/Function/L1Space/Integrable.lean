/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integrable functions

In this file, the predicate `Integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `MemLp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `MemLp 1`.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`
  which also a `MeasurableSpace`. Then `f` is called `Integrable` if
  `f` is `Measurable` and `HasFiniteIntegral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`Integrable.induction` in the file `SetIntegral`.

## Tags

integrable

-/

@[expose] public section


noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set TopologicalSpace

open scoped Topology

variable {α β γ δ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] [ENorm ε'']

namespace MeasureTheory

/-! ### The predicate `Integrable` -/

/-- `Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `Integrable f` means `Integrable f volume`. -/
@[fun_prop, wikidata Q3153745]
/-
**MeasureTheory.Integrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Integrable {α} {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α
参数：f : α -> ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖
 ∂μ` is finite.
  `Integrable f` means `Integrable f volume`.
-/
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

/-- Notation for `Integrable` with respect to a non-standard σ-algebra. -/
scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

/-
**MeasureTheory.memLp_one_iff_integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：memLp_one_iff_integrable {f : α -> ε} : MemLp f 1 μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_one_iff_integrable {f : α → ε} : MemLp f 1 μ ↔ Integrable f μ := by
  simp_rw [Integrable, hasFiniteIntegral_iff_enorm, MemLp, eLpNorm_one_eq_lintegral_enorm]

@[fun_prop]
/-
**MeasureTheory.Integrable.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε}, MeasureTheory.Integrable f μ → MeasureTheory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Integrable.aestronglyMeasurable {f : α → ε} (hf : Integrable f μ) :
    AEStronglyMeasurable f μ :=
  hf.1

@[fun_prop]
/-
**MeasureTheory.Integrable.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] [inst_2 :
 MeasurableSpace ε] [BorelSpace ε] [TopologicalSpace.PseudoMetrizableSpace ε]   
{f : α → ε}, MeasureTheory.Integrable f μ → AEMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.aemeasurable [MeasurableSpace ε] [BorelSpace ε] [PseudoMetrizableSpace ε]
    {f : α → ε} (hf : Integrable f μ) : AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

@[fun_prop]
/-
**MeasureTheory.Integrable.hasFiniteIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε}, MeasureTheory.Integrable f μ → MeasureTheory.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Integrable.hasFiniteIntegral {f : α → ε} (hf : Integrable f μ) : HasFiniteIntegral f μ :=
  hf.2
/-
**MeasureTheory.Integrable.mono_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {ε' : Type u_6} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε']   {f : α → ε
} {g : α → ε'},   MeasureTheory.Integrable g μ →     MeasureTheory.AEStronglyMea
surable f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ) → MeasureTheory.Integrable f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_enorm`：∀ {α : Type u_1} {ε : Type u
_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst 
: ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono_enorm {f : α → ε} {g : α → ε'} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩
/-
**MeasureTheory.Integrable.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {f : α → β} {g : α → γ},   MeasureTheory.Integrable g μ →     Measure
Theory.AEStronglyMeasurable f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ ‖g a‖) → MeasureTheory
.Integrable f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ ‖g a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono h⟩
/-
**MeasureTheory.Integrable.mono_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [inst_1 : Lattice β] [HasSolidNorm β
] [AddLeftMono β] {f g : α → β},   MeasureTheory.Integrable g μ →     MeasureThe
ory.AEStronglyMeasurable f μ →       (∀ᵐ (a : α) ∂μ, 0 ≤ f a) → (∀ᵐ (a : α) ∂μ, 
f a ≤ g a) → MeasureTheory.Integrable f μ
参数：∀ᵐ (a : α) ∂μ, 0 ≤ f a；∀ᵐ (a : α) ∂μ, f a ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_nonneg`：∀ {α : Type u_1} {β : Type 
u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddComm
Group β]   [inst_1 : Lattice β] […
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α → β}
    (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hnonneg : ∀ᵐ a ∂μ, 0 ≤ f a)
    (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_nonneg hnonneg h⟩
/-
**MeasureTheory.Integrable.mono'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε} {g : α → ENNReal},   MeasureTheory.Integrable g μ →     MeasureTheory.AEStron
glyMeasurable f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a) → MeasureTheory.Integrable f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_enorm`：∀ {α : Type u_1} {ε : Type u
_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst 
: ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩
/-
**MeasureTheory.Integrable.mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
able`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} {g : α → ℝ},   MeasureTh
eory.Integrable g μ →     MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ (a : α) ∂
μ, ‖f a‖ ≤ g a) → MeasureTheory.Integrable f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'`：∀ {α : Type u_1} {β : Type u_2} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup 
β]   {f : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono' h⟩
/-
**MeasureTheory.Integrable.congr'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {ε' : Type u_6} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε']   {f : α → ε
} {g : α → ε'},   MeasureTheory.Integrable f μ →     MeasureTheory.AEStronglyMea
surable g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) → MeasureTheory.Integrable g μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr'_enorm`：∀ {α : Type u_1} {ε : Type
 u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.congr'_enorm {f : α → ε} {g : α → ε'} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr'_enorm h⟩
/-
**MeasureTheory.Integrable.congr'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integ
rable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {f : α → β} {g : α → γ},   MeasureTheory.Integrable f μ →     Measure
Theory.AEStronglyMeasurable g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ = ‖g a‖) → MeasureTheory
.Integrable g μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ = ‖g a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr'`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : N
ormedAddCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.congr' {f : α → β} {g : α → γ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr' h⟩
/-
**MeasureTheory.integrable_congr'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {ε' : Type u_6} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε']   {f : α → ε
} {g : α → ε'},   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheory.AES
tronglyMeasurable g μ →       (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) → (MeasureTheory.
Integrable f μ ↔ MeasureTheory.Integrable g μ)
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ；MeasureTheory.Integrable f μ ↔ MeasureTheory.I
ntegrable g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr'_enorm`：∀ {α : Type u_1} {ε : Type u_5} {
ε' : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : T
opologicalSpace ε] [inst_1 …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem integrable_congr'_enorm {f : α → ε} {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    Integrable f μ ↔ Integrable g μ :=
  ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf <| EventuallyEq.symm h⟩
/-
**MeasureTheory.integrable_congr'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_congr'_enorm {f : α -> ε} {g : α -> ε'} (hf : AEStronglyMeasura
ble f μ) (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : I
ntegrable f μ ↔ Integrable g μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；h : forallᵐ a ∂μ,
 ‖f a‖ₑ = ‖g a‖ₑ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integrable_congr'_enorm`：∀ {α : Type u_1} {ε : Type u_5} {
ε' : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : T
opologicalSpace ε] [inst_1 …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `enorm_eq_iff_norm_eq`：∀ {E : Type u_5} {F : Type u_6} [inst : Seminormed
AddGroup E] [inst_1 : SeminormedAddGroup F] {x : E} {y : F},   ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖
 = ‖y‖
-/
theorem integrable_congr' {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    Integrable f μ ↔ Integrable g μ :=
  integrable_congr'_enorm hf hg <| h.mono fun _x hx ↦ enorm_eq_iff_norm_eq.mpr hx
/-
**MeasureTheory.Integrable.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
able`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f g : α 
→ ε}, MeasureTheory.Integrable f μ → f =ᵐ[μ] g → MeasureTheory.Integrable g μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr`：∀ {α : Type u_1} {ε : Type u_4} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f g : α →
 ε},   MeasureTheory.HasFin…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Integrable.congr {f g : α → ε} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩
/-
**MeasureTheory.integrable_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_congr {f g : α -> ε} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integra
ble g μ
参数：h : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem integrable_congr {f g : α → ε} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩
/-
**MeasureTheory.integrable_const_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_const_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : 
α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.eq_1`：∀ {ε : Type u_5} [inst : TopologicalSpace
 ε] [inst_1 : ContinuousENorm ε] {α : Type u_8} {x : MeasurableSpace α}   (f : α
 → ε) (μ : MeasureT…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_iff_enorm`：hasFiniteIntegral_const
_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α => c) μ ↔ ‖c‖
ₑ = 0 ∨ IsFiniteMeasure μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrable_const_iff_enorm {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable, and_iff_right this, hasFiniteIntegral_const_iff_enorm hc]
/-
**MeasureTheory.integrable_const_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_const_iff {c : β} : Integrable (fun _ : α => c) μ ↔ c = 0 ∨ IsF
initeMeasure μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_const_iff_enorm`：integrable_const_iff_enorm {c 
: ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasu
re μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_const_iff {c : β} : Integrable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  rw [integrable_const_iff_enorm enorm_ne_top]
  simp
/-
**MeasureTheory.integrable_const_iff_isFiniteMeasure_enorm** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory`。
形式化陈述：integrable_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ != 0) (hc' :
 ‖c‖ₑ != ∞) : Integrable (fun _ => c) μ ↔ IsFiniteMeasure μ
参数：hc : ‖c‖ₑ != 0；hc' : ‖c‖ₑ != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_const_iff_enorm`：integrable_const_iff_enorm {c 
: ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasu
re μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ ≠ 0) (hc' : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff_enorm hc', hc, isFiniteMeasure_iff]
/-
**MeasureTheory.integrable_const_iff_isFiniteMeasure** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：integrable_const_iff_isFiniteMeasure {c : β} (hc : c != 0) : Integrable (f
un _ => c) μ ↔ IsFiniteMeasure μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_const_iff_isFiniteMeasure {c : β} (hc : c ≠ 0) :
    Integrable (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]
/-
**MeasureTheory.Integrable.of_mem_Icc_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asureTheory.IsFiniteMeasure μ]   {a b : ENNReal},   a ≠ ⊤ →     b ≠ ⊤ → ∀ {X : α
 → ENNReal}, AEMeasurable X μ → (∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b) → MeasureTheo
ry.Integrable X μ
参数：∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_mem_Icc_of_ne_top`：∀ {α : Type u_1} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeas
ure μ]   {a b : ENNReal},   a ≠ ⊤ → b ≠ ⊤ …
-/
theorem Integrable.of_mem_Icc_enorm [IsFiniteMeasure μ]
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) {X : α → ℝ≥0∞} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc_of_ne_top ha hb h⟩
/-
**MeasureTheory.Integrable.of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asureTheory.IsFiniteMeasure μ] (a b : ℝ)   {X : α → ℝ}, AEMeasurable X μ → (∀ᵐ (
ω : α) ∂μ, X ω ∈ Set.Icc a b) → MeasureTheory.Integrable X μ
参数：a b : ℝ；∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_mem_Icc`：∀ {α : Type u_1} {m : Measur
ableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] (a 
b : ℝ)   {X : α → ℝ}, (∀ᵐ (ω : α…
-/
theorem Integrable.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp, fun_prop]
/-
**MeasureTheory.integrable_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : Inte
grable (fun _ : α => c) μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_const_iff_enorm`：integrable_const_iff_enorm {c 
: ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasu
re μ
-/
theorem integrable_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ : α ↦ c) μ :=
  (integrable_const_iff_enorm hc).2 <| .inr ‹_›

@[fun_prop]
/-
**MeasureTheory.integrable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c)
 μ
参数：c : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.integrable_const_iff`：integrable_const_iff {c : β} : Integ
rable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ
-/
theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c) μ :=
  integrable_const_iff.2 <| .inr ‹_›

-- TODO: an `ENorm`-version of this lemma requires `HasFiniteIntegral.of_finite`
@[fun_prop, simp]
/-
**MeasureTheory.Integrable.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [Finite α] [MeasurableSingletonClass
 α] [MeasureTheory.IsFiniteMeasure μ] {f : α → β}, MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_discrete`：of_discrete [Countable α
] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_finite`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   [Finite α] [MeasureThe…
-/
lemma Integrable.of_finite [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] {f : α → β} :
    Integrable f μ := ⟨.of_discrete, .of_finite⟩

/-- This lemma is a special case of `Integrable.of_finite`. -/
/-
**MeasureTheory.Integrable.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [IsEmpty α] {f : α → β}, MeasureTheo
ry.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_finite`：∀ {α : Type u_1} {β : Type u_2} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β] 
  [Finite α] [Measurable…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Subsingleton.measurableSingletonClass`：∀ {α : Type u_1} [inst : Measurab
leSpace α] [Subsingleton α], MeasurableSingletonClass α
· 使用定理 `MeasureTheory.isFiniteMeasureOfIsEmpty`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [IsEmpty α], MeasureTheory.IsFiniteMeasu
re μ

--- 原说明 ---
This lemma is a special case of `Integrable.of_finite`.
-/
lemma Integrable.of_isEmpty [IsEmpty α] {f : α → β} : Integrable f μ := .of_finite

/-- This lemma is a special case of `Integrable.of_finite`. -/
/-
**MeasureTheory.Integrable.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [Subsingleton α] [MeasureTheory.IsFi
niteMeasure μ] {f : α → β}, MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_finite`：∀ {α : Type u_1} {β : Type u_2} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β] 
  [Finite α] [Measurable…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Subsingleton.measurableSingletonClass`：∀ {α : Type u_1} [inst : Measurab
leSpace α] [Subsingleton α], MeasurableSingletonClass α

--- 原说明 ---
This lemma is a special case of `Integrable.of_finite`.
-/
lemma Integrable.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α → β} :
    Integrable f μ :=
  .of_finite
/-
**MeasureTheory.MemLp.integrable_enorm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε} {p : ENNReal},   MeasureTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → MeasureTheory.In
tegrable (fun x => ‖f x‖ₑ ^ p.toReal) μ
参数：fun x => ‖f x‖ₑ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.enorm_rpow`：∀ {α : Type u_1} {m : MeasurableSpace α}
 {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_6}   [inst : Topologica
lSpace ε] [inst_1 : …
-/
theorem MemLp.integrable_enorm_rpow {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.enorm_rpow hp_ne_zero hp_ne_top
/-
**MeasureTheory.MemLp.integrable_norm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} {p : ENNReal},   Measure
Theory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → MeasureTheory.Integrable (fun x => ‖f x‖ ^ 
p.toReal) μ
参数：fun x => ‖f x‖ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.norm_rpow`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] {f : α →…
-/
theorem MemLp.integrable_norm_rpow {f : α → β} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top
/-
**MeasureTheory.MemLp.integrable_enorm_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] [MeasureT
heory.IsFiniteMeasure μ] {f : α → ε} {p : ENNReal},   MeasureTheory.MemLp f p μ 
→ MeasureTheory.Integrable (fun x => ‖f x‖ₑ ^ p.toReal) μ
参数：fun x => ‖f x‖ₑ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.MemLp.integrable_enorm_rpow`：∀ {α : Type u_1} {ε : Type u_
5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpac
e ε]   [inst_1 : ContinuousENor…
-/
theorem MemLp.integrable_enorm_rpow' [IsFiniteMeasure μ] {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_enorm_rpow h_zero h_top
/-
**MeasureTheory.MemLp.integrable_norm_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [MeasureTheory.IsFiniteMeasure μ] {f
 : α → β} {p : ENNReal},   MeasureTheory.MemLp f p μ → MeasureTheory.Integrable 
(fun x => ‖f x‖ ^ p.toReal) μ
参数：fun x => ‖f x‖ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.MemLp.integrable_norm_rpow`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {f : α → β} {p : ENNRe…
-/
theorem MemLp.integrable_norm_rpow' [IsFiniteMeasure μ] {f : α → β} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_norm_rpow h_zero h_top
/-
**MeasureTheory.MemLp.integrable_enorm_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε} {p : ℕ},   MeasureTheory.MemLp f (↑p) μ → p ≠ 0 → MeasureTheory.Integrable (f
un x => ‖f x‖ₑ ^ p) μ
参数：↑p；fun x => ‖f x‖ₑ ^ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `MeasureTheory.MemLp.integrable_enorm_rpow`：∀ {α : Type u_1} {ε : Type u_
5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpac
e ε]   [inst_1 : ContinuousENor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma MemLp.integrable_enorm_pow {f : α → ε} {p : ℕ} (hf : MemLp f p μ) (hp : p ≠ 0) :
    Integrable (fun x : α ↦ ‖f x‖ₑ ^ p) μ := by
  simpa using hf.integrable_enorm_rpow (mod_cast hp) (by simp)
/-
**MeasureTheory.MemLp.integrable_norm_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} {p : ℕ}, MeasureTheory.M
emLp f (↑p) μ → p ≠ 0 → MeasureTheory.Integrable (fun x => ‖f x‖ ^ p) μ
参数：↑p；fun x => ‖f x‖ ^ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `MeasureTheory.MemLp.integrable_norm_rpow`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {f : α → β} {p : ENNRe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma MemLp.integrable_norm_pow {f : α → β} {p : ℕ} (hf : MemLp f p μ) (hp : p ≠ 0) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by
  simpa using hf.integrable_norm_rpow (mod_cast hp) (by simp)
/-
**MeasureTheory.MemLp.integrable_enorm_pow'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] [MeasureT
heory.IsFiniteMeasure μ] {f : α → ε} {p : ℕ},   MeasureTheory.MemLp f (↑p) μ → M
easureTheory.Integrable (fun x => ‖f x‖ₑ ^ p) μ
参数：↑p；fun x => ‖f x‖ₑ ^ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `MeasureTheory.MemLp.integrable_enorm_rpow'`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
lemma MemLp.integrable_enorm_pow' [IsFiniteMeasure μ] {f : α → ε} {p : ℕ} (hf : MemLp f p μ) :
    Integrable (fun x : α ↦ ‖f x‖ₑ ^ p) μ := by simpa using hf.integrable_enorm_rpow'
/-
**MeasureTheory.MemLp.integrable_norm_pow'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [MeasureTheory.IsFiniteMeasure μ] {f
 : α → β} {p : ℕ},   MeasureTheory.MemLp f (↑p) μ → MeasureTheory.Integrable (fu
n x => ‖f x‖ ^ p) μ
参数：↑p；fun x => ‖f x‖ ^ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `MeasureTheory.MemLp.integrable_norm_rpow'`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   [MeasureTheory.IsFinit…
-/
lemma MemLp.integrable_norm_pow' [IsFiniteMeasure μ] {f : α → β} {p : ℕ} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by simpa using hf.integrable_norm_rpow'
/-
**MeasureTheory.integrable_enorm_rpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_enorm_rpow_iff {f : α -> ε} {p : Real>=0∞} (hf : AEStronglyMeas
urable f μ) (p_zero : p != 0) (p_top : p != ∞) : Integrable (fun x : α => ‖f x‖ₑ
 ^ p.toReal) μ ↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ；p_zero : p != 0；p_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_enorm_rpow_iff`：memLp_enorm_rpow_iff {q : Real>=0∞} 
{f : α -> ε} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0) (q_top : q != ∞) 
: MemLp (‖f ·‖ₑ ^ q.toRe…
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma integrable_enorm_rpow_iff {f : α → ε} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p ≠ 0) (p_top : p ≠ ∞) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_enorm_rpow_iff (q := p) hf p_zero p_top, ← memLp_one_iff_integrable,
    ENNReal.div_self p_zero p_top]
/-
**MeasureTheory.integrable_norm_rpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_norm_rpow_iff {f : α -> β} {p : Real>=0∞} (hf : AEStronglyMeasu
rable f μ) (p_zero : p != 0) (p_top : p != ∞) : Integrable (fun x : α => ‖f x‖ ^
 p.toReal) μ ↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ；p_zero : p != 0；p_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_norm_rpow_iff`：memLp_norm_rpow_iff {q : Real>=0∞} {f
 : α -> E} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0) (q_top : q != ∞) : 
MemLp (fun x : α => ‖f …
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma integrable_norm_rpow_iff {f : α → β} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p ≠ 0) (p_top : p ≠ ∞) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_norm_rpow_iff (q := p) hf p_zero p_top, ← memLp_one_iff_integrable,
    ENNReal.div_self p_zero p_top]
/-
**MeasureTheory.integrable_norm_rpow_of_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_norm_rpow_of_le [IsFiniteMeasure μ] {f : α -> β} (hf : AEStrong
lyMeasurable f μ) {p q : Real} (hp : 0 <= p) (hq : 0 <= q) (hpq : p <= q) (hint 
: Integrable (fun x => ‖f x‖ ^ q) μ) : Integrable (fun x => ‖f x‖ ^ p) μ
参数：hf : AEStronglyMeasurable f μ；hp : 0 <= p；hq : 0 <= q；hpq : p <= q；hint : Int
egrable (fun x => ‖f x‖ ^ q) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `MeasureTheory.integrable_norm_rpow_iff`：integrable_norm_rpow_iff {f : α 
-> β} {p : Real>=0∞} (hf : AEStronglyMeasurable f μ) (p_zero : p != 0) (p_top : 
p != ∞) : Integrable (fun x …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
lemma integrable_norm_rpow_of_le [IsFiniteMeasure μ] {f : α → β} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ≤ q) (hint : Integrable (fun x ↦ ‖f x‖ ^ q) μ) :
    Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · grind
  rw [← ENNReal.toReal_ofReal hp.le, integrable_norm_rpow_iff hf (by simp [hp]) (by simp)]
  rw [← ENNReal.toReal_ofReal hq.le, integrable_norm_rpow_iff hf (by simp [hq]) (by simp)] at hint
  exact MemLp.mono_exponent hint (ENNReal.ofReal_le_ofReal hpq)
/-
**MeasureTheory.integrable_norm_pow_of_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_norm_pow_of_le [IsFiniteMeasure μ] {f : α -> β} (hf : AEStrongl
yMeasurable f μ) {p q : Nat} (hpq : p <= q) (hint : Integrable (fun x => ‖f x‖ ^
 q) μ) : Integrable (fun x => ‖f x‖ ^ p) μ
参数：hf : AEStronglyMeasurable f μ；hpq : p <= q；hint : Integrable (fun x => ‖f x‖ 
^ q) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.integrable_norm_rpow_of_le`：integrable_norm_rpow_of_le [Is
FiniteMeasure μ] {f : α -> β} (hf : AEStronglyMeasurable f μ) {p q : Real} (hp :
 0 <= p) (hq : 0 <= q) (hpq : …
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma integrable_norm_pow_of_le [IsFiniteMeasure μ] {f : α → β} (hf : AEStronglyMeasurable f μ)
    {p q : ℕ} (hpq : p ≤ q) (hint : Integrable (fun x ↦ ‖f x‖ ^ q) μ) :
    Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
  simp_rw [← Real.rpow_natCast] at *
  exact integrable_norm_rpow_of_le hf p.cast_nonneg q.cast_nonneg (by simpa) hint
/-
**MeasureTheory.Integrable.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α 
→ ε}, MeasureTheory.Integrable f ν → μ ≤ ν → MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_measure`：∀ {α : Type u_1} {ε : Type
 u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : ENorm ε] {
f : α → ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.mono_measure {f : α → ε} (h : Integrable f ν) (hμ : μ ≤ ν) : Integrable f μ :=
  ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩
/-
**MeasureTheory.Integrable.of_measure_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] {μ' 
: MeasureTheory.Measure α} {c : ENNReal},   c ≠ ⊤ → μ' ≤ c • μ → ∀ {f : α → ε}, 
MeasureTheory.Integrable f μ → MeasureTheory.Integrable f μ'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.of_measure_le_smul`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : T
opologicalSpace ε] [inst_1 :…
-/
theorem Integrable.of_measure_le_smul {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → ε} (hf : Integrable f μ) : Integrable f μ' := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul hc hμ'_le

@[fun_prop]
/-
**MeasureTheory.Integrable.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] [Topolo
gicalSpace.PseudoMetrizableSpace ε] {f : α → ε},   MeasureTheory.Integrable f μ 
→ MeasureTheory.Integrable f ν → MeasureTheory.Integrable f (μ + ν)
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add_measure`：add_measure [PseudoMetri
zableSpace β] {ν : Measure α} {f : α -> β} (hμ : AEStronglyMeasurable f μ) (hν :
 AEStronglyMeasurable f ν) : AEStron…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_one_add_measure`：eLpNorm_one_add_measure (f : α ->
 ε) (μ ν : Measure α) : eLpNorm f 1 (μ + ν) = eLpNorm f 1 μ + eLpNorm f 1 ν
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem Integrable.add_measure [PseudoMetrizableSpace ε]
    {f : α → ε} (hμ : Integrable f μ) (hν : Integrable f ν) :
    Integrable f (μ + ν) := by
  simp_rw [← memLp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure, ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩
/-
**MeasureTheory.Integrable.left_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α 
→ ε}, MeasureTheory.Integrable f (μ + ν) → MeasureTheory.Integrable f μ
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.left_of_add_measure`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {p : ENNReal} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst 
: TopologicalSpace ε] [inst_1…
-/
theorem Integrable.left_of_add_measure {f : α → ε} (h : Integrable f (μ + ν)) : Integrable f μ := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure
/-
**MeasureTheory.Integrable.right_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α 
→ ε}, MeasureTheory.Integrable f (μ + ν) → MeasureTheory.Integrable f ν
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.right_of_add_measure`：∀ {α : Type u_1} {m0 : Measura
bleSpace α} {p : ENNReal} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst
 : TopologicalSpace ε] [inst_1…
-/
theorem Integrable.right_of_add_measure {f : α → ε} (h : Integrable f (μ + ν)) :
    Integrable f ν := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]
/-
**MeasureTheory.integrable_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_add_measure [PseudoMetrizableSpace ε] {f : α -> ε} : Integrable
 f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.left_of_add_measure`：∀ {α : Type u_1} {ε : Type
 u_5} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : Topologica
lSpace ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.right_of_add_measure`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : Topologic
alSpace ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrable_add_measure [PseudoMetrizableSpace ε] {f : α → ε} :
    Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]
/-
**MeasureTheory.integrable_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrable_zero_measure {f : α -> ε} : Integrable f (0 : Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_zero_measure`：aestronglyMeasurable_ze
ro_measure (f : α -> β) : AEStronglyMeasurable[m] f (0 : Measure[m₀] α)
· 使用定理 `MeasureTheory.hasFiniteIntegral_zero_measure`：hasFiniteIntegral_zero_mea
sure {m : MeasurableSpace α} (f : α -> ε) : HasFiniteIntegral f (0 : Measure α)
-/
theorem integrable_zero_measure {f : α → ε} : Integrable f (0 : Measure α) := by
  constructor <;> fun_prop

/-- In a measurable space with measurable singletons, every function is integrable with respect to
a Dirac measure.
See `integrable_dirac'` for a version which requires `f` to be strongly measurable but does not
need singletons to be measurable. -/
@[fun_prop]
/-
**MeasureTheory.integrable_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_dirac [MeasurableSingletonClass α] {a : α} {f : α -> ε} (hfa : 
‖f a‖ₑ < ∞) : Integrable f (Measure.dirac a)
参数：hfa : ‖f a‖ₑ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `aestronglyMeasurable_dirac`：aestronglyMeasurable_dirac [MeasurableSingle
tonClass α] {a : α} {f : α -> β} : AEStronglyMeasurable f (Measure.dirac a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a

--- 原说明 ---
In a measurable space with measurable singletons, every function is integrable w
ith respect to
a Dirac measure.
See `integrable_dirac'` for a version which requires `f` to be strongly measurab
le but does not
need singletons to be measurable.
-/
lemma integrable_dirac [MeasurableSingletonClass α] {a : α} {f : α → ε} (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨aestronglyMeasurable_dirac, by simpa [HasFiniteIntegral]⟩

/-- Every strongly measurable function is integrable with respect to a Dirac measure.
See `integrable_dirac` for a version which requires that singletons are measurable sets but has no
hypothesis on `f`. -/
@[fun_prop]
/-
**MeasureTheory.integrable_dirac'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_dirac' {a : α} {f : α -> ε} (hf : StronglyMeasurable f) (hfa : 
‖f a‖ₑ < ∞) : Integrable f (Measure.dirac a)
参数：hf : StronglyMeasurable f；hfa : ‖f a‖ₑ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…

--- 原说明 ---
Every strongly measurable function is integrable with respect to a Dirac measure
.
See `integrable_dirac` for a version which requires that singletons are measurab
le sets but has no
hypothesis on `f`.
-/
lemma integrable_dirac' {a : α} {f : α → ε} (hf : StronglyMeasurable f) (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨hf.aestronglyMeasurable, by simpa [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]⟩
/-
**MeasureTheory.integrable_finsetSum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrable_finsetSum_measure [PseudoMetrizableSpace ε] {ι} {m : Measurable
Space α} {f : α -> ε} {μ : ι -> Measure α} {s : Finset ι} : Integrable f (∑ i in
 s, μ i) ↔ forall i in s, Integrable f (μ i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem integrable_finsetSum_measure [PseudoMetrizableSpace ε]
    {ι} {m : MeasurableSpace α} {f : α → ε} {μ : ι → Measure α}
    {s : Finset ι} : Integrable f (∑ i ∈ s, μ i) ↔ ∀ i ∈ s, Integrable f (μ i) := by
  classical
  induction s using Finset.induction_on <;> simp [*]

@[deprecated (since := "2026-04-08")]
alias integrable_finset_sum_measure := integrable_finsetSum_measure

section

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[fun_prop]
/-
**MeasureTheory.Integrable.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] {f :
 α → ε},   MeasureTheory.Integrable f μ → ∀ {c : ENNReal}, c ≠ ⊤ → MeasureTheory
.Integrable f (c • μ)
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.smul_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topolog
icalSpace ε] [inst_1 :…
-/
theorem Integrable.smul_measure {f : α → ε} (h : Integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    Integrable f (c • μ) := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

@[fun_prop]
/-
**MeasureTheory.Integrable.smul_measure_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] {f :
 α → ε},   MeasureTheory.Integrable f μ → ∀ {c : NNReal}, MeasureTheory.Integrab
le f (c • μ)
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul_measure`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]
   [inst_1 : ESeminormedAdd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Integrable.smul_measure_nnreal {f : α → ε} (h : Integrable f μ) {c : ℝ≥0} :
    Integrable f (c • μ) := by
  apply h.smul_measure
  simp
/-
**MeasureTheory.integrable_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrable_smul_measure {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c 
!= ∞) : Integrable f (c • μ) ↔ Integrable f μ
参数：h₁ : c != 0；h₂ : c != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Integrable.smul_measure`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]
   [inst_1 : ESeminormedAdd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
-/
theorem integrable_smul_measure {f : α → ε} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c • μ) ↔ Integrable f μ :=
  ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩
/-
**MeasureTheory.integrable_inv_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrable_inv_smul_measure {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ 
: c != ∞) : Integrable f (c⁻¹ • μ) ↔ Integrable f μ
参数：h₁ : c != 0；h₂ : c != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_smul_measure`：integrable_smul_measure {f : α ->
 ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c • μ) ↔ Integrab
le f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem integrable_inv_smul_measure {f : α → ε} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c⁻¹ • μ) ↔ Integrable f μ :=
  integrable_smul_measure (by simpa using h₂) (by simpa using h₁)
/-
**MeasureTheory.Integrable.to_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] {f :
 α → ε},   MeasureTheory.Integrable f μ → MeasureTheory.Integrable f ((μ Set.uni
v)⁻¹ • μ)
参数：(μ Set.univ)⁻¹ • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Integrable.smul_measure`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]
   [inst_1 : ESeminormedAdd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Integrable.to_average {f : α → ε} (h : Integrable f μ) : Integrable f ((μ univ)⁻¹ • μ) := by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa
/-
**MeasureTheory.integrable_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_average [IsFiniteMeasure μ] {f : α -> ε} : Integrable f ((μ uni
v)⁻¹ • μ) ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.integrable_smul_measure`：integrable_smul_measure {f : α ->
 ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c • μ) ↔ Integrab
le f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
-/
theorem integrable_average [IsFiniteMeasure μ] {f : α → ε} :
    Integrable f ((μ univ)⁻¹ • μ) ↔ Integrable f μ := by
  classical
  exact (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| by finiteness)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

end

section

variable {α' : Type*} [MeasurableSpace α']

/-
**MeasureTheory.integrable_map_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_map_measure {f : α -> α'} {g : α' -> ε} (hg : AEStronglyMeasura
ble g (Measure.map f μ)) (hf : AEMeasurable f μ) : Integrable g (Measure.map f μ
) ↔ Integrable (g ∘ f) μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
-/
theorem integrable_map_measure {f : α → α'} {g : α' → ε}
    (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_map_measure_iff hg hf
/-
**MeasureTheory.Integrable.comp_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {α' : Typ
e u_8} [inst_2 : MeasurableSpace α'] {f : α → α'} {g : α' → ε},   MeasureTheory.
Integrable g (MeasureTheory.Measure.map f μ) → AEMeasurable f μ → MeasureTheory.
Integrable (g ∘ f) μ
参数：MeasureTheory.Measure.map f μ；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.comp_aemeasurable {f : α → α'} {g : α' → ε}
    (hg : Integrable g (Measure.map f μ)) (hf : AEMeasurable f μ) : Integrable (g ∘ f) μ :=
  (integrable_map_measure hg.aestronglyMeasurable hf).mp hg
/-
**MeasureTheory.Integrable.comp_measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {α' : Typ
e u_8} [inst_2 : MeasurableSpace α'] {f : α → α'} {g : α' → ε},   MeasureTheory.
Integrable g (MeasureTheory.Measure.map f μ) → Measurable f → MeasureTheory.Inte
grable (g ∘ f) μ
参数：MeasureTheory.Measure.map f μ；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_aemeasurable`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem Integrable.comp_measurable {f : α → α'} {g : α' → ε} (hg : Integrable g (Measure.map f μ))
    (hf : Measurable f) : Integrable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

end

/-
**MeasureTheory._root_.MeasurableEmbedding.integrable_map_iff** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrable_map_iff {f : α → δ} (hf : MeasurableEmbedding f)
    {g : δ → ε} : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact hf.memLp_map_measure_iff
/-
**MeasureTheory.integrable_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_map_equiv (f : α ≃ᵐ δ) (g : δ -> ε) : Integrable g (Measure.map
 f μ) ↔ Integrable (g ∘ f) μ
参数：f : α ≃ᵐ δ；g : δ -> ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.memLp_map_measure_iff`：∀ {α : Type u_1} {m0 : Measurable
Space α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : To
pologicalSpace ε] [inst_1 :…
-/
theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → ε) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff
/-
**MeasureTheory.MeasurePreserving.integrable_comp** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {δ : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : MeasurableSpace δ] [inst_1 : TopologicalSpa
ce ε] [inst_2 : ContinuousENorm ε] {ν : MeasureTheory.Measure δ}   {g : δ → ε} {
f : α → δ},   MeasureTheory.MeasurePreserving f μ ν →     MeasureTheory.AEStrong
lyMeasurable g ν → (MeasureTheory.Integrable (g ∘ f) μ ↔ MeasureTheory.Integrabl
e g ν)
参数：MeasureTheory.Integrable (g ∘ f) μ ↔ MeasureTheory.Integrable g ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
-/
theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : AEStronglyMeasurable g ν) :
    Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm
/-
**MeasureTheory.MeasurePreserving.integrable_comp_of_integrable** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {δ : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : MeasurableSpace δ] [inst_1 : TopologicalSpa
ce ε] [inst_2 : ContinuousENorm ε] {ν : MeasureTheory.Measure δ}   {g : δ → ε} {
f : α → δ},   MeasureTheory.MeasurePreserving f μ ν → MeasureTheory.Integrable g
 ν → MeasureTheory.Integrable (g ∘ f) μ
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp`：∀ {α : Type u_1} {δ : T
ype u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
[inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem MeasurePreserving.integrable_comp_of_integrable {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) :
    Integrable (g ∘ f) μ :=
  hf.integrable_comp hg.aestronglyMeasurable |>.mpr hg
/-
**MeasureTheory.MeasurePreserving.integrable_comp_emb** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {δ : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : MeasurableSpace δ] [inst_1 : TopologicalSpa
ce ε] [inst_2 : ContinuousENorm ε] {f : α → δ}   {ν : MeasureTheory.Measure δ}, 
  MeasureTheory.MeasurePreserving f μ ν →     MeasurableEmbedding f → ∀ {g : δ →
 ε}, MeasureTheory.Integrable (g ∘ f) μ ↔ MeasureTheory.Integrable g ν
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasurableEmbedding.integrable_map_iff`：∀ {α : Type u_1} {δ : Type u_4} 
{ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : M
easurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → ε} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff
/-
**MeasureTheory.lintegral_edist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_edist_lt_top {f g : α -> β} (hf : Integrable f μ) (hg : Integrab
le g μ) : (∫⁻ a, edist (f a) (g a) ∂μ) < ∞
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_edist_triangle`：lintegral_edist_triangle {f g h 
: α -> β} (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ) : (∫⁻ 
a, edist (f a) (g a) ∂μ) <= …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.aestronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   [inst_1 : Zero β], Me…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem lintegral_edist_lt_top {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

section ESeminormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

variable (α ε') in
@[to_fun (attr := fun_prop, simp) integrable_fun_zero]
/-
**MeasureTheory.integrable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_zero (μ : Measure α) : Integrable (0 : α -> ε') μ
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem integrable_zero (μ : Measure α) : Integrable (0 : α → ε') μ := by
  simp [Integrable, aestronglyMeasurable_zero]
/-
**MeasureTheory.Integrable.add'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε'
 : Type u_8} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] {
f g : α → ε'},   MeasureTheory.Integrable f μ → MeasureTheory.Integrable g μ → M
easureTheory.HasFiniteIntegral (f + g) μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `MeasureTheory.lintegral_enorm_add_left`：lintegral_enorm_add_left {f : α 
-> ε''} (hf : AEStronglyMeasurable f μ) (g : α -> ε') : ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ
 = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.add' {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f + g) μ :=
  calc
    ∫⁻ a, ‖f a + g a‖ₑ ∂μ ≤ ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ := lintegral_mono fun _ ↦ enorm_add_le _ _
    _ = _ := lintegral_enorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.Integrable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε'
 : Type u_8} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] [
ContinuousAdd ε'] {f g : α → ε'},   MeasureTheory.Integrable f μ → MeasureTheory
.Integrable g μ → MeasureTheory.Integrable (f + g) μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.add'`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [in
st_1 : ESeminormedA…
-/
theorem Integrable.add [ContinuousAdd ε']
    {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f + g) μ :=
  ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

@[deprecated (since := "2026-03-19")] alias Integrable.add'' := Integrable.fun_add

@[simp]
/-
**MeasureTheory.Integrable.of_subsingleton_codomain** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε'
 : Type u_8} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] [
Subsingleton ε'] {f : α → ε'}, MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma Integrable.of_subsingleton_codomain [Subsingleton ε'] {f : α → ε'} :
    Integrable f μ :=
  integrable_zero _ _ _ |>.congr <| .of_forall fun _ ↦ Subsingleton.elim _ _

end ESeminormedAddMonoid

section ESeminormedAddCommMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [ContinuousAdd ε']

@[fun_prop]
/-
**MeasureTheory.integrable_finsetSum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_finsetSum' {ι} (s : Finset ι) {f : ι -> α -> ε'} (hf : forall i
 in s, Integrable (f i) μ) : Integrable (∑ i in s, f i) μ
参数：s : Finset ι；hf : forall i in s, Integrable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem integrable_finsetSum' {ι} (s : Finset ι) {f : ι → α → ε'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum' := integrable_finsetSum'

@[fun_prop]
/-
**MeasureTheory.integrable_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_finsetSum {ι} (s : Finset ι) {f : ι -> α -> ε'} (hf : forall i 
in s, Integrable (f i) μ) : Integrable (fun a => ∑ i in s, f i a) μ
参数：s : Finset ι；hf : forall i in s, Integrable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
-/
theorem integrable_finsetSum {ι} (s : Finset ι) {f : ι → α → ε'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (fun a => ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using integrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum := integrable_finsetSum

end ESeminormedAddCommMonoid

/-- If `f` is integrable, then so is `-f`. -/
@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.Integrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.Integrabl
e f μ → MeasureTheory.Integrable (-f) μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.neg`：∀ {α : Type u_1} {β : Type u_2} {m 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]
   {f : α → β}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…

--- 原说明 ---
If `f` is integrable, then so is `-f`.
-/
theorem Integrable.neg {f : α → β} (hf : Integrable f μ) : Integrable (-f) μ :=
  ⟨hf.aestronglyMeasurable.neg, by fun_prop⟩

@[deprecated (since := "2026-03-19")] alias Integrable.neg' := Integrable.fun_neg

@[simp]
/-
**MeasureTheory.integrable_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_neg_iff {f : α -> β} : Integrable (-f) μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem integrable_neg_iff {f : α → β} : Integrable (-f) μ ↔ Integrable f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

@[simp]
/-
**MeasureTheory.integrable_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_fun_neg_iff {f : α -> β} : Integrable (fun x => -f x) μ ↔ Integ
rable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
-/
theorem integrable_fun_neg_iff {f : α → β} : Integrable (fun x ↦ -f x) μ ↔ Integrable f μ :=
  integrable_neg_iff

/-- if `f` is integrable, then `f + g` is integrable iff `g` is.
See `integrable_add_iff_integrable_right'` for the same statement with `fun x ↦ f x + g x` instead
of `f + g`. -/
@[simp]
/-
**MeasureTheory.integrable_add_iff_integrable_right** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：integrable_add_iff_integrable_right {f g : α -> β} (hf : Integrable f μ) :
 Integrable (f + g) μ ↔ Integrable g μ
参数：hf : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 a + b + -a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
if `f` is integrable, then `f + g` is integrable iff `g` is.
See `integrable_add_iff_integrable_right'` for the same statement with `fun x ↦ 
f x + g x` instead
of `f + g`.
-/
lemma integrable_add_iff_integrable_right {f g : α → β} (hf : Integrable f μ) :
    Integrable (f + g) μ ↔ Integrable g μ :=
  ⟨fun h ↦ show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h ↦ hf.add h⟩

/-- if `f` is integrable, then `fun x ↦ f x + g x` is integrable iff `g` is.
See `integrable_add_iff_integrable_right` for the same statement with `f + g` instead
of `fun x ↦ f x + g x`. -/
@[simp]
/-
**MeasureTheory.integrable_add_iff_integrable_right'** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：integrable_add_iff_integrable_right' {f g : α -> β} (hf : Integrable f μ) 
: Integrable (fun x => f x + g x) μ ↔ Integrable g μ
参数：hf : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_right`：integrable_add_iff_in
tegrable_right {f g : α -> β} (hf : Integrable f μ) : Integrable (f + g) μ ↔ Int
egrable g μ

--- 原说明 ---
if `f` is integrable, then `fun x ↦ f x + g x` is integrable iff `g` is.
See `integrable_add_iff_integrable_right` for the same statement with `f + g` in
stead
of `fun x ↦ f x + g x`.
-/
lemma integrable_add_iff_integrable_right' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ f x + g x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_right hf

/-- if `f` is integrable, then `g + f` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `fun x ↦ g x + f x` instead
of `g + f`. -/
@[simp]
/-
**MeasureTheory.integrable_add_iff_integrable_left** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：integrable_add_iff_integrable_left {f g : α -> β} (hf : Integrable f μ) : 
Integrable (g + f) μ ↔ Integrable g μ
参数：hf : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_right`：integrable_add_iff_in
tegrable_right {f g : α -> β} (hf : Integrable f μ) : Integrable (f + g) μ ↔ Int
egrable g μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
if `f` is integrable, then `g + f` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `fun x ↦ g
 x + f x` instead
of `g + f`.
-/
lemma integrable_add_iff_integrable_left {f g : α → β} (hf : Integrable f μ) :
    Integrable (g + f) μ ↔ Integrable g μ := by
  rw [add_comm, integrable_add_iff_integrable_right hf]

/-- if `f` is integrable, then `fun x ↦ g x + f x` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `g + f` instead
of `fun x ↦ g x + f x`. -/
@[simp]
/-
**MeasureTheory.integrable_add_iff_integrable_left'** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：integrable_add_iff_integrable_left' {f g : α -> β} (hf : Integrable f μ) :
 Integrable (fun x => g x + f x) μ ↔ Integrable g μ
参数：hf : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_left`：integrable_add_iff_int
egrable_left {f g : α -> β} (hf : Integrable f μ) : Integrable (g + f) μ ↔ Integ
rable g μ

--- 原说明 ---
if `f` is integrable, then `fun x ↦ g x + f x` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `g + f` in
stead
of `fun x ↦ g x + f x`.
-/
lemma integrable_add_iff_integrable_left' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ g x + f x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_left hf
/-
**MeasureTheory.integrable_left_of_integrable_add_of_nonneg** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：integrable_left_of_integrable_add_of_nonneg {f g : α -> Real} (h_meas : AE
StronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) (h_int : Integrable 
(f + g) μ) : Integrable f μ
参数：h_meas : AEStronglyMeasurable f μ；hf : 0 <=ᵐ[μ] f；hg : 0 <=ᵐ[μ] g；h_int : Int
egrable (f + g) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
-/
lemma integrable_left_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable f μ := by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag
/-
**MeasureTheory.integrable_right_of_integrable_add_of_nonneg** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：integrable_right_of_integrable_add_of_nonneg {f g : α -> Real} (h_meas : A
EStronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) (h_int : Integrable
 (f + g) μ) : Integrable g μ
参数：h_meas : AEStronglyMeasurable f μ；hf : 0 <=ᵐ[μ] f；hg : 0 <=ᵐ[μ] g；h_int : Int
egrable (f + g) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integrable_left_of_integrable_add_of_nonneg`：integrable_le
ft_of_integrable_add_of_nonneg {f g : α -> Real} (h_meas : AEStronglyMeasurable 
f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) (h_int…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add_iff_right`：∀ {α : Type u_1} {β : 
Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureThe
ory.Measure α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma integrable_right_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable g μ :=
  integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)
/-
**MeasureTheory.integrable_add_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrable_add_iff_of_nonneg {f g : α -> Real} (h_meas : AEStronglyMeasura
ble f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) : Integrable (f + g) μ ↔ Integrable
 f μ ∧ Integrable g μ
参数：h_meas : AEStronglyMeasurable f μ；hf : 0 <=ᵐ[μ] f；hg : 0 <=ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integrable_left_of_integrable_add_of_nonneg`：integrable_le
ft_of_integrable_add_of_nonneg {f g : α -> Real} (h_meas : AEStronglyMeasurable 
f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) (h_int…
· 使用引理 `MeasureTheory.integrable_right_of_integrable_add_of_nonneg`：integrable_r
ight_of_integrable_add_of_nonneg {f g : α -> Real} (h_meas : AEStronglyMeasurabl
e f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) (h_in…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma integrable_add_iff_of_nonneg {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h ↦ ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ ↦ hf.add hg⟩
/-
**MeasureTheory.integrable_add_iff_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrable_add_iff_of_nonpos {f g : α -> Real} (h_meas : AEStronglyMeasura
ble f μ) (hf : f <=ᵐ[μ] 0) (hg : g <=ᵐ[μ] 0) : Integrable (f + g) μ ↔ Integrable
 f μ ∧ Integrable g μ
参数：h_meas : AEStronglyMeasurable f μ；hf : f <=ᵐ[μ] 0；hg : g <=ᵐ[μ] 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用引理 `MeasureTheory.integrable_add_iff_of_nonneg`：integrable_add_iff_of_nonneg
 {f g : α -> Real} (h_meas : AEStronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0
 <=ᵐ[μ] g) : Integrable (f + g) …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
-/
lemma integrable_add_iff_of_nonpos {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : f ≤ᵐ[μ] 0) (hg : g ≤ᵐ[μ] 0) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  rw [← integrable_neg_iff, ← integrable_neg_iff (f := f), ← integrable_neg_iff (f := g), neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ ↦ neg_nonneg_of_nonpos))
    (hg.mono (fun _ ↦ neg_nonneg_of_nonpos))
/-
**MeasureTheory.integrable_add_const_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_add_const_iff [IsFiniteMeasure μ] {f : α -> β} {c : β} : Integr
able (fun x => f x + c) μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_left`：integrable_add_iff_int
egrable_left {f g : α -> β} (hf : Integrable f μ) : Integrable (g + f) μ ↔ Integ
rable g μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
lemma integrable_add_const_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ f x + c) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_left (integrable_const _)
/-
**MeasureTheory.integrable_const_add_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_const_add_iff [IsFiniteMeasure μ] {f : α -> β} {c : β} : Integr
able (fun x => c + f x) μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_add_iff_integrable_right`：integrable_add_iff_in
tegrable_right {f g : α -> β} (hf : Integrable f μ) : Integrable (f + g) μ ↔ Int
egrable g μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
lemma integrable_const_add_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ c + f x) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_right (integrable_const _)

-- TODO: generalise these lemmas to an `ENormedAddCommSubMonoid`
@[fun_prop]
/-
**MeasureTheory.Integrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f g : α → β}, MeasureTheory.Integra
ble f μ → MeasureTheory.Integrable g μ → MeasureTheory.Integrable (f - g) μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem Integrable.sub {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f - g) μ := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
/-
**MeasureTheory.Integrable.sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f g : α → β},   MeasureTheory.Integ
rable f μ → MeasureTheory.Integrable g μ → MeasureTheory.Integrable (fun a => f 
a - g a) μ
参数：fun a => f a - g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem Integrable.sub' {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a ↦ f a - g a) μ := by simpa only [sub_eq_add_neg] using! hf.add hg.neg

@[fun_prop]
/-
**MeasureTheory.Integrable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
able`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε}, MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun x => ‖f x‖ₑ) μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用引理 `Continuous.enorm`：Continuous.enorm : Continuous f -> Continuous (‖f ·‖ₑ)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.enorm`：∀ {α : Type u_1} {ε : Type u_4} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f : α → ε
},   MeasureTheory.HasFinit…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.enorm {f : α → ε} (hf : Integrable f μ) : Integrable (‖f ·‖ₑ) μ := by
  constructor <;> fun_prop

@[fun_prop]
/-
**MeasureTheory.Integrable.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.Integrabl
e f μ → MeasureTheory.Integrable (fun a => ‖f a‖) μ
参数：fun a => ‖f a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.norm`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {f : α → β}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.norm {f : α → β} (hf : Integrable f μ) : Integrable (fun a => ‖f a‖) μ := by
  constructor <;> fun_prop

@[fun_prop]
/-
**MeasureTheory.Integrable.inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_8} [inst : NormedAddCommGroup β]   [inst_1 : Lattice β] [HasSolidNorm β
] [IsOrderedAddMonoid β] {f g : α → β},   MeasureTheory.Integrable f μ → Measure
Theory.Integrable g μ → MeasureTheory.Integrable (f ⊓ g) μ
参数：f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.inf`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {p : ENNReal}   [inst : NormedAddCommGrou
p E] [inst_1 …
-/
theorem Integrable.inf {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊓ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

@[fun_prop]
/-
**MeasureTheory.Integrable.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_8} [inst : NormedAddCommGroup β]   [inst_1 : Lattice β] [HasSolidNorm β
] [IsOrderedAddMonoid β] {f g : α → β},   MeasureTheory.Integrable f μ → Measure
Theory.Integrable g μ → MeasureTheory.Integrable (f ⊔ g) μ
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.sup`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {p : ENNReal}   [inst : NormedAddCommGrou
p E] [inst_1 …
-/
theorem Integrable.sup {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊔ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

@[fun_prop]
/-
**MeasureTheory.Integrable.abs** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_8} [inst : NormedAddCommGroup β]   [inst_1 : Lattice β] [HasSolidNorm β
] [IsOrderedAddMonoid β] {f : α → β},   MeasureTheory.Integrable f μ → MeasureTh
eory.Integrable (fun a => |f a|) μ
参数：fun a => |f a|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.abs`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {p : ENNReal}   [inst : NormedAddCommGrou
p E] [inst_1 …
-/
theorem Integrable.abs {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f : α → β} (hf : Integrable f μ) :
    Integrable (fun a => |f a|) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.abs

-- TODO: generalise the following lemmas to enorm classes

/-- **Hölder's inequality for integrable functions**: the scalar multiplication of an integrable
vector-valued function by a scalar function with finite essential supremum is integrable. -/
/-
**MeasureTheory.Integrable.essSup_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {R : Type u_8} [inst_1 : NormedRing 
R] [inst_2 : _root_.Module R β] [IsBoundedSMul R β] {f : α → β},   MeasureTheory
.Integrable f μ →     ∀ {g : α → R},       MeasureTheory.AEStronglyMeasurable g 
μ →         essSup (fun x => ‖g x‖ₑ) μ ≠ ⊤ → MeasureTheory.Integrable (fun x => 
g x • f x) μ
参数：fun x => ‖g x‖ₑ；fun x => g x • f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`：eLpNorm_smul_le_mul_eLpNorm {
p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) {φ : α -> 𝕜} (hφ 
: AEStronglyMeasurable φ μ) [hp…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Hölder's inequality for integrable functions**: the scalar multiplication of a
n integrable
vector-valued function by a scalar function with finite essential supremum is in
tegrable.
-/
theorem Integrable.essSup_smul {R : Type*} [NormedRing R] [Module R β] [IsBoundedSMul R β]
    {f : α → β} (hf : Integrable f μ) {g : α → R}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ ≠ ∞) :
    Integrable (fun x : α => g x • f x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ ≤ _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable
        (p := ∞) (q := 1)
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

/-- Hölder's inequality for integrable functions: the scalar multiplication of an integrable
scalar-valued function by a vector-value function with finite essential supremum is integrable. -/
/-
**MeasureTheory.Integrable.smul_essSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → 𝕜},   MeasureTh
eory.Integrable f μ →     ∀ {g : α → β},       MeasureTheory.AEStronglyMeasurabl
e g μ →         essSup (fun x => ‖g x‖ₑ) μ ≠ ⊤ → MeasureTheory.Integrable (fun x
 => f x • g x) μ
参数：fun x => ‖g x‖ₑ；fun x => f x • g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`：eLpNorm_smul_le_mul_eLpNorm {
p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) {φ : α -> 𝕜} (hφ 
: AEStronglyMeasurable φ μ) [hp…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
Hölder's inequality for integrable functions: the scalar multiplication of an in
tegrable
scalar-valued function by a vector-value function with finite essential supremum
 is integrable.
-/
theorem Integrable.smul_essSup {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → 𝕜} (hf : Integrable f μ) {g : α → β}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ ≠ ∞) :
    Integrable (fun x : α => f x • g x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ ≤ _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1
        (p := 1) (q := ∞)
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top
/-
**MeasureTheory.integrable_enorm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_enorm_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) : Integr
able (‖f ·‖ₑ) μ ↔ Integrable f μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_enorm_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (‖f ·‖ₑ) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.enorm.aestronglyMeasurable,
    hasFiniteIntegral_enorm_iff]
/-
**MeasureTheory.integrable_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_norm_iff {f : α -> β} (hf : AEStronglyMeasurable f μ) : Integra
ble (fun a => ‖f a‖) μ ↔ Integrable f μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_norm_iff {f : α → β} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

-- TODO: generalise this lemma to an `ENormedAddCommSubMonoid`
/-
**MeasureTheory.integrable_of_norm_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_of_norm_sub_le {f₀ f₁ : α -> β} {g : α -> Real} (hf₁_m : AEStro
nglyMeasurable f₁ μ) (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : fora
llᵐ a ∂μ, ‖f₀ a - f₁ a‖ <= g a) : Integrable f₁ μ
参数：hf₁_m : AEStronglyMeasurable f₁ μ；hf₀_i : Integrable f₀ μ；hg_i : Integrable g
 μ；h : forallᵐ a ∂μ, ‖f₀ a - f₁ a‖ <= g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `norm_le_insert`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (u v : E)
, ‖v‖ ≤ ‖u‖ + ‖u - v‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem integrable_of_norm_sub_le {f₀ f₁ : α → β} {g : α → ℝ} (hf₁_m : AEStronglyMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : ∀ᵐ a ∂μ, ‖f₀ a - f₁ a‖ ≤ g a) :
    Integrable f₁ μ :=
  haveI : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ ≤ ‖f₀ a‖ + g a := by gcongr
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this
/-
**MeasureTheory.integrable_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_of_le_of_le {f g₁ g₂ : α -> Real} (hf : AEStronglyMeasurable f 
μ) (h_le₁ : g₁ <=ᵐ[μ] f) (h_le₂ : f <=ᵐ[μ] g₂) (h_int₁ : Integrable g₁ μ) (h_int
₂ : Integrable g₂ μ) : Integrable f μ
参数：hf : AEStronglyMeasurable f μ；h_le₁ : g₁ <=ᵐ[μ] f；h_le₂ : f <=ᵐ[μ] g₂；h_int₁ 
: Integrable g₁ μ；h_int₂ : Integrable g₂ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_le_max_abs_abs`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : L
inearOrder G] [IsOrderedAddMonoid G] {a b c : G},   a ≤ b → b ≤ c → |b| ≤ max |a
| |c|
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `max_le_add_of_nonneg`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : 
AddZeroClass α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ b → ma
x a b ≤ a …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
-/
lemma integrable_of_le_of_le {f g₁ g₂ : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ ≤ᵐ[μ] f) (h_le₂ : f ≤ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (by fun_prop) hf h_le_add

-- TODO: generalising this to enorms requires defining a product instance for enormed monoids first
@[fun_prop]
/-
**MeasureTheory.Integrable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integ
rable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {f : α → β} {g : α → γ},   MeasureTheory.Integrable f μ → MeasureTheo
ry.Integrable g μ → MeasureTheory.Integrable (fun x => (f x, g x)) μ
参数：fun x => (f x, g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.add'`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [in
st_1 : ESeminormedA…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `max_le_add_of_nonneg`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : 
AddZeroClass α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ b → ma
x a b ≤ a …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem Integrable.prodMk {f : α → β} {g : α → γ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x, g x)) μ :=
  ⟨by fun_prop,
    (hf.norm.add' hg.norm).mono <|
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ ≤ ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩
/-
**MeasureTheory.MemLp.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {q : ENNR
eal},   1 ≤ q → ∀ {f : α → ε} [MeasureTheory.IsFiniteMeasure μ], MeasureTheory.M
emLp f q μ → MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
-/
theorem MemLp.integrable {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → ε} [IsFiniteMeasure μ]
    (hfq : MemLp f q μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hfq.mono_exponent hq1)

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ₑ ≥ ε` is finite for all positive `ε`. -/
/-
**MeasureTheory.Integrable.measure_enorm_ge_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_8} [inst : TopologicalSpace E]   [inst_1 : ContinuousENorm E] {f : α → 
E},   MeasureTheory.Integrable f μ → ∀ {ε : ENNReal}, 0 < ε → ε ≠ ⊤ → μ {x | ε ≤
 ‖f x‖ₑ} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm`：meas_ge_le_mul_pow_eLpNo
rm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStrong
lyMeasurable f μ) {ε : Real>=0∞} (hε…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ

--- 原说明 ---
A non-quantitative version of Markov inequality for integrable functions: the me
asure of points
where `‖f x‖ₑ ≥ ε` is finite for all positive `ε`.
-/
theorem Integrable.measure_enorm_ge_lt_top {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) (hε' : ε ≠ ∞) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ := by
  refine meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero one_ne_top hf.1 hε.ne' (by simp [hε'])
    |>.trans_lt ?_
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one] using
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ ≥ ε` is finite for all positive `ε`. -/
/-
**MeasureTheory.Integrable.measure_norm_ge_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.Integrabl
e f μ → ∀ {ε : ℝ}, 0 < ε → μ {x | ε ≤ ‖f x‖} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `enorm_le_iff_norm_le`：∀ {E : Type u_5} {F : Type u_6} [inst : Seminormed
AddGroup E] [inst_1 : SeminormedAddGroup F] {x : E} {y : F},   ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖
 ≤ ‖y‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Integrable.measure_enorm_ge_lt_top`：∀ {α : Type u_1} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_8} [inst : Topologi
calSpace E]   [inst_1 : ContinuousENor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞

--- 原说明 ---
A non-quantitative version of Markov inequality for integrable functions: the me
asure of points
where `‖f x‖ ≥ ε` is finite for all positive `ε`.
-/
theorem Integrable.measure_norm_ge_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ { x | ε ≤ ‖f x‖ } < ∞ := by
  convert! Integrable.measure_enorm_ge_lt_top hf (ofReal_pos.mpr hε) ofReal_ne_top with x
  rw [← Real.enorm_of_nonneg hε.le, enorm_le_iff_norm_le, Real.norm_of_nonneg hε.le]

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ₑ > ε` is finite for all positive `ε`. -/
/-
**MeasureTheory.Integrable.measure_norm_gt_lt_top_enorm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_8} [inst : TopologicalSpace E]   [inst_1 : ContinuousENorm E] {f : α → 
E},   MeasureTheory.Integrable f μ → ∀ {ε : ENNReal}, 0 < ε → μ {x | ε < ‖f x‖ₑ}
 < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `MeasureTheory.Integrable.measure_enorm_ge_lt_top`：∀ {α : Type u_1} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_8} [inst : Topologi
calSpace E]   [inst_1 : ContinuousENor…

--- 原说明 ---
A non-quantitative version of Markov inequality for integrable functions: the me
asure of points
where `‖f x‖ₑ > ε` is finite for all positive `ε`.
-/
lemma Integrable.measure_norm_gt_lt_top_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) : μ {x | ε < ‖f x‖ₑ} < ∞ := by
  by_cases hε' : ε = ∞
  · simp [hε']
  exact lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_enorm_ge_lt_top hε hε')

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ > ε` is finite for all positive `ε`. -/
/-
**MeasureTheory.Integrable.measure_norm_gt_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.Integrabl
e f μ → ∀ {ε : ℝ}, 0 < ε → μ {x | ε < ‖f x‖} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `MeasureTheory.Integrable.measure_norm_ge_lt_top`：∀ {α : Type u_1} {β : T
ype u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAdd
CommGroup β]   {f : α → β}, MeasureTh…

--- 原说明 ---
A non-quantitative version of Markov inequality for integrable functions: the me
asure of points
where `‖f x‖ > ε` is finite for all positive `ε`.
-/
lemma Integrable.measure_norm_gt_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε < ‖f x‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_norm_ge_lt_top hε)

/-- If `f` is integrable, then for any `c > 0` the set `{x | f x ≥ c}` has finite
measure. -/
/-
**MeasureTheory.Integrable.measure_ge_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} [inst_1 : Lattice β] [Ha
sSolidNorm β] [AddLeftMono β],   MeasureTheory.Integrable f μ → ∀ {ε : β}, 0 < ε
 → μ {a | ε ≤ f a} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_le_norm_of_abs_le_abs`：norm_le_norm_of_abs_le_abs {a b : α} (h : |a
| <= |b|) : ‖a‖ <= ‖b‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Integrable.measure_norm_ge_lt_top`：∀ {α : Type u_1} {β : T
ype u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAdd
CommGroup β]   {f : α → β}, MeasureTh…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
If `f` is integrable, then for any `c > 0` the set `{x | f x ≥ c}` has finite
measure.
-/
lemma Integrable.measure_ge_lt_top {f : α → β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {ε : β} (ε_pos : 0 < ε) :
    μ {a : α | ε ≤ f a} < ∞ :=
  lt_of_le_of_lt (measure_mono fun x hx => norm_le_norm_of_abs_le_abs <|
    (abs_of_nonneg ε_pos.le).symm ▸ hx.trans (le_abs_self (f x)))
    (hf.measure_norm_ge_lt_top (by positivity [ε_pos.ne']))

/-- If `f` is integrable, then for any `c < 0` the set `{x | f x ≤ c}` has finite
measure. -/
/-
**MeasureTheory.Integrable.measure_le_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} [inst_1 : Lattice β] [Ha
sSolidNorm β] [AddLeftMono β],   MeasureTheory.Integrable f μ → ∀ {c : β}, c < 0
 → μ {a | f a ≤ c} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_le_norm_of_abs_le_abs`：norm_le_norm_of_abs_le_abs {a b : α} (h : |a
| <= |b|) : ‖a‖ <= ‖b‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Integrable.measure_norm_ge_lt_top`：∀ {α : Type u_1} {β : T
ype u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAdd
CommGroup β]   {f : α → β}, MeasureTh…

--- 原说明 ---
If `f` is integrable, then for any `c < 0` the set `{x | f x ≤ c}` has finite
measure.
-/
lemma Integrable.measure_le_lt_top {f : α → β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {c : β} (c_neg : c < 0) :
    μ {a : α | f a ≤ c} < ∞ := by
  have : 0 < ‖c‖ := by positivity [c_neg.ne]
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hf.measure_norm_ge_lt_top this)
  have : -c ≤ -f x := by simp; grind
  exact norm_le_norm_of_abs_le_abs <| abs_of_nonpos c_neg.le ▸ this.trans (neg_le_abs _)

/-- If `f` is integrable, then for any `c > 0` the set `{x | f x > c}` has finite
measure. -/
/-
**MeasureTheory.Integrable.measure_gt_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} [inst_1 : Lattice β] [Ha
sSolidNorm β] [AddLeftMono β],   MeasureTheory.Integrable f μ → ∀ {ε : β}, 0 < ε
 → μ {a | ε < f a} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `MeasureTheory.Integrable.measure_ge_lt_top`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {f : α → β} [inst_1 : …

--- 原说明 ---
If `f` is integrable, then for any `c > 0` the set `{x | f x > c}` has finite
measure.
-/
lemma Integrable.measure_gt_lt_top {f : α → β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {ε : β} (ε_pos : 0 < ε) :
    μ {a : α | ε < f a} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x < c}` has finite
measure. -/
/-
**MeasureTheory.Integrable.measure_lt_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} [inst_1 : Lattice β] [Ha
sSolidNorm β] [AddLeftMono β],   MeasureTheory.Integrable f μ → ∀ {c : β}, c < 0
 → μ {a | f a < c} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `MeasureTheory.Integrable.measure_le_lt_top`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {f : α → β} [inst_1 : …

--- 原说明 ---
If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x < c}
` has finite
measure.
-/
lemma Integrable.measure_lt_lt_top {f : α → β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {c : β} (c_neg : c < 0) :
    μ {a : α | f a < c} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)
/-
**MeasureTheory.LipschitzWith.integrable_comp_iff_of_antilipschitz** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.LipschitzWith`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {K K' : NNReal} {f : α → β} {g : β → γ},   LipschitzWith K g →     An
tilipschitzWith K' g → g 0 = 0 → (MeasureTheory.Integrable (g ∘ f) μ ↔ MeasureTh
eory.Integrable f μ)
参数：MeasureTheory.Integrable (g ∘ f) μ ↔ MeasureTheory.Integrable f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LipschitzWith.memLp_comp_iff_of_antilipschitz`：memLp_comp_iff_of_antilip
schitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
 [NormedAddCommGroup F] {f : α -> E…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem LipschitzWith.integrable_comp_iff_of_antilipschitz {K K'} {f : α → β} {g : β → γ}
    (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
    Integrable (g ∘ f) μ ↔ Integrable f μ := by
  simp [← memLp_one_iff_integrable, hg.memLp_comp_iff_of_antilipschitz hg' g0]

@[fun_prop]
/-
**MeasureTheory.Integrable.real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun x => ↑(
f x).toNNReal) μ
参数：fun x => ↑(f x).toNNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.real_toNNReal`：∀ {α : Type u_1} {m₀ :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.A
EStronglyMeasurable f μ → MeasureTheor…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_norm`：hasFiniteIntegral_iff_norm (f 
: α -> β) : HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.real_toNNReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ((f x).toNNReal : ℝ)) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [abs_le, le_abs_self]
/-
**MeasureTheory.ofReal_toReal_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ofReal_toReal_ae_eq {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞) : (fu
n x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f
参数：hf : forallᵐ x ∂μ, f x < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_toReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]
/-
**MeasureTheory.coe_toNNReal_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：coe_toNNReal_ae_eq {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞) : (fun
 x => ((f x).toNNReal : Real>=0∞)) =ᵐ[μ] f
参数：hf : forallᵐ x ∂μ, f x < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_toNNReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ((f x).toNNReal : ℝ≥0∞)) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

section count

variable [MeasurableSingletonClass α] {f : α → β}

/-- A function is integrable for the counting measure iff its norm is summable. -/
/-
**MeasureTheory.integrable_count_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_count_iff : Integrable f Measure.count ↔ Summable (‖f ·‖)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.eq_1`：∀ {ε : Type u_5} [inst : TopologicalSpace
 ε] [inst_1 : ContinuousENorm ε] {α : Type u_8} {x : MeasurableSpace α}   (f : α
 → ε) (μ : MeasureT…
· 使用引理 `MeasureTheory.hasFiniteIntegral_count_iff`：hasFiniteIntegral_count_iff {
f : α -> β} : HasFiniteIntegral f Measure.count ↔ Summable (‖f ·‖)
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.countable_support`：∀ {α : Type u_1} {G : Type u_4} [inst : Topo
logicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α → G
} [FirstCountabl…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.measurable_of_countable_ne`：Measurable.measurable_of_countabl
e_ne [MeasurableSingletonClass α] (hf : Measurable f) (h : Set.Countable { x | f
 x != g x }) : Measurable g
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `Set.Countable.isSeparable`：∀ {α : Type u} [t : TopologicalSpace α] {s : 
Set α}, s.Countable → TopologicalSpace.IsSeparable s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
A function is integrable for the counting measure iff its norm is summable.
-/
lemma integrable_count_iff :
    Integrable f Measure.count ↔ Summable (‖f ·‖) := by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable, hasFiniteIntegral_count_iff, and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  let : MeasurableSpace β := borel β
  have : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a ↦ ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ ⊆ (f '' f.support) ∪ {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    grind [Function.mem_support]

end count

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**MeasureTheory.integrable_withDensity_iff_integrable_coe_smul** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Me
asurable f) {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrabl
e (fun x => (f x : Real) • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `aestronglyMeasurable_withDensity_iff`：aestronglyMeasurable_withDensity_i
ff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : α -> Real>=0} (h
f : Measurable f) {g : α -…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'`：lintegral_withDe
nsity_eq_lintegral_mul₀' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable 
f μ) {g : α -> Real>=0∞} (hg : AEMeasurable …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `MeasureTheory.aemeasurable_withDensity_ennreal_iff`：aemeasurable_withDen
sity_ennreal_iff {f : α -> Real>=0} (hf : Measurable f) {g : α -> Real>=0∞} : AE
Measurable g (μ.withDensity fun x => (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem integrable_withDensity_iff_integrable_coe_smul {f : α → ℝ≥0} (hf : Measurable f)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : ℝ) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_enorm, H,
      true_and]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · simp [enorm_smul]
    · simpa [aemeasurable_withDensity_ennreal_iff hf, enorm_smul] using H.enorm
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]
/-
**MeasureTheory.integrable_withDensity_iff_integrable_smul** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measur
able f) {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (f
un x => f x • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_coe_smul`：integrable
_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Measurable f) {g :
 α -> E} : Integrable g (μ.withDensity fun x => f …
-/
theorem integrable_withDensity_iff_integrable_smul {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul hf
/-
**MeasureTheory.integrable_withDensity_iff_integrable_smul'** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_smul' {f : α -> Real>=0∞} (hf : Meas
urable f) (hflt : forallᵐ x ∂μ, f x < ∞) {g : α -> E} : Integrable g (μ.withDens
ity f) ↔ Integrable (fun x => (f x).toReal • g x) μ
参数：hf : Measurable f；hflt : forallᵐ x ∂μ, f x < ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
· 使用定理 `MeasureTheory.coe_toNNReal_ae_eq`：coe_toNNReal_ae_eq {f : α -> Real>=0∞}
 (hf : forallᵐ x ∂μ, f x < ∞) : (fun x => ((f x).toNNReal : Real>=0∞)) =ᵐ[μ] f
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul`：integrable_wit
hDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measurable f) {g : α -> E}
 : Integrable g (μ.withDensity fun x => f x) ↔…
· 使用定理 `Measurable.ennreal_toNNReal`：Measurable.ennreal_toNNReal {f : α -> Real>
=0∞} (hf : Measurable f) : Measurable fun x => (f x).toNNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_withDensity_iff_integrable_smul' {f : α → ℝ≥0∞} (hf : Measurable f)
    (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal
/-
**MeasureTheory.integrable_withDensity_iff_integrable_coe_smul** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Me
asurable f) {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrabl
e (fun x => (f x : Real) • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `aestronglyMeasurable_withDensity_iff`：aestronglyMeasurable_withDensity_i
ff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : α -> Real>=0} (h
f : Measurable f) {g : α -…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'`：lintegral_withDe
nsity_eq_lintegral_mul₀' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable 
f μ) {g : α -> Real>=0∞} (hg : AEMeasurable …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `MeasureTheory.aemeasurable_withDensity_ennreal_iff`：aemeasurable_withDen
sity_ennreal_iff {f : α -> Real>=0} (hf : Measurable f) {g : α -> Real>=0∞} : AE
Measurable g (μ.withDensity fun x => (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem integrable_withDensity_iff_integrable_coe_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ :=
  calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : ℝ≥0)) := by
      suffices (fun x => (f x : ℝ≥0∞)) =ᵐ[μ] (fun x => (hf.mk f x : ℝ≥0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : ℝ≥0) : ℝ) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
/-
**MeasureTheory.integrable_withDensity_iff_integrable_smul** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measur
able f) {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (f
un x => f x • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_coe_smul`：integrable
_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Measurable f) {g :
 α -> E} : Integrable g (μ.withDensity fun x => f …
-/
theorem integrable_withDensity_iff_integrable_smul₀' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    integrable_withDensity_iff_integrable_coe_smul₀]
  · congr!
  · exact hf.ennreal_toNNReal
/-
**MeasureTheory.integrable_withDensity_iff_integrable_smul** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：integrable_withDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measur
able f) {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (f
un x => f x • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_coe_smul`：integrable
_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Measurable f) {g :
 α -> E} : Integrable g (μ.withDensity fun x => f …
-/
theorem integrable_withDensity_iff_integrable_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul₀ hf

end

/-
**MeasureTheory.integrable_withDensity_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_withDensity_iff {f : α -> Real>=0∞} (hf : Measurable f) (hflt :
 forallᵐ x ∂μ, f x < ∞) {g : α -> Real} : Integrable g (μ.withDensity f) ↔ Integ
rable (fun x => g x * (f x).toReal) μ
参数：hf : Measurable f；hflt : forallᵐ x ∂μ, f x < ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul'`：integrable_wi
thDensity_iff_integrable_smul' {f : α -> Real>=0∞} (hf : Measurable f) (hflt : f
orallᵐ x ∂μ, f x < ∞) {g : α -> E} : Integrable…
-/
theorem integrable_withDensity_iff {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    {g : α → ℝ} : Integrable g (μ.withDensity f) ↔ Integrable (fun x => g x * (f x).toReal) μ := by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**MeasureTheory.memL1_smul_of_L1_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：memL1_smul_of_L1_withDensity {f : α -> Real>=0} (f_meas : Measurable f) (u
 : Lp E 1 (μ.withDensity fun x => f x)) : MemLp (fun x => f x • u x) 1 μ
参数：f_meas : Measurable f；u : Lp E 1 (μ.withDensity fun x => f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul`：integrable_wit
hDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measurable f) {g : α -> E}
 : Integrable g (μ.withDensity fun x => f x) ↔…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem memL1_smul_of_L1_withDensity {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) : MemLp (fun x => f x • u x) 1 μ :=
  memLp_one_iff_integrable.2 <|
    (integrable_withDensity_iff_integrable_smul f_meas).1 <| memLp_one_iff_integrable.1 (Lp.memLp u)

variable (μ)

/-- The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.withDensity f` and `μ`. -/
/-
**MeasureTheory.withDensitySMulLI** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：withDensitySMulLI {f : α -> Real>=0} (f_meas : Measurable f) : Lp E 1 (μ.w
ithDensity fun x => f x) ->ₗᵢ[Real] Lp E 1 μ where toFun u
参数：f_meas : Measurable f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.memL1_smul_of_L1_withDensity`：memL1_smul_of_L1_withDensity
 {f : α -> Real>=0} (f_meas : Measurable f) (u : Lp E 1 (μ.withDensity fun x => 
f x)) : MemLp (fun x => f x • u …

--- 原说明 ---
The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.withDensity f
` and `μ`.
-/
noncomputable def withDensitySMulLI {f : α → ℝ≥0} (f_meas : Measurable f) :
    Lp E 1 (μ.withDensity fun x => f x) →ₗᵢ[ℝ] Lp E 1 μ where
  toFun u := (memL1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memL1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memL1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv, h', Pi.add_apply, hu, hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memL1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memL1_smul_of_L1_withDensity f_meas u).toLp _),
      (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply, h', h'', Pi.smul_apply, h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    simp only [eLpNorm, LinearMap.coe_mk, AddHom.coe_mk,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.toReal_one, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx]
    simp [NNReal.smul_def, enorm_smul]

@[simp]
/-
**MeasureTheory.withDensitySMulLI_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：withDensitySMulLI_apply {f : α -> Real>=0} (f_meas : Measurable f) (u : Lp
 E 1 (μ.withDensity fun x => f x)) : withDensitySMulLI μ (E
参数：f_meas : Measurable f；u : Lp E 1 (μ.withDensity fun x => f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
-/
theorem withDensitySMulLI_apply {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) :
    withDensitySMulLI μ (E := E) f_meas u =
      (memL1_smul_of_L1_withDensity f_meas u).toLp fun x => f x • u x :=
  rfl

end

section ENNReal

/-
**MeasureTheory.mem_L1_toReal_of_lintegral_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：mem_L1_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable 
f μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : MemLp (fun x => (f x).toReal) 1 μ
参数：hfm : AEMeasurable f μ；hfi : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.eq_1`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measurab
leSpace α} [inst : ENorm ε] [inst_1 : TopologicalSpace ε] (f : α → ε)   (p : ENN
Real) (μ : Mea…
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.ennreal_toReal`：AEMeasurable.ennreal_toReal {f : α -> Real>
=0∞} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.to
Real (f x)) μ
· 使用定理 `MeasureTheory.hasFiniteIntegral_toReal_of_lintegral_ne_top`：hasFiniteInt
egral_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hf : ∫⁻ x, f x ∂μ != ∞) : 
HasFiniteIntegral (fun x => (f x).toReal) μ
-/
theorem mem_L1_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : MemLp (fun x ↦ (f x).toReal) 1 μ := by
  rw [MemLp, eLpNorm_one_eq_lintegral_enorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩
/-
**MeasureTheory.integrable_toReal_of_lintegral_ne_top** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integrable_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasura
ble f μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : Integrable (fun x => (f x).toReal) μ
参数：hfm : AEMeasurable f μ；hfi : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.mem_L1_toReal_of_lintegral_ne_top`：mem_L1_toReal_of_linteg
ral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x ∂μ != ∞
) : MemLp (fun x => (f x).toReal) 1 μ
-/
theorem integrable_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : Integrable (fun x ↦ (f x).toReal) μ :=
  memLp_one_iff_integrable.1 <| mem_L1_toReal_of_lintegral_ne_top hfm hfi
/-
**MeasureTheory.integrable_toReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_toReal_iff {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_t
op : forallᵐ x ∂μ, f x != ∞) : Integrable (fun x => (f x).toReal) μ ↔ ∫⁻ x, f x 
∂μ != ∞
参数：hf : AEMeasurable f μ；hf_ne_top : forallᵐ x ∂μ, f x != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.eq_1`：∀ {ε : Type u_5} [inst : TopologicalSpace
 ε] [inst_1 : ContinuousENorm ε] {α : Type u_8} {x : MeasurableSpace α}   (f : α
 → ε) (μ : MeasureT…
· 使用引理 `MeasureTheory.hasFiniteIntegral_toReal_iff`：hasFiniteIntegral_toReal_iff
 {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x != ∞) : HasFiniteIntegral (fun x =>
 (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.ennreal_toReal`：AEMeasurable.ennreal_toReal {f : α -> Real>
=0∞} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.to
Real (f x)) μ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  rw [Integrable, hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]
/-
**MeasureTheory.lintegral_ofReal_ne_top_iff_integrable** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：lintegral_ofReal_ne_top_iff_integrable {f : α -> Real} (hfm : AEStronglyMe
asurable f μ) (hf : 0 <=ᵐ[μ] f) : ∫⁻ a, ENNReal.ofReal (f a) ∂μ != ∞ ↔ Integrabl
e f μ
参数：hfm : AEStronglyMeasurable f μ；hf : 0 <=ᵐ[μ] f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.eq_1`：∀ {ε : Type u_5} [inst : TopologicalSpace
 ε] [inst_1 : ContinuousENorm ε] {α : Type u_8} {x : MeasurableSpace α}   (f : α
 → ε) (μ : MeasureT…
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_ofReal`：hasFiniteIntegral_iff_ofReal
 {f : α -> Real} (h : 0 <=ᵐ[μ] f) : HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofRea
l (f a) ∂μ) < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma lintegral_ofReal_ne_top_iff_integrable {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ∞ ↔ Integrable f μ := by
  rw [Integrable, hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

end ENNReal

section PosPart

/-! ### Lemmas used for defining the positive part of an `L¹` function -/


@[fun_prop]
/-
**MeasureTheory.Integrable.pos_part** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun a => ma
x (f a) 0) μ
参数：fun a => max (f a) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_sup`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Meas
ure α}   {f g : α → β} [inst_1 :…
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.HasFiniteIntegral.max_zero`：∀ {α : Type u_1} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.HasFiniteI
ntegral f μ → MeasureTheory.Ha…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…

--- 原说明 ---
### Lemmas used for defining the positive part of an `L¹` function
-/
theorem Integrable.pos_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (f a) 0) μ := by
  constructor <;> fun_prop

@[fun_prop]
/-
**MeasureTheory.Integrable.neg_part** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.Integrable f μ → MeasureTheory.Integrable (fun a => ma
x (-f a) 0) μ
参数：fun a => max (-f a) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.pos_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem Integrable.neg_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (-f a) 0) μ :=
  hf.neg.pos_part

end PosPart

section IsBoundedSMul

variable {𝕜 : Type*}
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.Integrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedAddCo
mmGroup 𝕜] [inst_2 : SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜) {f : α → β},
   MeasureTheory.Integrable f μ → MeasureTheory.Integrable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {𝕜 : Type u_7} [inst_1…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    {f : α → β} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop

@[to_fun (attr := fun_prop)]
/-
**MeasureTheory.Integrable.smul_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} {ε : Type u_9}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAd
dMonoid ε] [inst_2 : NormedAddCommGroup 𝕜] [inst_3 : SMul 𝕜 ε]   [ContinuousCons
tSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜) {f : α → ε},   MeasureTheory.Integrable 
f μ → MeasureTheory.Integrable (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.HasFiniteIntegral.smul_enorm`：∀ {α : Type u_1} {ε'' : Type
 u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalS
pace ε'']   [inst_1 : ESeminorme…
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.smul_enorm
    [NormedAddCommGroup 𝕜] [SMul 𝕜 ε] [ContinuousConstSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜)
    {f : α → ε} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop
/-
**MeasureTheory._root_.IsUnit.integrable_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.integrable_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : IsUnit c) (f : α → β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)
/-
**MeasureTheory.integrable_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoun
dedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -> β) : Integrable (c • f) μ ↔ Integra
ble f μ
参数：hc : c != 0；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.integrable_smul_iff`：∀ {α : Type u_1} {β : Type u_2} {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : T
ype u_8} [inst_1…
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
-/
theorem integrable_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  (IsUnit.mk0 _ hc).integrable_smul_iff f
/-
**MeasureTheory.integrable_fun_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrable_fun_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [Is
BoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -> β) : Integrable (fun x => c • f
 x) μ ↔ Integrable f μ
参数：hc : c != 0；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_smul_iff`：integrable_smul_iff [NormedDivisionRi
ng 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -
> β) : Integrable (c • …
-/
theorem integrable_fun_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
    Integrable (fun x ↦ c • f x) μ ↔ Integrable f μ :=
  integrable_smul_iff hc f

variable [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
/-
**MeasureTheory.Integrable.smul_of_top_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → β} {φ : α → 𝕜},   M
easureTheory.Integrable f μ → MeasureTheory.MemLp φ ⊤ μ → MeasureTheory.Integrab
le (φ • f) μ
参数：φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
-/
theorem Integrable.smul_of_top_right {f : α → β} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact MemLp.smul hf hφ
/-
**MeasureTheory.Integrable.bdd_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → β} {φ : α → 𝕜},   M
easureTheory.Integrable f μ →     ∀ (C : ℝ), MeasureTheory.AEStronglyMeasurable 
φ μ → (∀ᵐ (a : α) ∂μ, ‖φ a‖ ≤ C) → MeasureTheory.Integrable (φ • f) μ
参数：C : ℝ；∀ᵐ (a : α) ∂μ, ‖φ a‖ ≤ C；φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.smul_of_top_right`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
-/
theorem Integrable.bdd_smul {f : α → β} {φ : α → 𝕜} (hf : Integrable f μ)
    (C : ℝ) (hφ1 : AEStronglyMeasurable φ μ) (hφ2 : ∀ᵐ a ∂μ, ‖φ a‖ ≤ C) :
    Integrable (φ • f) μ :=
  hf.smul_of_top_right (memLp_top_of_bound hφ1 C hφ2)
/-
**MeasureTheory.Integrable.smul_of_top_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → β} {φ : α → 𝕜},   M
easureTheory.Integrable φ μ → MeasureTheory.MemLp f ⊤ μ → MeasureTheory.Integrab
le (φ • f) μ
参数：φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
-/
theorem Integrable.smul_of_top_left {f : α → β} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hφ ⊢
  exact MemLp.smul hf hφ
/-
**MeasureTheory.Integrable.smul_bdd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → β} {φ : α → 𝕜},   M
easureTheory.Integrable φ μ →     ∀ (C : ℝ), MeasureTheory.AEStronglyMeasurable 
f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ C) → MeasureTheory.Integrable (φ • f) μ
参数：C : ℝ；∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ C；φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.smul_of_top_left`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
-/
theorem Integrable.smul_bdd {f : α → β} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (C : ℝ) (hf1 : AEStronglyMeasurable f μ) (hf2 : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) :
    Integrable (φ • f) μ :=
  hφ.smul_of_top_left (memLp_top_of_bound hf1 C hf2)

@[fun_prop]
/-
**MeasureTheory.Integrable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_8} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul 𝕜 β] {f : α → 𝕜},   MeasureTheory
.Integrable f μ → ∀ (c : β), MeasureTheory.Integrable (fun x => f x • c) μ
参数：c : β；fun x => f x • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul_of_top_left`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.memLp_top_const`：memLp_top_const (c : E) : MemLp (fun _ : 
α => c) ∞ μ
-/
theorem Integrable.smul_const {f : α → 𝕜} (hf : Integrable f μ) (c : β) :
    Integrable (fun x => f x • c) μ :=
  hf.smul_of_top_left (memLp_top_const c)

end IsBoundedSMul

section NormedSpaceOverCompleteField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**MeasureTheory.integrable_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_smul_const {f : α -> 𝕜} {c : E} (hc : c != 0) : Integrable (fun
 x => f x • c) μ ↔ Integrable f μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aestronglyMeasurable_smul_const_iff`：aestronglyMeasurable_smul_const_iff
 {f : α -> 𝕜} {c : E} (hc : c != 0) : AEStronglyMeasurable (fun x => f x • c) μ 
↔ AEStronglyMeasurable f …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.lintegral_mul_const'`：lintegral_mul_const' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `ENNReal.mul_lt_top_iff`：mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a 
< ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    Integrable (fun x => f x • c) μ ↔ Integrable f μ := by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_enorm, enorm_smul]
  intro _; rw [lintegral_mul_const' _ _ enorm_ne_top, ENNReal.mul_lt_top_iff]
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

end NormedSpaceOverCompleteField

section NormedRing

variable {𝕜 : Type*} [NormedRing 𝕜] {f : α → 𝕜}

@[fun_prop]
/-
**MeasureTheory.Integrable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → 
∀ (c : 𝕜), MeasureTheory.Integrable (fun x => c * f x) μ
参数：c : 𝕜；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem Integrable.const_mul {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => c * f x) μ :=
  h.smul c

@[fun_prop]
/-
**MeasureTheory.Integrable.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → 
∀ (c : 𝕜), MeasureTheory.Integrable ((fun x => c) * f) μ
参数：c : 𝕜；(fun x => c) * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
-/
theorem Integrable.const_mul' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable ((fun _ : α => c) * f) μ :=
  Integrable.const_mul h c

@[fun_prop]
/-
**MeasureTheory.Integrable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → 
∀ (c : 𝕜), MeasureTheory.Integrable (fun x => f x * c) μ
参数：c : 𝕜；fun x => f x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem Integrable.mul_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

@[fun_prop]
/-
**MeasureTheory.Integrable.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → 
∀ (c : 𝕜), MeasureTheory.Integrable (f * fun x => c) μ
参数：c : 𝕜；f * fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mul_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
-/
theorem Integrable.mul_const' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (f * fun _ : α => c) μ :=
  Integrable.mul_const h c
/-
**MeasureTheory.integrable_const_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜) : Integrable
 (fun x => c * f x) μ ↔ Integrable f μ
参数：hc : IsUnit c；f : α -> 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.integrable_smul_iff`：∀ {α : Type u_1} {β : Type u_2} {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : T
ype u_8} [inst_1…
-/
theorem integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => c * f x) μ ↔ Integrable f μ :=
  hc.integrable_smul_iff f
/-
**MeasureTheory.integrable_mul_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_mul_const_iff {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜) : Integrable
 (fun x => f x * c) μ ↔ Integrable f μ
参数：hc : IsUnit c；f : α -> 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.integrable_smul_iff`：∀ {α : Type u_1} {β : Type u_2} {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : T
ype u_8} [inst_1…
· 使用定理 `IsUnit.op`：∀ {M : Type u_2} [inst : Monoid M] {m : M}, IsUnit m → IsUnit
 (MulOpposite.op m)
-/
theorem integrable_mul_const_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => f x * c) μ ↔ Integrable f μ :=
  hc.op.integrable_smul_iff f

-- TODO: generalise this to enorms, once there is an `ENormedDivisionRing` class
/-
**MeasureTheory.Integrable.bdd_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Inte
grable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜]   {f g : α → 𝕜} {c : ℝ},   MeasureTheory.Integ
rable g μ →     MeasureTheory.AEStronglyMeasurable f μ →       (∀ᵐ (x : α) ∂μ, ‖
f x‖ ≤ c) → MeasureTheory.Integrable (fun x => f x * g x) μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ c；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.bdd_smul`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
-/
theorem Integrable.bdd_mul {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    Integrable (fun x => f x * g x) μ :=
  hg.bdd_smul c hf hf_bound
/-
**MeasureTheory.Integrable.mul_bdd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Inte
grable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜]   {f g : α → 𝕜} {c : ℝ},   MeasureTheory.Integ
rable f μ →     MeasureTheory.AEStronglyMeasurable g μ →       (∀ᵐ (x : α) ∂μ, ‖
g x‖ ≤ c) → MeasureTheory.Integrable (fun x => f x * g x) μ
参数：∀ᵐ (x : α) ∂μ, ‖g x‖ ≤ c；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.smul_bdd`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
-/
theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c) :
    Integrable (fun x => f x * g x) μ :=
  hf.smul_bdd c hg hg_bound
/-
**MeasureTheory.Integrable.mul_of_top_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜]   {f φ : α → 𝕜}, MeasureTheory.Integrable f μ 
→ MeasureTheory.MemLp φ ⊤ μ → MeasureTheory.Integrable (φ * f) μ
参数：φ * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul_of_top_right`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {𝕜 : Type u_8} [inst_1…
-/
theorem Integrable.mul_of_top_right {f : α → 𝕜} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ * f) μ :=
  hf.smul_of_top_right hφ
/-
**MeasureTheory.Integrable.mul_of_top_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜]   {f φ : α → 𝕜}, MeasureTheory.Integrable φ μ 
→ MeasureTheory.MemLp f ⊤ μ → MeasureTheory.Integrable (φ * f) μ
参数：φ * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul_of_top_left`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {𝕜 : Type u_8} [inst_1…
-/
theorem Integrable.mul_of_top_left {f : α → 𝕜} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ * f) μ :=
  hφ.smul_of_top_left hf
/-
**MeasureTheory.MemLp.integrable_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedRing 𝕜]   {p q : ENNReal} {f g : α → 𝕜},   MeasureTheo
ry.MemLp f p μ → MeasureTheory.MemLp g q μ → ∀ [p.HolderTriple q 1], MeasureTheo
ry.Integrable (f * g) μ
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.mul`：∀ {α : Type u_1} {x : MeasurableSpace α} {𝕜 : T
ype u_2} [inst : NormedRing 𝕜] {μ : MeasureTheory.Measure α}   {p q r : ENNReal}
 {f φ : α → 𝕜…
-/
lemma MemLp.integrable_mul {p q : ℝ≥0∞} {f g : α → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [HolderTriple p q 1] :
    Integrable (f * g) μ :=
  memLp_one_iff_integrable.1 <| hg.mul hf

end NormedRing

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {f : α → 𝕜}

@[fun_prop]
/-
**MeasureTheory.Integrable.div_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : NormedDivisionRing 𝕜]   {f : α → 𝕜}, MeasureTheory.Integrabl
e f μ → ∀ (c : 𝕜), MeasureTheory.Integrable (fun x => f x / c) μ
参数：c : 𝕜；fun x => f x / c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Integrable.mul_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
-/
theorem Integrable.div_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x / c) μ := by simp_rw [div_eq_mul_inv, h.mul_const]

end NormedDivisionRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

@[fun_prop]
/-
**MeasureTheory.Integrable.ofReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integ
rable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : RCLike 𝕜] {f : α → ℝ},   MeasureTheory.Integrable f μ → Meas
ureTheory.Integrable (fun x => ↑(f x)) μ
参数：fun x => ↑(f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {p 
: ENNReal} {μ : MeasureTheory.Measure α} {K : Type u_8} [inst : RCLike K]   {f :
 α → ℝ}, Measure…
-/
theorem Integrable.ofReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => (f x : 𝕜)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.ofReal
/-
**MeasureTheory.Integrable.re_im_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : RCLike 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable (fun x => 
RCLike.re (f x)) μ ∧ MeasureTheory.Integrable (fun x => RCLike.im (f x)) μ ↔    
 MeasureTheory.Integrable f μ
参数：fun x => RCLike.re (f x)；fun x => RCLike.im (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_re_im_iff`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {K : Type u_8} [inst : RCLike K]   {
f : α → K},   Measu…
-/
theorem Integrable.re_im_iff :
    Integrable (fun x => RCLike.re (f x)) μ ∧ Integrable (fun x => RCLike.im (f x)) μ ↔
      Integrable f μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_re_im_iff

@[fun_prop]
/-
**MeasureTheory.Integrable.re** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrabl
e`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : RCLike 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → Meas
ureTheory.Integrable (fun x => RCLike.re (f x)) μ
参数：fun x => RCLike.re (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.re`：∀ {α : Type u_1} {m : MeasurableSpace α} {p : EN
NReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_5} [inst : RCLike 𝕜]   {f : α →
 𝕜}, Measure…
-/
theorem Integrable.re (hf : Integrable f μ) : Integrable (fun x => RCLike.re (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.re

@[fun_prop]
/-
**MeasureTheory.Integrable.im** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrabl
e`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_8} [inst : RCLike 𝕜] {f : α → 𝕜},   MeasureTheory.Integrable f μ → Meas
ureTheory.Integrable (fun x => RCLike.im (f x)) μ
参数：fun x => RCLike.im (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.im`：∀ {α : Type u_1} {m : MeasurableSpace α} {p : EN
NReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_5} [inst : RCLike 𝕜]   {f : α →
 𝕜}, Measure…
-/
theorem Integrable.im (hf : Integrable f μ) : Integrable (fun x => RCLike.im (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.im

end RCLike

section Trim

variable {H : Type*} [NormedAddCommGroup H] {m0 : MeasurableSpace α} {μ' : Measure α} {f : α → H}

/-
**MeasureTheory.Integrable.trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {H : Type u_8} [inst : NormedAddC
ommGroup H] {m0 : MeasurableSpace α}   {μ' : MeasureTheory.Measure α} {f : α → H
} (hm : m ≤ m0),   MeasureTheory.Integrable f μ' → MeasureTheory.StronglyMeasura
ble f → MeasureTheory.Integrable f (μ'.trim hm)
参数：hm : m ≤ m0；μ'.trim hm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.HasFiniteIntegral.eq_1`：∀ {α : Type u_1} {ε : Type u_4} [i
nst : ENorm ε] {x : MeasurableSpace α} (f : α → ε) (μ : MeasureTheory.Measure α)
,   MeasureTheory.HasFinit…
· 使用定理 `MeasureTheory.lintegral_trim`：lintegral_trim {μ : Measure α} (hm : m <= 
m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f 
a ∂μ
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Integrable.trim (hm : m ≤ m0) (hf_int : Integrable f μ') (hf : StronglyMeasurable[m] f) :
    Integrable f (μ'.trim hm) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_trim hm _]
  · exact hf_int.2
  · fun_prop
/-
**MeasureTheory.integrable_of_integrable_trim** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integrable_of_integrable_trim (hm : m <= m0) (hf_int : Integrable f (μ'.tr
im hm)) : Integrable f μ'
参数：hm : m <= m0；hf_int : Integrable f (μ'.trim hm)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aestronglyMeasurable_of_aestronglyMeasurable_trim`：∀ {β : Type u_2} [ins
t : TopologicalSpace β] {α : Type u_5} {m m0 : MeasurableSpace α} {μ : MeasureTh
eory.Measure α}   (hm : m ≤ m0) {f : α …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_trim_ae`：lintegral_trim_ae {μ : Measure α} (hm :
 m <= m0) {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.t
rim hm = ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : Integrable f (μ'.trim hm)) :
    Integrable f μ' := by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  simpa [HasFiniteIntegral, lintegral_trim_ae hm hf_meas_ae.enorm] using hf

end Trim

section SigmaFinite

variable {E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-
**MeasureTheory.integrable_of_forall_fin_meas_le'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m <= m0) [SigmaFin
ite (μ.trim hm)] (C : Real>=0∞) (hC : C < ∞) {f : α -> ε} (hf_meas : AEStronglyM
easurable f μ) (hf : forall s, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x
‖ₑ ∂μ <= C) : Integrable f μ
参数：hm : m <= m0；μ.trim hm；C : Real>=0∞；hC : C < ∞；hf_meas : AEStronglyMeasurable
 f μ；hf : forall s, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x‖ₑ ∂μ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.lintegral_le_of_forall_fin_meas_trim_le`：lintegral_le_of_f
orall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] 
(C : Real>=0∞) {f : α -> Real>=0∞} (hf : fo…
-/
theorem integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) (hC : C < ∞) {f : α → ε} (hf_meas : AEStronglyMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ C) : Integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩
/-
**MeasureTheory.integrable_of_forall_fin_meas_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : Real>=0∞) (hC : C < 
∞) {f : α -> ε} (hf_meas : AEStronglyMeasurable[m] f μ) (hf : forall s : Set α, 
MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x‖ₑ ∂μ <= C) : Integrable f μ
参数：C : Real>=0∞；hC : C < ∞；hf_meas : AEStronglyMeasurable[m] f μ；hf : forall s :
 Set α, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x‖ₑ ∂μ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_eq_self`：trim_eq_self [MeasurableSpace α] {μ : Measur
e α} : μ.trim le_rfl = μ
· 使用定理 `MeasureTheory.integrable_of_forall_fin_meas_le'`：integrable_of_forall_fi
n_meas_le' {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] (C : Real>=0
∞) (hC : C < ∞) {f : α -> ε} (hf_meas…
-/
theorem integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : ℝ≥0∞) (hC : C < ∞) {f : α → ε}
    (hf_meas : AEStronglyMeasurable[m] f μ)
    (hf : ∀ s : Set α, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ C) :
    Integrable f μ :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

end SigmaFinite

section restrict

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

/-- One should usually use `MeasureTheory.Integrable.integrableOn` instead. -/
/-
**MeasureTheory.Integrable.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → 
ε},   MeasureTheory.Integrable f μ → ∀ {s : Set α}, MeasureTheory.Integrable f (
μ.restrict s)
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ

--- 原说明 ---
One should usually use `MeasureTheory.Integrable.integrableOn` instead.
-/
lemma Integrable.restrict (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

end restrict

end MeasureTheory

section ContinuousLinearMap

open MeasureTheory

variable {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedSpace 𝕜' E] [NormedSpace 𝕜 H]

variable {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomIsometric σ] [RingHomIsometric σ']
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

@[fun_prop]
/-
**ContinuousLinearMap.integrable_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.integrable_comp {φ : α -> H} (L : H ->SL[σ] E) (φ_int 
: Integrable φ μ) : Integrable (fun a : α => L (φ a)) μ
参数：L : H ->SL[σ] E；φ_int : Integrable φ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem ContinuousLinearMap.integrable_comp {φ : α → H} (L : H →SL[σ] E) (φ_int : Integrable φ μ) :
    Integrable (fun a : α => L (φ a)) μ :=
  ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (by fun_prop)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]
/-
**ContinuousLinearEquiv.integrable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.integrable_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) : 
Integrable (fun a : α => L (φ a)) μ ↔ Integrable φ μ
参数：L : H ≃SL[σ] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
theorem ContinuousLinearEquiv.integrable_comp_iff {φ : α → H} (L : H ≃SL[σ] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ⟨fun h ↦ by simpa using ContinuousLinearMap.integrable_comp (L.symm : E →SL[σ'] H) h,
  fun h ↦ ContinuousLinearMap.integrable_comp (L : H →SL[σ] E) h⟩

@[simp]
/-
**LinearIsometryEquiv.integrable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.integrable_comp_iff {φ : α -> H} (L : H ≃ₛₗᵢ[σ] E) : I
ntegrable (fun a : α => L (φ a)) μ ↔ Integrable φ μ
参数：L : H ≃ₛₗᵢ[σ] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.integrable_comp_iff`：ContinuousLinearEquiv.integra
ble_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) : Integrable (fun a : α => L (φ a)) μ
 ↔ Integrable φ μ
-/
theorem LinearIsometryEquiv.integrable_comp_iff {φ : α → H} (L : H ≃ₛₗᵢ[σ] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ContinuousLinearEquiv.integrable_comp_iff (L : H ≃SL[σ] E)
/-
**MeasureTheory.Integrable.apply_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：MeasureTheory.Integrable.apply_continuousLinearMap {φ : α -> H ->SL[σ] E} 
(φ_int : Integrable φ μ) (v : H) : Integrable (fun a => φ a v) μ
参数：φ_int : Integrable φ μ；v : H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α → H →SL[σ] E}
    (φ_int : Integrable φ μ) (v : H) : Integrable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply' E σ v).integrable_comp φ_int

end ContinuousLinearMap

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[fun_prop]
/-
**MeasureTheory.Integrable.fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_8} {F : Type u_9}   [inst : NormedAddCommGroup E] [NormedSpace ℝ E] [in
st_2 : NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E × F},   MeasureTheory.
Integrable f μ → MeasureTheory.Integrable (fun x => (f x).1) μ
参数：fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
lemma Integrable.fst {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).1) μ :=
  (ContinuousLinearMap.fst ℝ E F).integrable_comp hf

@[fun_prop]
/-
**MeasureTheory.Integrable.snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integrab
le`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_8} {F : Type u_9}   [inst : NormedAddCommGroup E] [NormedSpace ℝ E] [in
st_2 : NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E × F},   MeasureTheory.
Integrable f μ → MeasureTheory.Integrable (fun x => (f x).2) μ
参数：fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
lemma Integrable.snd {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).2) μ :=
  (ContinuousLinearMap.snd ℝ E F).integrable_comp hf
/-
**MeasureTheory.integrable_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_prod {f : α -> E × F} : Integrable f μ ↔ Integrable (fun x => (
f x).1) μ ∧ Integrable (fun x => (f x).2) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.fst`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {E : Type u_8} {F : Type u_9}   [inst : NormedAddCo
mmGroup E] [Normed…
· 使用定理 `MeasureTheory.Integrable.snd`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {E : Type u_8} {F : Type u_9}   [inst : NormedAddCo
mmGroup E] [Normed…
· 使用定理 `MeasureTheory.Integrable.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma integrable_prod {f : α → E × F} :
    Integrable f μ ↔ Integrable (fun x ↦ (f x).1) μ ∧ Integrable (fun x ↦ (f x).2) μ :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

section Limit

/-- If `G n` tends to `f` a.e. and each `‖G n ·‖ₑ` is `AEMeasurable`, then the lower Lebesgue
integral of `‖f ·‖ₑ` is at most the liminf of the lower Lebesgue integral of `‖G n ·‖ₑ`. -/
/-
**MeasureTheory.lintegral_enorm_le_liminf_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：lintegral_enorm_le_liminf_of_tendsto {G : Nat -> Real -> Real} {f : Real -
> Real} {μ : Measure Real} (hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x)
 atTop (𝓝 (f x))) (hG : forall (n : Nat), AEMeasurable (fun x => ‖G n x‖ₑ) μ) : 
∫⁻ x, ‖f x‖ₑ ∂μ <= liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop
参数：hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x) atTop (𝓝 (f x))；hG : for
all (n : Nat), AEMeasurable (fun x => ‖G n x‖ₑ) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_liminf_le'`：lintegral_liminf_le' {ι : Type*} {f 
: ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i
, AEMeasurable (f i) μ) …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Filter.Tendsto.enorm`：Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Ten
dsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ)

--- 原说明 ---
If `G n` tends to `f` a.e. and each `‖G n ·‖ₑ` is `AEMeasurable`, then the lower
 Lebesgue
integral of `‖f ·‖ₑ` is at most the liminf of the lower Lebesgue integral of `‖G
 n ·‖ₑ`.
-/
theorem lintegral_enorm_le_liminf_of_tendsto
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    (hGf : ∀ᵐ x ∂μ, Tendsto (fun (n : ℕ) ↦ G n x) atTop (𝓝 (f x)))
    (hG : ∀ (n : ℕ), AEMeasurable (fun x ↦ ‖G n x‖ₑ) μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ liminf (fun n ↦ ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
  lintegral_congr_ae (by filter_upwards [hGf] with x hx using hx.enorm.liminf_eq) ▸
    (MeasureTheory.lintegral_liminf_le' hG)

/-- If `G n` tends to `f` a.e., each `G n` is `AEStronglyMeasurable` and the liminf of the lower
Lebesgue integral of `‖G n ·‖ₑ` is finite, then `f` is Lebesgue integrable. -/
/-
**MeasureTheory.integrable_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_of_tendsto {G : Nat -> Real -> Real} {f : Real -> Real} {μ : Me
asure Real} (hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x) atTop (𝓝 (f x)
)) (hG : forall (n : Nat), AEStronglyMeasurable (G n) μ) (hG' : liminf (fun n =>
 ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop != ⊤) : Integrable f μ
参数：hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x) atTop (𝓝 (f x))；hG : for
all (n : Nat), AEStronglyMeasurable (G n) μ；hG' : liminf (fun n => ∫⁻ x, ‖G n x‖
ₑ ∂μ) atTop != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_enorm_le_liminf_of_tendsto`：lintegral_enorm_le_l
iminf_of_tendsto {G : Nat -> Real -> Real} {f : Real -> Real} {μ : Measure Real}
 (hGf : forallᵐ x ∂μ, Tendsto (fun (n : …
· 使用定理 `AEMeasurable.enorm`：∀ {β : Type u_2} {ε : Type u_5} [inst : MeasurableSp
ace ε] [inst_1 : TopologicalSpace ε] [inst_2 : ContinuousENorm ε]   [OpensMeasur
ableSpac…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
If `G n` tends to `f` a.e., each `G n` is `AEStronglyMeasurable` and the liminf 
of the lower
Lebesgue integral of `‖G n ·‖ₑ` is finite, then `f` is Lebesgue integrable.
-/
theorem integrable_of_tendsto
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    (hGf : ∀ᵐ x ∂μ, Tendsto (fun (n : ℕ) ↦ G n x) atTop (𝓝 (f x)))
    (hG : ∀ (n : ℕ), AEStronglyMeasurable (G n) μ)
    (hG' : liminf (fun n ↦ ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop ≠ ⊤) :
    Integrable f μ :=
  ⟨aestronglyMeasurable_of_tendsto_ae _ hG hGf,
   lt_of_le_of_lt (lintegral_enorm_le_liminf_of_tendsto hGf
    (fun n ↦ (hG n).aemeasurable.enorm)) hG'.lt_top⟩

end Limit

end MeasureTheory

