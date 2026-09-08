/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Functions integrable on a set and at a filter

We define `IntegrableOn f s μ := Integrable f (μ.restrict s)` and prove theorems like
`integrableOn_union : IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ`.

Next we define a predicate `IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ ae μ` and `μ` is finite
at `l`.

-/

@[expose] public section


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E F : Type*} {mα : MeasurableSpace α}

section

variable [TopologicalSpace β] [ENorm ε] [TopologicalSpace ε]
  {l l' : Filter α} {f g : α → β} {μ ν : Measure α}

/-- A function `f` is strongly measurable at a filter `l` w.r.t. a measure `μ` if it is
ae strongly measurable w.r.t. `μ.restrict s` for some `s ∈ l`. -/
/-
**StronglyMeasurableAtFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StronglyMeasurableAtFilter (f : α -> β) (l : Filter α) (μ : Measure α
参数：f : α -> β；l : Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is strongly measurable at a filter `l` w.r.t. a measure `μ` if it
 is
ae strongly measurable w.r.t. `μ.restrict s` for some `s ∈ l`.
-/
def StronglyMeasurableAtFilter (f : α → β) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s)

@[simp]
/-
**stronglyMeasurableAt_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurableAt_bot {f : α -> β} : StronglyMeasurableAtFilter f ⊥ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_bot`：mem_bot {s : Set α} : s in (⊥ : Filter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
-/
theorem stronglyMeasurableAt_bot {f : α → β} : StronglyMeasurableAtFilter f ⊥ μ :=
  ⟨∅, mem_bot, by simp⟩
/-
**StronglyMeasurableAtFilter.eventually** 是 Mathlib 中的一个定理，位于命名空间 `StronglyMeasu
rableAtFilter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {l : Filter α} {f : α → β}   {μ : MeasureTheory.Measure α},   Strongl
yMeasurableAtFilter f l μ → ∀ᶠ (s : Set α) in l.smallSets, MeasureTheory.AEStron
glyMeasurable f (μ.restrict s)
参数：s : Set α；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_set`：mono_set {s t} (h : s subse
teq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) : AEStronglyMeasurable[m]
 f (μ.restrict s)
-/
protected theorem StronglyMeasurableAtFilter.eventually (h : StronglyMeasurableAtFilter f l μ) :
    ∀ᶠ s in l.smallSets, AEStronglyMeasurable f (μ.restrict s) :=
  (eventually_smallSets' fun _ _ => AEStronglyMeasurable.mono_set).2 h
/-
**StronglyMeasurableAtFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `StronglyMeas
urableAtFilter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {l l' : Filter α} {f : α → β}   {μ : MeasureTheory.Measure α}, Strong
lyMeasurableAtFilter f l μ → l' ≤ l → StronglyMeasurableAtFilter f l' μ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem StronglyMeasurableAtFilter.filter_mono (h : StronglyMeasurableAtFilter f l μ)
    (h' : l' ≤ l) : StronglyMeasurableAtFilter f l' μ :=
  let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩
/-
**MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {l : Filter α} {f : α → β}   {μ : MeasureTheory.Measure α}, MeasureTh
eory.AEStronglyMeasurable f μ → StronglyMeasurableAtFilter f l μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
protected theorem MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
    (h : AEStronglyMeasurable f μ) : StronglyMeasurableAtFilter f l μ :=
  ⟨univ, univ_mem, by rwa [Measure.restrict_univ]⟩
/-
**AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem {s} (h : AEStrongly
Measurable f (μ.restrict s)) (hl : s in l) : StronglyMeasurableAtFilter f l μ
参数：h : AEStronglyMeasurable f (μ.restrict s)；hl : s in l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem {s}
    (h : AEStronglyMeasurable f (μ.restrict s)) (hl : s ∈ l) : StronglyMeasurableAtFilter f l μ :=
  ⟨s, hl, h⟩
/-
**MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : Topologic
alSpace β] {l : Filter α} {f : α → β}   {μ : MeasureTheory.Measure α}, MeasureTh
eory.StronglyMeasurable f → StronglyMeasurableAtFilter f l μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
-/
protected theorem MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter
    (h : StronglyMeasurable f) : StronglyMeasurableAtFilter f l μ :=
  h.aestronglyMeasurable.stronglyMeasurableAtFilter

end

namespace MeasureTheory

section NormedAddCommGroup

/-
**MeasureTheory.HasFiniteIntegral.restrict_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {f : α → E} {s : Set α}   {μ : MeasureTheory.Measure α} (C : ℝ),   
μ s < ⊤ → (∀ᵐ (x : α) ∂μ.restrict s, ‖f x‖ ≤ C) → MeasureTheory.HasFiniteIntegra
l f (μ.restrict s)
参数：C : ℝ；∀ᵐ (x : α) ∂μ.restrict s, ‖f x‖ ≤ C；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
-/
theorem HasFiniteIntegral.restrict_of_bounded [NormedAddCommGroup E] {f : α → E} {s : Set α}
    {μ : Measure α} (C : ℝ) (hs : μ s < ∞) (hf : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  .of_bounded hf

variable [NormedAddCommGroup E] {f g : α → ε} {s t : Set α} {μ ν : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε]
/-
**MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : Con
tinuousENorm ε] {C : ENNReal},   autoParam (‖C‖ₑ ≠ ⊤) MeasureTheory.HasFiniteInt
egral.restrict_of_bounded_enorm._auto_1 →     autoParam (μ s ≠ ⊤) MeasureTheory.
HasFiniteIntegral.restrict_of_bounded_enorm._auto_3 →       (∀ᵐ (x : α) ∂μ.restr
ict s, ‖f x‖ₑ ≤ C) → MeasureTheory.HasFiniteIntegral f (μ.restrict s)
参数：‖C‖ₑ ≠ ⊤；μ s ≠ ⊤；∀ᵐ (x : α) ∂μ.restrict s, ‖f x‖ₑ ≤ C；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded_enorm`：∀ {α : Type u_1} {ε : 
Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε]
   [MeasureTheory.IsFiniteMeasure μ] {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem HasFiniteIntegral.restrict_of_bounded_enorm {C : ℝ≥0∞} (hC : ‖C‖ₑ ≠ ∞ := by finiteness)
    (hs : μ s ≠ ∞ := by finiteness) (hf : ∀ᵐ x ∂μ.restrict s, ‖f x‖ₑ ≤ C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  .of_bounded_enorm hC hf

/-- A function is `IntegrableOn` a set `s` if it is almost everywhere strongly measurable on `s`
and if the integral of its pointwise norm over `s` is less than infinity. -/
/-
**MeasureTheory.IntegrableOn** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IntegrableOn (f : α -> ε) (s : Set α) (μ : Measure α
参数：f : α -> ε；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is `IntegrableOn` a set `s` if it is almost everywhere strongly measu
rable on `s`
and if the integral of its pointwise norm over `s` is less than infinity.
-/
def IntegrableOn (f : α → ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)
/-
**MeasureTheory.IntegrableOn.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : Con
tinuousENorm ε],   MeasureTheory.IntegrableOn f s μ → MeasureTheory.Integrable f
 (μ.restrict s)
参数：μ.restrict s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IntegrableOn.integrable (h : IntegrableOn f s μ) : Integrable f (μ.restrict s) :=
  h

variable [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

@[simp]
/-
**MeasureTheory.integrableOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_empty : IntegrableOn f ∅ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
-/
theorem integrableOn_empty : IntegrableOn f ∅ μ := by
  simp [IntegrableOn]

@[simp]
/-
**MeasureTheory.integrableOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_univ : IntegrableOn f univ μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_univ : IntegrableOn f univ μ ↔ Integrable f μ := by
  rw [IntegrableOn, Measure.restrict_univ]
/-
**MeasureTheory.integrableOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_zero : IntegrableOn (fun _ => (0 : ε')) s μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem integrableOn_zero : IntegrableOn (fun _ => (0 : ε')) s μ :=
  integrable_zero _ _ _
/-
**MeasureTheory.IntegrableOn.of_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : Con
tinuousENorm ε], μ s = 0 → MeasureTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
-/
theorem IntegrableOn.of_measure_zero (hs : μ s = 0) : IntegrableOn f s μ := by
  simp [IntegrableOn, Measure.restrict_eq_zero.2 hs]

@[simp]
/-
**MeasureTheory.integrableOn_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrableOn_const_iff {C : ε'} (hC : ‖C‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_const_iff_enorm`：integrable_const_iff_enorm {c 
: ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasu
re μ
· 使用引理 `MeasureTheory.isFiniteMeasure_restrict`：isFiniteMeasure_restrict : IsFin
iteMeasure (μ.restrict s) ↔ μ s != ∞
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_const_iff {C : ε'} (hC : ‖C‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn (fun _ ↦ C) s μ ↔ ‖C‖ₑ = 0 ∨ μ s < ∞ := by
  rw [IntegrableOn, integrable_const_iff_enorm hC, isFiniteMeasure_restrict, lt_top_iff_ne_top]
/-
**MeasureTheory.integrableOn_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_const {C : ε'} (hs : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_const_iff`：integrableOn_const_iff {C : ε'} (h
C : ‖C‖ₑ != ∞
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem integrableOn_const {C : ε'} (hs : μ s ≠ ∞ := by finiteness)
    (hC : ‖C‖ₑ ≠ ∞ := by finiteness) : IntegrableOn (fun _ ↦ C) s μ :=
  (integrableOn_const_iff hC).2 <| Or.inr <| lt_top_iff_ne_top.2 hs

@[gcongr]
/-
**MeasureTheory.IntegrableOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integ
rableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ ν : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 :
 ContinuousENorm ε],   MeasureTheory.IntegrableOn f t ν → s ⊆ t → μ ≤ ν → Measur
eTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
-/
theorem IntegrableOn.mono (h : IntegrableOn f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) : IntegrableOn f s μ :=
  h.mono_measure <| Measure.restrict_mono hs hμ

@[gcongr]
/-
**MeasureTheory.IntegrableOn.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f t μ → s ⊆ t → MeasureTheory.In
tegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IntegrableOn.mono_set (h : IntegrableOn f t μ) (hst : s ⊆ t) : IntegrableOn f s μ :=
  h.mono hst le_rfl
/-
**MeasureTheory.IntegrableOn.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ ν : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s ν → μ ≤ ν → MeasureTheory.In
tegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IntegrableOn.mono_measure (h : IntegrableOn f s ν) (hμ : μ ≤ ν) : IntegrableOn f s μ :=
  h.mono (Subset.refl _) hμ
/-
**MeasureTheory.IntegrableOn.mono_measure'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ ν : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s ν → μ.restrict s ≤ ν.restric
t s → MeasureTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
-/
theorem IntegrableOn.mono_measure' (h : IntegrableOn f s ν) (hμ : μ.restrict s ≤ ν.restrict s) :
    IntegrableOn f s μ :=
  Integrable.mono_measure h hμ
/-
**MeasureTheory.IntegrableOn.mono_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f t μ → s ≤ᵐ[μ] t → MeasureTheor
y.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Measure.restrict_mono_ae`：restrict_mono_ae (h : s <=ᵐ[μ] t
) : μ.restrict s <= μ.restrict t
-/
theorem IntegrableOn.mono_set_ae (h : IntegrableOn f t μ) (hst : s ≤ᵐ[μ] t) : IntegrableOn f s μ :=
  h.integrable.mono_measure <| Measure.restrict_mono_ae hst
/-
**MeasureTheory.IntegrableOn.congr_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f t μ → s =ᵐ[μ] t → MeasureTheor
y.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set_ae`：∀ {α : Type u_1} {ε : Type u_3} 
{mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}
   [inst : TopologicalSpace …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
-/
theorem IntegrableOn.congr_set_ae (h : IntegrableOn f t μ) (hst : s =ᵐ[μ] t) : IntegrableOn f s μ :=
  h.mono_set_ae hst.le
/-
**MeasureTheory.integrableOn_congr_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrableOn_congr_set_ae (hst : s =ᵐ[μ] t) : IntegrableOn f s μ ↔ Integra
bleOn f t μ
参数：hst : s =ᵐ[μ] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.congr_set_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem integrableOn_congr_set_ae (hst : s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  ⟨fun h ↦ h.congr_set_ae hst.symm, fun h ↦ h.congr_set_ae hst⟩
/-
**MeasureTheory.IntegrableOn.congr_fun_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f g : α → ε} {s 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s μ → f =ᵐ[μ.restrict s] g → M
easureTheory.IntegrableOn g s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
-/
theorem IntegrableOn.congr_fun_ae (h : IntegrableOn f s μ) (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn g s μ :=
  Integrable.congr h hst

@[gcongr]
/-
**MeasureTheory.integrableOn_congr_fun_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrableOn_congr_fun_ae (hst : f =ᵐ[μ.restrict s] g) : IntegrableOn f s 
μ ↔ IntegrableOn g s μ
参数：hst : f =ᵐ[μ.restrict s] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem integrableOn_congr_fun_ae (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun_ae hst, fun h => h.congr_fun_ae hst.symm⟩
/-
**MeasureTheory.IntegrableOn.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f g : α → ε} {s 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s μ → Set.EqOn f g s → Measura
bleSet s → MeasureTheory.IntegrableOn g s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem IntegrableOn.congr_fun (h : IntegrableOn f s μ) (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn g s μ :=
  h.congr_fun_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall hst))
/-
**MeasureTheory.integrableOn_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrableOn_congr_fun (hst : EqOn f g s) (hs : MeasurableSet s) : Integra
bleOn f s μ ↔ IntegrableOn g s μ
参数：hst : EqOn f g s；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem integrableOn_congr_fun (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun hst hs, fun h => h.congr_fun hst.symm hs⟩
/-
**MeasureTheory.Integrable.integrableOn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : Con
tinuousENorm ε],   MeasureTheory.Integrable f μ → MeasureTheory.IntegrableOn f s
 μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
-/
theorem Integrable.integrableOn (h : Integrable f μ) : IntegrableOn f s μ := h.restrict

@[simp]
/-
**MeasureTheory.IntegrableOn.of_subsingleton_codomain** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] [Subsingleton ε'] {f : α → ε'},   MeasureTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_subsingleton_codomain`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : Topolo
gicalSpace ε']   [inst_1 : ESeminormedA…
-/
lemma IntegrableOn.of_subsingleton_codomain [Subsingleton ε'] {f : α → ε'} :
    IntegrableOn f s μ :=
  Integrable.of_subsingleton_codomain
/-
**MeasureTheory.Integrable.of_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteMeasure μ] {
f : α → E},   MeasureTheory.AEStronglyMeasurable f μ → ∀ (C : ℝ), (∀ᵐ (x : α) ∂μ
, ‖f x‖ ≤ C) → MeasureTheory.Integrable f μ
参数：C : ℝ；∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
-/
lemma Integrable.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ := ⟨hf, .of_bounded hfC⟩
/-
**MeasureTheory.IntegrableOn.of_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {s : Set α}   {μ : MeasureTheory.Measure α},   μ s < ⊤ →     ∀ {f :
 α → E},       MeasureTheory.AEStronglyMeasurable f (μ.restrict s) →         ∀ (
C : ℝ), (∀ᵐ (x : α) ∂μ.restrict s, ‖f x‖ ≤ C) → MeasureTheory.IntegrableOn f s μ
参数：μ.restrict s；C : ℝ；∀ᵐ (x : α) ∂μ.restrict s, ‖f x‖ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.restrict_of_bounded`：∀ {α : Type u_1} {E
 : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {f : α → E} 
{s : Set α}   {μ : MeasureTheory.Measure …
-/
lemma IntegrableOn.of_bound (hs : μ s < ∞) {f : α → E} (hf : AEStronglyMeasurable f (μ.restrict s))
    (C : ℝ) (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : IntegrableOn f s μ :=
  ⟨hf, .restrict_of_bounded C hs hfC⟩
/-
**MeasureTheory.IntegrableOn.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s μ → MeasureTheory.Integrable
On f s (μ.restrict t)
参数：μ.restrict t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.restrict_mono_measure`：restrict_mono_measure {_ : 
MeasurableSpace α} {μ ν : Measure α} (h : μ <= ν) (s : Set α) : μ.restrict s <= 
ν.restrict s
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem IntegrableOn.restrict (h : IntegrableOn f s μ) : IntegrableOn f s (μ.restrict t) := by
  dsimp only [IntegrableOn] at h ⊢
  exact h.mono_measure <| Measure.restrict_mono_measure Measure.restrict_le_self _
/-
**MeasureTheory.IntegrableOn.inter_of_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f s (μ.restrict t) → MeasureTheo
ry.IntegrableOn f (s ∩ t) μ
参数：μ.restrict t；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_restrict_of_subset`：restrict_restrict_of_
subset (h : s subseteq t) : (μ.restrict t).restrict s = μ.restrict s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
-/
theorem IntegrableOn.inter_of_restrict (h : IntegrableOn f s (μ.restrict t)) :
    IntegrableOn f (s ∩ t) μ := by
  have := h.mono_set (inter_subset_left (t := t))
  rwa [IntegrableOn, μ.restrict_restrict_of_subset inter_subset_right] at this
/-
**MeasureTheory.Integrable.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f g : α → ε'}   [inst_2 : DecidablePred fun x => x ∈ s],   Measurab
leSet s →     MeasureTheory.IntegrableOn f s μ → MeasureTheory.IntegrableOn g sᶜ
 μ → MeasureTheory.Integrable (s.piecewise f g) μ
参数：s.piecewise f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.piecewise`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologica
lSpace ε] [inst_1 :…
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
-/
lemma Integrable.piecewise {f g : α → ε'} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ) :
    Integrable (s.piecewise f g) μ := by
  rw [IntegrableOn] at hf hg
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact MemLp.piecewise hs hf hg
/-
**MeasureTheory.IntegrableOn.left_of_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f (s ∪ t) μ → MeasureTheory.Inte
grableOn f s μ
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem IntegrableOn.left_of_union (h : IntegrableOn f (s ∪ t) μ) : IntegrableOn f s μ :=
  h.mono_set subset_union_left
/-
**MeasureTheory.IntegrableOn.right_of_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε],   MeasureTheory.IntegrableOn f (s ∪ t) μ → MeasureTheory.Inte
grableOn f t μ
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem IntegrableOn.right_of_union (h : IntegrableOn f (s ∪ t) μ) : IntegrableOn f t μ :=
  h.mono_set subset_union_right
/-
**MeasureTheory.IntegrableOn.union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Inte
grableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s t 
: Set α} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε] [TopologicalSpace.PseudoMetrizableSpace ε],   MeasureTheory.In
tegrableOn f s μ → MeasureTheory.IntegrableOn f t μ → MeasureTheory.IntegrableOn
 f (s ∪ t) μ
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.restrict_union_le`：restrict_union_le (s s' : Set α
) : μ.restrict (s union s') <= μ.restrict s + μ.restrict s'
-/
theorem IntegrableOn.union [PseudoMetrizableSpace ε]
    (hs : IntegrableOn f s μ) (ht : IntegrableOn f t μ) :
    IntegrableOn f (s ∪ t) μ :=
  (hs.add_measure ht).mono_measure <| Measure.restrict_union_le _ _

@[simp]
/-
**MeasureTheory.integrableOn_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_union [PseudoMetrizableSpace ε] : IntegrableOn f (s union t) 
μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.left_of_union`：∀ {α : Type u_1} {ε : Type u_3
} {mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure 
α}   [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.IntegrableOn.right_of_union`：∀ {α : Type u_1} {ε : Type u_
3} {mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure
 α}   [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrableOn_union [PseudoMetrizableSpace ε] :
    IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ :=
  ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

@[simp]
/-
**MeasureTheory.integrableOn_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrableOn_singleton_iff {f : α -> ε'} {x : α} [MeasurableSingletonClass
 α] (hfx : ‖f x‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.integrable_const_iff_enorm`：integrable_const_iff_enorm {c 
: ε} (hc : ‖c‖ₑ != ∞) : Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasu
re μ
· 使用引理 `MeasureTheory.isFiniteMeasure_restrict`：isFiniteMeasure_restrict : IsFin
iteMeasure (μ.restrict s) ↔ μ s != ∞
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_singleton_iff {f : α → ε'} {x : α}
    [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ ≠ ⊤ := by finiteness) :
    IntegrableOn f {x} μ ↔ ‖f x‖ₑ = 0 ∨ μ {x} < ∞ := by
  have : f =ᵐ[μ.restrict {x}] fun _ => f x := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton x)] with _ ha
    simp only [mem_singleton_iff.1 ha]
  rw [IntegrableOn, integrable_congr this, integrable_const_iff_enorm, isFiniteMeasure_restrict,
    lt_top_iff_ne_top]
  exact hfx
/-
**MeasureTheory.integrableOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrableOn_singleton {f : α -> ε'} {x : α} [MeasurableSingletonClass α] 
(hfx : ‖f x‖ₑ != ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_singleton_iff`：integrableOn_singleton_iff {f 
: α -> ε'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
-/
theorem integrableOn_singleton {f : α → ε'} {x : α} [MeasurableSingletonClass α]
    (hfx : ‖f x‖ₑ ≠ ⊤ := by finiteness) (hx : μ {x} < ∞ := by finiteness) : IntegrableOn f {x} μ :=
  (integrableOn_singleton_iff hfx).mpr (Or.inr hx)

@[simp]
/-
**MeasureTheory.integrableOn_finite_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrableOn_finite_biUnion [PseudoMetrizableSpace ε] {s : Set β} (hs : s.
Finite) {t : β -> Set α} : IntegrableOn f (⋃ i in s, t i) μ ↔ forall i in s, Int
egrableOn f (t i) μ
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
-/
theorem integrableOn_finite_biUnion [PseudoMetrizableSpace ε]
    {s : Set β} (hs : s.Finite) {t : β → Set α} :
    IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hf => simp [hf, or_imp, forall_and]

@[simp]
/-
**MeasureTheory.integrableOn_finset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrableOn_finset_iUnion [PseudoMetrizableSpace ε] {s : Finset β} {t : β
 -> Set α} : IntegrableOn f (⋃ i in s, t i) μ ↔ forall i in s, IntegrableOn f (t
 i) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_finite_biUnion`：integrableOn_finite_biUnion [
PseudoMetrizableSpace ε] {s : Set β} (hs : s.Finite) {t : β -> Set α} : Integrab
leOn f (⋃ i in s, t i) μ ↔ fora…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem integrableOn_finset_iUnion [PseudoMetrizableSpace ε] {s : Finset β} {t : β → Set α} :
    IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ :=
  integrableOn_finite_biUnion s.finite_toSet

@[simp]
/-
**MeasureTheory.integrableOn_finite_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrableOn_finite_iUnion [PseudoMetrizableSpace ε] [Finite β] {t : β -> 
Set α} : IntegrableOn f (⋃ i, t i) μ ↔ forall i, IntegrableOn f (t i) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.integrableOn_finset_iUnion`：integrableOn_finset_iUnion [Ps
eudoMetrizableSpace ε] {s : Finset β} {t : β -> Set α} : IntegrableOn f (⋃ i in 
s, t i) μ ↔ forall i in s, Int…
-/
theorem integrableOn_finite_iUnion [PseudoMetrizableSpace ε] [Finite β] {t : β → Set α} :
    IntegrableOn f (⋃ i, t i) μ ↔ ∀ i, IntegrableOn f (t i) μ := by
  cases nonempty_fintype β
  simpa using integrableOn_finset_iUnion (f := f) (μ := μ) (s := Finset.univ) (t := t)

-- TODO: generalise this lemma and the next to enorm classes; this entails assuming that
-- f is finite on almost every element of `s`
/-
**MeasureTheory.IntegrableOn.finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] [MeasurableSingletonClass α]   {μ : MeasureTheory.Measure α} [Measu
reTheory.IsFiniteMeasure μ] {s : Finset α} {f : α → E},   MeasureTheory.Integrab
leOn f (↑s) μ
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IntegrableOn.finset [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Finset α} {f : α → E} : IntegrableOn f s μ := by
  rw [← (s : Set α).biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]
/-
**MeasureTheory.IntegrableOn.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] [MeasurableSingletonClass α]   {μ : MeasureTheory.Measure α} [Measu
reTheory.IsFiniteMeasure μ] {s : Set α},   s.Finite → ∀ {f : α → E}, MeasureTheo
ry.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `MeasureTheory.IntegrableOn.finset`：∀ {α : Type u_1} {E : Type u_5} {mα :
 MeasurableSpace α} [inst : NormedAddCommGroup E] [MeasurableSingletonClass α]  
 {μ : MeasureTheory.Mea…
-/
lemma IntegrableOn.of_finite [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Finite) {f : α → E} : IntegrableOn f s μ := by
  simpa using IntegrableOn.finset (s := hs.toFinset)
/-
**MeasureTheory.IntegrableOn.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] [MeasurableSingletonClass α]   {μ : MeasureTheory.Measure α} [Measu
reTheory.IsFiniteMeasure μ] {s : Set α},   s.Subsingleton → ∀ {f : α → E}, Measu
reTheory.IntegrableOn f s μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.of_finite`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] [MeasurableSingletonClass α
]   {μ : MeasureTheory.Mea…
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
lemma IntegrableOn.of_subsingleton [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Subsingleton) {f : α → E} :
    IntegrableOn f s μ :=
  .of_finite hs.finite
/-
**MeasureTheory.IntegrableOn.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {s : 
Set α} {μ ν : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : C
ontinuousENorm ε] [TopologicalSpace.PseudoMetrizableSpace ε],   MeasureTheory.In
tegrableOn f s μ → MeasureTheory.IntegrableOn f s ν → MeasureTheory.IntegrableOn
 f s (μ + ν)
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.IntegrableOn.integrable`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
-/
theorem IntegrableOn.add_measure [PseudoMetrizableSpace ε]
    (hμ : IntegrableOn f s μ) (hν : IntegrableOn f s ν) :
    IntegrableOn f s (μ + ν) := by
  delta IntegrableOn; rw [Measure.restrict_add]; exact hμ.integrable.add_measure hν

@[to_fun]
/-
**MeasureTheory.IntegrableOn.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
ableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] [ContinuousAdd ε'] {f g : α → ε'},   MeasureTheory.IntegrableOn f s 
μ → MeasureTheory.IntegrableOn g s μ → MeasureTheory.IntegrableOn (f + g) s μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
-/
theorem IntegrableOn.add [ContinuousAdd ε'] {f g : α → ε'}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f + g) s μ :=
  Integrable.add hf hg

@[to_fun]
/-
**MeasureTheory.IntegrableOn.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
ableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {s : Set α}   {μ : MeasureTheory.Measure α} {f g : α → E},   Measur
eTheory.IntegrableOn f s μ → MeasureTheory.IntegrableOn g s μ → MeasureTheory.In
tegrableOn (f - g) s μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
theorem IntegrableOn.sub {f g : α → E}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f - g) s μ :=
  Integrable.sub hf hg

@[to_fun]
/-
**MeasureTheory.IntegrableOn.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integr
ableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {s : Set α}   {μ : MeasureTheory.Measure α} {f : α → E}, MeasureThe
ory.IntegrableOn f s μ → MeasureTheory.IntegrableOn (-f) s μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem IntegrableOn.neg {f : α → E} (hf : IntegrableOn f s μ) : IntegrableOn (-f) s μ :=
  Integrable.neg hf

@[simp]
/-
**MeasureTheory.integrableOn_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_neg_iff {f : α -> E} : IntegrableOn (-f) s μ ↔ IntegrableOn f
 s μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
-/
theorem integrableOn_neg_iff {f : α → E} : IntegrableOn (-f) s μ ↔ IntegrableOn f s μ :=
  integrable_neg_iff

@[simp]
/-
**MeasureTheory.integrableOn_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrableOn_fun_neg_iff {f : α -> E} : IntegrableOn (fun x => -f x) s μ ↔
 IntegrableOn f s μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
-/
theorem integrableOn_fun_neg_iff {f : α → E} :
    IntegrableOn (fun x ↦ -f x) s μ ↔ IntegrableOn f s μ :=
  integrable_neg_iff

@[simp]
/-
**MeasureTheory.integrableOn_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrableOn_add_measure [PseudoMetrizableSpace ε] : IntegrableOn f s (μ +
 ν) ↔ IntegrableOn f s μ ∧ IntegrableOn f s ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_measure`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ ν : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用定理 `MeasureTheory.IntegrableOn.add_measure`：∀ {α : Type u_1} {ε : Type u_3} 
{mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ ν : MeasureTheory.Measure α}
   [inst : TopologicalSpace …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrableOn_add_measure [PseudoMetrizableSpace ε] :
    IntegrableOn f s (μ + ν) ↔ IntegrableOn f s μ ∧ IntegrableOn f s ν :=
  ⟨fun h =>
    ⟨h.mono_measure (Measure.le_add_right le_rfl), h.mono_measure (Measure.le_add_left le_rfl)⟩,
    fun h => h.1.add_measure h.2⟩
/-
**MeasureTheory._root_.MeasurableEmbedding.integrableOn_map_iff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrableOn_map_iff [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure α} {s : Set β} :
    IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp_rw [IntegrableOn, he.restrict_map, he.integrable_map_iff]
/-
**MeasureTheory._root_.MeasurableEmbedding.integrableOn_iff_comap** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrableOn_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} {s : Set β} (hs : s ⊆ range e) :
    IntegrableOn f s μ ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) (μ.comap e) := by
  simp_rw [← he.integrableOn_map_iff, he.map_comap, IntegrableOn,
    Measure.restrict_restrict_of_subset hs]
/-
**MeasureTheory._root_.MeasurableEmbedding.integrableOn_range_iff_comap** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrableOn_range_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} :
    IntegrableOn f (range e) μ ↔ Integrable (f ∘ e) (μ.comap e) := by
  rw [he.integrableOn_iff_comap .rfl, preimage_range, integrableOn_univ]
/-
**MeasureTheory.integrableOn_iff_comap_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrableOn_iff_comap_subtypeVal (hs : MeasurableSet s) : IntegrableOn f 
s μ ↔ Integrable (f ∘ (↑) : s -> ε) (μ.comap (↑))
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integrableOn_range_iff_comap`：∀ {α : Type u_1} {β : 
Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} [inst : TopologicalSpace ε]   
[inst_1 : ContinuousENorm ε] [inst_2 :…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_iff_comap_subtypeVal (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ Integrable (f ∘ (↑) : s → ε) (μ.comap (↑)) := by
  rw [← (MeasurableEmbedding.subtype_coe hs).integrableOn_range_iff_comap, Subtype.range_val]
/-
**MeasureTheory.integrableOn_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrableOn_map_equiv [MeasurableSpace β] (e : α ≃ᵐ β) {f : β -> ε} {μ : 
Measure α} {s : Set β} : IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹
' s) μ
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.restrict_map`：∀ {α : Type u_2} {β : Type u_3} {m0 : Meas
urableSpace α} {m1 : MeasurableSpace β} (e : α ≃ᵐ β)   (μ : MeasureTheory.Measur
e α) (s : Set β), …
· 使用定理 `MeasureTheory.integrable_map_equiv`：integrable_map_equiv (f : α ≃ᵐ δ) (g
 : δ -> ε) : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrableOn_map_equiv [MeasurableSpace β] (e : α ≃ᵐ β) {f : β → ε} {μ : Measure α}
    {s : Set β} : IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp only [IntegrableOn, e.restrict_map, integrable_map_equiv e]
/-
**MeasureTheory.MeasurePreserving.integrableOn_comp_preimage** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : MeasurableSpace β] {e : α → β}   {ν : MeasureTheory.Measure β},
   MeasureTheory.MeasurePreserving e μ ν →     MeasurableEmbedding e →       ∀ {
f : β → ε} {s : Set β}, MeasureTheory.IntegrableOn (f ∘ e) (e ⁻¹' s) μ ↔ Measure
Theory.IntegrableOn f s ν
参数：f ∘ e；e ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_preimage_emb`：restrict_preimage
_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) 
(s : Set β) : MeasurePreserving f (μa.restr…
-/
theorem MeasurePreserving.integrableOn_comp_preimage [MeasurableSpace β] {e : α → β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β → ε} {s : Set β} :
    IntegrableOn (f ∘ e) (e ⁻¹' s) μ ↔ IntegrableOn f s ν :=
  (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂
/-
**MeasureTheory.MeasurePreserving.integrableOn_image** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : MeasurableSpace β] {e : α → β}   {ν : MeasureTheory.Measure β},
   MeasureTheory.MeasurePreserving e μ ν →     MeasurableEmbedding e →       ∀ {
f : β → ε} {s : Set α}, MeasureTheory.IntegrableOn f (e '' s) ν ↔ MeasureTheory.
IntegrableOn (f ∘ e) s μ
参数：e '' s；f ∘ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_image_emb`：restrict_image_emb {
f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) (s : S
et α) : MeasurePreserving f (μa.restrict…
-/
theorem MeasurePreserving.integrableOn_image [MeasurableSpace β] {e : α → β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β → ε} {s : Set α} :
    IntegrableOn f (e '' s) ν ↔ IntegrableOn (f ∘ e) s μ :=
  ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

section indicator

-- All results in this section hold for any enormed monoid.
variable {f : α → ε'}

/-
**MeasureTheory.integrable_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_indicator_iff (hs : MeasurableSet s) : Integrable (indicator s 
f) μ ↔ IntegrableOn f s μ
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_indicator_iff (hs : MeasurableSet s) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  simp_rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_enorm,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator hs,
    aestronglyMeasurable_indicator_iff hs]
/-
**MeasureTheory.IntegrableOn.integrable_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f : α → ε'},   MeasureTheory.IntegrableOn f s μ → MeasurableSet s →
 MeasureTheory.Integrable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
-/
theorem IntegrableOn.integrable_indicator (h : IntegrableOn f s μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  (integrable_indicator_iff hs).2 h
/-
**MeasureTheory.IntegrableOn.integrable_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f : α → ε'},   MeasureTheory.IntegrableOn f s μ → MeasurableSet s →
 MeasureTheory.Integrable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
-/
theorem IntegrableOn.integrable_indicator₀ (h : IntegrableOn f s μ) (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ :=
  (h.congr_set_ae hs.toMeasurable_ae_eq).integrable_indicator
    (measurableSet_toMeasurable μ s) |>.congr
    (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)

@[fun_prop]
/-
**MeasureTheory.Integrable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f : α → ε'},   MeasureTheory.Integrable f μ → MeasurableSet s → Mea
sureTheory.Integrable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
-/
theorem Integrable.indicator (h : Integrable f μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  h.integrableOn.integrable_indicator hs

@[fun_prop]
/-
**MeasureTheory.Integrable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f : α → ε'},   MeasureTheory.Integrable f μ → MeasurableSet s → Mea
sureTheory.Integrable (s.indicator f) μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
-/
theorem Integrable.indicator₀ (h : Integrable f μ) (hs : NullMeasurableSet s μ) :
    Integrable (s.indicator f) μ :=
  h.integrableOn.integrable_indicator₀ hs
/-
**MeasureTheory.IntegrableOn.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s t : Set α} {μ
 : MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormed
AddMonoid ε'] {f : α → ε'},   MeasureTheory.IntegrableOn f s μ → MeasurableSet t
 → MeasureTheory.IntegrableOn (t.indicator f) s μ
参数：t.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
-/
theorem IntegrableOn.indicator (h : IntegrableOn f s μ) (ht : MeasurableSet t) :
    IntegrableOn (indicator t f) s μ :=
  Integrable.indicator h ht
/-
**MeasureTheory.integrable_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrable_indicatorConstLp {E} [NormedAddCommGroup E] {p : Real>=0∞} {s :
 Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : Integrable (indicatorC
onstLp p hs hμs c) μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用引理 `MeasureTheory.integrable_const_iff`：integrable_const_iff {c : β} : Integ
rable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ
· 使用引理 `MeasureTheory.isFiniteMeasure_restrict`：isFiniteMeasure_restrict : IsFin
iteMeasure (μ.restrict s) ↔ μ s != ∞
-/
theorem integrable_indicatorConstLp {E} [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Integrable (indicatorConstLp p hs hμs c) μ := by
  rw [integrable_congr indicatorConstLp_coeFn, integrable_indicator_iff hs, IntegrableOn,
    integrable_const_iff, isFiniteMeasure_restrict]
  exact .inr hμs
/-
**MeasureTheory.integrableOn_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrableOn_indicator_iff (hs : MeasurableSet s) : IntegrableOn (indicato
r s f) t μ ↔ IntegrableOn f (s inter t) μ
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrableOn_indicator_iff (hs : MeasurableSet s) :
    IntegrableOn (indicator s f) t μ ↔ IntegrableOn f (s ∩ t) μ := by
  simp_rw [IntegrableOn, integrable_indicator_iff hs, IntegrableOn, Measure.restrict_restrict hs]

end indicator

/-- If a function is integrable on a set `s` and nonzero there, then the measurable hull of `s` is
well behaved: the restriction of the measure to `toMeasurable μ s` coincides with its restriction
to `s`. -/
/-
**MeasureTheory.IntegrableOn.restrict_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ :
 MeasureTheory.Measure α}   [inst : TopologicalSpace ε'] [inst_1 : ESeminormedAd
dMonoid ε'] {f : α → ε'},   MeasureTheory.IntegrableOn f s μ → (∀ x ∈ s, ‖f x‖ₑ 
≠ 0) → μ.restrict (MeasureTheory.toMeasurable μ s) = μ.restrict s
参数：∀ x ∈ s, ‖f x‖ₑ ≠ 0；MeasureTheory.toMeasurable μ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Integrable.measure_enorm_ge_lt_top`：∀ {α : Type u_1} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_8} [inst : Topologi
calSpace E]   [inst_1 : ContinuousENor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable_of_cover`：restrict_toMeasura
ble_of_cover {s : Set α} {v : Nat -> Set α} (hv : s subseteq ⋃ n, v n) (h'v : fo
rall n, μ (s inter v n) != ∞) : μ.restrict…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is integrable on a set `s` and nonzero there, then the measurable 
hull of `s` is
well behaved: the restriction of the measure to `toMeasurable μ s` coincides wit
h its restriction
to `s`.
-/
theorem IntegrableOn.restrict_toMeasurable {f : α → ε'}
    (hf : IntegrableOn f s μ) (h's : ∀ x ∈ s, ‖f x‖ₑ ≠ 0) :
    μ.restrict (toMeasurable μ s) = μ.restrict s := by
  rcases exists_seq_strictAnti_tendsto' ENNReal.zero_lt_top with ⟨u, _, u_pos, u_lim⟩
  let v n := toMeasurable (μ.restrict s) { x | u n ≤ ‖f x‖ₑ }
  have A : ∀ n, μ (s ∩ v n) ≠ ∞ := by
    intro n
    rw [inter_comm, ← Measure.restrict_apply (measurableSet_toMeasurable _ _),
      measure_toMeasurable]
    exact (hf.measure_enorm_ge_lt_top (u_pos n).1 (u_pos n).2.ne).ne
  apply Measure.restrict_toMeasurable_of_cover _ A
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n, u n < ‖f x‖ₑ :=
    ((tendsto_order.1 u_lim).2 _ (pos_of_ne_zero (h's x hx))).exists
  exact mem_iUnion.2 ⟨n, subset_toMeasurable _ _ hn.le⟩

-- TODO: investigate generalising this section to e-seminormed monoids
section ENormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ENormedAddMonoid ε'] [PseudoMetrizableSpace ε']

-- TODO: generalise this to e-seminormed commutative monoids,
-- by merely assuming ‖f x‖ₑ vanishes on t \ s
/-- If a function is integrable on a set `s`, and its enorm vanishes on `t \ s`,
then it is integrable on `t` if `t` is null-measurable. -/
/-
**MeasureTheory.IntegrableOn.of_ae_sdiff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory
.Measure α} {ε' : Type u_7}   [inst : TopologicalSpace ε'] [inst_1 : ENormedAddM
onoid ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'},   MeasureThe
ory.IntegrableOn f s μ →     MeasureTheory.NullMeasurableSet t μ → (∀ᵐ (x : α) ∂
μ, x ∈ t \ s → f x = 0) → MeasureTheory.IntegrableOn f t μ
参数：∀ᵐ (x : α) ∂μ, x ∈ t \ s → f x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.IntegrableOn.restrict_toMeasurable`：∀ {α : Type u_1} {ε' :
 Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrableOn_zero`：integrableOn_zero : IntegrableOn (fun _
 => (0 : ε')) s μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem₀`：ae_restrict_mem₀ (hs : NullMeasurableSet
 s μ) : forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t

--- 原说明 ---
If a function is integrable on a set `s`, and its enorm vanishes on `t \ s`,
then it is integrable on `t` if `t` is null-measurable.
-/
theorem IntegrableOn.of_ae_sdiff_eq_zero {f : α → ε'}
    (hf : IntegrableOn f s μ) (ht : NullMeasurableSet t μ)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) : IntegrableOn f t μ := by
  let u := { x ∈ s | f x ≠ 0 }
  have hu : IntegrableOn f u μ := hf.mono_set fun x hx => hx.1
  let v := toMeasurable μ u
  have A : IntegrableOn f v μ := by
    rw [IntegrableOn, hu.restrict_toMeasurable]
    · exact hu
    · intro x hx; simpa using hx.2
  have B : IntegrableOn f (t \ v) μ := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_of_ae h't,
      ae_restrict_mem₀ (ht.diff (measurableSet_toMeasurable μ u).nullMeasurableSet)] with x hxt hx
    by_cases h'x : x ∈ s
    · by_contra H
      exact hx.2 (subset_toMeasurable μ u ⟨h'x, Ne.symm H⟩)
    · exact (hxt ⟨hx.1, h'x⟩).symm
  apply (A.union B).mono_set _
  rw [union_sdiff_self]
  exact subset_union_right

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_ae_diff_eq_zero := IntegrableOn.of_ae_sdiff_eq_zero

/-- If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is integrable on `t`
if `t` is measurable. -/
/-
**MeasureTheory.IntegrableOn.of_forall_sdiff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory
.Measure α} {ε' : Type u_7}   [inst : TopologicalSpace ε'] [inst_1 : ENormedAddM
onoid ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'},   MeasureThe
ory.IntegrableOn f s μ → MeasurableSet t → (∀ x ∈ t \ s, f x = 0) → MeasureTheor
y.IntegrableOn f t μ
参数：∀ x ∈ t \ s, f x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.of_ae_sdiff_eq_zero`：∀ {α : Type u_1} {mα : M
easurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α} {ε' : Type u_7}   
[inst : TopologicalSpace ε'] [inst_1…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is in
tegrable on `t`
if `t` is measurable.
-/
theorem IntegrableOn.of_forall_sdiff_eq_zero {f : α → ε'}
    (hf : IntegrableOn f s μ) (ht : MeasurableSet t)
    (h't : ∀ x ∈ t \ s, f x = 0) : IntegrableOn f t μ :=
  hf.of_ae_sdiff_eq_zero ht.nullMeasurableSet (Eventually.of_forall h't)

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_forall_diff_eq_zero := IntegrableOn.of_forall_sdiff_eq_zero

/-- If a function is integrable on a set `s` and vanishes almost everywhere on its complement,
then it is integrable. -/
/-
**MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.M
easure α} {ε' : Type u_7}   [inst : TopologicalSpace ε'] [inst_1 : ENormedAddMon
oid ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'},   MeasureTheor
y.IntegrableOn f s μ → (∀ᵐ (x : α) ∂μ, x ∉ s → f x = 0) → MeasureTheory.Integrab
le f μ
参数：∀ᵐ (x : α) ∂μ, x ∉ s → f x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.IntegrableOn.of_ae_sdiff_eq_zero`：∀ {α : Type u_1} {mα : M
easurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α} {ε' : Type u_7}   
[inst : TopologicalSpace ε'] [inst_1…
· 使用定理 `MeasureTheory.nullMeasurableSet_univ`：nullMeasurableSet_univ : NullMeasu
rableSet univ μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function is integrable on a set `s` and vanishes almost everywhere on its c
omplement,
then it is integrable.
-/
theorem IntegrableOn.integrable_of_ae_notMem_eq_zero
    {f : α → ε'} (hf : IntegrableOn f s μ) (h't : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable f μ := by
  rw [← integrableOn_univ]
  apply hf.of_ae_sdiff_eq_zero nullMeasurableSet_univ
  filter_upwards [h't] with x hx h'x using hx h'x.2

/-- If a function is integrable on a set `s` and vanishes everywhere on its complement,
then it is integrable. -/
/-
**MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.M
easure α} {ε' : Type u_7}   [inst : TopologicalSpace ε'] [inst_1 : ENormedAddMon
oid ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'},   MeasureTheor
y.IntegrableOn f s μ → (∀ x ∉ s, f x = 0) → MeasureTheory.Integrable f μ
参数：∀ x ∉ s, f x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero`：∀ {α : Type 
u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α} {ε' : Ty
pe u_7}   [inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If a function is integrable on a set `s` and vanishes everywhere on its compleme
nt,
then it is integrable.
-/
theorem IntegrableOn.integrable_of_forall_notMem_eq_zero
    {f : α → ε'} (hf : IntegrableOn f s μ) (h't : ∀ x, x ∉ s → f x = 0) : Integrable f μ :=
  hf.integrable_of_ae_notMem_eq_zero (Eventually.of_forall fun x hx => h't x hx)
/-
**MeasureTheory.IntegrableOn.of_inter_support** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.M
easure α} {ε' : Type u_7}   [inst : TopologicalSpace ε'] [inst_1 : ENormedAddMon
oid ε'] [TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'},   MeasurableSe
t s → MeasureTheory.IntegrableOn f (s ∩ Function.support f) μ → MeasureTheory.In
tegrableOn f s μ
参数：s ∩ Function.support f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.IntegrableOn.of_forall_sdiff_eq_zero`：∀ {α : Type u_1} {mα
 : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α} {ε' : Type u_7
}   [inst : TopologicalSpace ε'] [inst_1…
-/
theorem IntegrableOn.of_inter_support {f : α → ε'}
    (hs : MeasurableSet s) (hf : IntegrableOn f (s ∩ support f) μ) :
    IntegrableOn f s μ := by
  simpa using hf.of_forall_sdiff_eq_zero hs
/-
**MeasureTheory.integrableOn_iff_integrable_of_support_subset** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support
 f subseteq s) : IntegrableOn f s μ ↔ Integrable f μ
参数：h1s : support f subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero`：∀ {α : T
ype u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α} {ε' 
: Type u_7}   [inst : TopologicalSpace ε'] [inst_1 :…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
-/
theorem integrableOn_iff_integrable_of_support_subset
    {f : α → ε'} (h1s : support f ⊆ s) : IntegrableOn f s μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.integrableOn⟩
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  contrapose! hx
  exact h1s (mem_support.2 hx)

end ENormedAddMonoid

/-
**MeasureTheory.integrableOn_Lp_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrableOn_Lp_of_measure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞
} {s : Set α} (f : Lp E p μ) (hp : 1 <= p) (hμs : μ s != ∞) : IntegrableOn f s μ
参数：f : Lp E p μ；hp : 1 <= p；hμs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem integrableOn_Lp_of_measure_ne_top {E} [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (f : Lp E p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) : IntegrableOn f s μ := by
  refine memLp_one_iff_integrable.mp ?_
  have hμ_restrict_univ : (μ.restrict s) Set.univ < ∞ := by
    simpa only [Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply, lt_top_iff_ne_top]
  have hμ_finite : IsFiniteMeasure (μ.restrict s) := ⟨hμ_restrict_univ⟩
  exact ((Lp.memLp _).restrict s).mono_exponent hp
/-
**MeasureTheory.Integrable.lintegral_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : α → ℝ},   MeasureTheory.Integrable f μ → ∫⁻ (x : α), ENNReal.ofReal (f x) ∂μ 
< ⊤
参数：x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_ofReal_le_lintegral_enorm`：lintegral_ofReal_le_l
integral_enorm (f : α -> Real) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ <= ∫⁻ x, ‖f x‖ₑ ∂
μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Integrable.lintegral_lt_top {f : α → ℝ} (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ∫⁻ x, ↑‖f x‖₊ ∂μ := lintegral_ofReal_le_lintegral_enorm f
    _ < ∞ := hf.2
/-
**MeasureTheory.IntegrableOn.setLIntegral_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IntegrableOn`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : α → ℝ} {s : Set α},   MeasureTheory.IntegrableOn f s μ → ∫⁻ (x : α) in s, ENN
Real.ofReal (f x) ∂μ < ⊤
参数：x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.lintegral_lt_top`：∀ {α : Type u_1} {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrab
le f μ → ∫⁻ (x : α), ENNReal.of…
-/
theorem IntegrableOn.setLIntegral_lt_top {f : α → ℝ} {s : Set α} (hf : IntegrableOn f s μ) :
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  Integrable.lintegral_lt_top hf
/-
**MeasureTheory._root_.ContinuousLinearMap.integrableOn_comp** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.integrableOn_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ] {f : α → H} (L : H →SL[σ] E) (hf : IntegrableOn f s μ) :
    IntegrableOn (L ∘ f) s μ :=
  L.integrable_comp hf

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.smallSets`. -/
/-
**MeasureTheory.IntegrableAtFilter** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IntegrableAtFilter (f : α -> ε) (l : Filter α) (μ : Measure α
参数：f : α -> ε；l : Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a function `f` is *integrable at filter* `l` if it is integrable on 
some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.smallSets`.
-/
def IntegrableAtFilter (f : α → ε) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, IntegrableOn f s μ

variable {l l' : Filter α}
/-
**MeasureTheory._root_.MeasurableEmbedding.integrableAtFilter_map_iff** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrableAtFilter_map_iff [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} :
    IntegrableAtFilter f (l.map e) (μ.map e) ↔ IntegrableAtFilter (f ∘ e) l μ := by
  simp_rw [IntegrableAtFilter, he.integrableOn_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩
/-
**MeasureTheory._root_.MeasurableEmbedding.integrableAtFilter_iff_comap** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrableAtFilter_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} :
    IntegrableAtFilter f (l.map e) μ ↔ IntegrableAtFilter (f ∘ e) l (μ.comap e) := by
  simp_rw [← he.integrableAtFilter_map_iff, IntegrableAtFilter, he.map_comap]
  constructor <;> rintro ⟨s, hs, int⟩
  · exact ⟨s, hs, int.mono_measure <| μ.restrict_le_self⟩
  · exact ⟨_, inter_mem hs range_mem_map, int.inter_of_restrict⟩
/-
**MeasureTheory.Integrable.integrableAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Integrable`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε],   MeasureTheory.Integrable f μ → ∀ (l : Filter α), MeasureTheory.Integrable
AtFilter f l μ
参数：l : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
-/
theorem Integrable.integrableAtFilter (h : Integrable f μ) (l : Filter α) :
    IntegrableAtFilter f l μ :=
  ⟨univ, Filter.univ_mem, integrableOn_univ.2 h⟩
/-
**MeasureTheory.IntegrableAtFilter.eventually** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → ∀ᶠ (s : Set α) in
 l.smallSets, MeasureTheory.IntegrableOn f s μ
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
-/
protected theorem IntegrableAtFilter.eventually (h : IntegrableAtFilter f l μ) :
    ∀ᶠ s in l.smallSets, IntegrableOn f s μ :=
  Iff.mpr (eventually_smallSets' fun _s _t hst ht => ht.mono_set hst) h
/-
**MeasureTheory.integrableAtFilter_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrableAtFilter_atBot_iff [Preorder α] [IsCodirectedOrder α] [Nonempty 
α] : IntegrableAtFilter f atBot μ ↔ exists a, IntegrableOn f (Iic a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
-/
theorem integrableAtFilter_atBot_iff [Preorder α] [IsCodirectedOrder α] [Nonempty α] :
    IntegrableAtFilter f atBot μ ↔ ∃ a, IntegrableOn f (Iic a) μ := by
  refine ⟨fun ⟨s, hs, hi⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨Iic a, Iic_mem_atBot a, ha⟩⟩
  obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
  exact ⟨t, hi.mono_set fun _ hx ↦ ht _ hx⟩
/-
**MeasureTheory.integrableAtFilter_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrableAtFilter_atTop_iff [Preorder α] [IsDirectedOrder α] [Nonempty α]
 : IntegrableAtFilter f atTop μ ↔ exists a, IntegrableOn f (Ici a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableAtFilter_atBot_iff`：integrableAtFilter_atBot_iff
 [Preorder α] [IsCodirectedOrder α] [Nonempty α] : IntegrableAtFilter f atBot μ 
↔ exists a, IntegrableOn f (Iic …
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
theorem integrableAtFilter_atTop_iff [Preorder α] [IsDirectedOrder α] [Nonempty α] :
    IntegrableAtFilter f atTop μ ↔ ∃ a, IntegrableOn f (Ici a) μ :=
  integrableAtFilter_atBot_iff (α := αᵒᵈ)

@[gcongr]
/-
**MeasureTheory.IntegrableAtFilter.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ ν 
: MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {l : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → ν ≤ μ → Measure
Theory.IntegrableAtFilter f l ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.mono_measure`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ ν : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
-/
lemma IntegrableAtFilter.mono_measure (hf : IntegrableAtFilter f l μ) (h : ν ≤ μ) :
    IntegrableAtFilter f l ν :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.mono_measure h⟩

@[gcongr]
/-
**MeasureTheory.IntegrableAtFilter.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f g : α → ε} {μ 
: MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {l : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → f =ᵐ[μ] g → Mea
sureTheory.IntegrableAtFilter g l μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `Filter.EventuallyEq.restrict`：∀ {α : Type u_2} {δ : Type u_4} {m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {f g : α → δ} {s : Set α},   f =ᵐ[μ
] g → f =ᵐ[μ.restr…
-/
lemma IntegrableAtFilter.congr (hf : IntegrableAtFilter f l μ) (h : f =ᵐ[μ] g) :
    IntegrableAtFilter g l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr h.restrict⟩
/-
**MeasureTheory.integrableAtFilter_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrableAtFilter_congr (h : f =ᵐ[μ] g) : IntegrableAtFilter f l μ ↔ Inte
grableAtFilter g l μ
参数：h : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableAtFilter.congr`：∀ {α : Type u_1} {ε : Type u_3} 
{mα : MeasurableSpace α} {f g : α → ε} {μ : MeasureTheory.Measure α}   [inst : T
opologicalSpace ε] [inst_1 :…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma integrableAtFilter_congr (h : f =ᵐ[μ] g) :
    IntegrableAtFilter f l μ ↔ IntegrableAtFilter g l μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩
/-
**MeasureTheory.IntegrableAtFilter.congr'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l : Filter α} {ε'' : Type u_7}   [inst_2 : TopologicalSpace ε''] [inst_3 : 
ContinuousENorm ε''] {g : α → ε''},   MeasureTheory.IntegrableAtFilter f l μ →  
   MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) → M
easureTheory.IntegrableAtFilter g l μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr'_enorm`：∀ {α : Type u_1} {ε : Type u_5} {
ε' : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : T
opologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用引理 `MeasureTheory.ae_restrict_le`：ae_restrict_le : ae (μ.restrict s) <= ae μ
-/
lemma IntegrableAtFilter.congr'_enorm {ε'' : Type*} [TopologicalSpace ε''] [ContinuousENorm ε'']
    {g : α → ε''} (hf : IntegrableAtFilter f l μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    IntegrableAtFilter g l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr'_enorm hg.restrict (ae_restrict_le h)⟩

@[simp]
/-
**MeasureTheory.integrableAtFilter_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrableAtFilter_zero : IntegrableAtFilter (0 : α -> E) l μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
lemma integrableAtFilter_zero : IntegrableAtFilter (0 : α → E) l μ :=
  ⟨univ, by simp, integrableOn_univ.mpr (integrable_zero ..)⟩
/-
**MeasureTheory.IntegrableAtFilter.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] 
{l : Filter α} [ContinuousAdd ε'] {f g : α → ε'},   MeasureTheory.IntegrableAtFi
lter f l μ →     MeasureTheory.IntegrableAtFilter g l μ → MeasureTheory.Integrab
leAtFilter (f + g) l μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `MeasureTheory.IntegrableOn.add`：∀ {α : Type u_1} {ε' : Type u_4} {mα : M
easurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topologica
lSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
protected theorem IntegrableAtFilter.add [ContinuousAdd ε'] {f g : α → ε'}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f + g) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  rcases hg with ⟨t, tl, ht⟩
  refine ⟨s ∩ t, inter_mem sl tl, ?_⟩
  exact (hs.mono_set inter_subset_left).add (ht.mono_set inter_subset_right)
/-
**MeasureTheory.IntegrableAtFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {f : α → E}, Measure
Theory.IntegrableAtFilter f l μ → MeasureTheory.IntegrableAtFilter (-f) l μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …
-/
protected theorem IntegrableAtFilter.neg {f : α → E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (-f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.neg⟩

@[simp]
/-
**MeasureTheory.integrableAtFilter_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {f : α → E}, Measure
Theory.IntegrableAtFilter (-f) l μ ↔ MeasureTheory.IntegrableAtFilter f l μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IntegrableAtFilter.neg`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f : α…
-/
protected theorem integrableAtFilter_neg_iff {f : α → E} :
    IntegrableAtFilter (-f) l μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.neg⟩
  convert! h.neg; simp
/-
**MeasureTheory.IntegrableAtFilter.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {f g : α → E},   Mea
sureTheory.IntegrableAtFilter f l μ →     MeasureTheory.IntegrableAtFilter g l μ
 → MeasureTheory.IntegrableAtFilter (f - g) l μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.IntegrableAtFilter.add`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε
']   [inst_1 : ESeminormed…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.IntegrableAtFilter.neg`：∀ {α : Type u_1} {E : Type u_5} {m
α : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure 
α}   {l : Filter α} {f : α…
-/
protected theorem IntegrableAtFilter.sub {f g : α → E}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f - g) l μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
/-
**MeasureTheory.IntegrableAtFilter.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {𝕜 : Type u_7} [inst
_1 : NormedAddCommGroup 𝕜] [inst_2 : SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]   {f
 : α → E}, MeasureTheory.IntegrableAtFilter f l μ → ∀ (c : 𝕜), MeasureTheory.Int
egrableAtFilter (c • f) l μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
protected theorem IntegrableAtFilter.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α → E} (hf : IntegrableAtFilter f l μ) (c : 𝕜) :
    IntegrableAtFilter (c • f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.smul c⟩

-- See `integrableAtFilter_smul_iff` below for the fully general version.
/-
**MeasureTheory.integrableAtFilter_smul_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem integrableAtFilter_smul_iff' {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    IntegrableAtFilter (c • f) l μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨fun hf ↦ ?_, fun h ↦ h.smul c⟩
  convert! hf.smul c⁻¹
  simp [← smul_assoc, inv_mul_cancel₀ hc]
/-
**MeasureTheory.integrableAtFilter_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrableAtFilter_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] 
{f : α -> E} (c : 𝕜) : IntegrableAtFilter (c • f) l μ ↔ c = 0 ∨ IntegrableAtFilt
er f l μ
参数：c : 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntegrableOn.0.MeasureTheory.int
egrableAtFilter_smul_iff'`：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace
 α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α}
 {𝕜 : T…
-/
theorem integrableAtFilter_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : α → E} (c : 𝕜) :
    IntegrableAtFilter (c • f) l μ ↔ c = 0 ∨ IntegrableAtFilter f l μ := by
  by_cases hc : c = 0
  · simp [hc]
  · simpa [hc] using MeasureTheory.integrableAtFilter_smul_iff' hc
/-
**MeasureTheory.IntegrableAtFilter.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → MeasureTheory.Int
egrableAtFilter (fun x => ‖f x‖ₑ) l μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Integrable.enorm`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IntegrableAtFilter.enorm (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖ₑ) l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.enorm⟩
/-
**MeasureTheory.IntegrableAtFilter.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {f : α → E},   Measu
reTheory.IntegrableAtFilter f l μ → MeasureTheory.IntegrableAtFilter (fun x => ‖
f x‖) l μ
参数：fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IntegrableAtFilter.norm {f : α → E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖) l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.norm⟩
/-
**MeasureTheory.IntegrableAtFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l l' : Filter α},   l ≤ l' → MeasureTheory.IntegrableAtFilter f l' μ → Meas
ureTheory.IntegrableAtFilter f l μ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IntegrableAtFilter.filter_mono (hl : l ≤ l') (hl' : IntegrableAtFilter f l' μ) :
    IntegrableAtFilter f l μ :=
  let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩
/-
**MeasureTheory.IntegrableAtFilter.inf_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l l' : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → MeasureTheory.
IntegrableAtFilter f (l ⊓ l') μ
参数：l ⊓ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IntegrableAtFilter.inf_of_left (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l ⊓ l') μ :=
  hl.filter_mono inf_le_left
/-
**MeasureTheory.IntegrableAtFilter.inf_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l l' : Filter α},   MeasureTheory.IntegrableAtFilter f l μ → MeasureTheory.
IntegrableAtFilter f (l' ⊓ l) μ
参数：l' ⊓ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem IntegrableAtFilter.inf_of_right (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l' ⊓ l) μ :=
  hl.filter_mono inf_le_right

@[simp]
/-
**MeasureTheory.IntegrableAtFilter.inf_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : 
MeasureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm
 ε] {l : Filter α},   MeasureTheory.IntegrableAtFilter f (l ⊓ MeasureTheory.ae μ
) μ ↔ MeasureTheory.IntegrableAtFilter f l μ
参数：l ⊓ MeasureTheory.ae μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.congr_set_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IntegrableAtFilter.inf_ae_iff {l : Filter α} :
    IntegrableAtFilter f (l ⊓ ae μ) μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨?_, fun h ↦ h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
  refine ⟨t, ht, hf.congr_set_ae <| eventuallyEq_set.2 ?_⟩
  filter_upwards [hu] with x hx using (and_iff_left hx).symm

alias ⟨IntegrableAtFilter.of_inf_ae, _⟩ := IntegrableAtFilter.inf_ae_iff

variable {ε' : Type*} [TopologicalSpace ε'] [ENormedAddMonoid ε'] in
@[simp]
/-
**MeasureTheory.integrableAtFilter_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrableAtFilter_top [PseudoMetrizableSpace ε'] {f : α -> ε'} : Integrab
leAtFilter f ⊤ μ ↔ Integrable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.Integrable.integrableAtFilter`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
-/
theorem integrableAtFilter_top [PseudoMetrizableSpace ε'] {f : α → ε'} :
    IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ ↦ hsf _).mp hs
/-
**MeasureTheory.IntegrableAtFilter.sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {mα : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] 
[TopologicalSpace.PseudoMetrizableSpace ε'] {f : α → ε'} {l l' : Filter α},   Me
asureTheory.IntegrableAtFilter f (l ⊔ l') μ ↔     MeasureTheory.IntegrableAtFilt
er f l μ ∧ MeasureTheory.IntegrableAtFilter f l' μ
参数：l ⊔ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IntegrableAtFilter.filter_mono`：∀ {α : Type u_1} {ε : Type
 u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst
 : TopologicalSpace ε] [inst_1 : C…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `MeasureTheory.IntegrableOn.union`：∀ {α : Type u_1} {ε : Type u_3} {mα : 
MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   [in
st : TopologicalSpace …
-/
theorem IntegrableAtFilter.sup_iff [PseudoMetrizableSpace ε'] {f : α → ε'} {l l' : Filter α} :
    IntegrableAtFilter f (l ⊔ l') μ ↔ IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  constructor
  · exact fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  · exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ ↦ ⟨s ∪ t, union_mem_sup hsl htl, hs.union ht⟩
/-
**MeasureTheory._root_.ContinuousLinearMap.integrableAtFilter_comp** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.integrableAtFilter_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ] {f : α → H} (L : H →SL[σ] E)
    (hf : IntegrableAtFilter f l μ) : IntegrableAtFilter (L ∘ f) l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, L.integrableOn_comp hf⟩

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
/-
**MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {f : α → E} {l : Filter α} [l.IsMea
surablyGenerated],   StronglyMeasurableAtFilter f l μ →     μ.FiniteAtFilter l →
       Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l (norm ∘ f) → MeasureTheory
.IntegrableAtFilter f l μ
参数：fun x1 x2 => x1 ≤ x2；norm ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets`：eventually_smallSets {p : Set α -> Prop} : 
(forallᶠ s in l.smallSets, p s) ↔ exists s in l, forall t, t subseteq s -> p t
· 使用定理 `Filter.Eventually.exists_measurable_mem_of_smallSets`：∀ {α : Type u_1} [
inst : MeasurableSpace α] {f : Filter α} [f.IsMeasurablyGenerated] {p : Set α → 
Prop},   (∀ᶠ (s : Set α) in f.smallSets, p…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `StronglyMeasurableAtFilter.eventually`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} [inst : TopologicalSpace β] {l : Filter α} {f : α → β}  
 {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.eventually`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : Filter α},   μ.FiniteAtFil
ter f → ∀ᶠ (s : Set α) in f.smallSets…
· 使用定理 `MeasureTheory.HasFiniteIntegral.restrict_of_bounded`：∀ {α : Type u_1} {E
 : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {f : α → E} 
{s : Set α}   {μ : MeasureTheory.Measure …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `μ` is a measure finite at filter `l` and `f` is a function such that its nor
m is bounded
above at `l`, then `f` is integrable at `l`.
-/
theorem Measure.FiniteAtFilter.integrableAtFilter {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l)
    (hf : l.IsBoundedUnder (· ≤ ·) (norm ∘ f)) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ s in l.smallSets, ∀ x ∈ s, ‖f x‖ ≤ C :=
    hf.imp fun C hC => eventually_smallSets.2 ⟨_, hC, fun t => id⟩
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_smallSets with
    ⟨s, hsl, hsm, hfm, hμ, hC⟩
  refine ⟨s, hsl, ⟨hfm, .restrict_of_bounded hμ (C := C) ?_⟩⟩
  rw [ae_restrict_eq hsm, eventually_inf_principal]
  exact Eventually.of_forall hC
/-
**MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {f : α → E} {l : Filter α} [l.IsMea
surablyGenerated],   StronglyMeasurableAtFilter f l μ →     μ.FiniteAtFilter l →
       ∀ {b : E}, Filter.Tendsto f (l ⊓ MeasureTheory.ae μ) (nhds b) → MeasureTh
eory.IntegrableAtFilter f l μ
参数：l ⊓ MeasureTheory.ae μ；nhds b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableAtFilter.of_inf_ae`：∀ {α : Type u_1} {ε : Type u
_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst :
 TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter`：∀ {α : Type u_1
} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : Mea
sureTheory.Measure α}   {f : α → E} {l : Filt…
· 使用定理 `StronglyMeasurableAtFilter.filter_mono`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} [inst : TopologicalSpace β] {l l' : Filter α} {f : α → 
β}   {μ : MeasureTheory.Meas…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.inf_of_left`：inf_of_left (h : μ.Fin
iteAtFilter f) : μ.FiniteAtFilter (f ⊓ g)
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f (l ⊓ ae μ) (𝓝 b)) : IntegrableAtFilter f l μ :=
  (hμ.inf_of_left.integrableAtFilter (hfm.filter_mono inf_le_left)
      hf.norm.isBoundedUnder_le).of_inf_ae

alias _root_.Filter.Tendsto.integrableAtFilter_ae :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae
/-
**MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter_of_tendsto** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure.FiniteAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {f : α → E} {l : Filter α} [l.IsMea
surablyGenerated],   StronglyMeasurableAtFilter f l μ →     μ.FiniteAtFilter l →
 ∀ {b : E}, Filter.Tendsto f l (nhds b) → MeasureTheory.IntegrableAtFilter f l μ
参数：nhds b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter`：∀ {α : Type u_1
} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : Mea
sureTheory.Measure α}   {f : α → E} {l : Filt…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f l (𝓝 b)) : IntegrableAtFilter f l μ :=
  hμ.integrableAtFilter hfm hf.norm.isBoundedUnder_le

alias _root_.Filter.Tendsto.integrableAtFilter :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto
/-
**MeasureTheory.Measure.integrableOn_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {s : Set α}   {μ : MeasureTheory.Measure α} {f : α → E},   μ s ≠ ⊤ 
→     MeasureTheory.AEStronglyMeasurable f μ →       ∀ {M : ℝ}, (∀ᵐ (a : α) ∂μ.r
estrict s, ‖f a‖ ≤ M) → MeasureTheory.IntegrableOn f s μ
参数：∀ᵐ (a : α) ∂μ.restrict s, ‖f a‖ ≤ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.HasFiniteIntegral.restrict_of_bounded`：∀ {α : Type u_1} {E
 : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {f : α → E} 
{s : Set α}   {μ : MeasureTheory.Measure …
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma Measure.integrableOn_of_bounded {f : α → E} (s_finite : μ s ≠ ∞)
    (f_mble : AEStronglyMeasurable f μ) {M : ℝ} (f_bdd : ∀ᵐ a ∂(μ.restrict s), ‖f a‖ ≤ M) :
    IntegrableOn f s μ :=
  ⟨f_mble.restrict, .restrict_of_bounded (C := M) s_finite.lt_top f_bdd⟩
/-
**MeasureTheory.integrable_add_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_add_of_disjoint {f g : α -> E} (h : Disjoint (support f) (suppo
rt g)) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : Integrable (f +
 g) μ ↔ Integrable f μ ∧ Integrable g μ
参数：h : Disjoint (support f) (support g)；hf : StronglyMeasurable f；hg : StronglyM
easurable g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_add_eq_left`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZe
roClass M] {f g : α → M},   Disjoint (Function.support f) (Function.support g) →
 (Function.supp…
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurableSet_support`：∀ {α : Type u_1}
 {β : Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : Zero β] [inst_1 : To
pologicalSpace β]   [TopologicalSpace.Metriz…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.indicator_add_eq_right`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZ
eroClass M] {f g : α → M},   Disjoint (Function.support f) (Function.support g) 
→ (Function.supp…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integrable_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator hf.measurableSet_support
  · rw [← indicator_add_eq_right h]; exact hfg.indicator hg.measurableSet_support

/-- If a function converges along a filter to a limit `a`, is integrable along this filter, and
all elements of the filter have infinite measure, then the limit has to vanish. -/
/-
**MeasureTheory.IntegrableAtFilter.eq_zero_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IntegrableAtFilter`。
形式化陈述：∀ {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {μ : MeasureTheory.Measure α}   {l : Filter α} {f : α → E},   Measu
reTheory.IntegrableAtFilter f l μ → (∀ s ∈ l, μ s = ⊤) → ∀ {a : E}, Filter.Tends
to f l (nhds a) → a = 0
参数：∀ s ∈ l, μ s = ⊤；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Integrable.measure_gt_lt_top`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {f : α → β} [inst_1 : …
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s

--- 原说明 ---
If a function converges along a filter to a limit `a`, is integrable along this 
filter, and
all elements of the filter have infinite measure, then the limit has to vanish.
-/
lemma IntegrableAtFilter.eq_zero_of_tendsto {f : α → E}
    (h : IntegrableAtFilter f l μ) (h' : ∀ s ∈ l, μ s = ∞) {a : E}
    (hf : Tendsto f l (𝓝 a)) : a = 0 := by
  by_contra H
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), 0 < ε ∧ ε < ‖a‖ := exists_between (norm_pos_iff.mpr H)
  rcases h with ⟨u, ul, hu⟩
  let v := u ∩ {b | ε < ‖f b‖}
  have hv : IntegrableOn f v μ := hu.mono_set inter_subset_left
  have vl : v ∈ l := inter_mem ul ((tendsto_order.1 hf.norm).1 _ hε)
  have : μ.restrict v v < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right)
    (Integrable.measure_gt_lt_top hv.norm εpos)
  have : μ v ≠ ∞ := ne_of_lt (by simpa only [Measure.restrict_apply_self])
  exact this (h' v vl)

end NormedAddCommGroup

end MeasureTheory

open MeasureTheory

variable [NormedAddCommGroup E]

/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
/-
**ContinuousOn.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.aemeasurable [TopologicalSpace α] [OpensMeasurableSpace α] [M
easurableSpace β] [TopologicalSpace β] [BorelSpace β] {f : α -> β} {s : Set α} {
μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) : AEMeasurable f (
μ.restrict s)
参数：hf : ContinuousOn f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `piecewise_ae_eq_restrict`：piecewise_ae_eq_restrict [DecidablePred (· in 
s)] (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict s] f
· 使用定理 `measurable_of_isOpen`：measurable_of_isOpen {f : δ -> γ} (hf : forall s, 
IsOpen s -> MeasurableSet (f ⁻¹' s)) : Measurable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_preimage`：piecewise_preimage (f g : α -> β) (t) : s.piecew
ise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
A function which is continuous on a set `s` is almost everywhere measurable with
 respect to
`μ.restrict s`.
-/
theorem ContinuousOn.aemeasurable [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : AEMeasurable f (μ.restrict s) := by
  classical
  nontriviality α; inhabit α
  have : (Set.piecewise s f fun _ => f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs
  refine ⟨Set.piecewise s f fun _ => f default, ?_, this.symm⟩
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    _root_.continuousOn_iff'.1 hf t ht
  rw [piecewise_preimage, Set.ite, hu]
  exact (u_open.measurableSet.inter hs).union ((measurable_const ht.measurableSet).diff hs)
/-
**ContinuousOn.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.aemeasurable [TopologicalSpace α] [OpensMeasurableSpace α] [M
easurableSpace β] [TopologicalSpace β] [BorelSpace β] {f : α -> β} {s : Set α} {
μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) : AEMeasurable f (
μ.restrict s)
参数：hf : ContinuousOn f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `piecewise_ae_eq_restrict`：piecewise_ae_eq_restrict [DecidablePred (· in 
s)] (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict s] f
· 使用定理 `measurable_of_isOpen`：measurable_of_isOpen {f : δ -> γ} (hf : forall s, 
IsOpen s -> MeasurableSet (f ⁻¹' s)) : Measurable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_preimage`：piecewise_preimage (f g : α -> β) (t) : s.piecew
ise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ContinuousOn.aemeasurable₀ [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : NullMeasurableSet s μ) : AEMeasurable f (μ.restrict s) := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  rw [← Measure.restrict_congr_set t_eq_s]
  exact ContinuousOn.aemeasurable (hf.mono ts) ht

/-- A function which is continuous on a separable set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
/-
**ContinuousOn.aestronglyMeasurable_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.aestronglyMeasurable_of_isSeparable [TopologicalSpace α] [Pse
udoMetrizableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetri
zableSpace β] {f : α -> β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (
hs : MeasurableSet s) (h's : TopologicalSpace.IsSeparable s) : AEStronglyMeasura
ble f (μ.restrict s)
参数：hf : ContinuousOn f s；hs : MeasurableSet s；h's : TopologicalSpace.IsSeparable
 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `ContinuousOn.aemeasurable`：ContinuousOn.aemeasurable [TopologicalSpace α
] [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpace 
β] {f : α -> β}…
· 使用定理 `ContinuousOn.isSeparable_image`：ContinuousOn.isSeparable_image {α : Type
*} [TopologicalSpace α] [PseudoMetrizableSpace α] [TopologicalSpace β] {f : α ->
 β} {s : Set α} (hf …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
A function which is continuous on a separable set `s` is almost everywhere stron
gly measurable
with respect to `μ.restrict s`.
-/
theorem ContinuousOn.aestronglyMeasurable_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] {f : α → β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s)
    (hs : MeasurableSet s) (h's : TopologicalSpace.IsSeparable s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  let := pseudoMetrizableSpacePseudoMetric α
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable hs, f '' s, hf.isSeparable_image h's, ?_⟩
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)

/-- A function which is continuous on a set `s` is almost everywhere strongly measurable with
respect to `μ.restrict s` when either the source space or the target space is second-countable. -/
/-
**ContinuousOn.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.aestronglyMeasurable [TopologicalSpace α] [TopologicalSpace β
] [h : SecondCountableTopologyEither α β] [OpensMeasurableSpace α] [PseudoMetriz
ableSpace β] {f : α -> β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (h
s : MeasurableSet s) : AEStronglyMeasurable f (μ.restrict s)
参数：hf : ContinuousOn f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `ContinuousOn.aemeasurable`：ContinuousOn.aemeasurable [TopologicalSpace α
] [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpace 
β] {f : α -> β}…
· 使用定理 `SecondCountableTopologyEither.out`：∀ {α : Type u_6} {β : Type u_7} {inst
 : TopologicalSpace α} {inst_1 : TopologicalSpace β}   [self : SecondCountableTo
pologyEither α β], Seco…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `TopologicalSpace.isSeparable_range`：isSeparable_range [TopologicalSpace 
β] [SeparableSpace α] {f : α -> β} (hf : Continuous f) : IsSeparable (range f)
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `TopologicalSpace.IsSeparable.of_separableSpace`：∀ {α : Type u} [t : Topo
logicalSpace α] [h : TopologicalSpace.SeparableSpace α] (s : Set α),   Topologic
alSpace.IsSeparable s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
A function which is continuous on a set `s` is almost everywhere strongly measur
able with
respect to `μ.restrict s` when either the source space or the target space is se
cond-countable.
-/
theorem ContinuousOn.aestronglyMeasurable [TopologicalSpace α] [TopologicalSpace β]
    [h : SecondCountableTopologyEither α β] [OpensMeasurableSpace α] [PseudoMetrizableSpace β]
    {f : α → β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨hf.aemeasurable hs, f '' s, ?_,
        mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩
  cases h.out
  · rw [image_eq_range]
    exact isSeparable_range <| continuousOn_iff_continuous_domRestrict.1 hf
  · exact .of_separableSpace _

/-- A function which is continuous on a compact set `s` is almost everywhere strongly measurable
with respect to `μ.restrict t` for any measurable subset `t` of `s`. -/
/-
**ContinuousOn.aestronglyMeasurable_of_subset_isCompact** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：ContinuousOn.aestronglyMeasurable_of_subset_isCompact [TopologicalSpace α]
 [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α 
-> β} {s t : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : IsCompact s) (
ht : MeasurableSet t) (hts : t subseteq s) : AEStronglyMeasurable f (μ.restrict 
t)
参数：hf : ContinuousOn f s；hs : IsCompact s；ht : MeasurableSet t；hts : t subseteq 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `ContinuousOn.aemeasurable`：ContinuousOn.aemeasurable [TopologicalSpace α
] [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpace 
β] {f : α -> β}…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `IsCompact.isSeparable`：IsCompact.isSeparable {α : Type*} [TopologicalSpa
ce α] [PseudoMetrizableSpace α] {s : Set α} (hs : IsCompact s) : IsSeparable s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
A function which is continuous on a compact set `s` is almost everywhere strongl
y measurable
with respect to `μ.restrict t` for any measurable subset `t` of `s`.
-/
theorem ContinuousOn.aestronglyMeasurable_of_subset_isCompact
    [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α → β} {s t : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : IsCompact s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    AEStronglyMeasurable f (μ.restrict t) := by
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨(hf.mono hts).aemeasurable ht, f '' s, ?_, ?_⟩
  · exact (hs.image_of_continuousOn hf).isSeparable
  · filter_upwards [ae_restrict_mem ht] with a ha using image_mono hts (mem_image_of_mem f ha)

/-- A function which is continuous on a compact set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
/-
**ContinuousOn.aestronglyMeasurable_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.aestronglyMeasurable_of_isCompact [TopologicalSpace α] [Opens
MeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α -> β} {
s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : IsCompact s) (h's : Mea
surableSet s) : AEStronglyMeasurable f (μ.restrict s)
参数：hf : ContinuousOn f s；hs : IsCompact s；h's : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aestronglyMeasurable_of_subset_isCompact`：ContinuousOn.aest
ronglyMeasurable_of_subset_isCompact [TopologicalSpace α] [OpensMeasurableSpace 
α] [TopologicalSpace β] [PseudoMetrizableSp…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
A function which is continuous on a compact set `s` is almost everywhere strongl
y measurable
with respect to `μ.restrict s`.
-/
theorem ContinuousOn.aestronglyMeasurable_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : IsCompact s) (h's : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) :=
  hf.aestronglyMeasurable_of_subset_isCompact hs h's Subset.rfl
/-
**Continuous.aestronglyMeasurable_of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.aestronglyMeasurable_of_compactSpace [TopologicalSpace α] [Open
sMeasurableSpace α] [CompactSpace α] [TopologicalSpace β] [PseudoMetrizableSpace
 β] {μ : Measure α} {f : α -> β} (hf : Continuous f) : AEStronglyMeasurable f μ
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `ContinuousOn.aestronglyMeasurable_of_isCompact`：ContinuousOn.aestronglyM
easurable_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α] [Topologica
lSpace β] [PseudoMetrizableSpace β] …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma Continuous.aestronglyMeasurable_of_compactSpace [TopologicalSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] {μ : Measure α} {f : α → β}
    (hf : Continuous f) : AEStronglyMeasurable f μ := by
  simpa using hf.continuousOn.aestronglyMeasurable_of_isCompact isCompact_univ .univ
/-
**ContinuousOn.integrableAt_nhdsWithin_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ContinuousOn.integrableAt_nhdsWithin_of_isSeparable [TopologicalSpace α] [
PseudoMetrizableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFini
teMeasure μ] {a : α} {t : Set α} {f : α -> E} (hft : ContinuousOn f t) (ht : Mea
surableSet t) (h't : TopologicalSpace.IsSeparable t) (ha : a in t) : IntegrableA
tFilter f (𝓝[t] a) μ
参数：hft : ContinuousOn f t；ht : MeasurableSet t；h't : TopologicalSpace.IsSeparabl
e t；ha : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_5} {mα :
 MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure α} 
  {f : α → E} {l : Filt…
· 使用定理 `MeasurableSet.nhdsWithin_isMeasurablyGenerated`：MeasurableSet.nhdsWithin
_isMeasurablyGenerated {s : Set α} (hs : MeasurableSet s) (a : α) : (𝓝[s] a).IsM
easurablyGenerated
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContinuousOn.aestronglyMeasurable_of_isSeparable`：ContinuousOn.aestrongl
yMeasurable_of_isSeparable [TopologicalSpace α] [PseudoMetrizableSpace α] [Opens
MeasurableSpace α] [TopologicalSpace β…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Measure.finiteAt_nhdsWithin`：finiteAt_nhdsWithin [Topologi
calSpace α] {_m0 : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ]
 (x : α) (s : Set α) : μ.Finite…
-/
theorem ContinuousOn.integrableAt_nhdsWithin_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
    {a : α} {t : Set α} {f : α → E} (hft : ContinuousOn f t) (ht : MeasurableSet t)
    (h't : TopologicalSpace.IsSeparable t) (ha : a ∈ t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter
    ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable ht h't⟩
    (μ.finiteAt_nhdsWithin _ _)
/-
**ContinuousOn.integrableAt_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integrableAt_nhdsWithin [TopologicalSpace α] [SecondCountable
TopologyEither α E] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMea
sure μ] {a : α} {t : Set α} {f : α -> E} (hft : ContinuousOn f t) (ht : Measurab
leSet t) (ha : a in t) : IntegrableAtFilter f (𝓝[t] a) μ
参数：hft : ContinuousOn f t；ht : MeasurableSet t；ha : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_5} {mα :
 MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure α} 
  {f : α → E} {l : Filt…
· 使用定理 `MeasurableSet.nhdsWithin_isMeasurablyGenerated`：MeasurableSet.nhdsWithin
_isMeasurablyGenerated {s : Set α} (hs : MeasurableSet s) (a : α) : (𝓝[s] a).IsM
easurablyGenerated
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Measure.finiteAt_nhdsWithin`：finiteAt_nhdsWithin [Topologi
calSpace α] {_m0 : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ]
 (x : α) (s : Set α) : μ.Finite…
-/
theorem ContinuousOn.integrableAt_nhdsWithin [TopologicalSpace α]
    [SecondCountableTopologyEither α E] [OpensMeasurableSpace α] {μ : Measure α}
    [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α → E} (hft : ContinuousOn f t)
    (ht : MeasurableSet t) (ha : a ∈ t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩
    (μ.finiteAt_nhdsWithin _ _)
/-
**Continuous.integrableAt_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.integrableAt_nhds [TopologicalSpace α] [SecondCountableTopology
Either α E] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] 
{f : α -> E} (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝 a) μ
参数：hf : Continuous f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `ContinuousOn.integrableAt_nhdsWithin`：ContinuousOn.integrableAt_nhdsWith
in [TopologicalSpace α] [SecondCountableTopologyEither α E] [OpensMeasurableSpac
e α] {μ : Measure α} [IsLo…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem Continuous.integrableAt_nhds [TopologicalSpace α] [SecondCountableTopologyEither α E]
    [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → E}
    (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝 a) μ := by
  rw [← nhdsWithin_univ]
  exact hf.continuousOn.integrableAt_nhdsWithin MeasurableSet.univ (mem_univ a)

/-- If a function is continuous on an open set `s`, then it is strongly measurable at the filter
`𝓝 x` for all `x ∈ s` if either the source space or the target space is second-countable. -/
/-
**ContinuousOn.stronglyMeasurableAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasura
bleSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopol
ogyEither α β] {f : α -> β} {s : Set α} {μ : Measure α} (hs : IsOpen s) (hf : Co
ntinuousOn f s) : forall x in s, StronglyMeasurableAtFilter f (𝓝 x) μ
参数：hs : IsOpen s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s

--- 原说明 ---
If a function is continuous on an open set `s`, then it is strongly measurable a
t the filter
`𝓝 x` for all `x ∈ s` if either the source space or the target space is second-c
ountable.
-/
theorem ContinuousOn.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α → β}
    {s : Set α} {μ : Measure α} (hs : IsOpen s) (hf : ContinuousOn f s) :
    ∀ x ∈ s, StronglyMeasurableAtFilter f (𝓝 x) μ := fun _x hx =>
  ⟨s, IsOpen.mem_nhds hs hx, hf.aestronglyMeasurable hs.measurableSet⟩
/-
**ContinuousAt.stronglyMeasurableAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasura
bleSpace α] [SecondCountableTopologyEither α E] {f : α -> E} {s : Set α} {μ : Me
asure α} (hs : IsOpen s) (hf : forall x in s, ContinuousAt f x) : forall x in s,
 StronglyMeasurableAtFilter f (𝓝 x) μ
参数：hs : IsOpen s；hf : forall x in s, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.stronglyMeasurableAtFilter`：ContinuousOn.stronglyMeasurable
AtFilter [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [Pse
udoMetrizableSpace β] [Second…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
-/
theorem ContinuousAt.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopologyEither α E] {f : α → E} {s : Set α} {μ : Measure α} (hs : IsOpen s)
    (hf : ∀ x ∈ s, ContinuousAt f x) : ∀ x ∈ s, StronglyMeasurableAtFilter f (𝓝 x) μ :=
  ContinuousOn.stronglyMeasurableAtFilter hs <| continuousOn_of_forall_continuousAt hf
/-
**Continuous.stronglyMeasurableAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurabl
eSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopolog
yEither α β] {f : α -> β} (hf : Continuous f) (μ : Measure α) (l : Filter α) : S
tronglyMeasurableAtFilter f l μ
参数：hf : Continuous f；μ : Measure α；l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l : F
ilter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `Continuous.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α]   [inst
_3 : TopologicalSpa…
-/
theorem Continuous.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α → β}
    (hf : Continuous f) (μ : Measure α) (l : Filter α) : StronglyMeasurableAtFilter f l μ :=
  hf.stronglyMeasurable.stronglyMeasurableAtFilter

/-- If a function is continuous on a measurable set `s`, then it is measurable at the filter
  `𝓝[s] x` for all `x`. -/
/-
**ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin {α β : Type*} [Measurab
leSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [P
seudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α -> β} {s : Se
t α} {μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) (x : α) : St
ronglyMeasurableAtFilter f (𝓝[s] x) μ
参数：hf : ContinuousOn f s；hs : MeasurableSet s；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…

--- 原说明 ---
If a function is continuous on a measurable set `s`, then it is measurable at th
e filter
  `𝓝[s] x` for all `x`.
-/
theorem ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopologyEither α β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (x : α) :
    StronglyMeasurableAtFilter f (𝓝[s] x) μ :=
  ⟨s, self_mem_nhdsWithin, hf.aestronglyMeasurable hs⟩

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the measure being finite at the endpoint, while
the unprimed ones use `[NullSingletonClass μ]`.
-/


section PartialOrder

variable [PartialOrder α] [MeasurableSingletonClass α]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε'] [PseudoMetrizableSpace ε']
  {f : α → ε'} {μ : Measure α} {a b : α}

/-
**integrableOn_Icc_iff_integrableOn_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ioc' (ha : μ {a} != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_union_left`：Ioc_union_left (hab : a <= b) : Ioc a b union {a} = 
Icc a b
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem integrableOn_Icc_iff_integrableOn_Ioc'
    (ha : μ {a} ≠ ∞ := by finiteness) (ha' : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ := by
  by_cases hab : a ≤ b
  · rw [← Ioc_union_left hab, integrableOn_union, eq_true (integrableOn_singleton ha'), and_true]
  · rw [Icc_eq_empty hab, Ioc_eq_empty]
    contrapose hab
    exact hab.le
/-
**integrableOn_Icc_iff_integrableOn_Ico'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ico' (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != 
∞
参数：hb : μ {b} != ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_union_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → Set.Ico b a ∪ {a} = Set.Icc b a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem integrableOn_Icc_iff_integrableOn_Ico'
    (hb : μ {b} ≠ ∞) (hb' : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ := by
  by_cases hab : a ≤ b
  · rw [← Ico_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Icc_eq_empty hab, Ico_eq_empty]
    contrapose hab
    exact hab.le
/-
**integrableOn_Ico_iff_integrableOn_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ico_iff_integrableOn_Ioo' (ha : μ {a} != ∞) (ha' : ‖f a‖ₑ != 
∞
参数：ha : μ {a} != ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_union_left`：Ioo_union_left (hab : a < b) : Ioo a b union {a} = I
co a b
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
-/
theorem integrableOn_Ico_iff_integrableOn_Ioo'
    (ha : μ {a} ≠ ∞) (ha' : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_left hab, integrableOn_union,
      eq_true (integrableOn_singleton ha'), and_true]
  · rw [Ioo_eq_empty hab, Ico_eq_empty hab]
/-
**integrableOn_Ioc_iff_integrableOn_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ioc_iff_integrableOn_Ioo' (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != 
∞
参数：hb : μ {b} != ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_union_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b < a → Set.Ioo b a ∪ {a} = Set.Ioc b a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
-/
theorem integrableOn_Ioc_iff_integrableOn_Ioo'
    (hb : μ {b} ≠ ∞) (hb' : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Ioo_eq_empty hab, Ioc_eq_empty hab]
/-
**integrableOn_Icc_iff_integrableOn_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ioo' (ha : μ {a} != ∞) (ha' : ‖f a‖ₑ != 
∞
参数：ha : μ {a} != ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc'`：integrableOn_Icc_iff_integrableO
n_Ioc' (ha : μ {a} != ∞
· 使用定理 `integrableOn_Ioc_iff_integrableOn_Ioo'`：integrableOn_Ioc_iff_integrableO
n_Ioo' (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_Icc_iff_integrableOn_Ioo' (ha : μ {a} ≠ ∞)
    (ha' : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : μ {b} ≠ ∞) (hb' : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha ha', integrableOn_Ioc_iff_integrableOn_Ioo' hb hb']
/-
**integrableOn_Ici_iff_integrableOn_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ici_iff_integrableOn_Ioi' (hb : μ {b} != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_union_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ioi a ∪ {a} = Set.Ici a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_Ici_iff_integrableOn_Ioi'
    (hb : μ {b} ≠ ∞ := by finiteness) (hb' : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ := by
  rw [← Ioi_union_left, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
/-
**integrableOn_Iic_iff_integrableOn_Iio'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Iic_iff_integrableOn_Iio' (hb : μ {b} != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_right`：Iio_union_right : Iio a union {a} = Iic a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.integrableOn_singleton`：integrableOn_singleton {f : α -> ε
'} {x : α} [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_Iic_iff_integrableOn_Iio'
    (hb : μ {b} ≠ ∞ := by finiteness) (hb' : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ := by
  rw [← Iio_union_right, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]

variable [NullSingletonClass μ]
/-
**integrableOn_Icc_iff_integrableOn_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ioc (ha : ‖f a‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc'`：integrableOn_Icc_iff_integrableO
n_Ioc' (ha : μ {a} != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Icc_iff_integrableOn_Ioc (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha
/-
**integrableOn_Icc_iff_integrableOn_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ico (hb : ‖f b‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ico'`：integrableOn_Icc_iff_integrableO
n_Ico' (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Icc_iff_integrableOn_Ico (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb
/-
**integrableOn_Ico_iff_integrableOn_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ico_iff_integrableOn_Ioo (ha : ‖f a‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Ico_iff_integrableOn_Ioo'`：integrableOn_Ico_iff_integrableO
n_Ioo' (ha : μ {a} != ∞) (ha' : ‖f a‖ₑ != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Ico_iff_integrableOn_Ioo (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ico_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha
/-
**integrableOn_Ioc_iff_integrableOn_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ioc_iff_integrableOn_Ioo (hb : ‖f b‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Ioc_iff_integrableOn_Ioo'`：integrableOn_Ioc_iff_integrableO
n_Ioo' (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Ioc_iff_integrableOn_Ioo (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ioc_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb
/-
**integrableOn_Icc_iff_integrableOn_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Icc_iff_integrableOn_Ioo (ha : ‖f a‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `integrableOn_Ioc_iff_integrableOn_Ioo`：integrableOn_Ioc_iff_integrableOn
_Ioo (hb : ‖f b‖ₑ != ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrableOn_Icc_iff_integrableOn_Ioo
    (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc ha, integrableOn_Ioc_iff_integrableOn_Ioo hb]
/-
**integrableOn_Ici_iff_integrableOn_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ici_iff_integrableOn_Ioi (hb : ‖f b‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Ici_iff_integrableOn_Ioi'`：integrableOn_Ici_iff_integrableO
n_Ioi' (hb : μ {b} != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Ici_iff_integrableOn_Ioi (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ :=
  integrableOn_Ici_iff_integrableOn_Ioi' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb
/-
**integrableOn_Iic_iff_integrableOn_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Iic_iff_integrableOn_Iio (hb : ‖f b‖ₑ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrableOn_Iic_iff_integrableOn_Iio'`：integrableOn_Iic_iff_integrableO
n_Iio' (hb : μ {b} != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem integrableOn_Iic_iff_integrableOn_Iio (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ :=
  integrableOn_Iic_iff_integrableOn_Iio' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

end PartialOrder

