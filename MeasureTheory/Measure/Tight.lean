/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker, Arav Bhattacharyya
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular

import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Tight sets of measures

A set of measures is tight if for all `0 < ε`, there exists a compact set `K` such that for all
measures in the set, the complement of `K` has measure at most `ε`.

## Main definitions

* `MeasureTheory.IsTightMeasureSet`: A set of measures `S` is tight if for all `0 < ε`, there exists
  a compact set `K` such that for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `⨆ μ ∈ S, μ` tends to `0` along the
  filter of cocompact sets.
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` establishes equivalence between
  the two definitions.

## Main statements

* `isTightMeasureSet_singleton_of_innerRegularWRT`: every finite, inner-regular measure is tight.
* `isTightMeasureSet_of_isCompact_closure`: every relatively compact set of measures is tight.


-/

@[expose] public section

open Filter Set TopologicalSpace

open scoped Topology

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} {S T : Set (Measure 𝓧)}

section Basic

variable [TopologicalSpace 𝓧]

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the definition above
in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
/-
**MeasureTheory.IsTightMeasureSet** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IsTightMeasureSet (S : Set (Measure 𝓧)) : Prop
参数：S : Set (Measure 𝓧)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K
` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the definition 
above
in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`.
-/
def IsTightMeasureSet (S : Set (Measure 𝓧)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact 𝓧).smallSets (𝓝 0)

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`. -/
/-
**MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSe
t S ↔ forall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ in S, μ (Kᶜ) <
= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.tendsto_nhds`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNReal} 
{a : ENNReal},   a ≠ ⊤ → (Filter.Tendsto u f (nhds a) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f
, u x ∈ Se…
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂

--- 原说明 ---
A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K
` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
-/
lemma isTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set 𝓧, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
    exact ⟨K, h1, hA Kᶜ h2⟩
  · obtain ⟨K, h1, h2⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS ↦ (μ.mono hA).trans (h2 μ hμS)⟩

/-- Finite measures that are inner regular with respect to closed compact sets are tight. -/
/-
**MeasureTheory.isTightMeasureSet_singleton_of_innerRegularWRT** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [I
sFiniteMeasure μ] (h : μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) Mea
surableSet) : IsTightMeasureSet {μ}
参数：h : μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) MeasurableSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.sub_lt_iff_lt_right`：∀ {a b c : ENNReal}, b ≠ ⊤ → b ≤ a → (a - b
 < c ↔ a < c + b)
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ

--- 原说明 ---
Finite measures that are inner regular with respect to closed compact sets are t
ight.
-/
theorem isTightMeasureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ]
    (h : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet) :
    IsTightMeasureSet {μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hεr.ne_bot hε.ne'
    obtain ⟨K, _, ⟨hK_compact, hK_closed⟩, hKμ⟩ := h .univ (r - ε) hεr'
    refine ⟨K, hK_compact, ?_⟩
    simp only [mem_singleton_iff, forall_eq]
    rw [measure_compl hK_closed.measurableSet (measure_ne_top μ _), tsub_le_iff_right]
    rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
    exact hKμ.le
  | inr hεr => exact ⟨∅, isCompact_empty, by simpa⟩

/-- Inner regular finite measures on T2 spaces are tight. -/
/-
**MeasureTheory.isTightMeasureSet_singleton_of_innerRegular** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_singleton_of_innerRegular [T2Space 𝓧] [OpensMeasurableSp
ace 𝓧] [IsFiniteMeasure μ] [h : μ.InnerRegular] : IsTightMeasureSet {μ}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isTightMeasureSet_singleton_of_innerRegularWRT`：isTightMea
sureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ
] (h : μ.InnerRegularWRT (fun s => IsCompact s ∧ I…
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s

--- 原说明 ---
Inner regular finite measures on T2 spaces are tight.
-/
lemma isTightMeasureSet_singleton_of_innerRegular [T2Space 𝓧] [OpensMeasurableSpace 𝓧]
    [IsFiniteMeasure μ] [h : μ.InnerRegular] :
    IsTightMeasureSet {μ} := by
  refine isTightMeasureSet_singleton_of_innerRegularWRT ?_
  intro s hs r hr
  obtain ⟨K, hKs, hK_compact, hμK⟩ := h.innerRegular hs r hr
  exact ⟨K, hKs, ⟨hK_compact, hK_compact.isClosed⟩, hμK⟩

/-- In a complete second-countable pseudo-metric space, finite measures are tight. -/
/-
**MeasureTheory.isTightMeasureSet_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：isTightMeasureSet_singleton {α : Type*} [MeasurableSpace α] [TopologicalSp
ace α] [IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α] [BorelS
pace α] {μ : Measure α} [IsFiniteMeasure μ] : IsTightMeasureSet {μ}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isTightMeasureSet_singleton_of_innerRegularWRT`：isTightMea
sureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ
] (h : μ.InnerRegularWRT (fun s => IsCompact s ∧ I…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite`：i
nnerRegular_isCompact_isClosed_measurableSet_of_finite [TopologicalSpace α] [Sec
ondCountableTopology α] [IsCompletelyPseudoMetrizableSpace …

--- 原说明 ---
In a complete second-countable pseudo-metric space, finite measures are tight.
-/
theorem isTightMeasureSet_singleton {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

namespace IsTightMeasureSet

/-- In a compact space, every set of measures is tight. -/
/-
**MeasureTheory.IsTightMeasureSet.of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.IsTightMeasureSet`。
形式化陈述：of_compactSpace [CompactSpace 𝓧] : IsTightMeasureSet S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cocompact_eq_bot`：Filter.cocompact_eq_bot [CompactSpace X] : Filt
er.cocompact X = ⊥
· 使用定理 `Filter.smallSets_bot`：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
In a compact space, every set of measures is tight.
-/
lemma of_compactSpace [CompactSpace 𝓧] : IsTightMeasureSet S := by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ ↦ mem_of_mem_nhds
/-
**MeasureTheory.IsTightMeasureSet.subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsTightMeasureSet`。
形式化陈述：∀ {𝓧 : Type u_1} {m𝓧 : MeasurableSpace 𝓧} {S T : Set (MeasureTheory.Measur
e 𝓧)} [inst : TopologicalSpace 𝓧],   MeasureTheory.IsTightMeasureSet T → S ⊆ T →
 MeasureTheory.IsTightMeasureSet S
参数：MeasureTheory.Measure 𝓧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iSup_le_iSup_of_subset`：iSup_le_iSup_of_subset {f : β -> α} {s t : Set β
} : s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
-/
protected lemma subset (hT : IsTightMeasureSet T) (hST : S ⊆ T) :
    IsTightMeasureSet S :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ ↦ by simp)
    (iSup_le_iSup_of_subset hST)
/-
**MeasureTheory.IsTightMeasureSet.union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsTightMeasureSet`。
形式化陈述：∀ {𝓧 : Type u_1} {m𝓧 : MeasurableSpace 𝓧} {S T : Set (MeasureTheory.Measur
e 𝓧)} [inst : TopologicalSpace 𝓧],   MeasureTheory.IsTightMeasureSet S → Measure
Theory.IsTightMeasureSet T → MeasureTheory.IsTightMeasureSet (S ∪ T)
参数：MeasureTheory.Measure 𝓧；S ∪ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsTightMeasureSet.eq_1`：∀ {𝓧 : Type u_1} {m𝓧 : MeasurableS
pace 𝓧} [inst : TopologicalSpace 𝓧] (S : Set (MeasureTheory.Measure 𝓧)),   Measu
reTheory.IsTightMeasureSet…
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Filter.Tendsto.sup_nhds`：sup_nhds [Max L] [ContinuousSup L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y
))
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `LinearOrder.topologicalLattice`：∀ {L : Type u_1} [inst : TopologicalSpac
e L] [inst_1 : LinearOrder L] [OrderClosedTopology L], TopologicalLattice L
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
protected lemma union (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet (S ∪ T) := by
  rw [IsTightMeasureSet, iSup_union]
  convert! Tendsto.sup_nhds hS hT
  simp
/-
**MeasureTheory.IsTightMeasureSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsTightMeasureSet`。
形式化陈述：∀ {𝓧 : Type u_1} {m𝓧 : MeasurableSpace 𝓧} {S : Set (MeasureTheory.Measure 
𝓧)} [inst : TopologicalSpace 𝓧],   MeasureTheory.IsTightMeasureSet S → ∀ (T : Se
t (MeasureTheory.Measure 𝓧)), MeasureTheory.IsTightMeasureSet (S ∩ T)
参数：MeasureTheory.Measure 𝓧；T : Set (MeasureTheory.Measure 𝓧)；S ∩ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsTightMeasureSet.subset`：∀ {𝓧 : Type u_1} {m𝓧 : Measurabl
eSpace 𝓧} {S T : Set (MeasureTheory.Measure 𝓧)} [inst : TopologicalSpace 𝓧],   M
easureTheory.IsTightMeasureS…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
protected lemma inter (hS : IsTightMeasureSet S) (T : Set (Measure 𝓧)) :
    IsTightMeasureSet (S ∩ T) :=
  hS.subset inter_subset_left
/-
**MeasureTheory.IsTightMeasureSet.map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.I
sTightMeasureSet`。
形式化陈述：map [TopologicalSpace 𝓨] [MeasurableSpace 𝓨] [OpensMeasurableSpace 𝓨] [T2S
pace 𝓨] (hS : IsTightMeasureSet S) {f : 𝓧 -> 𝓨} (hf : Continuous f) : IsTightMea
sureSet (Measure.map f '' S)
参数：hS : IsTightMeasureSet S；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma map [TopologicalSpace 𝓨] [MeasurableSpace 𝓨] [OpensMeasurableSpace 𝓨] [T2Space 𝓨]
    (hS : IsTightMeasureSet S) {f : 𝓧 → 𝓨} (hf : Continuous f) :
    IsTightMeasureSet (Measure.map f '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro ε hε
  obtain ⟨K, hK_compact, hKS⟩ := hS ε hε
  refine ⟨f '' K, hK_compact.image hf, fun μ hμS ↦ ?_⟩
  by_cases hf_meas : AEMeasurable f μ
  swap; · simp [Measure.map_of_not_aemeasurable hf_meas]
  rw [Measure.map_apply_of_aemeasurable hf_meas (hK_compact.image hf).measurableSet.compl]
  refine (measure_mono ?_).trans (hKS μ hμS)
  simp only [preimage_compl, compl_subset_compl]
  exact subset_preimage_image f K

/-- A set of measures on a product space is tight if both marginals are tight. -/
/-
**MeasureTheory.IsTightMeasureSet.prodMk** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.IsTightMeasureSet`。
形式化陈述：prodMk {m𝓨 : MeasurableSpace 𝓨} [TopologicalSpace 𝓨] {μ : Set (Measure (𝓧 
× 𝓨))} (hμ₁ : IsTightMeasureSet (Measure.fst '' μ)) (hμ₂ : IsTightMeasureSet (Me
asure.snd '' μ)) : IsTightMeasureSet μ
参数：Measure (𝓧 × 𝓨)；hμ₁ : IsTightMeasureSet (Measure.fst '' μ)；hμ₂ : IsTightMeasu
reSet (Measure.snd '' μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用引理 `Set.compl_prod_eq_union`：compl_prod_eq_union {α β : Type*} (s : Set α) (
t : Set β) : (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `MeasureTheory.Measure.le_map_apply`：le_map_apply {f : α -> β} (hf : AEMe
asurable f μ) (s : Set β) : μ (f ⁻¹' s) <= μ.map f s
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
A set of measures on a product space is tight if both marginals are tight.
-/
lemma prodMk {m𝓨 : MeasurableSpace 𝓨} [TopologicalSpace 𝓨] {μ : Set (Measure (𝓧 × 𝓨))}
    (hμ₁ : IsTightMeasureSet (Measure.fst '' μ)) (hμ₂ : IsTightMeasureSet (Measure.snd '' μ)) :
    IsTightMeasureSet μ := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ₁ hμ₂ ⊢
  intro ε hε
  obtain ⟨K₁, hK₁_compact, hK₁_le⟩ := hμ₁ (ε / 2) (by aesop)
  obtain ⟨K₂, hK₂_compact, hK₂_le⟩ := hμ₂ (ε / 2) (by aesop)
  refine ⟨K₁ ×ˢ K₂, hK₁_compact.prod hK₂_compact, fun κ hκ_mem ↦ ?_⟩
  grw [compl_prod_eq_union, measure_union_le, ← ENNReal.add_halves (a := ε)]
  apply add_le_add
  · specialize hK₁_le _ <| mem_image_of_mem _ hκ_mem
    grw [Measure.fst, ← Measure.le_map_apply (by fun_prop)] at hK₁_le
    simpa [prod_univ] using hK₁_le
  · specialize hK₂_le _ <| Set.mem_image_of_mem _ hκ_mem
    grw [Measure.snd, ← Measure.le_map_apply (by fun_prop)] at hK₂_le
    simpa [univ_prod] using hK₂_le

end IsTightMeasureSet
end Basic

end MeasureTheory

