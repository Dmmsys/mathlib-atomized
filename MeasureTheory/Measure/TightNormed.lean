/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Order.Filter.ENNReal

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a proper normed group, a set of measures `S`
  is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.
* `isTightMeasureSet_iff_inner_tendsto`: in a finite-dimensional inner product space,
  a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < |⟪y, x⟫|}`
  tends to `0` at infinity for all `y`.
* `isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt`: in a proper normed group,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to `0` at infinity.
* `isTightMeasureSet_range_iff_tendsto_limsup_inner`: in a finite-dimensional inner product space,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infinity for all `y`.

-/

public section

open Filter

open scoped Topology ENNReal NNReal InnerProductSpace

namespace MeasureTheory

variable {E : Type*} {mE : MeasurableSpace E} {S : Set (Measure E)}

section PseudoMetricSpace

variable [PseudoMetricSpace E]

/-
**MeasureTheory.tendsto_measure_compl_closedBall_of_isTightMeasureSet** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasure
Set S) (x : E) : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) 
atTop (𝓝 0)
参数：hS : IsTightMeasureSet S；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.HasAntitoneBasis.tendsto_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {ι : Type u_4} [inst : Preorder ι] {s : ι → Set α},   l.HasAntitoneBasis s → 
Filter.Tendsto s Filter.atTop l…
· 使用定理 `Metric.hasAntitoneBasis_cobounded_compl_closedBall`：hasAntitoneBasis_cob
ounded_compl_closedBall (c : α) : (cobounded α).HasAntitoneBasis (fun r => (clos
edBall c r)ᶜ)
· 使用定理 `Filter.monotone_smallSets`：monotone_smallSets : Monotone (@smallSets α)
· 使用定理 `Metric.cobounded_le_cocompact`：cobounded_le_cocompact : cobounded α <= c
ocompact α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tendsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x : E) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ ∈ S, μ) ∘ (fun r ↦ (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert! this with r
    simp
  refine hS.comp <| .mono_right ?_ <| monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets
/-
**MeasureTheory.isTightMeasureSet_of_tendsto_measure_compl_closedBall** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x :
 E} (h : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝
 0)) : IsTightMeasureSet S
参数：h : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma isTightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E}
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

/-- In a proper pseudo-metric space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ` tends to `0` at infinity. -/
/-
**MeasureTheory.isTightMeasureSet_iff_tendsto_measure_compl_closedBall** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_iff_tendsto_measure_compl_closedBall [ProperSpace E] (x 
: E) : IsTightMeasureSet S ↔ Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closed
Ball x r)ᶜ) atTop (𝓝 0)
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_measure_compl_closedBall_of_isTightMeasureSet`：ten
dsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x
 : E) : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.clos…
· 使用引理 `MeasureTheory.isTightMeasureSet_of_tendsto_measure_compl_closedBall`：isT
ightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E} (h : 
Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x…

--- 原说明 ---
In a proper pseudo-metric space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ` tends to `0` at infinity.
-/
lemma isTightMeasureSet_iff_tendsto_measure_compl_closedBall [ProperSpace E] (x : E) :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) :=
  ⟨fun hS ↦ tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

end PseudoMetricSpace

section NormedAddCommGroup

variable [NormedAddCommGroup E]

/-
**MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) : 
Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)
参数：hS : IsTightMeasureSet S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_measure_compl_closedBall_of_isTightMeasureSet`：ten
dsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x
 : E) : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.clos…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert! h using 6 with r
  ext
  simp
/-
**MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_of_tendsto_measure_norm_gt [ProperSpace E] (h : Tendsto 
(fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)) : IsTightMeasureSet S
参数：h : Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_of_tendsto_measure_compl_closedBall`：isT
ightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E} (h : 
Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isTightMeasureSet_of_tendsto_measure_norm_gt [ProperSpace E]
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert! h using 6 with r
  ext
  simp

/-- In a proper normed group, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity. -/
/-
**MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_iff_tendsto_measure_norm_gt [ProperSpace E] : IsTightMea
sureSet S ↔ Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet`：tendsto_meas
ure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) : Tendsto (fun r : R
eal => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)
· 使用引理 `MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt`：isTightMeasu
reSet_of_tendsto_measure_norm_gt [ProperSpace E] (h : Tendsto (fun r : Real => ⨆
 μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)) : IsTight…

--- 原说明 ---
In a proper normed group, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.
-/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt [ProperSpace E] :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

section Sequence

variable [BorelSpace E] [ProperSpace E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]

/-- For a sequence of measures indexed by `ℕ`, if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to 0 at infinity, then the set of measures
in the sequence is tight.
Compared to `isTightMeasureSet_of_tendsto_measure_norm_gt`, this lemma replaces a supremum over
all measures by a limsup. This is possible because the sequence is indexed by `ℕ`. -/
/-
**MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt** 是 Ma
thlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt (h : Tendsto (fu
n r : Real => limsup (fun n => μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) : IsTightM
easureSet (Set.range μ)
参数：h : Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖x‖}) atTop) atTop
 (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用引理 `Nat.tendsto_iSup_of_tendsto_limsup`：Nat.tendsto_iSup_of_tendsto_limsup {
α β : Type*} [ConditionallyCompleteLattice α] [CompleteLinearOrder β] [Topologic
alSpace β] [OrderTopolog…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.isTightMeasureSet_singleton`：isTightMeasureSet_singleton {
α : Type*} [MeasurableSpace α] [TopologicalSpace α] [IsCompletelyPseudoMetrizabl
eSpace α] [SecondCountableTopol…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt`：isTightMeas
ureSet_iff_tendsto_measure_norm_gt [ProperSpace E] : IsTightMeasureSet S ↔ Tends
to (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) at…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For a sequence of measures indexed by `ℕ`, if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to 0 at infinity, then 
the set of measures
in the sequence is tight.
Compared to `isTightMeasureSet_of_tendsto_measure_norm_gt`, this lemma replaces 
a supremum over
all measures by a limsup. This is possible because the sequence is indexed by `ℕ
`.
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
    (h : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  simp_rw [isTightMeasureSet_iff_tendsto_measure_norm_gt, iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) h (fun n u v huv ↦ by gcongr)
  have h_tight : IsTightMeasureSet {μ n} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  simpa using h_tight

/-- For a sequence of measures indexed by `ℕ`, the set of measures in the sequence is tight if and
only if the function `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to 0 at infinity.
Compared to `isTightMeasureSet_iff_tendsto_measure_norm_gt`, this lemma replaces a supremum over
all measures by a limsup. This is possible because the sequence is indexed by `ℕ`. -/
/-
**MeasureTheory.isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt** 是 M
athlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt : IsTightMeasur
eSet (Set.range μ) ↔ Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖x‖}
) atTop) atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet`：tendsto_meas
ure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) : Tendsto (fun r : R
eal => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用引理 `MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt`
：isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt (h : Tendsto (fun r :
 Real => limsup (fun n => μ n {x | r < ‖x‖}) atTop) atTop (𝓝 …

--- 原说明 ---
For a sequence of measures indexed by `ℕ`, the set of measures in the sequence i
s tight if and
only if the function `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to
 0 at infinity.
Compared to `isTightMeasureSet_iff_tendsto_measure_norm_gt`, this lemma replaces
 a supremum over
all measures by a limsup. This is possible because the sequence is indexed by `ℕ
`.
-/
lemma isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt :
    IsTightMeasureSet (Set.range μ)
      ↔ Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ ↦ zero_le) ?_
  intro r
  simp_rw [iSup_range]
  exact limsup_le_iSup

end Sequence

section InnerProductSpace

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-
**MeasureTheory.isTightMeasureSet_of_forall_basis_tendsto** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι 𝕜 E) (h 
: forall i, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪b i, x⟫_𝕜‖}) atTop (
𝓝 0)) : IsTightMeasureSet S
参数：b : OrthonormalBasis ι 𝕜 E；h : forall i, Tendsto (fun r : Real => ⨆ μ in S, μ
 {x | r < ‖⟪b i, x⟫_𝕜‖}) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.cocompact_eq_bot`：Filter.cocompact_eq_bot [CompactSpace X] : Filt
er.cocompact X = ⊥
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `Filter.smallSets_bot`：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_pure_nhds`：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (p
ure a) (𝓝 (f a))
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `FiniteDimensional.proper`：FiniteDimensional.proper [FiniteDimensional 𝕜 
E] : ProperSpace E
（共 64 条，此处仅展示前 30 条）
-/
lemma isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι 𝕜 E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪b i, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert! tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simpa [← Module.finrank_eq_card_basis b.toBasis, Module.finrank_pos_iff]
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖})
      ≤ fun r ↦ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
    intro r
    calc ⨆ μ ∈ S, μ {x | r < ‖x‖}
    _ ≤ ⨆ μ ∈ S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫_𝕜‖ :=
        hx.trans_le (b.norm_le_card_mul_iSup_norm_inner x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ ≤ ⨆ μ ∈ S, ∑ i, μ {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      refine iSup_le fun μ ↦ (iSup_le fun hμS ↦ ?_)
      gcongr with i
      exact le_biSup (fun μ ↦ μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) h_le
  rw [← Finset.sum_const_zero]
  refine tendsto_finsetSum Finset.univ fun i _ ↦ (h i).comp ?_
  exact tendsto_id.atTop_div_const (by positivity)

variable (𝕜)
/-
**MeasureTheory.isTightMeasureSet_of_inner_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：isTightMeasureSet_of_inner_tendsto (h : forall y, Tendsto (fun r : Real =>
 ⨆ μ in S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)) : IsTightMeasureSet S
参数：h : forall y, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTo
p (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_of_forall_basis_tendsto`：isTightMeasureS
et_of_forall_basis_tendsto (b : OrthonormalBasis ι 𝕜 E) (h : forall i, Tendsto (
fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪b i, x…
-/
lemma isTightMeasureSet_of_inner_tendsto
    (h : ∀ y, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_forall_basis_tendsto (stdOrthonormalBasis 𝕜 E)
    fun i ↦ h (stdOrthonormalBasis 𝕜 E i)

/-- In a finite-dimensional inner product space,
a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < |⟪y, x⟫|}`
tends to `0` at infinity for all `y`. -/
/-
**MeasureTheory.isTightMeasureSet_iff_inner_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：isTightMeasureSet_iff_inner_tendsto : IsTightMeasureSet S ↔ forall y, Tend
sto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.proper`：FiniteDimensional.proper [FiniteDimensional 𝕜 
E] : ProperSpace E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt`：isTightMeas
ureSet_iff_tendsto_measure_norm_gt [ProperSpace E] : IsTightMeasureSet S ↔ Tends
to (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) at…
· 使用定理 `Filter.tendsto_mul_const_atTop_of_pos`：tendsto_mul_const_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
In a finite-dimensional inner product space,
a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | 
r < |⟪y, x⟫|}`
tends to `0` at infinity for all `y`.
-/
lemma isTightMeasureSet_iff_inner_tendsto :
    IsTightMeasureSet S
      ↔ ∀ y, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0) := by
  refine ⟨fun h y ↦ ?_, isTightMeasureSet_of_inner_tendsto 𝕜⟩
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r ↦ ⨆ μ ∈ S, μ {x | r * ‖y‖⁻¹ < ‖x‖}) atTop (𝓝 0) :=
    h.comp <| (tendsto_mul_const_atTop_of_pos (by positivity)).mpr tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le) ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < ‖⟪y, x⟫_𝕜‖} ≤ μ {x | r * ‖y‖⁻¹ < ‖x‖} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [mul_inv_lt_iff₀]
    · rw [mul_comm]
      exact hx.trans_le (norm_inner_le_norm y x)
    · positivity
  refine iSup₂_le_iff.mpr fun μ hμS ↦ ?_
  exact le_iSup_of_le (i := μ) <| by simp [hμS, h_le]

variable [BorelSpace E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
/-
**MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_inner** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_of_tendsto_limsup_inner (h : forall y, Tendsto (fu
n r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) : I
sTightMeasureSet (Set.range μ)
参数：h : forall y, Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_
𝕜‖}) atTop) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_of_inner_tendsto`：isTightMeasureSet_of_i
nner_tendsto (h : forall y, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪y, x
⟫_𝕜‖}) atTop (𝓝 0)) : IsTightMeasureSe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用引理 `Nat.tendsto_iSup_of_tendsto_limsup`：Nat.tendsto_iSup_of_tendsto_limsup {
α β : Type*} [ConditionallyCompleteLattice α] [CompleteLinearOrder β] [Topologic
alSpace β] [OrderTopolog…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.isTightMeasureSet_singleton`：isTightMeasureSet_singleton {
α : Type*} [MeasurableSpace α] [TopologicalSpace α] [IsCompletelyPseudoMetrizabl
eSpace α] [SecondCountableTopol…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
（共 44 条，此处仅展示前 30 条）
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_inner
    (h : ∀ y, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_inner_tendsto 𝕜 fun z ↦ ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) (h z) (fun n u v huv ↦ by gcongr)
  have h_tight : IsTightMeasureSet {(μ n).map (fun x ↦ ⟪z, x⟫_𝕜)} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  have h_map r : (μ n).map (fun x ↦ ⟪z, x⟫_𝕜) {x | r < ‖x‖} = μ n {x | r < ‖⟪z, x⟫_𝕜‖} := by
    rw [Measure.map_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  simpa [h_map] using h_tight

/-- In a finite-dimensional inner product space, the range of a sequence of measures
`μ : ℕ → Measure E` is tight if and only if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infinity for all `y`. -/
/-
**MeasureTheory.isTightMeasureSet_range_iff_tendsto_limsup_inner** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_iff_tendsto_limsup_inner : IsTightMeasureSet (Set.
range μ) ↔ forall y, Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y,
 x⟫_𝕜‖}) atTop) atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_inner_tendsto`：isTightMeasureSet_iff
_inner_tendsto : IsTightMeasureSet S ↔ forall y, Tendsto (fun r : Real => ⨆ μ in
 S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用定理 `Filter.limsup_le_iSup`：limsup_le_iSup {f : Filter β} {u : β -> α} : lims
up u f <= ⨆ n, u n
· 使用引理 `MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_inner`：isTightMe
asureSet_range_of_tendsto_limsup_inner (h : forall y, Tendsto (fun r : Real => l
imsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) at…

--- 原说明 ---
In a finite-dimensional inner product space, the range of a sequence of measures
`μ : ℕ → Measure E` is tight if and only if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infini
ty for all `y`.
-/
lemma isTightMeasureSet_range_iff_tendsto_limsup_inner :
    IsTightMeasureSet (Set.range μ)
      ↔ ∀ y, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h z ↦ ?_, isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜⟩
  rw [isTightMeasureSet_iff_inner_tendsto 𝕜] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h z)
    (fun _ ↦ zero_le) fun r ↦ ?_
  simp_rw [iSup_range]
  exact limsup_le_iSup
/-
**MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one (h : forall
 y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖
}) atTop) atTop (𝓝 0)) : IsTightMeasureSet (Set.range μ)
参数：h : forall y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n => μ n {x | r
 < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_inner`：isTightMe
asureSet_range_of_tendsto_limsup_inner (h : forall y, Tendsto (fun r : Real => l
imsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) at…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
（共 51 条，此处仅展示前 30 条）
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one
    (h : ∀ y, ‖y‖ = 1
      → Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜 fun y ↦ ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | ‖y‖⁻¹ * r < ‖⟪(‖y‖⁻¹ : 𝕜) • y, x⟫_𝕜‖})
      atTop) atTop (𝓝 0) := by
    specialize h ((‖y‖⁻¹ : 𝕜) • y) ?_
    · simp only [norm_smul, norm_inv, norm_algebraMap', Real.norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀ (by positivity)]
    exact h.comp <| (tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id
  convert! h' using 7 with r n x
  rw [inner_smul_left]
  simp only [map_inv₀, RCLike.conj_ofReal, norm_mul, norm_inv, norm_algebraMap', norm_norm]
  rw [mul_lt_mul_iff_right₀]
  positivity
/-
**MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_n
orm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
 (h : forall y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n => (μ n).real 
{x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) (C : Real>=0) (hμ : forallᶠ n in atTop
, μ n .univ <= C) : IsTightMeasureSet (Set.range μ)
参数：h : forall y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n => (μ n).real
 {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)；C : Real>=0；hμ : forallᶠ n in atTop, μ
 n .univ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq
_one`：isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one (h : forall
 y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n => μ n {x | …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.ofReal_limsup_toReal`：ofReal_limsup_toReal [f.NeBot] {u : α -> R
eal>=0∞} {C : Real>=0} (hf : forallᶠ a in f, u a <= C) : ENNReal.ofReal (limsup 
(fun a => (u a).to…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
    (h : ∀ y, ‖y‖ = 1 →
      Tendsto (fun r : ℝ ↦ limsup (fun n ↦ (μ n).real {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0))
    (C : ℝ≥0) (hμ : ∀ᶠ n in atTop, μ n .univ ≤ C) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one 𝕜 fun z hz ↦ ?_
  have h_ofReal (r : ℝ) : limsup (fun n ↦ μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop
      = ENNReal.ofReal (limsup (fun n ↦ (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ENNReal.ofReal_limsup_toReal (C := C)]
    filter_upwards [hμ] with n hμn using (measure_mono (Set.subset_univ _)).trans hμn
  simpa only [h_ofReal, ← ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (h z hz)

end InnerProductSpace

end NormedAddCommGroup

end MeasureTheory

