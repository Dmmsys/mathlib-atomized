/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Prokhorov theorem

We prove statements about the compactness of sets of finite measures or probability measures,
notably several versions of Prokhorov theorem on tight sets of probability measures.

## Main statements

* `instCompactSpaceProbabilityMeasure` proves that the space of probability measures on a compact
  space is itself compact
* `isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le`: Given a sequence of compact
  sets `Kₙ` and a sequence `uₙ` tending to zero, the probability measures giving mass at most `uₙ`
  to the complement of `Kₙ` form a compact set.
* `isCompact_closure_of_isTightMeasureSet`: Given a tight set of probability measures, its closure
  is compact.
* `isTightMeasureSet_of_isCompact_closure`: In a second countable complete metric space, a set of
  probability measures with compact closure is tight.

Versions are also given for finite measures.

## Implementation

We do not assume second-countability or metrizability.

For the compactness of the space of probability measures in a compact space, we argue that every
ultrafilter converges, using the Riesz-Markov-Kakutani theorem to construct the limiting measure
in terms of its integrals against continuous functions.

For Prokhorov theorem `isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le`,
we rely on the compactness of the space of measures inside each compact set to get convergence
of the restriction there, and argue that the full measure converges to the sum of the individual
limits of the disjointed components. There is a subtlety that the space of finite measures
giving mass `uₙ` to `Kₙᶜ` doesn't have to be closed in our general setting, but we only need to
find *a* limit satisfying this condition. To ensure this, we need a technical condition
(monotonicity of `K` or normality of the space). In the first case, the bound follows readily
from the construction. In the second case, we modify the individual limits
(again using Riesz-Markov-Kakutani) to make sure that they are inner-regular, and then one can
check the condition.
-/

public section

open scoped CompactlySupported
open Metric ENNReal NNReal Filter Set Topology TopologicalSpace MeasureTheory
  BoundedContinuousFunction

section Forward

open FiniteMeasure

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency.types false in
variable (E) in
/-- In a compact space, the set of finite measures with mass at most `C` is compact. -/
/-
**isCompact_setOfPred_finiteMeasure_le_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：isCompact_setOfPred_finiteMeasure_le_of_compactSpace [CompactSpace E] (C :
 Real>=0) : IsCompact {μ : FiniteMeasure E | μ.mass <= C}
参数：C : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isCompact_iff_ultrafilter_le_nhds'`：isCompact_iff_ultrafilter_le_nhds' :
 IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `IsCompact.ultrafilter_le_nhds'`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, ↑f ≤ nhd
s x
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
· 使用定理 `enorm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), 
‖‖x‖‖ₑ = ‖x‖ₑ
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
In a compact space, the set of finite measures with mass at most `C` is compact.
-/
theorem isCompact_setOfPred_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C} := by
  /- To prove the compactness, we will show that any sequence has a converging subsequence, in
  ultrafilters terms as things are not second countable. The integral against any bounded continuous
  function has a limit along the ultrafilter, by compactness of real intervals and the mass control.
  The limit is a monotone linear form. By the Riesz-Markov-Kakutani theorem, it comes from a
  measure. This measure is finite, of mass at most `C`. It provides the desired limit
  for the ultrafilter. -/
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have L (g : C_c(E, ℝ)) :
      ∃ x ∈ Icc (-C * ‖g.toBoundedContinuousFunction‖) (C * ‖g.toBoundedContinuousFunction‖),
      Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x ∂μ) f (𝓝 x) := by
    simp only [Tendsto, ← Ultrafilter.coe_map]
    apply IsCompact.ultrafilter_le_nhds' isCompact_Icc
    simp only [neg_mul, Ultrafilter.mem_map]
    filter_upwards [hf] with μ hμ
    simp only [mem_preimage, mem_Icc]
    refine ⟨?_, ?_⟩
    · calc - (C * ‖g.toBoundedContinuousFunction‖)
      _ ≤ ∫ (x : E), - ‖g.toBoundedContinuousFunction‖ ∂μ := by
        simp only [integral_const, smul_eq_mul, mul_neg, neg_le_neg_iff]
        gcongr
        exact hμ
      _ ≤ ∫ x, g x ∂μ := by
        gcongr
        · simp
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · intro x
          apply neg_le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
    · calc ∫ x, g x ∂μ
      _ ≤ ∫ (x : E), ‖g.toBoundedContinuousFunction‖ ∂μ := by
        gcongr
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · simp
        · intro x
          apply le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
      _ ≤ C * ‖g.toBoundedContinuousFunction‖ := by
        simp only [integral_const, smul_eq_mul]
        gcongr
        exact hμ
  choose Λ h₀Λ hΛ using L
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := Λ
    map_add' g g' := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x + g' x ∂μ) f (𝓝 (Λ g + Λ g')) := by
        convert! (hΛ g).add (hΛ g')
        rw [integral_add]
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
      exact tendsto_nhds_unique (hΛ (g + g')) this
    map_smul' c g := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, c • g x ∂μ) f (𝓝 (c • Λ g)) := by
        convert! (hΛ g).const_smul c
        rw [integral_smul]
      exact tendsto_nhds_unique (hΛ (c • g)) this
    monotone' g g' hgg' := by
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ g') (fun μ ↦ ?_)
      apply integral_mono _ _ hgg'
      · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport }
  let μlim := RealRMK.rieszMeasure Λ'
  have μlim_le : μlim univ ≤ ENNReal.ofReal C := by
    let o : C_c(E, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
    have : μlim univ ≤ ENNReal.ofReal (Λ' o) := RealRMK.rieszMeasure_le_of_eq_one Λ'
      (fun x ↦ by simp [o]) isCompact_univ (fun x ↦ by simp [o])
    apply this.trans
    gcongr
    apply le_of_tendsto (hΛ o)
    filter_upwards [hf] with μ hμ using by simpa [o] using! hμ
  let μlim' : FiniteMeasure E := ⟨μlim, ⟨μlim_le.trans_lt (by simp)⟩⟩
  refine ⟨μlim', ?_, ?_⟩
  · simp only [mem_ofPred_eq, FiniteMeasure.mk_apply, μlim', FiniteMeasure.mass]
    rw [show C = (ENNReal.ofReal ↑C).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) μlim_le
  change Tendsto id f (𝓝 μlim')
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
  let g' : C_c(E, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  convert! hΛ g'
  change ∫ (x : E), g' x ∂μlim' = Λ g'
  simp only [FiniteMeasure.toMeasure_mk, RealRMK.integral_rieszMeasure, μlim', μlim]
  rfl

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_finiteMeasure_le_of_compactSpace :=
  isCompact_setOfPred_finiteMeasure_le_of_compactSpace

variable (E) in
/-- In a compact space, the set of finite measures with mass `C` is compact. -/
/-
**isCompact_setOfPred_finiteMeasure_eq_of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：isCompact_setOfPred_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C :
 Real>=0) : IsCompact {μ : FiniteMeasure E | μ.mass = C}
参数：C : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`：isCompact_setOfPre
d_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : Real>=0) : IsCompact {μ
 : FiniteMeasure E | μ.mass <= C}
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.FiniteMeasure.continuous_mass`：∀ {Ω : Type u_1} [inst : Me
asurableSpace Ω] [inst_1 : TopologicalSpace Ω] [inst_2 : OpensMeasurableSpace Ω]
,   Continuous fun μ => μ.mass
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
In a compact space, the set of finite measures with mass `C` is compact.
-/
lemma isCompact_setOfPred_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩ {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOfPred_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_finiteMeasure_eq_of_compactSpace :=
  isCompact_setOfPred_finiteMeasure_eq_of_compactSpace

/-- In a compact space, the space of probability measures is also compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a compact space, the space of probability measures is also compact.
-/
instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E) := by
  constructor
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  simpa using isCompact_setOfPred_finiteMeasure_eq_of_compactSpace E 1

/-- The set of finite measures of mass at most `C` supported on a given compact set `K` is
compact. -/
/-
**isCompact_setOfPred_finiteMeasure_le_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：isCompact_setOfPred_finiteMeasure_le_of_isCompact (C : Real>=0) {K : Set E
} (hK : IsCompact K) : IsCompact {μ : FiniteMeasure E | μ.mass <= C ∧ μ Kᶜ = 0}
参数：C : Real>=0；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.subtypeVal`：Topology.IsClosedEmbedding.subtyp
eVal (h : IsClosed {a | p a}) : IsClosedEmbedding ((↑) : Subtype p -> X)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.FiniteMeasure.mass_comap_le`：mass_comap_le (f : Ω -> Ω') (
μ : FiniteMeasure Ω') : (μ.comap f).mass <= μ.mass
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.FiniteMeasure.null_iff_toMeasure_null`：null_iff_toMeasure_
null (ν : FiniteMeasure Ω) (s : Set Ω) : ν s = 0 ↔ (ν : Measure Ω) s = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The set of finite measures of mass at most `C` supported on a given compact set 
`K` is
compact.
-/
lemma isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (C : ℝ≥0) {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} := by
  let f : K → E := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  let F : FiniteMeasure K → FiniteMeasure E := fun μ ↦ μ.map f
  let T : Set (FiniteMeasure K) := {μ | μ.mass ≤ C}
  have : {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} = F '' T := by
    apply Subset.antisymm
    · intro μ hμ
      simp only [mem_image]
      refine ⟨μ.comap f, (FiniteMeasure.mass_comap_le _ _).trans hμ.1, ?_⟩
      ext s hs
      simp only [toMeasure_map, F]
      rw [Measure.map_apply measurable_subtype_coe hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ (Subtype.val_injective), image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        apply (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp
        rw [rf]
        exact hμ.2
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs
    · simp only [null_iff_toMeasure_null, image_subset_iff, preimage_ofPred_eq, toMeasure_map,
        ofPred_subset_ofPred, F, T]
      intro μ hμ
      rw [Measure.map_apply hf.continuous.measurable hK.measurableSet.compl]
      refine ⟨(mass_map_le _ _).trans hμ, by simp [f]⟩
  rw [this]
  apply IsCompact.image _ (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_setOfPred_finiteMeasure_le_of_compactSpace _ _

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_finiteMeasure_le_of_isCompact :=
  isCompact_setOfPred_finiteMeasure_le_of_isCompact

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending
to zero, the finite measures of mass at most `C` giving mass at most `uₙ` to the complement of `Kₙ`
form a compact set. -/
/-
**isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le {u : Nat -> R
eal>=0} {K : Nat -> Set E} (C : Real>=0) (hu : Tendsto u atTop (𝓝 0)) (hK : fora
ll n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) : IsCompact {μ : FiniteM
easure E | μ.mass <= C ∧ forall n, μ (K n)ᶜ <= u n}
参数：C : Real>=0；hu : Tendsto u atTop (𝓝 0)；hK : forall n, IsCompact (K n)；h : Nor
malSpace E ∨ Monotone K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `biUnion_range_succ_disjointed`：biUnion_range_succ_disjointed {α : Type*}
 (f : Nat -> Set α) (n : Nat) : (⋃ i in Finset.range (n + 1), disjointed f i) = 
partialSups f n
· 使用引理 `MeasureTheory.FiniteMeasure.restrict_biUnion_finset`：restrict_biUnion_fi
nset {ι : Type*} {μ : FiniteMeasure Ω} {T : Finset ι} {s : ι -> Set Ω} (hd : (T 
: Set ι).Pairwise (Disjoint on s)) (hm : …
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Set.partialSups_eq_accumulate`：partialSups_eq_accumulate (f : Nat -> Set
 α) : partialSups f = accumulate f
· 使用定理 `isCompact_accumulate`：isCompact_accumulate {K : Nat -> Set X} (hK : fora
ll n, IsCompact (K n)) (n : Nat) : IsCompact (accumulate K n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_ultrafilter_le_nhds'`：isCompact_iff_ultrafilter_le_nhds' :
 IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `Ultrafilter.coe_map`：coe_map (m : α -> β) (f : Ultrafilter α) : (map m f
 : Filter β) = Filter.map m ↑f
· 使用定理 `IsCompact.ultrafilter_le_nhds'`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, ↑f ≤ nhd
s x
· 使用引理 `isCompact_setOfPred_finiteMeasure_le_of_isCompact`：isCompact_setOfPred_f
initeMeasure_le_of_isCompact (C : Real>=0) {K : Set E} (hK : IsCompact K) : IsCo
mpact {μ : FiniteMeasure E | μ.mass <= …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.FiniteMeasure.restrict_mass`：restrict_mass (μ : FiniteMeas
ure Ω) (A : Set Ω) : (μ.restrict A).mass = μ A
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.FiniteMeasure.apply_le_mass`：∀ {Ω : Type u_1} [inst : Meas
urableSpace Ω] (μ : MeasureTheory.FiniteMeasure Ω) (s : Set Ω), μ s ≤ μ.mass
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 200 条，此处仅展示前 30 条）

--- 原说明 ---
**Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ`
 tending
to zero, the finite measures of mass at most `C` giving mass at most `uₙ` to the
 complement of `Kₙ`
form a compact set.
-/
lemma isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
    {u : ℕ → ℝ≥0} {K : ℕ → Set E} (C : ℝ≥0)
    (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  /- Consider a sequence of measures with mass at most `C` and giving mass at most `uₙ` to `Kₙᶜ`,
  for which we want to find a converging subsequence.
  We want to write `⋃ n, Kₙ` as the disjoint union of `disjointed K n`, restrict the measures to
  each of these sets (which is contained in the compact set `Kₙ`), extract a converging subsequence
  there, to a limit `νₙ`, and then argue that the sequence converges to `μ := ∑ νₙ`.
  We will implement this rough idea, but there are two technical complications.
  First, we should not use a sequence and subsequences, but a ultrafilter as things are not second
  countable.
  Second, it is not obvious that the limit will satisfy the inequality `μ (Kₙᶜ) ≤ uₙ`, as this is
  not a closed condition in the space of measures in general (note that we are not assuming that
  our space is metrizable). To check this inequality, we need the technical condition that the
  space is normal or the sequence `K` is monotone. When the space is normal, the inequality can be
  proved from the weak convergence if we can ensure additionally that `μ` is
  inner regular. We will guarantee this by making sure each `νₙ` is inner regular. When the
  sequence `K` is monotone, on the other hand, the bound readily follows from the construction.
  -/
  -- We can decompose a measure as a sum of restrictions to `disjointed K n`, finite version.
  have I (μ : FiniteMeasure E) (n : ℕ) :
      ∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i) = μ.restrict (partialSups K n) := by
    rw [← biUnion_range_succ_disjointed, FiniteMeasure.restrict_biUnion_finset]
    · exact (disjoint_disjointed K).set_pairwise _
    · exact MeasurableSet.disjointed (fun i ↦ (hK i).measurableSet)
  have A n : IsCompact (partialSups K n) := by
    simpa [partialSups_eq_accumulate] using isCompact_accumulate hK _
  -- start with a ultrafilter `f`, for which we want to prove convergence.
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  -- the restrictions to `disjointed K n` converge along the ultrafilter, and moreover we can
  -- choose the limit to be inner regular.
  have M n : ∃ (ν : FiniteMeasure E), Measure.InnerRegular (ν : Measure E) ∧
      ν (partialSups K n)ᶜ = 0 ∧
      Tendsto (fun (ρ : FiniteMeasure E) ↦ ρ.restrict (disjointed K n)) f (𝓝 ν) := by
    -- the existence of a limit follows from the fact that these measures are supported in
    -- the compact set `partialSups K n`.
    obtain ⟨ν, hν, ν_lim⟩ : ∃ ν ∈ {ρ : FiniteMeasure E | ρ.mass ≤ C ∧ ρ (partialSups K n)ᶜ = 0},
        Tendsto (fun (ρ : FiniteMeasure E) ↦ ρ.restrict (disjointed K n)) f (𝓝 ν) := by
      simp only [Tendsto]
      rw [← Ultrafilter.coe_map]
      apply IsCompact.ultrafilter_le_nhds'
        (isCompact_setOfPred_finiteMeasure_le_of_isCompact C (A n))
      simp only [null_iff_toMeasure_null, Ultrafilter.mem_map, preimage_ofPred_eq]
      filter_upwards [hf] with ρ hρ
      simp only [restrict_mass, restrict_measure_eq,
        Measure.restrict_apply (A n).measurableSet.compl]
      refine ⟨(apply_le_mass ρ _).trans hρ.1, ?_⟩
      convert! measure_empty (μ := (ρ : Measure E))
      apply disjoint_iff.1
      apply disjoint_compl_left.mono_right
      exact le_trans sdiff_le (le_partialSups _ _)
    -- We can find an inner regular measure which coincides with the above limit wrt
    -- integration of bounded continuous functions.
    obtain ⟨ν', ν'_reg, ν'_fin, ν'K, hν'⟩ : ∃ ν', ν'.InnerRegular ∧ IsFiniteMeasure ν' ∧
        ν' (partialSups K n)ᶜ = 0 ∧ ∀ (g : E →ᵇ ℝ), ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
      apply Measure.exists_innerRegular_eq_of_isCompact _ (A n)
      rw [← MeasureTheory.FiniteMeasure.null_iff_toMeasure_null]
      exact hν.2
    -- This inner regular measure is also a limit for our ultrafilter
    let μ : FiniteMeasure E := ⟨ν', ν'_fin⟩
    refine ⟨μ, ν'_reg, by simp [μ, ν'K], ?_⟩
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    convert! tendsto_iff_forall_integral_tendsto.1 ν_lim g using 2
    exact (hν' g).symm
  -- let `νₙ` be such nice limits on `disjointed K n`.
  choose! ν ν_reg νK hν using M
  -- their sum is a finite measure, of mass at most `C`.
  have B : (Measure.sum (fun n ↦ (ν n : Measure E))) univ ≤ C := by
    -- this follows from the corresponding result for finite sums, where we can use the
    -- continuity of the mass of a finite measure under weak convergence.
    simp only [MeasurableSet.univ, Measure.sum_apply]
    have : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ) atTop
        (𝓝 (∑' i, (ν i : Measure E) univ)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    apply le_of_tendsto' this (fun n ↦ ?_)
    have : ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ
        = (∑ i ∈ Finset.range (n + 1), ν i).toMeasure univ := by simp
    rw [this]
    suffices (∑ i ∈ Finset.range (n + 1), ν i).mass ≤ C by
      convert! ENNReal.coe_le_coe.2 this
      simp
    have : Tendsto (fun (μ : FiniteMeasure E) ↦
        (∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i)).mass) f
        (𝓝 ((∑ i ∈ Finset.range (n + 1), ν i).mass)) := by
      apply Tendsto.mass
      exact tendsto_finsetSum _ (fun i hi ↦ hν i)
    apply le_of_tendsto this
    filter_upwards [hf] with μ hμ
    rw [I, restrict_mass]
    exact le_trans (apply_mono _ (subset_univ _)) hμ.1
  -- Let `μ` be the limiting measure
  let μ : FiniteMeasure E := ⟨Measure.sum (fun n ↦ (ν n : Measure E)), ⟨B.trans_lt (by simp)⟩⟩
  -- first, we show that it is indeed a limit of the ultrafilter
  have L : Tendsto id f (𝓝 μ) := by
    -- We need to check the convergence of the integral of a bounded continuous function.
    -- Finite sums of restrictions to `disjointed K n` converge obviously to finite sums of `νₙ`,
    -- but we need to control the infinite sums. For this, we split `ε` in 3, argue that for `μ`
    -- this is the limit of finite sums, and inside the space we can uniformly truncate the sum
    -- also as the tail is controlled by `uₙ`. Once we have fixed a truncation level satisfying
    -- both conditions, we can rely on the finite sum convergence to conclude.
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    rw [Metric.tendsto_nhds]
    intro ε εpos
    -- first, control truncation of the finite sums for the limiting measure
    have I1 : ∀ᶠ n in atTop,
        dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ x, g x ∂μ) < ε / 3 := by
      have : Tendsto (fun n ↦ ∫ x, g x ∂(∑ i ∈ Finset.range n, ν i)) atTop (𝓝 (∫ x, g x ∂μ)) := by
        simp only [FiniteMeasure.toMeasure_mk, μ]
        rw [integral_sum_measure (g.integrable (μ := μ))]
        simp_rw [integral_finsetSum_measure (fun i hi ↦ g.integrable _)]
        apply Summable.tendsto_sum_tsum_nat
        apply (hasSum_integral_measure _).summable
        exact g.integrable (μ := μ)
      exact Metric.tendsto_nhds.1 (this.comp (tendsto_add_atTop_nat 1)) _ (by positivity)
    -- second, truncation threshold in terms of tails `uₙ` (the relevance of this condition will
    -- appear below).
    have I2 : ∀ᶠ n in atTop, ‖g‖ * u n < ε / 3 := by
      have := (NNReal.tendsto_coe.2 hu).const_mul (‖g‖)
      simp only [NNReal.coe_zero, mul_zero] at this
      exact (tendsto_order.1 this).2 (ε / 3) (by positivity)
    -- fix a large `n` satisfying both truncation conditions
    rcases (I1.and I2).exists with ⟨n, hn, h'n⟩
    -- the finite sums up to the fixed `n` converge to the limit, by convergence of individual
    -- summands
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦
        ∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) : FiniteMeasure E)) f
        (𝓝 (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i : FiniteMeasure E))) := by
      apply tendsto_iff_forall_integral_tendsto.1 _ g
      apply tendsto_finsetSum _ (fun i hi ↦ hν i)
    -- therefore, after some point the difference is bounded by `ε / 3`.
    filter_upwards [Metric.tendsto_nhds.1 this (ε / 3) (by positivity), hf] with ρ hρ h'ρ
    -- let us show that in this case the full integrals differ by at most `ε`.
    calc dist (∫ (x : E), g x ∂ρ) (∫ (x : E), g x ∂μ)
    -- we separate away the tails from the sums up to `n`
    _ ≤ dist (∫ (x : E), g x ∂ρ)
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ (x : E), g x ∂μ) :=
      dist_triangle4 _ _ _ _
    -- each term is bounded by `ε / 3` by design.
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · have : ρ = ρ.restrict (partialSups K n)ᶜ +
            ∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) := by
          rw [I, ← FiniteMeasure.restrict_union disjoint_compl_left (A n).measurableSet]
          simp
        nth_rewrite 1 [this]
        rw [toMeasure_add, integral_add_measure (g.integrable _) (g.integrable _)]
        simp only [toMeasure_sum, dist_add_self_left]
        calc ‖∫ x, g x ∂(ρ.restrict ((partialSups K) n)ᶜ)‖
        _ ≤ ∫ x, ‖g x‖ ∂(ρ.restrict ((partialSups K) n)ᶜ) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖g‖ ∂(ρ.restrict ((partialSups K) n)ᶜ : Measure E) := by
          apply integral_mono_of_nonneg
          · filter_upwards with x using by positivity
          · simp
          · filter_upwards with x using norm_coe_le_norm g x
        _ = ‖g‖ * ρ ((partialSups K) n)ᶜ := by simp [mul_comm]
        _ ≤ ‖g‖ * ρ (K n)ᶜ := by gcongr; apply le_partialSups
        _ ≤ ‖g‖ * u n := by gcongr; exact h'ρ.2 n
        _ < ε / 3 := h'n
      · simpa using hρ
    _ = ε := by ring
  -- Now that we have proved the convergence, we can finish the proof of the theorem. It remains
  -- to check the mass control of the limit (which we have already done when proving finiteness)
  -- and to show that `μ (Kₙᶜ) ≤ uₙ`, which is harder.
  refine ⟨μ, ⟨?_, fun n ↦ ?_⟩, L⟩
  · simp only [mass, mk_apply, μ]
    rw [show C = (C : ℝ≥0∞).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) B
  -- Let us now prove that `μ (Kₙᶜ) ≤ uₙ`. We argue differently depending on whether the space is
  -- normal or if the sequence `K` is monotone.
  rcases h with h | h
  · -- To show that `μ (Kₙᶜ) ≤ uₙ` when the space is normal, we argue that `μ (Kₙᶜ)` is the
    -- supremum of the integrals of continuous functions supported in `Kₙᶜ` and bounded by `1`,
    -- as the measure is inner regular. Therefore, we are reduced to a question about integrals of
    -- continuous functions, for which we can take advantage of the weak convergence.
    have : Measure.InnerRegular (μ : Measure E) := by simp only [toMeasure_mk, μ]; infer_instance
    rw [← ENNReal.coe_le_coe, ennreal_coeFn_eq_coeFn_toMeasure,
      (hK n).isClosed.isOpen_compl.measure_eq_biSup_integral_continuous]
    simp only [compl_compl, iSup_le_iff, ENNReal.ofReal_le_coe]
    intro g g_cont gK g_nonneg g_le
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦ ∫ x, g x ∂ρ) f (𝓝 (∫ x, g x ∂μ)) := by
      let g' : E →ᵇ ℝ :=
      { toFun := g
        map_bounded' := by
          refine ⟨1, fun x y ↦ ?_⟩
          simp only [dist, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
          exact ⟨(g_le y).trans (by simpa using g_nonneg x),
            (g_le x).trans (by simpa using g_nonneg y)⟩ }
      exact tendsto_iff_forall_integral_tendsto.1 L g'
    apply le_of_tendsto this
    filter_upwards [hf] with ρ hρ
    calc ∫ x, g x ∂ρ
    _ ≤ ∫ x, indicator (K n)ᶜ 1 x ∂ρ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x using g_nonneg x
      · apply Integrable.indicator (integrable_const _) (hK n).measurableSet.compl
      · filter_upwards [] with x
        by_cases hx : x ∈ (K n)ᶜ
        · simpa [hx] using g_le x
        · simp only [hx, not_false_eq_true, indicator_of_notMem]
          apply le_of_eq
          apply gK
          simpa using hx
    _ = ρ (K n)ᶜ := by simp [integral_indicator (hK n).measurableSet.compl]
    _ ≤ u n := mod_cast hρ.2 n
  · -- to show that `μ (Kₙᶜ) ≤ uₙ` when the sequence `K` is monotone, we argue that the only
    -- contribution to `μ (Kₙᶜ)` comes from the measures `νᵢ` with `i > n`. Then we restrict to
    -- a finite sum `∑ i ∈ Ioc n m, νᵢ`, and argue that it is the limit of
    -- `∑ i ∈ Ioc n m, ρ.restricted (K i \ K(i - 1))`, i.e., `ρ.restricted (K m \ K n)`. The total
    -- mass converges (thanks to the weak convergence of finite sums), and the total mass of
    -- `ρ.restricted (K m \ K n)` is bounded by `ρ (Kₙᶜ) ≤ uₙ`.
    suffices (μ : Measure E) (K n)ᶜ ≤ u n by
      apply ENNReal.coe_le_coe.1
      convert! this
      simp
    simp only [toMeasure_mk, (hK n).measurableSet.compl, Measure.sum_apply, μ]
    have : Tendsto (fun m ↦ ∑ i ∈ Finset.range (m + 1), (ν i : Measure E) (K n)ᶜ) atTop
        (𝓝 (∑' i, (ν i : Measure E) (K n)ᶜ)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    apply le_of_tendsto this
    filter_upwards [Ici_mem_atTop n] with m (hm : n ≤ m)
    have : ∑ i ∈ Finset.range (m + 1), (ν i : Measure E) (K n)ᶜ
        = ∑ i ∈ Finset.Ioc n m, (ν i : Measure E) (K n)ᶜ := by
      apply (Finset.sum_subset (by grind) _).symm
      simp +contextual only [Finset.mem_range_succ_iff, Finset.mem_Ioc, not_and,
        not_true_eq_false, imp_false, not_lt, ← null_iff_toMeasure_null]
      intro i hi h'i
      apply (ν i).mono_null _ (νK i)
      rw [Monotone.partialSups_eq h]
      exact compl_subset_compl.2 (h h'i)
    rw [this]
    suffices (∑ i ∈ Finset.Ioc n m, ν i).toMeasure univ ≤ u n by
      apply le_trans _ this
      simp only [toMeasure_sum, Measure.coe_finsetSum, Finset.sum_apply]
      gcongr
      simp
    suffices (∑ i ∈ Finset.Ioc n m, ν i).mass ≤ u n by
      convert! ENNReal.coe_le_coe.2 this
      simp
    have : Tendsto (fun (μ : FiniteMeasure E) ↦
        (∑ i ∈ Finset.Ioc n m, μ.restrict (disjointed K i)).mass) f
        (𝓝 ((∑ i ∈ Finset.Ioc n m, ν i).mass)) := by
      apply Tendsto.mass
      exact tendsto_finsetSum _ (fun i hi ↦ hν i)
    apply le_of_tendsto this
    filter_upwards [hf] with μ hμ
    have : ∑ i ∈ Finset.Ioc n m, μ.restrict (disjointed K i) = μ.restrict (K m \ K n) := by
      rw [← biUnion_Ioc_disjointed_of_monotone h hm, FiniteMeasure.restrict_biUnion_finset]
      · exact (disjoint_disjointed K).set_pairwise _
      · exact MeasurableSet.disjointed (fun i ↦ (hK i).measurableSet)
    rw [this, restrict_mass]
    exact le_trans (apply_mono _ (sdiff_subset_compl (K m) (K n))) (hμ.2 n)

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le :=
  isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending to
zero, the finite measures of mass `C` giving mass at most `uₙ` to the complement of `Kₙ` form a
compact set. -/
/-
**isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le {u : Nat -> R
eal>=0} {K : Nat -> Set E} (C : Real>=0) (hu : Tendsto u atTop (𝓝 0)) (hK : fora
ll n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) : IsCompact {μ : FiniteM
easure E | μ.mass = C ∧ forall n, μ (K n)ᶜ <= u n}
参数：C : Real>=0；hu : Tendsto u atTop (𝓝 0)；hK : forall n, IsCompact (K n)；h : Nor
malSpace E ∨ Monotone K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用引理 `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`：isCompact_
setOfPred_finiteMeasure_mass_le_compl_isCompact_le {u : Nat -> Real>=0} {K : Nat
 -> Set E} (C : Real>=0) (hu : Tendsto u atTop (𝓝 …
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.FiniteMeasure.continuous_mass`：∀ {Ω : Type u_1} [inst : Me
asurableSpace Ω] [inst_1 : TopologicalSpace Ω] [inst_2 : OpensMeasurableSpace Ω]
,   Continuous fun μ => μ.mass
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
**Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ`
 tending to
zero, the finite measures of mass `C` giving mass at most `uₙ` to the complement
 of `Kₙ` form a
compact set.
-/
lemma isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (C : ℝ≥0) (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  have : {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} =
    {μ | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} ∩ {μ | μ.mass = C} := by ext; grind
  rw [this]
  apply IsCompact.inter_right
    (isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le C hu hK h)
  exact isClosed_eq (by fun_prop) (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le :=
  isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending to
zero, the probability measures giving mass at most `uₙ` to the complement of `Kₙ` form a
compact set. -/
/-
**isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le {u : Nat
 -> Real>=0} {K : Nat -> Set E} (hu : Tendsto u atTop (𝓝 0)) (hK : forall n, IsC
ompact (K n)) (h : NormalSpace E ∨ Monotone K) : IsCompact {μ : ProbabilityMeasu
re E | forall n, μ (K n)ᶜ <= u n}
参数：hu : Tendsto u atTop (𝓝 0)；hK : forall n, IsCompact (K n)；h : NormalSpace E ∨
 Monotone K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding`：toFiniteMe
asure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMea
surableSpace Ω] : IsEmbedding (toFiniteMeasure : P…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure`：mass_toFiniteMeas
ure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MeasureTheory.isProbabilityMeasure_iff_real`：isProbabilityMeasure_iff_re
al {μ : Measure α} : IsProbabilityMeasure μ ↔ μ.real univ = 1
· 使用定理 `MeasureTheory.FiniteMeasure.eq_of_forall_toMeasure_apply_eq`：eq_of_foral
l_toMeasure_apply_eq (μ ν : FiniteMeasure Ω) (h : forall s : Set Ω, MeasurableSe
t s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le`：isCompact_
setOfPred_finiteMeasure_mass_eq_compl_isCompact_le {u : Nat -> Real>=0} {K : Nat
 -> Set E} (C : Real>=0) (hu : Tendsto u atTop (𝓝 …

--- 原说明 ---
**Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ`
 tending to
zero, the probability measures giving mass at most `uₙ` to the complement of `Kₙ
` form a
compact set.
-/
lemma isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n} := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  have : ProbabilityMeasure.toFiniteMeasure '' {μ | ∀ (n : ℕ), μ (K n)ᶜ ≤ u n}
      = {μ : FiniteMeasure E | μ.mass = 1 ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
    ext μ
    simp only [mem_image, mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨ν, hν, rfl⟩
      simpa using! hν
    · rintro ⟨hμ, h'μ⟩
      let ν : ProbabilityMeasure E := ⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! hμ)⟩
      have : ν.toFiniteMeasure = μ := by ext; rfl
      exact ⟨ν, by simpa [← this] using! h'μ , this⟩
  rw [this]
  exact isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le 1 hu hK h

@[deprecated (since := "2026-07-09")]
alias isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le :=
  isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le

/-- **Prokhorov theorem**: the closure of a tight set of probability measures is compact.
We only require the space to be T2. -/
/-
**isCompact_closure_of_isTightMeasureSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)} (h
S : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ in S}) : IsC
ompact (closure S)
参数：ProbabilityMeasure E；hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Me
asure E) | μ in S}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用引理 `isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le`：isCom
pact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le {u : Nat -> Real>=0
} {K : Nat -> Set E} (hu : Tendsto u atTop (𝓝 0)) (hK :…
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
**Prokhorov theorem**: the closure of a tight set of probability measures is com
pact.
We only require the space to be T2.
-/
lemma isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have A n : ∃ (K : Set E), IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ u n := by
    rcases isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hS (u n)
      (by norm_cast; exact u_pos n) with ⟨K, K_comp, hK⟩
    refine ⟨K, K_comp, fun μ hμ ↦ ?_⟩
    have : (μ : Measure E) Kᶜ ≤ u n := hK _ ⟨μ, hμ, rfl⟩
    exact ENNReal.coe_le_coe.1 (by simpa using this)
  choose K K_comp hK using A
  let K' n := ⋃ i ∈ Iic n, K i
  have h'K : IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K' n)ᶜ ≤ u n} := by
    apply isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le u_lim
    · exact fun n ↦ (finite_Iic n).isCompact_biUnion (fun i hi ↦ K_comp i)
    · right
      simp only [Monotone, mem_Iic, iUnion_subset_iff, K']
      intro a b hab i hi
      apply subset_biUnion_of_mem
      exact hi.trans hab
  apply IsCompact.closure_of_subset h'K
  intro μ hμ n
  calc μ (K' n)ᶜ
  _ ≤ μ (K n)ᶜ := by
    gcongr
    simp only [mem_Iic, K']
    apply subset_biUnion_of_mem
    exact le_rfl (a := n)
  _ ≤ u n := by grind

end Forward

section Backward

open ProbabilityMeasure

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} [PseudoMetricSpace 𝓧]
  [OpensMeasurableSpace 𝓧] [SecondCountableTopology 𝓧] {S : Set (ProbabilityMeasure 𝓧)}

/-
**MeasureTheory.exists_measure_iUnion_gt_of_isCompact_closure** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measure_iUnion_gt_of_isCompact_closure (U : Nat -> Set 𝓧) (O : fora
ll i, IsOpen (U i)) (Cov : ⋃ i, U i = univ) (hcomp : IsCompact (closure S)) (ε :
 Real>=0∞) (hε : 0 < ε) (hεbound : ε <= 1) : exists (k : Nat), forall μ in S, 1 
- ε < μ (⋃ i <= k, U i)
参数：U : Nat -> Set 𝓧；O : forall i, IsOpen (U i)；Cov : ⋃ i, U i = univ；hcomp : IsC
ompact (closure S)；ε : Real>=0∞；hε : 0 < ε；hεbound : ε <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `MeasureTheory.instPseudoMetrizableSpaceProbabilityMeasureOfSeparableSpac
e`：∀ (X : Type u_2) [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizab
leSpace X]   [TopologicalSpace.SeparableSpace X] [inst_3 : Meas…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`：∀ {Ω
 : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] [inst_1 : 
TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
· 使用定理 `instHasOuterApproxClosedOfPseudoMetrizableSpace`：∀ (X : Type u_1) [inst 
: TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], HasOuterApprox
Closed X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNReal.toReal_liminf`：toReal_liminf : liminf (fun i => (u i : Real)) f =
 liminf u f
· 使用引理 `ENNReal.ofNNReal_liminf`：ofNNReal_liminf {u : ι -> Real>=0} (hf : f.IsCo
boundedUnder (· >= ·) u) : liminf u f = liminf (fun i => (u i : Real>=0∞)) f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
（共 125 条，此处仅展示前 30 条）
-/
lemma exists_measure_iUnion_gt_of_isCompact_closure
    (U : ℕ → Set 𝓧) (O : ∀ i, IsOpen (U i)) (Cov : ⋃ i, U i = univ) (hcomp : IsCompact (closure S))
    (ε : ℝ≥0∞) (hε : 0 < ε) (hεbound : ε ≤ 1) :
    ∃ (k : ℕ), ∀ μ ∈ S, 1 - ε < μ (⋃ i ≤ k, U i) := by
  have εfin : ε ≠ ∞ := ne_top_of_le_ne_top (by simp) hεbound
  lift ε to ℝ≥0 using εfin
  obtain ⟨ε, hε', rfl⟩ : ∃ (ε' : ℝ) (hε' : 0 ≤ ε'), ε = .mk ε' hε' := ⟨↑ε, ε.2, rfl⟩
  simp only [ENNReal.coe_pos, ← NNReal.coe_lt_coe, NNReal.coe_zero, coe_mk, coe_le_one_iff,
      ← NNReal.coe_le_coe, NNReal.coe_one] at hε hεbound
  by_contra! nh
  choose μ hμInS hcontradiction using nh
  obtain ⟨μlim, _, sub, hsubmono, hμconverges⟩ :=
      hcomp.isSeqCompact (fun n ↦ subset_closure <| hμInS n)
  have Measurebound n : (μlim (⋃ (i ≤ n), U i) : ℝ) ≤ 1 - ε := calc
    (μlim (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := isOpen_biUnion fun i a ↦ O i
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμconverges hopen
      simp_rw [Function.comp_apply, ← ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [← ofNNReal_liminf] at this
      · exact mod_cast this
      use 1
      simpa [eventually_map, eventually_atTop, forall_exists_index] using fun _ x h ↦
          (h x (by simp)).trans <| ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono
            <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        exact le_trans (Nat.le_add_right n 1) (le_trans hypo (StrictMono.le_apply hsubmono))
      · use 0; simp
      · use 1
        simpa [eventually_map, eventually_atTop, forall_exists_index] using
            fun _ d hyp ↦ (hyp d (by simp)).trans (by simp)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0; simp
      simp only [eventually_atTop, forall_exists_index]
      intro b c h
      apply le_trans (h c le_rfl)
      refine (ofReal_le_ofReal_iff (by rw [sub_nonneg]; exact hεbound)).mp ?_
      rw [ofReal_coe_nnreal]
      apply le_trans (hcontradiction (sub c))
      norm_cast
  have accumulation : Tendsto (fun n ↦ μlim (⋃ i ≤ n, U i)) atTop (𝓝 (μlim (⋃ i, U i))) := by
    simp_rw [← Set.accumulate_def, ProbabilityMeasure.tendsto_measure_iUnion_accumulate]
  rw [Cov, coeFn_univ, ← NNReal.tendsto_coe] at accumulation
  have exceeds_bound : ∀ᶠ n in atTop, (1 - ε / 2 : ℝ) ≤ μlim (⋃ i ≤ n, U i) :=
      Tendsto.eventually_const_le (v := 1)
        (by simp only [sub_lt_self_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right]; positivity)
        accumulation
  suffices ∀ᶠ n : ℕ in atTop, False from this.exists.choose_spec
  filter_upwards [exceeds_bound] with n hn
  linarith [hn.trans <| Measurebound n]

variable [CompleteSpace 𝓧]

/-- In a second countable complete metric space, a set of probability measures with compact closure
is tight. -/
/-
**MeasureTheory.isTightMeasureSet_of_isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：isTightMeasureSet_of_isCompact_closure (hcomp : IsCompact (closure S)) : I
sTightMeasureSet {((μ : ProbabilityMeasure 𝓧) : Measure 𝓧) | μ in S}
参数：hcomp : IsCompact (closure S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TopologicalSpace.exists_dense_seq`：exists_dense_seq [SeparableSpace α] [
Nonempty α] : exists u : Nat -> α, DenseRange u
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
（共 156 条，此处仅展示前 30 条）

--- 原说明 ---
In a second countable complete metric space, a set of probability measures with 
compact closure
is tight.
-/
theorem isTightMeasureSet_of_isCompact_closure (hcomp : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure 𝓧) : Measure 𝓧) | μ ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  rcases isEmpty_or_nonempty 𝓧 with hempty | hnonempty
  · rw [← univ_eq_empty_iff] at hempty
    exact fun ε εpos ↦ ⟨∅, isCompact_empty, by simp [hempty]⟩
  obtain ⟨D, hD⟩ := exists_dense_seq 𝓧
  obtain ⟨u, hu_anti, hu_pos, hu⟩ : ∃ u, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have hcov (m : ℕ) : ⋃ i, ball (D i) (u m) = univ := by
    rw [denseRange_iff] at hD
    ext p
    exact ⟨fun a ↦ trivial, fun _ ↦ mem_iUnion.mpr <| hD p (u m) (hu_pos m)⟩
  intro ε εpos
  rcases lt_or_ge 1 ε with hεbound | hεbound
  · refine ⟨∅, isCompact_empty, fun μ hμ ↦ ?_⟩
    simp only [mem_ofPred_eq] at hμ
    obtain ⟨μ', hμ', rfl⟩ := hμ
    rw [compl_empty, measure_univ]
    exact le_of_lt hεbound
  have byclaim (m : ℕ) : ∃ k, ∀ μ ∈ S, 1 - (ε * 2 ^ (-m : ℤ) : ℝ≥0∞) <
      μ (⋃ i ≤ k, ball (D i) (u m)) := by
    refine exists_measure_iUnion_gt_of_isCompact_closure
      (fun i ↦ ball (D i) (u m)) (fun _ ↦ isOpen_ball) (hcov m) hcomp (ε * 2 ^ (-m : ℤ)) ?_ ?_
    · simpa using ⟨εpos, (ENNReal.zpow_pos (by simp) (by simp) (-↑m))⟩
    · exact Left.mul_le_one hεbound <| zpow_le_one_of_nonpos (by linarith) (by simp)
  choose! km hbound using byclaim
  -- This is a set we can construct to show tightness
  let bigK := ⋂ m, ⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m))
  have bigcalc (μ : ProbabilityMeasure 𝓧) (hs : μ ∈ S) : μ.toMeasure bigKᶜ ≤ ε := calc
    μ.toMeasure bigKᶜ
    _ = μ.toMeasure (⋃ m, (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))ᶜ) := by simp [bigK]
    _ ≤ ∑' m, μ.toMeasure (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))ᶜ :=
      measure_iUnion_le _
    _ = ∑' m, (1 - μ.toMeasure (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))) := by
      congr! with m; rw [measure_compl (by measurability) (by simp)]; simp
    _ ≤ (∑' (m : ℕ), (ε : ℝ≥0∞) * 2 ^ (-(m + 1) : ℤ)) := by
      refine ENNReal.tsum_le_tsum fun m ↦ tsub_le_iff_tsub_le.mp ?_
      replace hbound := (hbound (m + 1) μ hs).le
      simp_all only [neg_add_rev, Int.reduceNeg, tsub_le_iff_right, Nat.cast_add, Nat.cast_one,
          ← coe_ofNat, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      grw [hbound]
      gcongr with i hi
      grw [← subset_closure (s := ball (D i) (u m)), ball_subset_ball]
      exact hu_anti.antitone (by grind)
    _ = ε := by
      rw [ENNReal.tsum_mul_left]
      nth_rw 2 [← mul_one (a := ε)]
      congr
      ring_nf
      exact tsum_two_zpow_neg_add_one
  -- Final proof
  refine ⟨bigK, ?_, by simpa⟩
  -- Compactness first
  refine TotallyBounded.isCompact_of_isClosed ?_ ?_
  --Totally bounded
  · refine Metric.totallyBounded_iff.mpr fun δ δpos ↦ ?_
    have ⟨δ_inv, hδ_inv⟩ : ∃ x, u x < δ := (Tendsto.eventually_lt_const δpos hu).exists
    refine ⟨D '' .Iic (km (δ_inv + 1)), (Set.finite_Iic _).image _, ?_⟩
    -- t should be image under D of the set of numbers less than km of δ_inv
    simp only [mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, bigK]
    calc
        ⋂ m, ⋃ i ≤ km (m + 1), closure (ball (D i) (u m))
    _ ⊆ ⋃ i ≤ km (δ_inv + 1), closure (ball (D i) (u δ_inv)) := iInter_subset ..
    _ ⊆ ⋃ i ≤ km (δ_inv + 1), ball (D i) δ := by
        gcongr
        exact closure_ball_subset_closedBall.trans <| closedBall_subset_ball <| hδ_inv
  -- Closedness
  · simp_rw [bigK, ← Set.mem_Iic]
    exact isClosed_iInter fun n =>
      Finite.isClosed_biUnion (finite_Iic _) (fun _ _ ↦ isClosed_closure)

end MeasureTheory -- namespace

end Backward

