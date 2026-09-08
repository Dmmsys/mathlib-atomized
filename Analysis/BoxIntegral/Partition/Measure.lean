/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Additive
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Box-additive functions defined by measures

In this file we prove a few simple facts about rectangular boxes, partitions, and measures:

- given a box `I : Box ι`, its coercion to `Set (ι → ℝ)` and `I.Icc` are measurable sets;
- if `μ` is a locally finite measure, then `(I : Set (ι → ℝ))` and `I.Icc` have finite measure;
- if `μ` is a locally finite measure, then `fun J ↦ μ.real J` is a box additive function.

For the last statement, we both prove it as a proposition and define a bundled
`BoxIntegral.BoxAdditiveMap` function.

## Tags

rectangular box, measure
-/

@[expose] public section

open Set

noncomputable section

open scoped ENNReal BoxIntegral

variable {ι : Type*}

namespace BoxIntegral

open MeasureTheory

namespace Box

variable (I : Box ι)

/-
**BoxIntegral.Box.measure_Icc_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：measure_Icc_lt_top (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] : 
μ (Box.Icc I) < ∞
参数：μ : Measure (ι -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `BoxIntegral.Box.isCompact_Icc`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι),
 IsCompact (BoxIntegral.Box.Icc I)
-/
theorem measure_Icc_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ (Box.Icc I) < ∞ :=
  show μ (Icc I.lower I.upper) < ∞ from I.isCompact_Icc.measure_lt_top
/-
**BoxIntegral.Box.measure_coe_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：measure_coe_lt_top (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] : 
μ I < ∞
参数：μ : Measure (ι -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
· 使用定理 `BoxIntegral.Box.measure_Icc_lt_top`：measure_Icc_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ (Box.Icc I) < ∞
-/
theorem measure_coe_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ I < ∞ :=
  (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

section Countable

variable [Countable ι]

/-
**BoxIntegral.Box.measurableSet_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：measurableSet_coe : MeasurableSet (I : Set (ι -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem measurableSet_coe : MeasurableSet (I : Set (ι → ℝ)) := by
  rw [coe_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ioc
/-
**BoxIntegral.Box.measurableSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：measurableSet_Icc : MeasurableSet (Box.Icc I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem measurableSet_Icc : MeasurableSet (Box.Icc I) :=
  _root_.measurableSet_Icc
/-
**BoxIntegral.Box.measurableSet_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：measurableSet_Ioo : MeasurableSet (Box.Ioo I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem measurableSet_Ioo : MeasurableSet (Box.Ioo I) :=
  MeasurableSet.univ_pi fun _ => _root_.measurableSet_Ioo

end Countable

variable [Fintype ι]

/-
**BoxIntegral.Box.coe_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_ae_eq_Icc : (I : Set (ι -> Real)) =ᵐ[volume] Box.Icc I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc`：univ_pi_Ioc_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
-/
theorem coe_ae_eq_Icc : (I : Set (ι → ℝ)) =ᵐ[volume] Box.Icc I := by
  rw [coe_eq_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc
/-
**BoxIntegral.Box.Ioo_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：Ioo_ae_eq_Icc : Box.Ioo I =ᵐ[volume] Box.Icc I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc`：univ_pi_Ioo_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
-/
theorem Ioo_ae_eq_Icc : Box.Ioo I =ᵐ[volume] Box.Icc I :=
  Measure.univ_pi_Ioo_ae_eq_Icc

end Box

/-
**BoxIntegral.Prepartition.measure_iUnion_toReal** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.Prepartition`。
形式化陈述：∀ {ι : Type u_1} [Finite ι] {I : BoxIntegral.Box ι} (π : BoxIntegral.Prepa
rtition I) (μ : MeasureTheory.Measure (ι → ℝ))   [MeasureTheory.IsLocallyFiniteM
easure μ], μ.real π.iUnion = ∑ J ∈ π.boxes, μ.real ↑J
参数：π : BoxIntegral.Prepartition I；μ : MeasureTheory.Measure (ι → ℝ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoxIntegral.Box.measure_coe_lt_top`：measure_coe_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ I < ∞
· 使用定理 `BoxIntegral.Prepartition.iUnion_def`：iUnion_def : π.iUnion = ⋃ J in π, ↑
J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `BoxIntegral.Prepartition.pairwiseDisjoint`：∀ {ι : Type u_1} {I : BoxInte
gral.Box ι} (self : BoxIntegral.Prepartition I),   (↑self.boxes).Pairwise (Funct
ion.onFun Disjoint BoxIntegral.…
· 使用定理 `BoxIntegral.Box.measurableSet_coe`：measurableSet_coe : MeasurableSet (I 
: Set (ι -> Real))
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
theorem Prepartition.measure_iUnion_toReal [Finite ι] {I : Box ι} (π : Prepartition I)
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] :
    μ.real π.iUnion = ∑ J ∈ π.boxes, μ.real J := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun J _ => (J.measure_coe_lt_top μ).ne), π.iUnion_def]
  simp only [← mem_boxes]
  rw [measure_biUnion_finset π.pairwiseDisjoint]
  exact fun J _ => J.measurableSet_coe

end BoxIntegral

open BoxIntegral BoxIntegral.Box

namespace MeasureTheory

namespace Measure

/-- If `μ` is a locally finite measure on `ℝⁿ`, then `fun J ↦ μ.real J` is a box-additive
function. -/
@[simps]
/-
**MeasureTheory.Measure.toBoxAdditive** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：toBoxAdditive [Finite ι] (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure
 μ] : ι ->ᵇᵃ[⊤] Real where toFun J
参数：μ : Measure (ι -> Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is a locally finite measure on `ℝⁿ`, then `fun J ↦ μ.real J` is a box-add
itive
function.
-/
def toBoxAdditive [Finite ι] (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : ι →ᵇᵃ[⊤] ℝ where
  toFun J := μ.real J
  sum_partition_boxes' J _ π hπ := by rw [← π.measure_iUnion_toReal, hπ.iUnion_eq]

end Measure

end MeasureTheory

namespace BoxIntegral

open MeasureTheory

namespace Box

variable [Fintype ι]

-- This is not a `simp` lemma because the left-hand side simplifies already.
-- See `volume_apply'` for the relevant `simp` lemma.
/-
**BoxIntegral.Box.volume_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：volume_apply (I : Box ι) : (volume : Measure (ι -> Real)).toBoxAdditive I 
= ∏ i, (I.upper i - I.lower i)
参数：I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toBoxAdditive_apply`：∀ {ι : Type u_1} [inst : Fini
te ι] (μ : MeasureTheory.Measure (ι → ℝ)) [inst_1 : MeasureTheory.IsLocallyFinit
eMeasure μ]   (J : BoxIntegral.…
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Real.volume_pi_Ioc_toReal`：volume_pi_Ioc_toReal {a b : ι -> Real} (h : a
 <= b) : (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i)
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
-/
theorem volume_apply (I : Box ι) :
    (volume : Measure (ι → ℝ)).toBoxAdditive I = ∏ i, (I.upper i - I.lower i) := by
  rw [Measure.toBoxAdditive_apply, coe_eq_pi, measureReal_def,
    Real.volume_pi_Ioc_toReal I.lower_le_upper]

@[simp]
/-
**BoxIntegral.Box.volume_apply'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：volume_apply' (I : Box ι) : ((volume : Measure (ι -> Real)) I).toReal = ∏ 
i, (I.upper i - I.lower i)
参数：I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `Real.volume_pi_Ioc_toReal`：volume_pi_Ioc_toReal {a b : ι -> Real} (h : a
 <= b) : (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i)
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
-/
theorem volume_apply' (I : Box ι) :
    ((volume : Measure (ι → ℝ)) I).toReal = ∏ i, (I.upper i - I.lower i) := by
  rw [coe_eq_pi, Real.volume_pi_Ioc_toReal I.lower_le_upper]
/-
**BoxIntegral.Box.volume_face_mul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：volume_face_mul {n} (i : Fin (n + 1)) (I : Box (Fin (n + 1))) : (∏ j, ((I.
face i).upper j - (I.face i).lower j)) * (I.upper i - I.lower i) = ∏ j, (I.upper
 j - I.lower j)
参数：i : Fin (n + 1)；I : Box (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `BoxIntegral.Box.face_upper`：∀ {n : ℕ} (I : BoxIntegral.Box (Fin (n + 1))
) (i : Fin (n + 1)) (a : Fin n),   (I.face i).upper a = I.upper (i.succAbove a)
· 使用定理 `BoxIntegral.Box.face_lower`：∀ {n : ℕ} (I : BoxIntegral.Box (Fin (n + 1))
) (i : Fin (n + 1)) (a : Fin n),   (I.face i).lower a = I.lower (i.succAbove a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_face_mul {n} (i : Fin (n + 1)) (I : Box (Fin (n + 1))) :
    (∏ j, ((I.face i).upper j - (I.face i).lower j)) * (I.upper i - I.lower i) =
      ∏ j, (I.upper j - I.lower j) := by
  simp only [face_lower, face_upper, Fin.prod_univ_succAbove _ i, mul_comm]

end Box

namespace BoxAdditiveMap

variable [Fintype ι]

/-- Box-additive map sending each box `I` to the continuous linear endomorphism
`x ↦ (volume I).toReal • x`. -/
/-
**BoxIntegral.BoxAdditiveMap.volume** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.BoxAd
ditiveMap`。
形式化陈述：{ι : Type u_1} →   [Fintype ι] →     {E : Type u_2} →       [inst : Normed
AddCommGroup E] → [inst_1 : NormedSpace ℝ E] → BoxIntegral.BoxAdditiveMap ι (E →
L[ℝ] E) ⊤
参数：E →L[ℝ] E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Box-additive map sending each box `I` to the continuous linear endomorphism
`x ↦ (volume I).toReal • x`.
-/
protected def volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : ι →ᵇᵃ E →L[ℝ] E :=
  (volume : Measure (ι → ℝ)).toBoxAdditive.toSMul
/-
**BoxIntegral.BoxAdditiveMap.volume_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.BoxAdditiveMap`。
形式化陈述：volume_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (I : 
Box ι) (x : E) : BoxAdditiveMap.volume I x = (∏ j, (I.upper j - I.lower j)) • x
参数：I : Box ι；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.BoxAdditiveMap.volume.eq_1`：∀ {ι : Type u_1} [inst : Fintype
 ι] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E],  
 BoxIntegral.BoxAdditiveMap.…
· 使用定理 `BoxIntegral.BoxAdditiveMap.toSMul_apply`：toSMul_apply (f : ι ->ᵇᵃ[I₀] Re
al) (I : Box ι) (x : E) : f.toSMul I x = f I • x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `BoxIntegral.Box.volume_apply`：volume_apply (I : Box ι) : (volume : Measu
re (ι -> Real)).toBoxAdditive I = ∏ i, (I.upper i - I.lower i)
-/
theorem volume_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Box ι) (x : E) :
    BoxAdditiveMap.volume I x = (∏ j, (I.upper j - I.lower j)) • x := by
  rw [BoxAdditiveMap.volume, toSMul_apply]
  exact congr_arg₂ (· • ·) I.volume_apply rfl

end BoxAdditiveMap

end BoxIntegral

