/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Density of smooth functions in the space of continuous functions

In this file we prove that smooth functions are dense in the set of continuous functions
from a real finite-dimensional vector space to a Banach space,
see `ContinuousMap.dense_setOfPred_contDiff`.
We also prove several unbundled versions of this statement.

The heavy part of the proof is done upstream in `ContDiffBump.dist_normed_convolution_le`
and `HasCompactSupport.contDiff_convolution_left`.
Here we wrap these results removing measure-related arguments from the assumptions.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {ε : ℝ}

open scoped ContDiff unitInterval Topology
open Function Set Metric MeasureTheory

/-
**MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dis
t_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball
_dist_le [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
 (hf : LocallyIntegrable f μ) (hε : 0 < ε) : exists g : E -> F, ContDiff Real ∞ 
g ∧ forall a, forall δ, (forall x in ball a ε, dist (f x) (f a) <= δ) -> dist (g
 a) (f a) <= δ
参数：hf : LocallyIntegrable f μ；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `HasCompactSupport.contDiff_convolution_left`：∀ {𝕜 : Type u𝕜} {G : Type u
G} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `ContDiffBump.hasCompactSupport_normed`：hasCompactSupport_normed : HasCom
pactSupport (f.normed μ)
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `ContDiffBump.contDiff_normed`：contDiff_normed {n : Nat∞} : ContDiff Real
 n (f.normed μ)
· 使用定理 `ContDiffBump.dist_normed_convolution_le`：dist_normed_convolution_le {x₀ 
: G} {ε : Real} (hmg : AEStronglyMeasurable g μ) (hg : forall x in ball x₀ φ.rOu
t, dist (g x) (g x₀) <= ε) : …
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…
-/
theorem MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (hf : LocallyIntegrable f μ) (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, ∀ δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) →
      dist (g a) (f a) ≤ δ := by
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨_, ?_, fun a δ ↦ φ.dist_normed_convolution_le hf.aestronglyMeasurable⟩
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf
/-
**Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Contin
uous f) (hε : 0 < ε) : exists g : E -> F, ContDiff Real ∞ g ∧ forall a, forall δ
, (forall x in ball a ε, dist (f x) (f a) <= δ) -> dist (g a) (f a) <= δ
参数：hf : Continuous f；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ba
ll_dist_le`：MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_me
m_ball_dist_le [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `Continuous.locallyIntegrable`：Continuous.locallyIntegrable [IsLocallyFin
iteMeasure μ] [SecondCountableTopologyEither X E] (hf : Continuous f) : LocallyI
ntegrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
-/
theorem Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Continuous f)
    (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, ∀ δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) →
      dist (g a) (f a) ≤ δ := by
  borelize E
  exact (hf.locallyIntegrable (μ := .addHaar)).exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε
/-
**UniformContinuous.exists_contDiff_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.exists_contDiff_dist_le (hf : UniformContinuous f) (hε :
 0 < ε) : exists g : E -> F, ContDiff Real ∞ g ∧ forall a, dist (g a) (f a) < ε
参数：hf : UniformContinuous f；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`：Continuou
s.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Continuous f) (hε : 0
 < ε) : exists g : E -> F, ContDiff Real ∞ g ∧ fora…
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
-/
theorem UniformContinuous.exists_contDiff_dist_le (hf : UniformContinuous f) (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, dist (g a) (f a) < ε := by
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ with ⟨g, hgc, hg⟩
  exact ⟨g, hgc, fun a ↦ (hg a _ fun _ h ↦ (hfδ h).le).trans_lt (half_lt_self hε)⟩

/-- Infinitely smooth functions are dense in the space of continuous functions. -/
/-
**ContinuousMap.dense_setOfPred_contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.dense_setOfPred_contDiff : Dense {f : C(E, F) | ContDiff Rea
l ∞ f}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Filter.HasBasis.compactConvergenceUniformity`：∀ {α : Type u₁} {β : Type 
u₂} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {ι : Type u_1} {pi : ι
 → Prop}   {s : ι → Set (β × β)}, …
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsCompact.uniformContinuousOn_of_continuous`：IsCompact.uniformContinuous
On_of_continuous {s : Set α} {f : α -> β} (hs : IsCompact s) (hf : ContinuousOn 
f s) : UniformContinuousOn f s
· 使用定理 `IsCompact.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSpace α] [Pr
operSpace α] {s : Set α},   IsCompact s → ∀ {r : ℝ}, IsCompact (Metric.cthickeni
ng r s)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.uniformContinuousOn_iff`：uniformContinuousOn_iff [PseudoMetricSpa
ce β] {f : α -> β} {s : Set α} : UniformContinuousOn f s ↔ forall ε > 0, exists 
δ > 0, forall x in s…
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`：Continuou
s.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Continuous f) (hε : 0
 < ε) : exists g : E -> F, ContDiff Real ∞ g ∧ fora…
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.mem_cthickening_of_dist_le`：mem_cthickening_of_dist_le {α : Type*
} [PseudoMetricSpace α] (x y : α) (δ : Real) (E : Set α) (h : y in E) (h' : dist
 x y <= δ) : x in cthic…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Infinitely smooth functions are dense in the space of continuous functions.
-/
theorem ContinuousMap.dense_setOfPred_contDiff : Dense {f : C(E, F) | ContDiff ℝ ∞ f} := by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)]
  simp only [Prod.forall, mem_ofPred_eq, and_imp]
  intro K ε hK hε
  have : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous <| by fun_prop
  rcases Metric.uniformContinuousOn_iff.mp this (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨⟨g, hgc.continuous⟩, hgc, fun x hx ↦ (hg _ _ fun y hy ↦ ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball, lt_min_iff] at hy
  exact hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
    (self_subset_cthickening _ hx) hy.2 |>.le

@[deprecated (since := "2026-07-09")]
alias ContinuousMap.dense_setOf_contDiff := ContinuousMap.dense_setOfPred_contDiff
