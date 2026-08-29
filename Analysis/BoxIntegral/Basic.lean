/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Filter
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.Oscillation
public import Mathlib.Data.Bool.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Integrals of Riemann, Henstock-Kurzweil, and McShane

In this file we define the integral of a function over a box in `ℝⁿ`. The same definition works for
Riemann, Henstock-Kurzweil, and McShane integrals.

As usual, we represent `ℝⁿ` as the type of functions `ι → ℝ` for some finite type `ι`. A rectangular
box `(l, u]` in `ℝⁿ` is defined to be the set `{x : ι → ℝ | ∀ i, l i < x i ∧ x i ≤ u i}`, see
`BoxIntegral.Box`.

Let `vol` be a box-additive function on boxes in `ℝⁿ` with codomain `E →L[ℝ] F`. Given a function
`f : ℝⁿ → E`, a box `I` and a tagged partition `π` of this box, the *integral sum* of `f` over `π`
with respect to the volume `vol` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. Here
`π.tag J` is the point (tag) in `ℝⁿ` associated with the box `J`.

The integral is defined as the limit of integral sums along a filter. Different filters correspond
to different integration theories. In order to avoid code duplication, all our definitions and
theorems take an argument `l : BoxIntegral.IntegrationParams`. This is a type that holds three
Boolean values, and encodes eight filters including those corresponding to Riemann,
Henstock-Kurzweil, and McShane integrals.

Following the design of infinite sums (see `hasSum` and `tsum`), we define a predicate
`BoxIntegral.HasIntegral` and a function `BoxIntegral.integral` that returns a vector satisfying
the predicate or zero if the function is not integrable.

Then we prove some basic properties of box integrals (linearity, a formula for the integral of a
constant). We also prove a version of the Henstock-Sacks inequality (see
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`), prove
integrability of continuous functions, and provide a criterion for integrability w.r.t. a
non-Riemann filter (e.g., Henstock-Kurzweil and McShane).

## Notation

- `ℝⁿ`: local notation for `ι → ℝ`

## Tags

integral
-/

@[expose] public section

open scoped Topology NNReal Filter Uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable section

namespace BoxIntegral

universe u v w

variable {ι : Type u} {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] {I J : Box ι} {π : TaggedPrepartition I}

open TaggedPrepartition

local notation "Realⁿ" => ι -> Real

/-!
### Integral sum and its basic properties
-/

/--
Definition of `integralSum` / `integralSum` 的定义

English:
definition integralSum
  signature: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
  body: ∑ J in π.boxes, vol J (f (π.tag J))

中文:
定义 integralSum
  签名: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : TaggedPrepartition I)
  定义体: ∑ J in π.boxes, vol J (f (π.tag J))
-/
def integralSum (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) : F :=
  ∑ J in π.boxes, vol J (f (π.tag J))

/--
theorem `integralSum_congr` / 定理 `integralSum_congr`

English:
theorem integralSum_congr
  statement: {f₁ f₂ : Realⁿ -> E} {vol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F}
  proof: by
  unfold integralSum
  refine Finset.sum_congr rfl (fun J hJ => ?_)
  congr 1
  · exact hvol hJ
  exact hf (π.tag_mem_Icc J)

中文:
定理 integralSum_congr
  结论: {f₁ f₂ : 实数ⁿ -> E} {vol₁ vol₂ : ι ->ᵇᵃ E ->L[实数] F}
  证明: by
  unfold integralSum
  refine Finset.sum_congr rfl (fun J hJ => ?_)
  congr 1
  · exact hvol hJ
  exact hf (π.tag_mem_Icc J)

Depends on / 依赖: Finset, Finset.sum_congr, integralSum, sum_congr, tag_mem_Icc
-/
theorem integralSum_congr {f₁ f₂ : Realⁿ -> E} {vol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F}
    (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ π.boxes) :
    integralSum f₁ vol₁ π = integralSum f₂ vol₂ π := by
  unfold integralSum
  refine Finset.sum_congr rfl (fun J hJ => ?_)
  congr 1
  · exact hvol hJ
  exact hf (π.tag_mem_Icc J)

/--
theorem `integralSum_biUnionTagged` / 定理 `integralSum_biUnionTagged`

English:
theorem integralSum_biUnionTagged
  statement: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : Prepartition I)
  proof: by
refine (π.sum_biUnion_boxes _ _).trans sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']

中文:
定理 integralSum_biUnionTagged
  结论: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : Prepartition I)
  证明: by
refine (π.sum_biUnion_boxes _ _).trans sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']

Depends on / 依赖: sum_biUnion_boxes, sum_congr, tag_biUnionTagged
-/
theorem integralSum_biUnionTagged (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : Prepartition I)
    (πi : forall J, TaggedPrepartition J) :
    integralSum f vol (π.biUnionTagged πi) = ∑ J in π.boxes, integralSum f vol (πi J) := by
refine (π.sum_biUnion_boxes _ _).trans sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']

/--
theorem `integralSum_biUnion_partition` / 定理 `integralSum_biUnion_partition`

English:
theorem integralSum_biUnion_partition
  statement: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
  proof: by
  refine (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => ?_)
  calc
    (∑ J' in (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' in (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ 

中文:
定理 integralSum_biUnion_partition
  结论: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F)
  证明: by
  refine (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => ?_)
  calc
    (∑ J' in (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' in (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ 

Depends on / 依赖: Prepartition, Prepartition.biUnionIndex_of_mem, biUnionIndex, biUnionIndex_of_mem, le_top, sum_biUnion_boxes, sum_congr, sum_partition_boxes, toPrepartition, toPrepartition.biUnionIndex, vol.map
-/
theorem integralSum_biUnion_partition (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
    (π : TaggedPrepartition I) (πi : forall J, Prepartition J) (hπi : forall J in π, (πi J).IsPartition) :
    integralSum f vol (π.biUnionPrepartition πi) = integralSum f vol π := by
  refine (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => ?_)
  calc
    (∑ J' in (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' in (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ hJ hJ']
    _ = vol J (f (π.tag J)) :=
      (vol.map ⟨⟨fun g : E ->L[Real] F => g (f (π.tag J)), rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes
        le_top (hπi J hJ)

/--
theorem `integralSum_inf_partition` / 定理 `integralSum_inf_partition`

English:
theorem integralSum_inf_partition
  statement: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
  proof: integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)

中文:
定理 integralSum_inf_partition
  结论: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : TaggedPrepartition I)
  证明: integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)

Depends on / 依赖: Prepartition, Prepartition.le_of_mem, h.restrict, integralSum_biUnion_partition, le_of_mem, restrict
-/
theorem integralSum_inf_partition (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
    {π' : Prepartition I} (h : π'.IsPartition) :
    integralSum f vol (π.infPrepartition π') = integralSum f vol π :=
  integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)

open scoped Classical in
/--
theorem `integralSum_fiberwise` / 定理 `integralSum_fiberwise`

English:
theorem integralSum_fiberwise
  statement: {α} (g : Box ι -> α) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
  proof: π.sum_fiberwise g fun J => vol J (f <| π.tag J)

中文:
定理 integralSum_fiberwise
  结论: {α} (g : Box ι -> α) (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F)
  证明: π.sum_fiberwise g fun J => vol J (f <| π.tag J)

Depends on / 依赖: sum_fiberwise
-/
theorem integralSum_fiberwise {α} (g : Box ι -> α) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
    (π : TaggedPrepartition I) :
    (∑ y in π.boxes.image g, integralSum f vol (π.filter (g · = y))) = integralSum f vol π :=
  π.sum_fiberwise g fun J => vol J (f <| π.tag J)

/--
theorem `integralSum_sub_partitions` / 定理 `integralSum_sub_partitions`

English:
theorem integralSum_sub_partitions
  statement: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
  proof: by
  rw [← integralSum_inf_partition f vol π₁ h₂]; rw [← integralSum_inf_partition f vol π₂ h₁]; rw [integralSum]; rw [integralSum]; rw [Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]

@[simp]

中文:
定理 integralSum_sub_partitions
  结论: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F)
  证明: by
  rw [← integralSum_inf_partition f vol π₁ h₂]; rw [← integralSum_inf_partition f vol π₂ h₁]; rw [integralSum]; rw [integralSum]; rw [Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]

@[simp]

Depends on / 依赖: Finset, Finset.sum_sub_distrib, infPrepartition_toPrepartition, inf_comm, integralSum, integralSum_inf_partition, sum_sub_distrib
-/
theorem integralSum_sub_partitions (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
    {π₁ π₂ : TaggedPrepartition I} (h₁ : π₁.IsPartition) (h₂ : π₂.IsPartition) :
    integralSum f vol π₁ - integralSum f vol π₂ =
      ∑ J in (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes,
        (vol J (f <| (π₁.infPrepartition π₂.toPrepartition).tag J) -
          vol J (f <| (π₂.infPrepartition π₁.toPrepartition).tag J)) := by
  rw [← integralSum_inf_partition f vol π₁ h₂]; rw [← integralSum_inf_partition f vol π₂ h₁]; rw [integralSum]; rw [integralSum]; rw [Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]

@[simp]
/--
theorem `integralSum_disjUnion` / 定理 `integralSum_disjUnion`

English:
theorem integralSum_disjUnion
  statement: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) {π₁ π₂ : TaggedPrepartition I}
  proof: by
  refine (Prepartition.sum_disj_union_boxes h _).trans
      (congr_arg₂ (· + ·) (sum_congr rfl fun J hJ => ?_) (sum_congr rfl fun J hJ => ?_))
  · rw [disjUnion_tag_of_mem_left _ hJ]
  · rw [disjUnion_tag_of_mem_right _ hJ]

@[simp]

中文:
定理 integralSum_disjUnion
  结论: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) {π₁ π₂ : TaggedPrepartition I}
  证明: by
  refine (Prepartition.sum_disj_union_boxes h _).trans
      (congr_arg₂ (· + ·) (sum_congr rfl fun J hJ => ?_) (sum_congr rfl fun J hJ => ?_))
  · rw [disjUnion_tag_of_mem_left _ hJ]
  · rw [disjUnion_tag_of_mem_right _ hJ]

@[simp]

Depends on / 依赖: Prepartition, Prepartition.sum_disj_union_boxes, disjUnion_tag_of_mem_left, disjUnion_tag_of_mem_right, sum_congr, sum_disj_union_boxes
-/
theorem integralSum_disjUnion (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) {π₁ π₂ : TaggedPrepartition I}
    (h : Disjoint π₁.iUnion π₂.iUnion) :
    integralSum f vol (π₁.disjUnion π₂ h) = integralSum f vol π₁ + integralSum f vol π₂ := by
  refine (Prepartition.sum_disj_union_boxes h _).trans
      (congr_arg₂ (· + ·) (sum_congr rfl fun J hJ => ?_) (sum_congr rfl fun J hJ => ?_))
  · rw [disjUnion_tag_of_mem_left _ hJ]
  · rw [disjUnion_tag_of_mem_right _ hJ]

@[simp]
/--
theorem `integralSum_add` / 定理 `integralSum_add`

English:
theorem integralSum_add
  given: (f g : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
  proof: by
  simp only [integralSum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]

@[simp]

中文:
定理 integralSum_add
  条件: (f g : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : TaggedPrepartition I)
  证明: by
  simp only [integralSum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, Pi.add_apply, add_apply, integralSum, map_add, sum_add_distrib
-/
theorem integralSum_add (f g : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) :
    integralSum (f + g) vol π = integralSum f vol π + integralSum g vol π := by
  simp only [integralSum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]

@[simp]
/--
theorem `integralSum_neg` / 定理 `integralSum_neg`

English:
theorem integralSum_neg
  given: (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
  proof: by
  simp only [integralSum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]

@[simp]

中文:
定理 integralSum_neg
  条件: (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : TaggedPrepartition I)
  证明: by
  simp only [integralSum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_neg_distrib, Pi.neg_apply, integralSum, map_neg, neg_apply, sum_neg_distrib
-/
theorem integralSum_neg (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) :
    integralSum (-f) vol π = -integralSum f vol π := by
  simp only [integralSum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]

@[simp]
/--
theorem `integralSum_smul` / 定理 `integralSum_smul`

English:
theorem integralSum_smul
  given: (c : Real) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I)
  proof: by
  simp only [integralSum, Finset.smul_sum, Pi.smul_apply, map_smul]

中文:
定理 integralSum_smul
  条件: (c : 实数) (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (π : TaggedPrepartition I)
  证明: by
  simp only [integralSum, Finset.smul_sum, Pi.smul_apply, map_smul]

Depends on / 依赖: Finset, Finset.smul_sum, Pi.smul_apply, integralSum, map_smul, smul_apply, smul_sum
-/
theorem integralSum_smul (c : Real) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (π : TaggedPrepartition I) :
    integralSum (c • f) vol π = c • integralSum f vol π := by
  simp only [integralSum, Finset.smul_sum, Pi.smul_apply, map_smul]

variable [Fintype ι]

/-!
### Basic integrability theory
-/

/--
Definition of `HasIntegral` / `HasIntegral` 的定义

English:
definition HasIntegral
  signature: (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (y : F)
  body: Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)

中文:
定义 HasIntegral
  签名: (I : Box ι) (l : 整数egrationParams) (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F) (y : F)
  定义体: Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)

Depends on / 依赖: Tendsto, integralSum, l.toFilteriUnion, toFilteriUnion
-/
def HasIntegral (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) (y : F) :
    Prop :=
  Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)

/--
Definition of `Integrable` / `Integrable` 的定义

English:
definition Integrable
  signature: (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
  body: exists y, HasIntegral I l f vol y

中文:
定义 Integrable
  签名: (I : Box ι) (l : 整数egrationParams) (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F)
  定义体: exists y, HasIntegral I l f vol y

Depends on / 依赖: HasIntegral
-/
def Integrable (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) :=
  exists y, HasIntegral I l f vol y

open scoped Classical in
/--
Definition of `integral` / `integral` 的定义

English:
definition integral
  signature: (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F)
  body: if h : Integrable I l f vol then h.choose else 0

中文:
定义 integral
  签名: (I : Box ι) (l : 整数egrationParams) (f : 实数ⁿ -> E) (vol : ι ->ᵇᵃ E ->L[实数] F)
  定义体: if h : Integrable I l f vol then h.choose else 0

Depends on / 依赖: Integrable, h.choose
-/
def integral (I : Box ι) (l : IntegrationParams) (f : Realⁿ -> E) (vol : ι ->ᵇᵃ E ->L[Real] F) :=
  if h : Integrable I l f vol then h.choose else 0

/--
theorem `hasIntegral_congr` / 定理 `hasIntegral_congr`

English:
theorem hasIntegral_congr
  statement: (I : Box ι) (l : IntegrationParams) {f₁ f₂ : Realⁿ -> E}
  proof: by
  unfold HasIntegral
  refine Filter.tendsto_congr (fun π => integralSum_congr hf (hvol.mono ?_))
  intro J hJ
  simp [π.le_of_mem' J hJ]

中文:
定理 hasIntegral_congr
  结论: (I : Box ι) (l : 整数egrationParams) {f₁ f₂ : 实数ⁿ -> E}
  证明: by
  unfold HasIntegral
  refine Filter.tendsto_congr (fun π => integralSum_congr hf (hvol.mono ?_))
  intro J hJ
  simp [π.le_of_mem' J hJ]

Depends on / 依赖: Filter, Filter.tendsto_congr, HasIntegral, hvol.mono, integralSum_congr, le_of_mem, tendsto_congr
-/
theorem hasIntegral_congr (I : Box ι) (l : IntegrationParams) {f₁ f₂ : Realⁿ -> E}
    {vol₁ vol₂ : ι ->ᵇᵃ E ->L[Real] F}
    (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ (Set.Iic I)) (y : F) :
    HasIntegral I l f₁ vol₁ y ↔ HasIntegral I l f₂ vol₂ y := by
  unfold HasIntegral
  refine Filter.tendsto_congr (fun π => integralSum_congr hf (hvol.mono ?_))
  intro J hJ
  simp [π.le_of_mem' J hJ]

-- Porting note: using the above notation ℝⁿ here causes the theorem below to be silently ignored
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Lean.204.20doesn't.20add.20lemma.20to.20the.20environment/near/363764522
-- and https://github.com/leanprover/lean4/issues/2257
variable {l : IntegrationParams} {f g : (ι -> Real) -> E} {vol : ι ->ᵇᵃ E ->L[Real] F} {y y' : F}

/--
theorem `HasIntegral.tendsto` / 定理 `HasIntegral.tendsto`

English:
theorem HasIntegral.tendsto
  given: (h : HasIntegral I l f vol y)
  proof: h

中文:
定理 HasIntegral.tendsto
  条件: (h : Has整数egral I l f vol y)
  证明: h
-/
theorem HasIntegral.tendsto (h : HasIntegral I l f vol y) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y) :=
  h

/--
theorem `hasIntegral_iff` / 定理 `hasIntegral_iff`

English:
theorem hasIntegral_iff
  statement: HasIntegral I l f vol y ↔
  proof: ((l.hasBasis_toFilteriUnion_top I).tendsto_iff nhds_basis_closedBall).trans by
    simp [@forall_comm Real>=0 (TaggedPrepartition I)]

中文:
定理 hasIntegral_iff
  结论: Has整数egral I l f vol y ↔
  证明: ((l.hasBasis_toFilteriUnion_top I).tendsto_iff nhds_basis_closedBall).trans by
    simp [@forall_comm Real>=0 (TaggedPrepartition I)]

Depends on / 依赖: TaggedPrepartition, forall_comm, hasBasis_toFilteriUnion_top, l.hasBasis_toFilteriUnion_top, nhds_basis_closedBall, tendsto_iff
-/
theorem hasIntegral_iff : HasIntegral I l f vol y ↔
    forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c, l.RCond (r c)) ∧
      forall c π, l.MemBaseSet I c (r c) π -> IsPartition π -> dist (integralSum f vol π) y <= ε :=
((l.hasBasis_toFilteriUnion_top I).tendsto_iff nhds_basis_closedBall).trans by
    simp [@forall_comm Real>=0 (TaggedPrepartition I)]

/--
theorem `HasIntegral.of_mul` / 定理 `HasIntegral.of_mul`

English:
theorem HasIntegral.of_mul
  statement: (a : Real)
  proof: by
  refine hasIntegral_iff.2 fun ε hε => ?_
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
  rcases h ε' hε' with ⟨r, hr, H⟩
  exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩

中文:
定理 HasIntegral.of_mul
  结论: (a : 实数)
  证明: by
  refine hasIntegral_iff.2 fun ε hε => ?_
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
  rcases h ε' hε' with ⟨r, hr, H⟩
  exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩

Depends on / 依赖: exists_pos_mul_lt, ha.le, hasIntegral_iff
-/
theorem HasIntegral.of_mul (a : Real)
    (h : forall ε : Real, 0 < ε -> exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c, l.RCond (r c)) ∧ forall c π,
      l.MemBaseSet I c (r c) π -> IsPartition π -> dist (integralSum f vol π) y <= a * ε) :
    HasIntegral I l f vol y := by
  refine hasIntegral_iff.2 fun ε hε => ?_
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
  rcases h ε' hε' with ⟨r, hr, H⟩
  exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩

/--
theorem `integrable_iff_cauchy` / 定理 `integrable_iff_cauchy`

English:
theorem integrable_iff_cauchy
  given: [CompleteSpace F]
  proof: cauchy_map_iff_exists_tendsto.symm

中文:
定理 integrable_iff_cauchy
  条件: [CompleteSpace F]
  证明: cauchy_map_iff_exists_tendsto.symm

Depends on / 依赖: cauchy_map_iff_exists_tendsto, cauchy_map_iff_exists_tendsto.symm
-/
theorem integrable_iff_cauchy [CompleteSpace F] :
    Integrable I l f vol ↔ Cauchy ((l.toFilteriUnion I ⊤).map (integralSum f vol)) :=
  cauchy_map_iff_exists_tendsto.symm

/--
theorem `integrable_iff_cauchy_basis` / 定理 `integrable_iff_cauchy_basis`

English:
theorem integrable_iff_cauchy_basis
  given: [CompleteSpace F]
  statement: Integrable I l f vol ↔
  proof: by
  rw [integrable_iff_cauchy]; rw [cauchy_map_iff']; rw [(l.hasBasis_toFilteriUnion_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
  refine forall₂_congr fun ε _ => exists_congr fun r => ?_
  simp only [Prod.forall, exists_imp, prodMk_mem_set_prod_eq, and_imp, mem_ofPred_eq]
  exact
    an

中文:
定理 integrable_iff_cauchy_basis
  条件: [CompleteSpace F]
  结论: 整数egrable I l f vol ↔
  证明: by
  rw [integrable_iff_cauchy]; rw [cauchy_map_iff']; rw [(l.hasBasis_toFilteriUnion_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
  refine forall₂_congr fun ε _ => exists_congr fun r => ?_
  simp only [Prod.forall, exists_imp, prodMk_mem_set_prod_eq, and_imp, mem_ofPred_eq]
  exact
    an

Depends on / 依赖: Iff.rfl, Prod.forall, and_congr, and_imp, cauchy_map_iff, exists_congr, exists_imp, hasBasis_toFilteriUnion_top, integrable_iff_cauchy, l.hasBasis_toFilteriUnion_top, mem_ofPred_eq, prodMk_mem_set_prod_eq, prod_self, prod_self.tendsto_iff, tendsto_iff, uniformity_basis_dist_le
-/
theorem integrable_iff_cauchy_basis [CompleteSpace F] : Integrable I l f vol ↔
    forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c, l.RCond (r c)) ∧
      forall c₁ c₂ π₁ π₂, l.MemBaseSet I c₁ (r c₁) π₁ -> π₁.IsPartition -> l.MemBaseSet I c₂ (r c₂) π₂ ->
        π₂.IsPartition -> dist (integralSum f vol π₁) (integralSum f vol π₂) <= ε := by
  rw [integrable_iff_cauchy]; rw [cauchy_map_iff']; rw [(l.hasBasis_toFilteriUnion_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
  refine forall₂_congr fun ε _ => exists_congr fun r => ?_
  simp only [Prod.forall, exists_imp, prodMk_mem_set_prod_eq, and_imp, mem_ofPred_eq]
  exact
    and_congr Iff.rfl
      ⟨fun H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂ => H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂,
        fun H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂ => H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂⟩

/--
theorem `HasIntegral.mono` / 定理 `HasIntegral.mono`

English:
theorem HasIntegral.mono
  given: {l₁ l₂ : IntegrationParams} (h : HasIntegral I l₁ f vol y) (hl : l₂ <= l₁)
  proof: h.mono_left IntegrationParams.toFilteriUnion_mono _ hl _

中文:
定理 HasIntegral.mono
  条件: {l₁ l₂ : 整数egrationParams} (h : Has整数egral I l₁ f vol y) (hl : l₂ <= l₁)
  证明: h.mono_left IntegrationParams.toFilteriUnion_mono _ hl _

Depends on / 依赖: IntegrationParams, IntegrationParams.toFilteriUnion_mono, h.mono_left, mono_left, toFilteriUnion_mono
-/
theorem HasIntegral.mono {l₁ l₂ : IntegrationParams} (h : HasIntegral I l₁ f vol y) (hl : l₂ <= l₁) :
    HasIntegral I l₂ f vol y :=
h.mono_left IntegrationParams.toFilteriUnion_mono _ hl _

/--
theorem `Integrable.hasIntegral` / 定理 `Integrable.hasIntegral`

English:
theorem Integrable.hasIntegral
  given: (h : Integrable I l f vol)
  proof: by
  rw [integral]; rw [dif_pos h]
  exact Classical.choose_spec h

中文:
定理 Integrable.hasIntegral
  条件: (h : 整数egrable I l f vol)
  证明: by
  rw [integral]; rw [dif_pos h]
  exact Classical.choose_spec h
-/
protected theorem Integrable.hasIntegral (h : Integrable I l f vol) :
    HasIntegral I l f vol (integral I l f vol) := by
  rw [integral]; rw [dif_pos h]
  exact Classical.choose_spec h

/--
theorem `Integrable.mono` / 定理 `Integrable.mono`

English:
theorem Integrable.mono
  given: {l'} (h : Integrable I l f vol) (hle : l' <= l)
  statement: Integrable I l' f vol
  proof: ⟨_, h.hasIntegral.mono hle⟩

中文:
定理 Integrable.mono
  条件: {l'} (h : 整数egrable I l f vol) (hle : l' <= l)
  结论: 整数egrable I l' f vol
  证明: ⟨_, h.hasIntegral.mono hle⟩

Depends on / 依赖: h.hasIntegral.mono, hasIntegral
-/
theorem Integrable.mono {l'} (h : Integrable I l f vol) (hle : l' <= l) : Integrable I l' f vol :=
  ⟨_, h.hasIntegral.mono hle⟩

/--
theorem `HasIntegral.unique` / 定理 `HasIntegral.unique`

English:
theorem HasIntegral.unique
  given: (h : HasIntegral I l f vol y) (h' : HasIntegral I l f vol y')
  statement: y = y'
  proof: tendsto_nhds_unique h h'

中文:
定理 HasIntegral.unique
  条件: (h : Has整数egral I l f vol y) (h' : Has整数egral I l f vol y')
  结论: y = y'
  证明: tendsto_nhds_unique h h'

Depends on / 依赖: tendsto_nhds_unique
-/
theorem HasIntegral.unique (h : HasIntegral I l f vol y) (h' : HasIntegral I l f vol y') : y = y' :=
  tendsto_nhds_unique h h'

/--
theorem `HasIntegral.integrable` / 定理 `HasIntegral.integrable`

English:
theorem HasIntegral.integrable
  given: (h : HasIntegral I l f vol y)
  statement: Integrable I l f vol
  proof: ⟨_, h⟩

中文:
定理 HasIntegral.integrable
  条件: (h : Has整数egral I l f vol y)
  结论: 整数egrable I l f vol
  证明: ⟨_, h⟩
-/
theorem HasIntegral.integrable (h : HasIntegral I l f vol y) : Integrable I l f vol :=
  ⟨_, h⟩

/--
theorem `HasIntegral.integral_eq` / 定理 `HasIntegral.integral_eq`

English:
theorem HasIntegral.integral_eq
  given: (h : HasIntegral I l f vol y)
  statement: integral I l f vol = y
  proof: h.integrable.hasIntegral.unique h

nonrec theorem HasIntegral.add (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f + g) vol (y + y') := by
  simpa only [HasIntegral, ← integralSum_add] using h.add h'

中文:
定理 HasIntegral.integral_eq
  条件: (h : Has整数egral I l f vol y)
  结论: integral I l f vol = y
  证明: h.integrable.hasIntegral.unique h

nonrec theorem HasIntegral.add (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f + g) vol (y + y') := by
  simpa only [HasIntegral, ← integralSum_add] using h.add h'

Depends on / 依赖: h.integrable.hasIntegral.unique, hasIntegral, integrable, unique
-/
theorem HasIntegral.integral_eq (h : HasIntegral I l f vol y) : integral I l f vol = y :=
  h.integrable.hasIntegral.unique h

nonrec theorem HasIntegral.add (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f + g) vol (y + y') := by
  simpa only [HasIntegral, ← integralSum_add] using h.add h'

/--
theorem `Integrable.add` / 定理 `Integrable.add`

English:
theorem Integrable.add
  given: (hf : Integrable I l f vol) (hg : Integrable I l g vol)
  proof: (hf.hasIntegral.add hg.hasIntegral).integrable

中文:
定理 Integrable.add
  条件: (hf : 整数egrable I l f vol) (hg : 整数egrable I l g vol)
  证明: (hf.hasIntegral.add hg.hasIntegral).integrable

Depends on / 依赖: hasIntegral, hf.hasIntegral.add, hg.hasIntegral, integrable
-/
theorem Integrable.add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f + g) vol :=
  (hf.hasIntegral.add hg.hasIntegral).integrable

/--
theorem `integral_add` / 定理 `integral_add`

English:
theorem integral_add
  given: (hf : Integrable I l f vol) (hg : Integrable I l g vol)
  proof: (hf.hasIntegral.add hg.hasIntegral).integral_eq

nonrec theorem HasIntegral.neg (hf : HasIntegral I l f vol y) : HasIntegral I l (-f) vol (-y) := by
  simpa only [HasIntegral, ← integralSum_neg] using hf.neg

中文:
定理 integral_add
  条件: (hf : 整数egrable I l f vol) (hg : 整数egrable I l g vol)
  证明: (hf.hasIntegral.add hg.hasIntegral).integral_eq

nonrec theorem HasIntegral.neg (hf : HasIntegral I l f vol y) : HasIntegral I l (-f) vol (-y) := by
  simpa only [HasIntegral, ← integralSum_neg] using hf.neg

Depends on / 依赖: hasIntegral, hf.hasIntegral.add, hg.hasIntegral, integral_eq
-/
theorem integral_add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
  (hf.hasIntegral.add hg.hasIntegral).integral_eq

nonrec theorem HasIntegral.neg (hf : HasIntegral I l f vol y) : HasIntegral I l (-f) vol (-y) := by
  simpa only [HasIntegral, ← integralSum_neg] using hf.neg

/--
theorem `Integrable.neg` / 定理 `Integrable.neg`

English:
theorem Integrable.neg
  given: (hf : Integrable I l f vol)
  statement: Integrable I l (-f) vol
  proof: hf.hasIntegral.neg.integrable

中文:
定理 Integrable.neg
  条件: (hf : 整数egrable I l f vol)
  结论: 整数egrable I l (-f) vol
  证明: hf.hasIntegral.neg.integrable

Depends on / 依赖: hasIntegral, hf.hasIntegral.neg.integrable, integrable
-/
theorem Integrable.neg (hf : Integrable I l f vol) : Integrable I l (-f) vol :=
  hf.hasIntegral.neg.integrable

/--
theorem `Integrable.of_neg` / 定理 `Integrable.of_neg`

English:
theorem Integrable.of_neg
  given: (hf : Integrable I l (-f) vol)
  statement: Integrable I l f vol
  proof: neg_neg f ▸ hf.neg

@[simp]

中文:
定理 Integrable.of_neg
  条件: (hf : 整数egrable I l (-f) vol)
  结论: 整数egrable I l f vol
  证明: neg_neg f ▸ hf.neg

@[simp]

Depends on / 依赖: hf.neg, neg_neg
-/
theorem Integrable.of_neg (hf : Integrable I l (-f) vol) : Integrable I l f vol :=
  neg_neg f ▸ hf.neg

@[simp]
/--
theorem `integrable_neg` / 定理 `integrable_neg`

English:
theorem integrable_neg
  statement: Integrable I l (-f) vol ↔ Integrable I l f vol
  proof: ⟨fun h => h.of_neg, fun h => h.neg⟩

@[simp]

中文:
定理 integrable_neg
  结论: 整数egrable I l (-f) vol ↔ 整数egrable I l f vol
  证明: ⟨fun h => h.of_neg, fun h => h.neg⟩

@[simp]

Depends on / 依赖: h.neg, h.of_neg, of_neg
-/
theorem integrable_neg : Integrable I l (-f) vol ↔ Integrable I l f vol :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩

@[simp]
/--
theorem `integral_neg` / 定理 `integral_neg`

English:
theorem integral_neg
  statement: integral I l (-f) vol = -integral I l f vol
  proof: by
  classical
  exact if h : Integrable I l f vol then h.hasIntegral.neg.integral_eq
  else by rw [integral, integral, dif_neg h, dif_neg (mt Integrable.of_neg h), neg_zero]

中文:
定理 integral_neg
  结论: integral I l (-f) vol = -integral I l f vol
  证明: by
  classical
  exact if h : Integrable I l f vol then h.hasIntegral.neg.integral_eq
  else by rw [integral, integral, dif_neg h, dif_neg (mt Integrable.of_neg h), neg_zero]

Depends on / 依赖: Integrable, Integrable.of_neg, classical, dif_neg, h.hasIntegral.neg.integral_eq, hasIntegral, integral, integral_eq, neg_zero, of_neg
-/
theorem integral_neg : integral I l (-f) vol = -integral I l f vol := by
  classical
  exact if h : Integrable I l f vol then h.hasIntegral.neg.integral_eq
  else by rw [integral, integral, dif_neg h, dif_neg (mt Integrable.of_neg h), neg_zero]

/--
theorem `HasIntegral.sub` / 定理 `HasIntegral.sub`

English:
theorem HasIntegral.sub
  given: (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y')
  proof: by simpa only [sub_eq_add_neg] using h.add h'.neg

中文:
定理 HasIntegral.sub
  条件: (h : Has整数egral I l f vol y) (h' : Has整数egral I l g vol y')
  证明: by simpa only [sub_eq_add_neg] using h.add h'.neg

Depends on / 依赖: h.add, sub_eq_add_neg
-/
theorem HasIntegral.sub (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f - g) vol (y - y') := by simpa only [sub_eq_add_neg] using h.add h'.neg

/--
theorem `Integrable.sub` / 定理 `Integrable.sub`

English:
theorem Integrable.sub
  given: (hf : Integrable I l f vol) (hg : Integrable I l g vol)
  proof: (hf.hasIntegral.sub hg.hasIntegral).integrable

中文:
定理 Integrable.sub
  条件: (hf : 整数egrable I l f vol) (hg : 整数egrable I l g vol)
  证明: (hf.hasIntegral.sub hg.hasIntegral).integrable

Depends on / 依赖: hasIntegral, hf.hasIntegral.sub, hg.hasIntegral, integrable
-/
theorem Integrable.sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f - g) vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integrable

/--
theorem `integral_sub` / 定理 `integral_sub`

English:
theorem integral_sub
  given: (hf : Integrable I l f vol) (hg : Integrable I l g vol)
  proof: (hf.hasIntegral.sub hg.hasIntegral).integral_eq

中文:
定理 integral_sub
  条件: (hf : 整数egrable I l f vol) (hg : 整数egrable I l g vol)
  证明: (hf.hasIntegral.sub hg.hasIntegral).integral_eq

Depends on / 依赖: hasIntegral, hf.hasIntegral.sub, hg.hasIntegral, integral_eq
-/
theorem integral_sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integral_eq

/--
theorem `hasIntegral_const` / 定理 `hasIntegral_const`

English:
theorem hasIntegral_const
  given: (c : E)
  statement: HasIntegral I l (fun _ => c) vol (vol I c)
  proof: tendsto_const_nhds.congr' (l.eventually_isPartition I).mono fun _π hπ => Eq.symm
    (vol.map ⟨⟨fun g : E ->L[Real] F => g c, rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes le_top hπ

@[simp]

中文:
定理 hasIntegral_const
  条件: (c : E)
  结论: Has整数egral I l (fun _ => c) vol (vol I c)
  证明: tendsto_const_nhds.congr' (l.eventually_isPartition I).mono fun _π hπ => Eq.symm
    (vol.map ⟨⟨fun g : E ->L[Real] F => g c, rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes le_top hπ

@[simp]

Depends on / 依赖: Eq.symm, eventually_isPartition, l.eventually_isPartition, le_top, sum_partition_boxes, tendsto_const_nhds, tendsto_const_nhds.congr, vol.map
-/
theorem hasIntegral_const (c : E) : HasIntegral I l (fun _ => c) vol (vol I c) :=
tendsto_const_nhds.congr' (l.eventually_isPartition I).mono fun _π hπ => Eq.symm
    (vol.map ⟨⟨fun g : E ->L[Real] F => g c, rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes le_top hπ

@[simp]
/--
theorem `integral_const` / 定理 `integral_const`

English:
theorem integral_const
  given: (c : E)
  statement: integral I l (fun _ => c) vol = vol I c
  proof: (hasIntegral_const c).integral_eq

中文:
定理 integral_const
  条件: (c : E)
  结论: integral I l (fun _ => c) vol = vol I c
  证明: (hasIntegral_const c).integral_eq

Depends on / 依赖: hasIntegral_const, integral_eq
-/
theorem integral_const (c : E) : integral I l (fun _ => c) vol = vol I c :=
  (hasIntegral_const c).integral_eq

/--
theorem `integrable_const` / 定理 `integrable_const`

English:
theorem integrable_const
  given: (c : E)
  statement: Integrable I l (fun _ => c) vol
  proof: ⟨_, hasIntegral_const c⟩

中文:
定理 integrable_const
  条件: (c : E)
  结论: 整数egrable I l (fun _ => c) vol
  证明: ⟨_, hasIntegral_const c⟩

Depends on / 依赖: hasIntegral_const
-/
theorem integrable_const (c : E) : Integrable I l (fun _ => c) vol :=
  ⟨_, hasIntegral_const c⟩

/--
theorem `hasIntegral_zero` / 定理 `hasIntegral_zero`

English:
theorem hasIntegral_zero
  statement: HasIntegral I l (fun _ => (0 : E)) vol 0
  proof: by
  simpa only [← (vol I).map_zero] using hasIntegral_const (0 : E)

中文:
定理 hasIntegral_zero
  结论: Has整数egral I l (fun _ => (0 : E)) vol 0
  证明: by
  simpa only [← (vol I).map_zero] using hasIntegral_const (0 : E)

Depends on / 依赖: hasIntegral_const, map_zero
-/
theorem hasIntegral_zero : HasIntegral I l (fun _ => (0 : E)) vol 0 := by
  simpa only [← (vol I).map_zero] using hasIntegral_const (0 : E)

/--
theorem `integrable_zero` / 定理 `integrable_zero`

English:
theorem integrable_zero
  statement: Integrable I l (fun _ => (0 : E)) vol
  proof: ⟨0, hasIntegral_zero⟩

中文:
定理 integrable_zero
  结论: 整数egrable I l (fun _ => (0 : E)) vol
  证明: ⟨0, hasIntegral_zero⟩

Depends on / 依赖: hasIntegral_zero
-/
theorem integrable_zero : Integrable I l (fun _ => (0 : E)) vol :=
  ⟨0, hasIntegral_zero⟩

/--
theorem `integral_zero` / 定理 `integral_zero`

English:
theorem integral_zero
  statement: integral I l (fun _ => (0 : E)) vol = 0
  proof: hasIntegral_zero.integral_eq

中文:
定理 integral_zero
  结论: integral I l (fun _ => (0 : E)) vol = 0
  证明: hasIntegral_zero.integral_eq

Depends on / 依赖: hasIntegral_zero, hasIntegral_zero.integral_eq, integral_eq
-/
theorem integral_zero : integral I l (fun _ => (0 : E)) vol = 0 :=
  hasIntegral_zero.integral_eq

/--
theorem `HasIntegral.sum` / 定理 `HasIntegral.sum`

English:
theorem HasIntegral.sum
  statement: {α : Type*} {s : Finset α} {f : α -> Realⁿ -> E} {g : α -> F}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hasIntegral_zero]
  | insert a s ha ihs =>
    simp only [Finset.sum_insert ha]; rw [Finset.forall_mem_insert] at h
    exact h.1.add (ihs h.2)

中文:
定理 HasIntegral.sum
  结论: {α : 类型} {s : Finset α} {f : α -> 实数ⁿ -> E} {g : α -> F}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hasIntegral_zero]
  | insert a s ha ihs =>
    simp only [Finset.sum_insert ha]; rw [Finset.forall_mem_insert] at h
    exact h.1.add (ihs h.2)

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.sum_insert, classical, forall_mem_insert, hasIntegral_zero, induction_on, insert, sum_insert
-/
theorem HasIntegral.sum {α : Type*} {s : Finset α} {f : α -> Realⁿ -> E} {g : α -> F}
    (h : forall i in s, HasIntegral I l (f i) vol (g i)) :
    HasIntegral I l (fun x => ∑ i in s, f i x) vol (∑ i in s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hasIntegral_zero]
  | insert a s ha ihs =>
    simp only [Finset.sum_insert ha]; rw [Finset.forall_mem_insert] at h
    exact h.1.add (ihs h.2)

/--
theorem `HasIntegral.smul` / 定理 `HasIntegral.smul`

English:
theorem HasIntegral.smul
  given: (hf : HasIntegral I l f vol y) (c : Real)
  proof: by
  simpa only [HasIntegral, ← integralSum_smul] using
    (tendsto_const_nhds : Tendsto _ _ (𝓝 c)).smul hf

中文:
定理 HasIntegral.smul
  条件: (hf : Has整数egral I l f vol y) (c : 实数)
  证明: by
  simpa only [HasIntegral, ← integralSum_smul] using
    (tendsto_const_nhds : Tendsto _ _ (𝓝 c)).smul hf

Depends on / 依赖: HasIntegral, Tendsto, integralSum_smul, tendsto_const_nhds
-/
theorem HasIntegral.smul (hf : HasIntegral I l f vol y) (c : Real) :
    HasIntegral I l (c • f) vol (c • y) := by
  simpa only [HasIntegral, ← integralSum_smul] using
    (tendsto_const_nhds : Tendsto _ _ (𝓝 c)).smul hf

/--
theorem `Integrable.smul` / 定理 `Integrable.smul`

English:
theorem Integrable.smul
  given: (hf : Integrable I l f vol) (c : Real)
  statement: Integrable I l (c • f) vol
  proof: (hf.hasIntegral.smul c).integrable

中文:
定理 Integrable.smul
  条件: (hf : 整数egrable I l f vol) (c : 实数)
  结论: 整数egrable I l (c • f) vol
  证明: (hf.hasIntegral.smul c).integrable

Depends on / 依赖: hasIntegral, hf.hasIntegral.smul, integrable
-/
theorem Integrable.smul (hf : Integrable I l f vol) (c : Real) : Integrable I l (c • f) vol :=
  (hf.hasIntegral.smul c).integrable

/--
theorem `Integrable.of_smul` / 定理 `Integrable.of_smul`

English:
theorem Integrable.of_smul
  given: {c : Real} (hf : Integrable I l (c • f) vol) (hc : c != 0)
  proof: by
  simpa [inv_smul_smul₀ hc] using hf.smul c⁻¹

@[simp]

中文:
定理 Integrable.of_smul
  条件: {c : 实数} (hf : 整数egrable I l (c • f) vol) (hc : c != 0)
  证明: by
  simpa [inv_smul_smul₀ hc] using hf.smul c⁻¹

@[simp]

Depends on / 依赖: hf.smul
-/
theorem Integrable.of_smul {c : Real} (hf : Integrable I l (c • f) vol) (hc : c != 0) :
    Integrable I l f vol := by
  simpa [inv_smul_smul₀ hc] using hf.smul c⁻¹

@[simp]
/--
theorem `integral_smul` / 定理 `integral_smul`

English:
theorem integral_smul
  given: (c : Real)
  statement: integral I l (fun x => c • f x) vol = c • integral I l f vol
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc); · simp only [zero_smul, integral_zero]
  by_cases hf : Integrable I l f vol
  · exact (hf.hasIntegral.smul c).integral_eq
  · have : ¬Integrable I l (fun x => c • f x) vol := mt (fun h => h.of_smul hc) hf
    rw [integral]; rw [integral]; rw [dif_neg hf]; rw

中文:
定理 integral_smul
  条件: (c : 实数)
  结论: integral I l (fun x => c • f x) vol = c • integral I l f vol
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc); · simp only [zero_smul, integral_zero]
  by_cases hf : Integrable I l f vol
  · exact (hf.hasIntegral.smul c).integral_eq
  · have : ¬Integrable I l (fun x => c • f x) vol := mt (fun h => h.of_smul hc) hf
    rw [integral]; rw [integral]; rw [dif_neg hf]; rw

Depends on / 依赖: Integrable, dif_neg, eq_or_ne, h.of_smul, hasIntegral, hf.hasIntegral.smul, integral, integral_eq, integral_zero, of_smul, smul_zero, zero_smul
-/
theorem integral_smul (c : Real) : integral I l (fun x => c • f x) vol = c • integral I l f vol := by
  rcases eq_or_ne c 0 with (rfl | hc); · simp only [zero_smul, integral_zero]
  by_cases hf : Integrable I l f vol
  · exact (hf.hasIntegral.smul c).integral_eq
  · have : ¬Integrable I l (fun x => c • f x) vol := mt (fun h => h.of_smul hc) hf
    rw [integral]; rw [integral]; rw [dif_neg hf]; rw [dif_neg this]; rw [smul_zero]

open MeasureTheory

/--
theorem `integral_nonneg` / 定理 `integral_nonneg`

English:
theorem integral_nonneg
  statement: {g : Realⁿ -> Real} (hg : forall x in Box.Icc I, 0 <= g x) (μ : Measure Realⁿ)
  proof: by
  by_cases hgi : Integrable I l g μ.toBoxAdditive.toSMul
  · refine ge_of_tendsto' hgi.hasIntegral fun π => sum_nonneg fun J _ => ?_
    exact mul_nonneg ENNReal.toReal_nonneg (hg _ <| π.tag_mem_Icc _)
  · rw [integral, dif_neg hgi]

中文:
定理 integral_nonneg
  结论: {g : 实数ⁿ -> 实数} (hg : 对任意 x in Box.Icc I, 0 <= g x) (μ : Measure 实数ⁿ)
  证明: by
  by_cases hgi : Integrable I l g μ.toBoxAdditive.toSMul
  · refine ge_of_tendsto' hgi.hasIntegral fun π => sum_nonneg fun J _ => ?_
    exact mul_nonneg ENNReal.toReal_nonneg (hg _ <| π.tag_mem_Icc _)
  · rw [integral, dif_neg hgi]

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Integrable, dif_neg, ge_of_tendsto, hasIntegral, hgi.hasIntegral, integral, mul_nonneg, sum_nonneg, tag_mem_Icc, toBoxAdditive, toBoxAdditive.toSMul, toReal_nonneg, toSMul
-/
theorem integral_nonneg {g : Realⁿ -> Real} (hg : forall x in Box.Icc I, 0 <= g x) (μ : Measure Realⁿ)
    [IsLocallyFiniteMeasure μ] : 0 <= integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hgi : Integrable I l g μ.toBoxAdditive.toSMul
  · refine ge_of_tendsto' hgi.hasIntegral fun π => sum_nonneg fun J _ => ?_
    exact mul_nonneg ENNReal.toReal_nonneg (hg _ <| π.tag_mem_Icc _)
  · rw [integral, dif_neg hgi]

/--
theorem `norm_integral_le_of_norm_le` / 定理 `norm_integral_le_of_norm_le`

English:
theorem norm_integral_le_of_norm_le
  statement: {g : Realⁿ -> Real} (hle : forall x in Box.Icc I, ‖f x‖ <= g x)
  proof: by
  by_cases hfi : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
  · refine le_of_tendsto_of_tendsto' hfi.hasIntegral.norm hg.hasIntegral fun π => ?_
    refine norm_sum_le_of_le _ fun J _ => ?_
    simp only [BoxAdditiveMap.toSMul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      μ.toBoxA

中文:
定理 norm_integral_le_of_norm_le
  结论: {g : 实数ⁿ -> 实数} (hle : 对任意 x in Box.Icc I, ‖f x‖ <= g x)
  证明: by
  by_cases hfi : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
  · refine le_of_tendsto_of_tendsto' hfi.hasIntegral.norm hg.hasIntegral fun π => ?_
    refine norm_sum_le_of_le _ fun J _ => ?_
    simp only [BoxAdditiveMap.toSMul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      μ.toBoxA

Depends on / 依赖: BoxAdditiveMap, BoxAdditiveMap.toSMul_apply, Integrable, Real.norm_eq_abs, abs_of_nonneg, dif_neg, hasIntegral, hfi.hasIntegral.norm, hg.hasIntegral, integral, integral_nonneg, le_of_tendsto_of_tendsto, measureReal_nonneg, norm_eq_abs, norm_nonneg, norm_smul, norm_sum_le_of_le, norm_zero, smul_eq_mul, tag_mem_Icc
-/
theorem norm_integral_le_of_norm_le {g : Realⁿ -> Real} (hle : forall x in Box.Icc I, ‖f x‖ <= g x)
    (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] (hg : Integrable I l g μ.toBoxAdditive.toSMul) :
    ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ <= integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hfi : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
  · refine le_of_tendsto_of_tendsto' hfi.hasIntegral.norm hg.hasIntegral fun π => ?_
    refine norm_sum_le_of_le _ fun J _ => ?_
    simp only [BoxAdditiveMap.toSMul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      μ.toBoxAdditive_apply, abs_of_nonneg measureReal_nonneg]
    gcongr
exact hle _ π.tag_mem_Icc _
  · rw [integral, dif_neg hfi, norm_zero]
    exact integral_nonneg (fun x hx => (norm_nonneg _).trans (hle x hx)) μ

/--
theorem `norm_integral_le_of_le_const` / 定理 `norm_integral_le_of_le_const`

English:
theorem norm_integral_le_of_le_const
  statement: {c : Real}
  proof: by
  simpa only [integral_const] using! norm_integral_le_of_norm_le hc μ (integrable_const c)

中文:
定理 norm_integral_le_of_le_const
  结论: {c : 实数}
  证明: by
  simpa only [integral_const] using! norm_integral_le_of_norm_le hc μ (integrable_const c)

Depends on / 依赖: integrable_const, integral_const, norm_integral_le_of_norm_le
-/
theorem norm_integral_le_of_le_const {c : Real}
    (hc : forall x in Box.Icc I, ‖f x‖ <= c) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] :
    ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ <= μ.real I * c := by
  simpa only [integral_const] using! norm_integral_le_of_norm_le hc μ (integrable_const c)

/-!
### Henstock-Sacks inequality and integrability on subboxes

Henstock-Sacks inequality for Henstock-Kurzweil integral says the following. Let `f` be a function
integrable on a box `I`; let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged partition of
`I` subordinate to `r`, the integral sum over this partition is `ε`-close to the integral. Then for
any tagged prepartition (i.e. a finite collections of pairwise disjoint subboxes of `I` with tagged
points) `π`, the integral sum over `π` differs from the integral of `f` over the part of `I` covered
by `π` by at most `ε`. The actual statement in the library is a bit more complicated to make it work
for any `BoxIntegral.IntegrationParams`. We formalize several versions of this inequality in
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet`,
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`, and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.

Instead of using predicate assumptions on `r`, we define
`BoxIntegral.Integrable.convergenceR (h : integrable I l f vol) (ε : ℝ) (c : ℝ≥0) : ℝⁿ → (0, ∞)`
to be a function `r` such that

- if `l.bRiemann`, then `r` is a constant;
- if `ε > 0`, then for any tagged partition `π` of `I` subordinate to `r` (more precisely,
  satisfying the predicate `l.mem_base_set I c r`), the integral sum of `f` over `π` differs from
  the integral of `f` over `I` by at most `ε`.

The proof is mostly based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

-/
namespace Integrable

/--
Definition of `convergenceR` / `convergenceR` 的定义

English:
definition convergenceR
  signature: (h : Integrable I l f vol) (ε : Real)
  body: if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩

中文:
定义 convergenceR
  签名: (h : 整数egrable I l f vol) (ε : 实数)
  定义体: if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩

Depends on / 依赖: Set.mem_Ioi, h.hasIntegral, hasIntegral, hasIntegral_iff, mem_Ioi, zero_lt_one
-/
def convergenceR (h : Integrable I l f vol) (ε : Real) : Real>=0 -> Realⁿ -> Ioi (0 : Real) :=
  if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩

variable {c c₁ c₂ : Real>=0} {ε ε₁ ε₂ : Real} {π₁ π₂ : TaggedPrepartition I}

/--
theorem `convergenceR_cond` / 定理 `convergenceR_cond`

English:
theorem convergenceR_cond
  given: (h : Integrable I l f vol) (ε : Real) (c : Real>=0)
  proof: by
  rw [convergenceR]; split_ifs with h₀
  exacts [(hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.1 _, fun _ x => rfl]

中文:
定理 convergenceR_cond
  条件: (h : 整数egrable I l f vol) (ε : 实数) (c : 实数>=0)
  证明: by
  rw [convergenceR]; split_ifs with h₀
  exacts [(hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.1 _, fun _ x => rfl]

Depends on / 依赖: choose_spec, convergenceR, exacts, h.hasIntegral, hasIntegral, hasIntegral_iff, split_ifs
-/
theorem convergenceR_cond (h : Integrable I l f vol) (ε : Real) (c : Real>=0) :
    l.RCond (h.convergenceR ε c) := by
  rw [convergenceR]; split_ifs with h₀
  exacts [(hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.1 _, fun _ x => rfl]

/--
theorem `dist_integralSum_integral_le_of_memBaseSet` / 定理 `dist_integralSum_integral_le_of_memBaseSet`

English:
theorem dist_integralSum_integral_le_of_memBaseSet
  statement: (h : Integrable I l f vol) (h₀ : 0 < ε)
  proof: by
  rw [convergenceR]; rw [dif_pos h₀] at hπ
  exact (hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.2 c _ hπ hπp

中文:
定理 dist_integralSum_integral_le_of_memBaseSet
  结论: (h : 整数egrable I l f vol) (h₀ : 0 < ε)
  证明: by
  rw [convergenceR]; rw [dif_pos h₀] at hπ
  exact (hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.2 c _ hπ hπp

Depends on / 依赖: choose_spec, convergenceR, dif_pos, h.hasIntegral, hasIntegral, hasIntegral_iff
-/
theorem dist_integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.IsPartition) :
    dist (integralSum f vol π) (integral I l f vol) <= ε := by
  rw [convergenceR]; rw [dif_pos h₀] at hπ
  exact (hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.2 c _ hπ hπp

/--
theorem `dist_integralSum_le_of_memBaseSet` / 定理 `dist_integralSum_le_of_memBaseSet`

English:
theorem dist_integralSum_le_of_memBaseSet
  statement: (h : Integrable I l f vol) (hpos₁ : 0 < ε₁)
  proof: by
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩
  set r : Realⁿ -> Ioi (0 : Real) := fun x => min (h.convergenceR ε₁ c₁ x) (h.convergenceR ε₂ c₂ x)
  set πr := π.toSubordinate r
  have H₁ :
    dist (integralSum f vol (π₁.unionComplToSubordinate π hπU r)) (integral I l f vol) <= ε

中文:
定理 dist_integralSum_le_of_memBaseSet
  结论: (h : 整数egrable I l f vol) (hpos₁ : 0 < ε₁)
  证明: by
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩
  set r : Realⁿ -> Ioi (0 : Real) := fun x => min (h.convergenceR ε₁ c₁ x) (h.convergenceR ε₂ c₂ x)
  set πr := π.toSubordinate r
  have H₁ :
    dist (integralSum f vol (π₁.unionComplToSubordinate π hπU r)) (integral I l f vol) <= ε

Depends on / 依赖: convergenceR, dist_integralSum_integral_le_of_memBaseSet, exists_common_compl, h.convergenceR, h.dist_integralSum_integral_le_of_memBaseSet, integral, integralSum, isPartition_unionComplToSubordinate, min_le_left, toSubordinate, unionComplToSubordinate
-/
theorem dist_integralSum_le_of_memBaseSet (h : Integrable I l f vol) (hpos₁ : 0 < ε₁)
    (hpos₂ : 0 < ε₂) (h₁ : l.MemBaseSet I c₁ (h.convergenceR ε₁ c₁) π₁)
    (h₂ : l.MemBaseSet I c₂ (h.convergenceR ε₂ c₂) π₂) (HU : π₁.iUnion = π₂.iUnion) :
    dist (integralSum f vol π₁) (integralSum f vol π₂) <= ε₁ + ε₂ := by
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩
  set r : Realⁿ -> Ioi (0 : Real) := fun x => min (h.convergenceR ε₁ c₁ x) (h.convergenceR ε₂ c₂ x)
  set πr := π.toSubordinate r
  have H₁ :
    dist (integralSum f vol (π₁.unionComplToSubordinate π hπU r)) (integral I l f vol) <= ε₁ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₁
      (h₁.unionComplToSubordinate (fun _ _ => min_le_left _ _) hπU hπc₁)
      (isPartition_unionComplToSubordinate _ _ _ _)
  rw [HU] at hπU
  have H₂ :
    dist (integralSum f vol (π₂.unionComplToSubordinate π hπU r)) (integral I l f vol) <= ε₂ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₂
      (h₂.unionComplToSubordinate (fun _ _ => min_le_right _ _) hπU hπc₂)
      (isPartition_unionComplToSubordinate _ _ _ _)
  simpa [unionComplToSubordinate] using (dist_triangle_right _ _ _).trans (add_le_add H₁ H₂)

/--
theorem `tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity` / 定理 `tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity`

English:
theorem tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity
  given: (h : Integrable I l f vol)
  proof: by
  refine (((l.hasBasis_toFilter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 fun ε ε0 => ?_
  replace ε0 := half_pos ε0
  use h.convergenceR (ε / 2), h.convergenceR_cond (ε / 2); rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩
  rw [← add_halves ε]
  exact h.dist_integralSum_le_of_mem

中文:
定理 tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity
  条件: (h : 整数egrable I l f vol)
  证明: by
  refine (((l.hasBasis_toFilter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 fun ε ε0 => ?_
  replace ε0 := half_pos ε0
  use h.convergenceR (ε / 2), h.convergenceR_cond (ε / 2); rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩
  rw [← add_halves ε]
  exact h.dist_integralSum_le_of_mem

Depends on / 依赖: add_halves, choose_spec, convergenceR, convergenceR_cond, dist_integralSum_le_of_memBaseSet, h.convergenceR, h.convergenceR_cond, h.dist_integralSum_le_of_memBaseSet, half_pos, hasBasis_toFilter, inf_principal, l.hasBasis_toFilter, prod_self, prod_self.inf_principal, replace, tendsto_iff, uniformity_basis_dist_le
-/
theorem tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity (h : Integrable I l f vol) :
    Tendsto (fun π : TaggedPrepartition I × TaggedPrepartition I =>
      (integralSum f vol π.1, integralSum f vol π.2))
        ((l.toFilter I ×ˢ l.toFilter I) ⊓ 𝓟 {π | π.1.iUnion = π.2.iUnion}) (𝓤 F) := by
  refine (((l.hasBasis_toFilter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 fun ε ε0 => ?_
  replace ε0 := half_pos ε0
  use h.convergenceR (ε / 2), h.convergenceR_cond (ε / 2); rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩
  rw [← add_halves ε]
  exact h.dist_integralSum_le_of_memBaseSet ε0 ε0 h₁.choose_spec h₂.choose_spec hU

/--
theorem `cauchy_map_integralSum_toFilteriUnion` / 定理 `cauchy_map_integralSum_toFilteriUnion`

English:
theorem cauchy_map_integralSum_toFilteriUnion
  given: (h : Integrable I l f vol) (π₀ : Prepartition I)
  proof: by
  refine ⟨inferInstance, ?_⟩
  rw [prod_map_map_eq]; rw [← toFilter_inf_iUnion_eq]; rw [← prod_inf_prod]; rw [prod_principal_principal]
  exact h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left
    (inf_le_inf_left _ <| principal_mono.2 fun π h => h.1.trans h.2.symm)

中文:
定理 cauchy_map_integralSum_toFilteriUnion
  条件: (h : 整数egrable I l f vol) (π₀ : Prepartition I)
  证明: by
  refine ⟨inferInstance, ?_⟩
  rw [prod_map_map_eq]; rw [← toFilter_inf_iUnion_eq]; rw [← prod_inf_prod]; rw [prod_principal_principal]
  exact h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left
    (inf_le_inf_left _ <| principal_mono.2 fun π h => h.1.trans h.2.symm)

Depends on / 依赖: h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left, inf_le_inf_left, mono_left, principal_mono, prod_inf_prod, prod_map_map_eq, prod_principal_principal, tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity, toFilter_inf_iUnion_eq
-/
theorem cauchy_map_integralSum_toFilteriUnion (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Cauchy ((l.toFilteriUnion I π₀).map (integralSum f vol)) := by
  refine ⟨inferInstance, ?_⟩
  rw [prod_map_map_eq]; rw [← toFilter_inf_iUnion_eq]; rw [← prod_inf_prod]; rw [prod_principal_principal]
  exact h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left
    (inf_le_inf_left _ <| principal_mono.2 fun π h => h.1.trans h.2.symm)

variable [CompleteSpace F]

/--
theorem `to_subbox_aux` / 定理 `to_subbox_aux`

English:
theorem to_subbox_aux
  given: (h : Integrable I l f vol) (hJ : J <= I)
  proof: by
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integralSum_toFilteriUnion (.single I J hJ))).imp fun y hy => ⟨?_, hy⟩
  convert!
    hy.comp
      (l.tendsto_embedBox_toFilteriUnion_top hJ) -- faster than `exact` here
         -- faster than `exact` here

中文:
定理 to_subbox_aux
  条件: (h : 整数egrable I l f vol) (hJ : J <= I)
  证明: by
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integralSum_toFilteriUnion (.single I J hJ))).imp fun y hy => ⟨?_, hy⟩
  convert!
    hy.comp
      (l.tendsto_embedBox_toFilteriUnion_top hJ) -- faster than `exact` here
         -- faster than `exact` here

Depends on / 依赖: cauchy_map_iff_exists_tendsto, cauchy_map_integralSum_toFilteriUnion, convert, faster, h.cauchy_map_integralSum_toFilteriUnion, hy.comp, l.tendsto_embedBox_toFilteriUnion_top, single, tendsto_embedBox_toFilteriUnion_top
-/
theorem to_subbox_aux (h : Integrable I l f vol) (hJ : J <= I) :
    exists y : F, HasIntegral J l f vol y ∧
      Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ)) (𝓝 y) := by
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integralSum_toFilteriUnion (.single I J hJ))).imp fun y hy => ⟨?_, hy⟩
  convert!
    hy.comp
      (l.tendsto_embedBox_toFilteriUnion_top hJ) -- faster than `exact` here
         -- faster than `exact` here

/--
theorem `to_subbox` / 定理 `to_subbox`

English:
theorem to_subbox
  given: (h : Integrable I l f vol) (hJ : J <= I)
  statement: Integrable J l f vol
  proof: (h.to_subbox_aux hJ).imp fun _ => And.left

中文:
定理 to_subbox
  条件: (h : 整数egrable I l f vol) (hJ : J <= I)
  结论: 整数egrable J l f vol
  证明: (h.to_subbox_aux hJ).imp fun _ => And.left

Depends on / 依赖: And.left, h.to_subbox_aux, to_subbox_aux
-/
theorem to_subbox (h : Integrable I l f vol) (hJ : J <= I) : Integrable J l f vol :=
  (h.to_subbox_aux hJ).imp fun _ => And.left

/--
theorem `tendsto_integralSum_toFilteriUnion_single` / 定理 `tendsto_integralSum_toFilteriUnion_single`

English:
theorem tendsto_integralSum_toFilteriUnion_single
  given: (h : Integrable I l f vol) (hJ : J <= I)
  proof: let ⟨_y, h₁, h₂⟩ := h.to_subbox_aux hJ
  h₁.integral_eq.symm ▸ h₂

中文:
定理 tendsto_integralSum_toFilteriUnion_single
  条件: (h : 整数egrable I l f vol) (hJ : J <= I)
  证明: let ⟨_y, h₁, h₂⟩ := h.to_subbox_aux hJ
  h₁.integral_eq.symm ▸ h₂

Depends on / 依赖: h.to_subbox_aux, integral_eq, integral_eq.symm, to_subbox_aux
-/
theorem tendsto_integralSum_toFilteriUnion_single (h : Integrable I l f vol) (hJ : J <= I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ))
      (𝓝 <| integral J l f vol) :=
  let ⟨_y, h₁, h₂⟩ := h.to_subbox_aux hJ
  h₁.integral_eq.symm ▸ h₂

/--
theorem `dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq` / 定理 `dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`

English:
theorem dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq
  statement: (h : Integrable I l f vol)
  proof: by
  -- Let us prove that the distance is less than or equal to `ε + δ` for all positive `δ`.
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  -- First we choose some constants.
  set δ' : Real := δ / (#π₀.boxes + 1)
  have H0 : 0 < (#π₀.boxes + 1 : Real) := Nat.cast_add_one_pos _
  have δ'0 : 0 < 

中文:
定理 dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq
  结论: (h : 整数egrable I l f vol)
  证明: by
  -- Let us prove that the distance is less than or equal to `ε + δ` for all positive `δ`.
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  -- First we choose some constants.
  set δ' : Real := δ / (#π₀.boxes + 1)
  have H0 : 0 < (#π₀.boxes + 1 : Real) := Nat.cast_add_one_pos _
  have δ'0 : 0 < 
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Integrable I l f vol)
    (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) {π₀ : Prepartition I}
    (hU : π.iUnion = π₀.iUnion) :
    dist (integralSum f vol π) (∑ J in π₀.boxes, integral J l f vol) <= ε := by
  -- Let us prove that the distance is less than or equal to `ε + δ` for all positive `δ`.
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  -- First we choose some constants.
  set δ' : Real := δ / (#π₀.boxes + 1)
  have H0 : 0 < (#π₀.boxes + 1 : Real) := Nat.cast_add_one_pos _
  have δ'0 : 0 < δ' := div_pos δ0 H0
  set C := max π₀.distortion π₀.compl.distortion
  /- Next we choose a tagged partition of each `J ∈ π₀` such that the integral sum of `f` over this
    partition is `δ'`-close to the integral of `f` over `J`. -/
  have : forall J in π₀, exists πi : TaggedPrepartition J,
      πi.IsPartition ∧ dist (integralSum f vol πi) (integral J l f vol) <= δ' ∧
        l.MemBaseSet J C (h.convergenceR δ' C) πi := by
    intro J hJ
    have Hle : J <= I := π₀.le_of_mem hJ
    have HJi : Integrable J l f vol := h.to_subbox Hle
    set r := fun x => min (h.convergenceR δ' C x) (HJi.convergenceR δ' C x)
    have hJd : J.distortion <= C := le_trans (Finset.le_sup hJ) (le_max_left _ _)
    rcases l.exists_memBaseSet_isPartition J hJd r with ⟨πJ, hC, hp⟩
    have hC₁ : l.MemBaseSet J C (HJi.convergenceR δ' C) πJ := by
      refine hC.mono J le_rfl le_rfl fun x _ => ?_; exact min_le_right _ _
    have hC₂ : l.MemBaseSet J C (h.convergenceR δ' C) πJ := by
      refine hC.mono J le_rfl le_rfl fun x _ => ?_; exact min_le_left _ _
    exact ⟨πJ, hp, HJi.dist_integralSum_integral_le_of_memBaseSet δ'0 hC₁ hp, hC₂⟩
  /- Now we combine these tagged partitions into a tagged prepartition of `I` that covers the
    same part of `I` as `π₀` and apply `BoxIntegral.dist_integralSum_le_of_memBaseSet` to
    `π` and this prepartition. -/
  choose! πi hπip hπiδ' hπiC using this
  have : l.MemBaseSet I C (h.convergenceR δ' C) (π₀.biUnionTagged πi) :=
    biUnionTagged_memBaseSet hπiC hπip fun _ => le_max_right _ _
  have hU' : π.iUnion = (π₀.biUnionTagged πi).iUnion :=
    hU.trans (Prepartition.iUnion_biUnion_partition _ hπip).symm
  have := h.dist_integralSum_le_of_memBaseSet h0 δ'0 hπ this hU'
  rw [integralSum_biUnionTagged] at this
  calc
    dist (integralSum f vol π) (∑ J in π₀.boxes, integral J l f vol) <=
        dist (integralSum f vol π) (∑ J in π₀.boxes, integralSum f vol (πi J)) +
          dist (∑ J in π₀.boxes, integralSum f vol (πi J)) (∑ J in π₀.boxes, integral J l f vol) :=
      dist_triangle _ _ _
    _ <= ε + δ' + ∑ _J in π₀.boxes, δ' := add_le_add this (dist_sum_sum_le_of_le _ hπiδ')
    _ = ε + δ := by simp [field, δ']; ring

/--
theorem `dist_integralSum_sum_integral_le_of_memBaseSet` / 定理 `dist_integralSum_sum_integral_le_of_memBaseSet`

English:
theorem dist_integralSum_sum_integral_le_of_memBaseSet
  statement: (h : Integrable I l f vol) (h0 : 0 < ε)
  proof: h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq h0 hπ rfl

中文:
定理 dist_integralSum_sum_integral_le_of_memBaseSet
  结论: (h : 整数egrable I l f vol) (h0 : 0 < ε)
  证明: h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq h0 hπ rfl

Depends on / 依赖: dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq, h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h0 : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) :
    dist (integralSum f vol π) (∑ J in π.boxes, integral J l f vol) <= ε :=
  h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq h0 hπ rfl

/--
theorem `tendsto_integralSum_sum_integral` / 定理 `tendsto_integralSum_sum_integral`

English:
theorem tendsto_integralSum_sum_integral
  given: (h : Integrable I l f vol) (π₀ : Prepartition I)
  proof: by
  refine ((l.hasBasis_toFilteriUnion I π₀).tendsto_iff nhds_basis_closedBall).2 fun ε ε0 => ?_
  refine ⟨h.convergenceR ε, h.convergenceR_cond ε, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hc, hU⟩
  exact h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq ε0 hc hU

中文:
定理 tendsto_integralSum_sum_integral
  条件: (h : 整数egrable I l f vol) (π₀ : Prepartition I)
  证明: by
  refine ((l.hasBasis_toFilteriUnion I π₀).tendsto_iff nhds_basis_closedBall).2 fun ε ε0 => ?_
  refine ⟨h.convergenceR ε, h.convergenceR_cond ε, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hc, hU⟩
  exact h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq ε0 hc hU

Depends on / 依赖: convergenceR, convergenceR_cond, dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq, h.convergenceR, h.convergenceR_cond, h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq, hasBasis_toFilteriUnion, l.hasBasis_toFilteriUnion, mem_ofPred_eq, nhds_basis_closedBall, tendsto_iff
-/
theorem tendsto_integralSum_sum_integral (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I π₀)
      (𝓝 <| ∑ J in π₀.boxes, integral J l f vol) := by
  refine ((l.hasBasis_toFilteriUnion I π₀).tendsto_iff nhds_basis_closedBall).2 fun ε ε0 => ?_
  refine ⟨h.convergenceR ε, h.convergenceR_cond ε, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hc, hU⟩
  exact h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq ε0 hc hU

/--
theorem `sum_integral_congr` / 定理 `sum_integral_congr`

English:
theorem sum_integral_congr
  statement: (h : Integrable I l f vol) {π₁ π₂ : Prepartition I}
  proof: by
  refine tendsto_nhds_unique (h.tendsto_integralSum_sum_integral π₁) ?_
  rw [l.toFilteriUnion_congr _ hU]
  exact h.tendsto_integralSum_sum_integral π₂

中文:
定理 sum_integral_congr
  结论: (h : 整数egrable I l f vol) {π₁ π₂ : Prepartition I}
  证明: by
  refine tendsto_nhds_unique (h.tendsto_integralSum_sum_integral π₁) ?_
  rw [l.toFilteriUnion_congr _ hU]
  exact h.tendsto_integralSum_sum_integral π₂

Depends on / 依赖: h.tendsto_integralSum_sum_integral, l.toFilteriUnion_congr, tendsto_integralSum_sum_integral, tendsto_nhds_unique, toFilteriUnion_congr
-/
theorem sum_integral_congr (h : Integrable I l f vol) {π₁ π₂ : Prepartition I}
    (hU : π₁.iUnion = π₂.iUnion) :
    ∑ J in π₁.boxes, integral J l f vol = ∑ J in π₂.boxes, integral J l f vol := by
  refine tendsto_nhds_unique (h.tendsto_integralSum_sum_integral π₁) ?_
  rw [l.toFilteriUnion_congr _ hU]
  exact h.tendsto_integralSum_sum_integral π₂

/-- If `f` is integrable on `I`, then `fun J ↦ integral J l f vol` is box-additive on subboxes of
`I`: if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `BoxIntegral.Integrable.sum_integral_congr` for an unbundled version. -/
@[simps]
/--
Definition of `toBoxAdditive` / `toBoxAdditive` 的定义

English:
definition toBoxAdditive
  signature: (h : Integrable I l f vol)
  body: integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ]; rw [Prepartition.top_boxes]; rw [sum_singleton]

中文:
定义 toBoxAdditive
  签名: (h : 整数egrable I l f vol)
  定义体: integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ]; rw [Prepartition.top_boxes]; rw [sum_singleton]

Depends on / 依赖: integral
-/
def toBoxAdditive (h : Integrable I l f vol) : ι ->ᵇᵃ[I] F where
  toFun J := integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ]; rw [Prepartition.top_boxes]; rw [sum_singleton]

end Integrable

open MeasureTheory

/-!
### Integrability conditions
-/

open Prepartition EMetric ENNReal BoxAdditiveMap Finset Metric TaggedPrepartition

variable (l)

/--
theorem `integrable_of_bounded_and_ae_continuousWithinAt` / 定理 `integrable_of_bounded_and_ae_continuousWithinAt`

English:
theorem integrable_of_bounded_and_ae_continuousWithinAt
  statement: [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
  proof: by
  /- We prove that f is integrable by proving that we can ensure that the integrals over any
     two tagged prepartitions π₁ and π₂ can be made ε-close by making the partitions
     sufficiently fine.

     Start by defining some constants C, ε₁, ε₂ that will be useful later. -/
  refine integra

中文:
定理 integrable_of_bounded_and_ae_continuousWithinAt
  结论: [CompleteSpace E] {I : Box ι} {f : 实数ⁿ -> E}
  证明: by
  /- We prove that f is integrable by proving that we can ensure that the integrals over any
     two tagged prepartitions π₁ and π₂ can be made ε-close by making the partitions
     sufficiently fine.

     Start by defining some constants C, ε₁, ε₂ that will be useful later. -/
  refine integra
-/
theorem integrable_of_bounded_and_ae_continuousWithinAt [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
    (hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ]
    (hc : forallᵐ x ∂(μ.restrict (Box.Icc I)), ContinuousWithinAt f (Box.Icc I) x) :
    Integrable I l f μ.toBoxAdditive.toSMul := by
  /- We prove that f is integrable by proving that we can ensure that the integrals over any
     two tagged prepartitions π₁ and π₂ can be made ε-close by making the partitions
     sufficiently fine.

     Start by defining some constants C, ε₁, ε₂ that will be useful later. -/
  refine integrable_iff_cauchy_basis.2 fun ε ε0 => ?_
  rcases exists_pos_mul_lt ε0 (2 * μ.toBoxAdditive I) with ⟨ε₁, ε₁0, hε₁⟩
  rcases hb with ⟨C, hC⟩
  have C0 : 0 <= C := by
    obtain ⟨x, hx⟩ := BoxIntegral.Box.nonempty_coe I
exact le_trans (norm_nonneg (f x)) hC x (I.coe_subset_Icc hx)
  rcases exists_pos_mul_lt ε0 (4 * C) with ⟨ε₂, ε₂0, hε₂⟩
have ε₂0' : ENNReal.ofReal ε₂ != 0 := ne_of_gt ofReal_pos.2 ε₂0
  -- The set of discontinuities of f is contained in an open set U with μ U < ε₂.
  let D := { x in Box.Icc I | ¬ ContinuousWithinAt f (Box.Icc I) x }
  let μ' := μ.restrict (Box.Icc I)
  have μ'D : μ' D = 0 := by
    rcases eventually_iff_exists_mem.1 hc with ⟨V, ae, hV⟩
    exact eq_of_le_of_not_lt (mem_ae_iff.1 ae ▸ (μ'.mono <| fun x h xV => h.2 (hV x xV)))
      _root_.not_lt_zero
  obtain ⟨U, UD, Uopen, hU⟩ := Set.exists_isOpen_lt_add D (show μ' D != ⊤ by simp [μ'D]) ε₂0'
  rw [μ'D]; rw [zero_add] at hU
  /- Box.Icc I \ U is compact and avoids discontinuities of f, so there exists r > 0 such that for
     every x ∈ Box.Icc I \ U, the oscillation (within Box.Icc I) of f on the ball of radius r
     centered at x is ≤ ε₁ -/
  have comp : IsCompact (Box.Icc I \ U) :=
    I.isCompact_Icc.of_isClosed_subset (I.isCompact_Icc.isClosed.sdiff Uopen) Set.sdiff_subset
  have : forall x in (Box.Icc I \ U), oscillationWithin f (Box.Icc I) x < (ENNReal.ofReal ε₁) := by
    intro x hx
    suffices oscillationWithin f (Box.Icc I) x = 0 by rw [this]; exact ofReal_pos.2 ε₁0
    simpa [OscillationWithin.eq_zero_iff_continuousWithinAt, D, hx.1] using hx.2 ∘ (fun a => UD a)
  rcases comp.uniform_oscillationWithin this with ⟨r, r0, hr⟩
  /- We prove the claim for partitions π₁ and π₂ subordinate to r/2, by writing the difference as
     an integralSum over π₁ ⊓ π₂ and considering separately the boxes of π₁ ⊓ π₂ which are/aren't
     fully contained within U. -/
  refine ⟨fun _ _ => ⟨r / 2, half_pos r0⟩, fun _ _ _ => rfl, fun c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p => ?_⟩
  simp only [dist_eq_norm, integralSum_sub_partitions _ _ h₁p h₂p, toSMul_apply, ← smul_sub]
  have μI : μ I < ⊤ := lt_of_le_of_lt (μ.mono I.coe_subset_Icc) I.isCompact_Icc.measure_lt_top
  let t₁ (J : Box ι) : Realⁿ := (π₁.infPrepartition π₂.toPrepartition).tag J
  let t₂ (J : Box ι) : Realⁿ := (π₂.infPrepartition π₁.toPrepartition).tag J
  let B := (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes
  classical
  let B' := {J in B | J.toSet subseteq U}
  have hB' : B' subseteq B := B.filter_subset (fun J => J.toSet subseteq U)
  have μJ_ne_top : forall J in B, μ J != ⊤ :=
fun J hJ => lt_top_iff_ne_top.1 lt_of_le_of_lt (μ.mono (Prepartition.le_of_mem' _ J hJ)) μI
  have un : forall S subseteq B, ⋃ J in S, J.toSet subseteq I.toSet :=
    fun S hS => iUnion_subset_iff.2 (fun J => iUnion_subset_iff.2 fun hJ => le_of_mem' _ J (hS hJ))
  rw [← sum_sdiff hB']; rw [← add_halves ε]
  apply le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  /- If a box J is not contained within U, then the oscillation of f on J is small, which bounds
     the contribution of J to the overall sum. -/
  · have : forall J in B \ B', ‖μ.toBoxAdditive J • (f (t₁ J) - f (t₂ J))‖ <= μ.toBoxAdditive J * ε₁ := by
      intro J hJ
      rw [Finset.mem_sdiff]; rw [B.mem_filter]; rw [not_and] at hJ
      rw [norm_smul]; rw [μ.toBoxAdditive_apply]; rw [Real.norm_of_nonneg measureReal_nonneg]
      gcongr _ * ?_
      obtain ⟨x, xJ, xnU⟩ : exists x in J, x ∉ U := Set.not_subset.1 (hJ.2 hJ.1)
      have hx : x in Box.Icc I \ U := ⟨Box.coe_subset_Icc ((le_of_mem' _ J hJ.1) xJ), xnU⟩
      have ineq : edist (f (t₁ J)) (f (t₂ J)) <= ediam (f '' (ball x r inter (Box.Icc I))) := by
        apply edist_le_ediam_of_mem <;>
          refine Set.mem_image_of_mem f ⟨?_, tag_mem_Icc _ J⟩ <;>
refine closedBall_subset_ball (div_two_lt_of_pos r0) mem_closedBall_comm.1 ?_
        · exact h₁.isSubordinate.infPrepartition π₂.toPrepartition J hJ.1 (Box.coe_subset_Icc xJ)
        · exact h₂.isSubordinate.infPrepartition π₁.toPrepartition J
            ((π₁.mem_infPrepartition_comm).1 hJ.1) (Box.coe_subset_Icc xJ)
      rw [← Metric.eball_ofReal] at ineq
      simpa only [edist_le_ofReal (le_of_lt ε₁0), dist_eq_norm, hJ.1] using ineq.trans (hr x hx)
refine (norm_sum_le _ _).trans (sum_le_sum this).trans ?_
    rw [← sum_mul]
    trans μ.toBoxAdditive I * ε₁; swap
    · linarith
    simp_rw [mul_le_mul_iff_left₀ ε₁0, μ.toBoxAdditive_apply]
refine le_trans ?_ toReal_mono (lt_top_iff_ne_top.1 μI) μ.mono un (B \ B') sdiff_subset
    simp_rw [measureReal_def]
    rw [← toReal_sum (fun J hJ => μJ_ne_top J (mem_sdiff.1 hJ).1)]; rw [← Finset.tsum_subtype]
    refine (toReal_mono <| ne_of_lt <| lt_of_le_of_lt (μ.mono <| un (B \ B') sdiff_subset) μI) ?_
    refine le_of_eq (measure_biUnion (countable_toSet _) ?_ (fun J _ => J.measurableSet_coe)).symm
    exact fun J hJ J' hJ' hJJ' => pairwiseDisjoint _ (mem_sdiff.1 hJ).1 (mem_sdiff.1 hJ').1 hJJ'
  -- The contribution of the boxes contained within U is bounded because f is bounded and μ U < ε₂.
  · have : forall J in B', ‖μ.toBoxAdditive J • (f (t₁ J) - f (t₂ J))‖ <= μ.toBoxAdditive J * (2 * C) := by
      intro J _
      rw [norm_smul]; rw [μ.toBoxAdditive_apply]; rw [Real.norm_of_nonneg measureReal_nonneg]; rw [two_mul]
      gcongr
      apply norm_sub_le_of_le <;> exact hC _ (TaggedPrepartition.tag_mem_Icc _ J)
    apply (norm_sum_le_of_le B' this).trans
    simp_rw [← sum_mul, μ.toBoxAdditive_apply, measureReal_def,
      ← toReal_sum (fun J hJ => μJ_ne_top J (hB' hJ))]
    suffices (∑ J in B', μ J).toReal <= ε₂ by
      linarith [mul_le_mul_of_nonneg_right this <| (mul_nonneg_iff_of_pos_left two_pos).2 C0]
    rw [← toReal_ofReal (le_of_lt ε₂0)]
    refine toReal_mono ofReal_ne_top (le_trans ?_ (le_of_lt hU))
    trans μ' (⋃ J in B', J)
    · simp only [μ', μ.restrict_eq_self <| (un _ hB').trans I.coe_subset_Icc]
exact le_of_eq Eq.symm measure_biUnion_finset
        (fun J hJ K hK hJK => pairwiseDisjoint _ (hB' hJ) (hB' hK) hJK) fun J _ => J.measurableSet_coe
    · apply μ'.mono
      simp_rw [iUnion_subset_iff]
      exact fun J hJ => (mem_filter.1 hJ).2

/--
theorem `integrable_of_bounded_and_ae_continuous` / 定理 `integrable_of_bounded_and_ae_continuous`

English:
theorem integrable_of_bounded_and_ae_continuous
  statement: [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
  proof: integrable_of_bounded_and_ae_continuousWithinAt l hb μ
    Eventually.filter_mono (ae_mono μ.restrict_le_self) (hc.mono fun _ h => h.continuousWithinAt)

中文:
定理 integrable_of_bounded_and_ae_continuous
  结论: [CompleteSpace E] {I : Box ι} {f : 实数ⁿ -> E}
  证明: integrable_of_bounded_and_ae_continuousWithinAt l hb μ
    Eventually.filter_mono (ae_mono μ.restrict_le_self) (hc.mono fun _ h => h.continuousWithinAt)

Depends on / 依赖: Eventually, Eventually.filter_mono, ae_mono, continuousWithinAt, filter_mono, h.continuousWithinAt, hc.mono, integrable_of_bounded_and_ae_continuousWithinAt, restrict_le_self
-/
theorem integrable_of_bounded_and_ae_continuous [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
    (hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ]
    (hc : forallᵐ x ∂μ, ContinuousAt f x) : Integrable I l f μ.toBoxAdditive.toSMul :=
integrable_of_bounded_and_ae_continuousWithinAt l hb μ
    Eventually.filter_mono (ae_mono μ.restrict_le_self) (hc.mono fun _ h => h.continuousWithinAt)


/--
theorem `integrable_of_continuousOn` / 定理 `integrable_of_continuousOn`

English:
theorem integrable_of_continuousOn
  statement: [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
  proof: by
  apply integrable_of_bounded_and_ae_continuousWithinAt
  · obtain ⟨C, hC⟩ := (NormedSpace.isBounded_iff_subset_smul_closedBall Real).1
                        (I.isCompact_Icc.image_of_continuousOn hc).isBounded
    use ‖C‖, fun x hx => by
      simpa only [smul_unitClosedBall, mem_closedBall_ze

中文:
定理 integrable_of_continuousOn
  结论: [CompleteSpace E] {I : Box ι} {f : 实数ⁿ -> E}
  证明: by
  apply integrable_of_bounded_and_ae_continuousWithinAt
  · obtain ⟨C, hC⟩ := (NormedSpace.isBounded_iff_subset_smul_closedBall Real).1
                        (I.isCompact_Icc.image_of_continuousOn hc).isBounded
    use ‖C‖, fun x hx => by
      simpa only [smul_unitClosedBall, mem_closedBall_ze

Depends on / 依赖: I.isCompact_Icc.image_of_continuousOn, I.measurableSet_Icc, MeasurableSet, MeasurableSet.compl_iff, NormedSpace, NormedSpace.isBounded_iff_subset_smul_closedBall, Set.mem_image_of_mem, compl_iff, continuousWithinAt, eventually_of_mem, hc.continuousWithinAt, image_of_continuousOn, integrable_of_bounded_and_ae_continuousWithinAt, isBounded, isBounded_iff_subset_smul_closedBall, isCompact_Icc, measurableSet_Icc, mem_ae_iff, mem_closedBall_zero_iff, mem_image_of_mem
-/
theorem integrable_of_continuousOn [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E}
    (hc : ContinuousOn f (Box.Icc I)) (μ : Measure Realⁿ) [IsLocallyFiniteMeasure μ] :
    Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul := by
  apply integrable_of_bounded_and_ae_continuousWithinAt
  · obtain ⟨C, hC⟩ := (NormedSpace.isBounded_iff_subset_smul_closedBall Real).1
                        (I.isCompact_Icc.image_of_continuousOn hc).isBounded
    use ‖C‖, fun x hx => by
      simpa only [smul_unitClosedBall, mem_closedBall_zero_iff] using hC (Set.mem_image_of_mem f hx)
  · refine eventually_of_mem ?_ (fun x hx => hc.continuousWithinAt hx)
    rw [mem_ae_iff]; rw [μ.restrict_apply] <;> simp [MeasurableSet.compl_iff.2 I.measurableSet_Icc]

variable {l}

/--
theorem `HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO` / 定理 `HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO`

English:
theorem HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO
  statement: (hl : l.bRiemann = false)
  proof: by
  /- We choose `r x` differently for `x ∈ s` and `x ∉ s`.

    For `x ∈ s`, we choose `εs` such that `∑' x : s, εs x < ε / 2 / 2 ^ #ι`, then choose `r x` so
    that `dist (vol J (f x)) (g J) ≤ εs x` for `J` in the `r x`-neighborhood of `x`. This guarantees
    that the sum of these distances ove

中文:
定理 HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO
  结论: (hl : l.bRiemann = false)
  证明: by
  /- We choose `r x` differently for `x ∈ s` and `x ∉ s`.

    For `x ∈ s`, we choose `εs` such that `∑' x : s, εs x < ε / 2 / 2 ^ #ι`, then choose `r x` so
    that `dist (vol J (f x)) (g J) ≤ εs x` for `J` in the `r x`-neighborhood of `x`. This guarantees
    that the sum of these distances ove
-/
theorem HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (hl : l.bRiemann = false)
    (B : ι ->ᵇᵃ[I] Real) (hB0 : forall J, 0 <= B J) (g : ι ->ᵇᵃ[I] F) (s : Set Realⁿ) (hs : s.Countable)
    (hlH : s.Nonempty -> l.bHenstock = true)
    (H₁ : forall (c : Real>=0), forall x in Box.Icc I inter s, forall ε > (0 : Real),
      exists δ > 0, forall J <= I, Box.Icc J subseteq Metric.closedBall x δ -> x in Box.Icc J ->
        (l.bDistortion -> J.distortion <= c) -> dist (vol J (f x)) (g J) <= ε)
    (H₂ : forall (c : Real>=0), forall x in Box.Icc I \ s, forall ε > (0 : Real),
      exists δ > 0, forall J <= I, Box.Icc J subseteq Metric.closedBall x δ -> (l.bHenstock -> x in Box.Icc J) ->
        (l.bDistortion -> J.distortion <= c) -> dist (vol J (f x)) (g J) <= ε * B J) :
    HasIntegral I l f vol (g I) := by
  /- We choose `r x` differently for `x ∈ s` and `x ∉ s`.

    For `x ∈ s`, we choose `εs` such that `∑' x : s, εs x < ε / 2 / 2 ^ #ι`, then choose `r x` so
    that `dist (vol J (f x)) (g J) ≤ εs x` for `J` in the `r x`-neighborhood of `x`. This guarantees
    that the sum of these distances over boxes `J` such that `π.tag J ∈ s` is less than `ε / 2`. We
    need an additional multiplier `2 ^ #ι` because different boxes can have the same tag.

    For `x ∉ s`, we choose `r x` so that `dist (vol (J (f x))) (g J) ≤ (ε / 2 / B I) * B J` for a
    box `J` in the `δ`-neighborhood of `x`. -/
  refine ((l.hasBasis_toFilteriUnion_top _).tendsto_iff Metric.nhds_basis_closedBall).2 ?_
  intro ε ε0
  simp only [← exists_prop, gt_iff_lt, Subtype.exists'] at H₁ H₂
  choose! δ₁ Hδ₁ using H₁
  choose! δ₂ Hδ₂ using H₂
  have ε0' := half_pos ε0; have H0 : 0 < (2 : Real) ^ Fintype.card ι := pow_pos zero_lt_two _
  rcases hs.exists_pos_forall_sum_le (div_pos ε0' H0) with ⟨εs, hεs0, hεs⟩
  simp only [le_div_iff₀' H0, mul_sum] at hεs
  rcases exists_pos_mul_lt ε0' (B I) with ⟨ε', ε'0, hεI⟩
  classical
  set δ : Real>=0 -> Realⁿ -> Ioi (0 : Real) := fun c x => if x in s then δ₁ c x (εs x) else (δ₂ c) x ε'
  refine ⟨δ, fun c => l.rCond_of_bRiemann_eq_false hl, ?_⟩
  simp only [mem_ofPred_eq]
  rintro π ⟨c, hπδ, hπp⟩
  -- Now we split the sum into two parts based on whether `π.tag J` belongs to `s` or not.
  rw [← g.sum_partition_boxes le_rfl hπp]; rw [Metric.mem_closedBall]; rw [integralSum]; rw [← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J in s]; rw [← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J in s]; rw [← add_halves ε]
  refine dist_add_add_le_of_le ?_ ?_
  · rcases s.eq_empty_or_nonempty with (rfl | hsne); · simp [ε0'.le]
    /- For the boxes such that `π.tag J ∈ s`, we use the fact that at most `2 ^ #ι` boxes have the
        same tag. -/
    specialize hlH hsne
    have : forall J in {J in π.boxes | π.tag J in s},
        dist (vol J (f <| π.tag J)) (g J) <= εs (π.tag J) := fun J hJ => by
      rw [Finset.mem_filter] at hJ; obtain ⟨hJ, hJs⟩ := hJ
      refine Hδ₁ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ (hεs0 _) _ (π.le_of_mem' _ hJ) ?_
        (hπδ.2 hlH J hJ) fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert! hπδ.1 J hJ using 3; exact (if_pos hJs).symm
    refine (dist_sum_sum_le_of_le _ this).trans ?_
    rw [sum_comp]
    refine (sum_le_sum ?_).trans (hεs _ ?_)
    · rintro b -
      rw [← Nat.cast_two]; rw [← Nat.cast_pow]; rw [← nsmul_eq_mul]
      refine nsmul_le_nsmul_left (hεs0 _).le ?_
      refine (Finset.card_le_card ?_).trans ((hπδ.isHenstock hlH).card_filter_tag_eq_le b)
      exact filter_subset_filter _ (filter_subset _ _)
    · rw [Finset.coe_image, Set.image_subset_iff]
      exact fun J hJ => (Finset.mem_filter.1 hJ).2
  /- Now we deal with boxes such that `π.tag J ∉ s`.
    In this case the estimate is straightforward. -/
  calc
    dist (∑ J in π.boxes with tag π J ∉ s, vol J (f (tag π J)))
      (∑ J in π.boxes with tag π J ∉ s, g J)
      <= ∑ J in π.boxes with tag π J ∉ s, ε' * B J := dist_sum_sum_le_of_le _ fun J hJ => by
      rw [Finset.mem_filter] at hJ; obtain ⟨hJ, hJs⟩ := hJ
      refine Hδ₂ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ ε'0 _ (π.le_of_mem' _ hJ) ?_ (fun hH => hπδ.2 hH J hJ)
        fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert! hπδ.1 J hJ using 3; exact (if_neg hJs).symm
    _ <= ∑ J in π.boxes, ε' * B J := by
      gcongr
      · exact fun _ _ _ => mul_nonneg ε'0.le (hB0 _)
      · apply filter_subset
    _ = B I * ε' := by rw [← mul_sum, B.sum_partition_boxes le_rfl hπp, mul_comm]
    _ <= ε / 2 := hεI.le

/--
theorem `HasIntegral.of_le_Henstock_of_forall_isLittleO` / 定理 `HasIntegral.of_le_Henstock_of_forall_isLittleO`

English:
theorem HasIntegral.of_le_Henstock_of_forall_isLittleO
  statement: (hl : l <= Henstock) (B : ι ->ᵇᵃ[I] Real)
  proof: have A : l.bHenstock := Bool.eq_true_of_true_le hl.2.1
  HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (Bool.eq_false_of_le_false hl.1) B hB0 _ s hs
(fun _ => A) H₁ by simpa only [A, true_imp_iff] using H₂

中文:
定理 HasIntegral.of_le_Henstock_of_forall_isLittleO
  结论: (hl : l <= Henstock) (B : ι ->ᵇᵃ[I] 实数)
  证明: have A : l.bHenstock := Bool.eq_true_of_true_le hl.2.1
  HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (Bool.eq_false_of_le_false hl.1) B hB0 _ s hs
(fun _ => A) H₁ by simpa only [A, true_imp_iff] using H₂

Depends on / 依赖: Bool.eq_false_of_le_false, Bool.eq_true_of_true_le, HasIntegral, HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO, bHenstock, eq_false_of_le_false, eq_true_of_true_le, l.bHenstock, of_bRiemann_eq_false_of_forall_isLittleO, true_imp_iff
-/
theorem HasIntegral.of_le_Henstock_of_forall_isLittleO (hl : l <= Henstock) (B : ι ->ᵇᵃ[I] Real)
    (hB0 : forall J, 0 <= B J) (g : ι ->ᵇᵃ[I] F) (s : Set Realⁿ) (hs : s.Countable)
    (H₁ : forall (c : Real>=0), forall x in Box.Icc I inter s, forall ε > (0 : Real),
      exists δ > 0, forall J <= I, Box.Icc J subseteq Metric.closedBall x δ -> x in Box.Icc J ->
        (l.bDistortion -> J.distortion <= c) -> dist (vol J (f x)) (g J) <= ε)
    (H₂ : forall (c : Real>=0), forall x in Box.Icc I \ s, forall ε > (0 : Real),
      exists δ > 0, forall J <= I, Box.Icc J subseteq Metric.closedBall x δ -> x in Box.Icc J ->
        (l.bDistortion -> J.distortion <= c) -> dist (vol J (f x)) (g J) <= ε * B J) :
    HasIntegral I l f vol (g I) :=
  have A : l.bHenstock := Bool.eq_true_of_true_le hl.2.1
  HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (Bool.eq_false_of_le_false hl.1) B hB0 _ s hs
(fun _ => A) H₁ by simpa only [A, true_imp_iff] using H₂

/--
theorem `HasIntegral.mcShane_of_forall_isLittleO` / 定理 `HasIntegral.mcShane_of_forall_isLittleO`

English:
theorem HasIntegral.mcShane_of_forall_isLittleO
  statement: (B : ι ->ᵇᵃ[I] Real) (hB0 : forall J, 0 <= B J)
  proof: (HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (l := McShane) rfl B hB0 g ∅ countable_empty
      (fun ⟨_x, hx⟩ => hx.elim) fun _ _ hx => hx.2.elim) <| by
    simpa only [McShane, Bool.coe_sort_false, false_imp_iff, true_imp_iff, sdiff_empty] using H

中文:
定理 HasIntegral.mcShane_of_forall_isLittleO
  结论: (B : ι ->ᵇᵃ[I] 实数) (hB0 : 对任意 J, 0 <= B J)
  证明: (HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (l := McShane) rfl B hB0 g ∅ countable_empty
      (fun ⟨_x, hx⟩ => hx.elim) fun _ _ hx => hx.2.elim) <| by
    simpa only [McShane, Bool.coe_sort_false, false_imp_iff, true_imp_iff, sdiff_empty] using H

Depends on / 依赖: Bool.coe_sort_false, HasIntegral, HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO, McShane, coe_sort_false, countable_empty, false_imp_iff, hx.elim, of_bRiemann_eq_false_of_forall_isLittleO, sdiff_empty, true_imp_iff
-/
theorem HasIntegral.mcShane_of_forall_isLittleO (B : ι ->ᵇᵃ[I] Real) (hB0 : forall J, 0 <= B J)
    (g : ι ->ᵇᵃ[I] F) (H : forall (_ : Real>=0), forall x in Box.Icc I, forall ε > (0 : Real), exists δ > 0, forall J <= I,
      Box.Icc J subseteq Metric.closedBall x δ -> dist (vol J (f x)) (g J) <= ε * B J) :
    HasIntegral I McShane f vol (g I) :=
  (HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (l := McShane) rfl B hB0 g ∅ countable_empty
      (fun ⟨_x, hx⟩ => hx.elim) fun _ _ hx => hx.2.elim) <| by
    simpa only [McShane, Bool.coe_sort_false, false_imp_iff, true_imp_iff, sdiff_empty] using H

end BoxIntegral
