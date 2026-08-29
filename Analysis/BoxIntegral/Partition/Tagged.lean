/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
`π`. For simplicity we require that the function `BoxIntegral.TaggedPrepartition.tag` is defined
on all boxes `J : Box ι` but use its values only on boxes of the partition. Given
`π : BoxIntegral.TaggedPrepartition I`, we require that each `BoxIntegral.TaggedPrepartition π J`
belongs to `BoxIntegral.Box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is
called a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

## Tags

rectangular box, box partition
-/

@[expose] public section


noncomputable section

open Finset Function ENNReal NNReal Set

namespace BoxIntegral

variable {ι : Type*}

/--
Definition of `TaggedPrepartition` / `TaggedPrepartition` 的定义

English:
structure TaggedPrepartition
  parameters: (I : Box ι)
  extends: Prepartition I
  axioms and operations (2):
    - tag : Box ι -> ι -> Real
    - tag_mem_Icc : forall J, tag J in Box.Icc I

中文:
结构 标记预分拆
  参数: (I : Box ι)
  继承: 预分拆 I
  公理与运算 (2 个):
    - tag : Box ι -> ι -> 实数
    - tag_mem_Icc : 对任意 J, tag J in Box.闭区间 I
-/
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  /-- Choice of tagged point of each box in this prepartition:
  we extend this to a total function, on all boxes in `ι → ℝ`. -/
  tag : Box ι -> ι -> Real
  /-- Each tagged point belongs to `I` -/
  tag_mem_Icc : forall J, tag J in Box.Icc I

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι -> Real}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Box ι) (TaggedPrepartition I)
  body: ⟨fun π J => J in π.boxes⟩

@[simp]

中文:
实例 :
  签名: Membership (Box ι) (标记预分拆 I)
  定义体: ⟨fun π J => J in π.boxes⟩

@[simp]
-/
instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun π J => J in π.boxes⟩

@[simp]
/--
theorem `mem_toPrepartition` / 定理 `mem_toPrepartition`

English:
theorem mem_toPrepartition
  given: {π : TaggedPrepartition I}
  statement: J in π.toPrepartition ↔ J in π
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toPrepartition
  条件: {π : 标记预分拆 I}
  结论: J in π.toPrepartition ↔ J in π
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toPrepartition {π : TaggedPrepartition I} : J in π.toPrepartition ↔ J in π := Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (π : Prepartition I) (f h)
  statement: J in mk π f h ↔ J in π
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: (π : 预分拆 I) (f h)
  结论: J in mk π f h ↔ J in π
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk (π : Prepartition I) (f h) : J in mk π f h ↔ J in π := Iff.rfl

/--
Definition of `iUnion` / `iUnion` 的定义

English:
definition iUnion
  signature: : Set (ι -> Real)
  body: π.toPrepartition.iUnion

中文:
定义 iUnion
  签名: : 集合 (ι -> 实数)
  定义体: π.toPrepartition.iUnion

Depends on / 依赖: iUnion, toPrepartition, toPrepartition.iUnion
-/
def iUnion : Set (ι -> Real) :=
  π.toPrepartition.iUnion

/--
theorem `iUnion_def` / 定理 `iUnion_def`

English:
theorem iUnion_def
  statement: π.iUnion = ⋃ J in π, ↑J
  proof: rfl

@[simp]

中文:
定理 iUnion_def
  结论: π.iUnion = ⋃ J in π, ↑J
  证明: rfl

@[simp]
-/
theorem iUnion_def : π.iUnion = ⋃ J in π, ↑J := rfl

@[simp]
/--
theorem `iUnion_mk` / 定理 `iUnion_mk`

English:
theorem iUnion_mk
  given: (π : Prepartition I) (f h)
  statement: (mk π f h).iUnion = π.iUnion
  proof: rfl

@[simp]

中文:
定理 iUnion_mk
  条件: (π : 预分拆 I) (f h)
  结论: (mk π f h).iUnion = π.iUnion
  证明: rfl

@[simp]
-/
theorem iUnion_mk (π : Prepartition I) (f h) : (mk π f h).iUnion = π.iUnion := rfl

@[simp]
/--
theorem `iUnion_toPrepartition` / 定理 `iUnion_toPrepartition`

English:
theorem iUnion_toPrepartition
  statement: π.toPrepartition.iUnion = π.iUnion
  proof: rfl

@[simp]

中文:
定理 iUnion_toPrepartition
  结论: π.toPrepartition.iUnion = π.iUnion
  证明: rfl

@[simp]
-/
theorem iUnion_toPrepartition : π.toPrepartition.iUnion = π.iUnion := rfl

@[simp]
/--
theorem `mem_iUnion` / 定理 `mem_iUnion`

English:
theorem mem_iUnion
  statement: x in π.iUnion ↔ exists J in π, x in J
  proof: by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [mem_toPrepartition]; rw [exists_prop]

中文:
定理 mem_iUnion
  结论: x in π.iUnion ↔ 存在 J in π, x in J
  证明: by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [mem_toPrepartition]; rw [exists_prop]

Depends on / 依赖: Box.mem_coe, Set.mem_iUnion, convert, exists_prop, mem_coe, mem_toPrepartition
-/
theorem mem_iUnion : x in π.iUnion ↔ exists J in π, x in J := by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [mem_toPrepartition]; rw [exists_prop]

/--
theorem `subset_iUnion` / 定理 `subset_iUnion`

English:
theorem subset_iUnion
  given: (h : J in π)
  statement: ↑J subseteq π.iUnion
  proof: subset_biUnion_of_mem h

中文:
定理 subset_iUnion
  条件: (h : J in π)
  结论: ↑J subseteq π.iUnion
  证明: subset_biUnion_of_mem h

Depends on / 依赖: subset_biUnion_of_mem
-/
theorem subset_iUnion (h : J in π) : ↑J subseteq π.iUnion :=
  subset_biUnion_of_mem h

/--
theorem `iUnion_subset` / 定理 `iUnion_subset`

English:
theorem iUnion_subset
  statement: π.iUnion subseteq I
  proof: iUnion₂_subset π.le_of_mem'

中文:
定理 iUnion_subset
  结论: π.iUnion subseteq I
  证明: iUnion₂_subset π.le_of_mem'

Depends on / 依赖: le_of_mem
-/
theorem iUnion_subset : π.iUnion subseteq I :=
  iUnion₂_subset π.le_of_mem'

/--
Definition of `IsPartition` / `IsPartition` 的定义

English:
definition IsPartition
  body: π.toPrepartition.IsPartition

中文:
定义 IsPartition
  定义体: π.toPrepartition.IsPartition

Depends on / 依赖: IsPartition, toPrepartition, toPrepartition.IsPartition
-/
def IsPartition :=
  π.toPrepartition.IsPartition

/--
theorem `isPartition_iff_iUnion_eq` / 定理 `isPartition_iff_iUnion_eq`

English:
theorem isPartition_iff_iUnion_eq
  statement: IsPartition π ↔ π.iUnion = I
  proof: Prepartition.isPartition_iff_iUnion_eq

中文:
定理 isPartition_iff_iUnion_eq
  结论: IsPartition π ↔ π.iUnion = I
  证明: Prepartition.isPartition_iff_iUnion_eq

Depends on / 依赖: Prepartition, Prepartition.isPartition_iff_iUnion_eq, isPartition_iff_iUnion_eq
-/
theorem isPartition_iff_iUnion_eq : IsPartition π ↔ π.iUnion = I :=
  Prepartition.isPartition_iff_iUnion_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps! -fullyApplied]
/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (p : Box ι -> Prop)
  body: ⟨π.1.filter p, π.2, π.3⟩

@[simp]

中文:
定义 filter
  签名: (p : Box ι -> 命题)
  定义体: ⟨π.1.filter p, π.2, π.3⟩

@[simp]

Depends on / 依赖: filter
-/
def filter (p : Box ι -> Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩

@[simp]
/--
theorem `mem_filter` / 定理 `mem_filter`

English:
theorem mem_filter
  given: {p : Box ι -> Prop}
  statement: J in π.filter p ↔ J in π ∧ p J
  proof: by
  classical exact Finset.mem_filter

@[simp]

中文:
定理 mem_filter
  条件: {p : Box ι -> 命题}
  结论: J in π.filter p ↔ J in π ∧ p J
  证明: by
  classical exact Finset.mem_filter

@[simp]

Depends on / 依赖: Finset, Finset.mem_filter, classical, mem_filter
-/
theorem mem_filter {p : Box ι -> Prop} : J in π.filter p ↔ J in π ∧ p J := by
  classical exact Finset.mem_filter

@[simp]
/--
theorem `iUnion_filter_not` / 定理 `iUnion_filter_not`

English:
theorem iUnion_filter_not
  given: (π : TaggedPrepartition I) (p : Box ι -> Prop)
  proof: π.toPrepartition.iUnion_filter_not p

中文:
定理 iUnion_filter_not
  条件: (π : 标记预分拆 I) (p : Box ι -> 命题)
  证明: π.toPrepartition.iUnion_filter_not p

Depends on / 依赖: iUnion_filter_not, toPrepartition, toPrepartition.iUnion_filter_not
-/
theorem iUnion_filter_not (π : TaggedPrepartition I) (p : Box ι -> Prop) :
    (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion :=
  π.toPrepartition.iUnion_filter_not p

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

/--
Definition of `biUnionTagged` / `biUnionTagged` 的定义

English:
definition biUnionTagged
  signature: (π : Prepartition I) (πi : forall J : Box ι, TaggedPrepartition J)
  body: π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)

@[simp]

中文:
定义 biUnionTagged
  签名: (π : 预分拆 I) (πi : 对任意 J : Box ι, 标记预分拆 J)
  定义体: π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)

@[simp]

Depends on / 依赖: biUnion, toPrepartition
-/
def biUnionTagged (π : Prepartition I) (πi : forall J : Box ι, TaggedPrepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)

@[simp]
/--
theorem `mem_biUnionTagged` / 定理 `mem_biUnionTagged`

English:
theorem mem_biUnionTagged
  given: (π : Prepartition I) {πi : forall J, TaggedPrepartition J}
  proof: π.mem_biUnion

中文:
定理 mem_biUnionTagged
  条件: (π : 预分拆 I) {πi : 对任意 J, 标记预分拆 J}
  证明: π.mem_biUnion

Depends on / 依赖: mem_biUnion
-/
theorem mem_biUnionTagged (π : Prepartition I) {πi : forall J, TaggedPrepartition J} :
    J in π.biUnionTagged πi ↔ exists J' in π, J in πi J' :=
  π.mem_biUnion

/--
theorem `tag_biUnionTagged` / 定理 `tag_biUnionTagged`

English:
theorem tag_biUnionTagged
  statement: (π : Prepartition I) {πi : forall J, TaggedPrepartition J} (hJ : J in π) {J'}
  proof: by
  rw [← π.biUnionIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl

@[simp]

中文:
定理 tag_biUnionTagged
  结论: (π : 预分拆 I) {πi : 对任意 J, 标记预分拆 J} (hJ : J in π) {J'}
  证明: by
  rw [← π.biUnionIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl

@[simp]

Depends on / 依赖: biUnionIndex_of_mem, toPrepartition
-/
theorem tag_biUnionTagged (π : Prepartition I) {πi : forall J, TaggedPrepartition J} (hJ : J in π) {J'}
    (hJ' : J' in πi J) : (π.biUnionTagged πi).tag J' = (πi J).tag J' := by
  rw [← π.biUnionIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl

@[simp]
/--
theorem `iUnion_biUnionTagged` / 定理 `iUnion_biUnionTagged`

English:
theorem iUnion_biUnionTagged
  given: (π : Prepartition I) (πi : forall J, TaggedPrepartition J)
  proof: iUnion_biUnion _ _

中文:
定理 iUnion_biUnionTagged
  条件: (π : 预分拆 I) (πi : 对任意 J, 标记预分拆 J)
  证明: iUnion_biUnion _ _

Depends on / 依赖: iUnion_biUnion
-/
theorem iUnion_biUnionTagged (π : Prepartition I) (πi : forall J, TaggedPrepartition J) :
    (π.biUnionTagged πi).iUnion = ⋃ J in π, (πi J).iUnion :=
  iUnion_biUnion _ _

/--
theorem `forall_biUnionTagged` / 定理 `forall_biUnionTagged`

English:
theorem forall_biUnionTagged
  statement: (p : (ι -> Real) -> Box ι -> Prop) (π : Prepartition I)
  proof: by
  simp only [mem_biUnionTagged]
  refine ⟨fun H J hJ J' hJ' => ?_, fun H J' ⟨J, hJ, hJ'⟩ => ?_⟩
  · rw [← π.tag_biUnionTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_biUnionTagged hJ hJ']
    exact H J hJ J' hJ'

中文:
定理 对任意_biUnionTagged
  结论: (p : (ι -> 实数) -> Box ι -> 命题) (π : 预分拆 I)
  证明: by
  simp only [mem_biUnionTagged]
  refine ⟨fun H J hJ J' hJ' => ?_, fun H J' ⟨J, hJ, hJ'⟩ => ?_⟩
  · rw [← π.tag_biUnionTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_biUnionTagged hJ hJ']
    exact H J hJ J' hJ'

Depends on / 依赖: mem_biUnionTagged, tag_biUnionTagged
-/
theorem forall_biUnionTagged (p : (ι -> Real) -> Box ι -> Prop) (π : Prepartition I)
    (πi : forall J, TaggedPrepartition J) :
    (forall J in π.biUnionTagged πi, p ((π.biUnionTagged πi).tag J) J) ↔
      forall J in π, forall J' in πi J, p ((πi J).tag J') J' := by
  simp only [mem_biUnionTagged]
  refine ⟨fun H J hJ J' hJ' => ?_, fun H J' ⟨J, hJ, hJ'⟩ => ?_⟩
  · rw [← π.tag_biUnionTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_biUnionTagged hJ hJ']
    exact H J hJ J' hJ'

/--
theorem `IsPartition.biUnionTagged` / 定理 `IsPartition.biUnionTagged`

English:
theorem IsPartition.biUnionTagged
  statement: {π : Prepartition I} (h : IsPartition π)
  proof: h.biUnion hi

中文:
定理 IsPartition.biUnionTagged
  结论: {π : 预分拆 I} (h : IsPartition π)
  证明: h.biUnion hi

Depends on / 依赖: biUnion, h.biUnion
-/
theorem IsPartition.biUnionTagged {π : Prepartition I} (h : IsPartition π)
    {πi : forall J, TaggedPrepartition J} (hi : forall J in π, (πi J).IsPartition) :
    (π.biUnionTagged πi).IsPartition :=
  h.biUnion hi

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι -> Real}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps -fullyApplied tag]
/--
Definition of `biUnionPrepartition` / `biUnionPrepartition` 的定义

English:
definition biUnionPrepartition
  signature: (π : TaggedPrepartition I) (πi : forall J : Box ι, Prepartition J)
  body: π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _

中文:
定义 biUnionPrepartition
  签名: (π : 标记预分拆 I) (πi : 对任意 J : Box ι, 预分拆 J)
  定义体: π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _

Depends on / 依赖: biUnion, toPrepartition, toPrepartition.biUnion
-/
def biUnionPrepartition (π : TaggedPrepartition I) (πi : forall J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _

/--
theorem `IsPartition.biUnionPrepartition` / 定理 `IsPartition.biUnionPrepartition`

English:
theorem IsPartition.biUnionPrepartition
  statement: {π : TaggedPrepartition I} (h : IsPartition π)
  proof: h.biUnion hi

中文:
定理 IsPartition.biUnionPrepartition
  结论: {π : 标记预分拆 I} (h : IsPartition π)
  证明: h.biUnion hi

Depends on / 依赖: biUnion, h.biUnion
-/
theorem IsPartition.biUnionPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : forall J, Prepartition J} (hi : forall J in π, (πi J).IsPartition) :
    (π.biUnionPrepartition πi).IsPartition :=
  h.biUnion hi

/--
Definition of `infPrepartition` / `infPrepartition` 的定义

English:
definition infPrepartition
  signature: (π : TaggedPrepartition I) (π' : Prepartition I)
  body: π.biUnionPrepartition fun J => π'.restrict J

@[simp]

中文:
定义 infPrepartition
  签名: (π : 标记预分拆 I) (π' : 预分拆 I)
  定义体: π.biUnionPrepartition fun J => π'.restrict J

@[simp]

Depends on / 依赖: biUnionPrepartition, restrict
-/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.biUnionPrepartition fun J => π'.restrict J

@[simp]
/--
theorem `infPrepartition_toPrepartition` / 定理 `infPrepartition_toPrepartition`

English:
theorem infPrepartition_toPrepartition
  given: (π : TaggedPrepartition I) (π' : Prepartition I)
  proof: rfl

中文:
定理 infPrepartition_toPrepartition
  条件: (π : 标记预分拆 I) (π' : 预分拆 I)
  证明: rfl
-/
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' := rfl

/--
theorem `mem_infPrepartition_comm` / 定理 `mem_infPrepartition_comm`

English:
theorem mem_infPrepartition_comm
  proof: by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]

中文:
定理 mem_infPrepartition_comm
  证明: by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]

Depends on / 依赖: infPrepartition_toPrepartition, inf_comm, mem_toPrepartition
-/
theorem mem_infPrepartition_comm :
    J in π₁.infPrepartition π₂.toPrepartition ↔ J in π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]

/--
theorem `IsPartition.infPrepartition` / 定理 `IsPartition.infPrepartition`

English:
theorem IsPartition.infPrepartition
  statement: (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
  proof: h₁.inf h₂

中文:
定理 IsPartition.infPrepartition
  结论: (h₁ : π₁.IsPartition) {π₂ : 预分拆 I}
  证明: h₁.inf h₂
-/
theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂

open Metric

/--
Definition of `IsHenstock` / `IsHenstock` 的定义

English:
definition IsHenstock
  signature: (π : TaggedPrepartition I)
  body: forall J in π, π.tag J in Box.Icc J

@[simp]

中文:
定义 IsHenstock
  签名: (π : 标记预分拆 I)
  定义体: forall J in π, π.tag J in Box.Icc J

@[simp]

Depends on / 依赖: Box.Icc
-/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  forall J in π, π.tag J in Box.Icc J

@[simp]
/--
theorem `isHenstock_biUnionTagged` / 定理 `isHenstock_biUnionTagged`

English:
theorem isHenstock_biUnionTagged
  given: {π : Prepartition I} {πi : forall J, TaggedPrepartition J}
  proof: π.forall_biUnionTagged (fun x J => x in Box.Icc J) πi

中文:
定理 isHenstock_biUnionTagged
  条件: {π : 预分拆 I} {πi : 对任意 J, 标记预分拆 J}
  证明: π.forall_biUnionTagged (fun x J => x in Box.Icc J) πi

Depends on / 依赖: Box.Icc, forall_biUnionTagged
-/
theorem isHenstock_biUnionTagged {π : Prepartition I} {πi : forall J, TaggedPrepartition J} :
    IsHenstock (π.biUnionTagged πi) ↔ forall J in π, (πi J).IsHenstock :=
  π.forall_biUnionTagged (fun x J => x in Box.Icc J) πi

/--
theorem `IsHenstock.card_filter_tag_eq_le` / 定理 `IsHenstock.card_filter_tag_eq_le`

English:
theorem IsHenstock.card_filter_tag_eq_le
  given: [Fintype ι] (h : π.IsHenstock) (x : ι -> Real)
  proof: by
  classical
  calc
    #{J in π.boxes | π.tag J = x} <= #{J in π.boxes | x in Box.Icc J} := by
      refine Finset.card_le_card fun J hJ => ?_
      rw [Finset.mem_filter] at hJ ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ <= 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Ic

中文:
定理 IsHenstock.card_filter_tag_eq_le
  条件: [有限类型 ι] (h : π.IsHenstock) (x : ι -> 实数)
  证明: by
  classical
  calc
    #{J in π.boxes | π.tag J = x} <= #{J in π.boxes | x in Box.Icc J} := by
      refine Finset.card_le_card fun J hJ => ?_
      rw [Finset.mem_filter] at hJ ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ <= 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Ic

Depends on / 依赖: Box.Icc, Finset, Finset.card_le_card, Finset.mem_filter, Fintype, Fintype.card, card_filter_mem_Icc_le, card_le_card, classical, mem_filter, toPrepartition, toPrepartition.card_filter_mem_Icc_le
-/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι -> Real) :
    #{J in π.boxes | π.tag J = x} <= 2 ^ Fintype.card ι := by
  classical
  calc
    #{J in π.boxes | π.tag J = x} <= #{J in π.boxes | x in Box.Icc J} := by
      refine Finset.card_le_card fun J hJ => ?_
      rw [Finset.mem_filter] at hJ ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ <= 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x

/--
Definition of `IsSubordinate` / `IsSubordinate` 的定义

English:
definition IsSubordinate
  signature: [Fintype ι] (π : TaggedPrepartition I) (r : (ι -> Real) -> Ioi (0 : Real))
  body: forall J in π, Box.Icc J subseteq closedBall (π.tag J) (r <| π.tag J)

中文:
定义 IsSubordinate
  签名: [有限类型 ι] (π : 标记预分拆 I) (r : (ι -> 实数) -> 左开右无界区间 (0 : 实数))
  定义体: forall J in π, Box.Icc J subseteq closedBall (π.tag J) (r <| π.tag J)

Depends on / 依赖: Box.Icc, closedBall, subseteq
-/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : Prop :=
  forall J in π, Box.Icc J subseteq closedBall (π.tag J) (r <| π.tag J)

variable {r r₁ r₂ : (ι -> Real) -> Ioi (0 : Real)}

@[simp]
/--
theorem `isSubordinate_biUnionTagged` / 定理 `isSubordinate_biUnionTagged`

English:
theorem isSubordinate_biUnionTagged
  statement: [Fintype ι] {π : Prepartition I}
  proof: π.forall_biUnionTagged (fun x J => Box.Icc J subseteq closedBall x (r x)) πi

中文:
定理 isSubordinate_biUnionTagged
  结论: [有限类型 ι] {π : 预分拆 I}
  证明: π.forall_biUnionTagged (fun x J => Box.Icc J subseteq closedBall x (r x)) πi

Depends on / 依赖: Box.Icc, closedBall, forall_biUnionTagged, subseteq
-/
theorem isSubordinate_biUnionTagged [Fintype ι] {π : Prepartition I}
    {πi : forall J, TaggedPrepartition J} :
    IsSubordinate (π.biUnionTagged πi) r ↔ forall J in π, (πi J).IsSubordinate r :=
  π.forall_biUnionTagged (fun x J => Box.Icc J subseteq closedBall x (r x)) πi

/--
theorem `IsSubordinate.biUnionPrepartition` / 定理 `IsSubordinate.biUnionPrepartition`

English:
theorem IsSubordinate.biUnionPrepartition
  statement: [Fintype ι] (h : IsSubordinate π r)
  proof: fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ)
h _ π.toPrepartition.biUnionIndex_mem hJ

中文:
定理 IsSubordinate.biUnionPrepartition
  结论: [有限类型 ι] (h : IsSubordinate π r)
  证明: fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ)
h _ π.toPrepartition.biUnionIndex_mem hJ

Depends on / 依赖: Box.le_iff_Icc, Subset, Subset.trans, biUnionIndex_mem, le_biUnionIndex, le_iff_Icc, toPrepartition, toPrepartition.biUnionIndex_mem, toPrepartition.le_biUnionIndex
-/
theorem IsSubordinate.biUnionPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : forall J, Prepartition J) : IsSubordinate (π.biUnionPrepartition πi) r :=
fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ)
h _ π.toPrepartition.biUnionIndex_mem hJ

/--
theorem `IsSubordinate.infPrepartition` / 定理 `IsSubordinate.infPrepartition`

English:
theorem IsSubordinate.infPrepartition
  given: [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I)
  proof: h.biUnionPrepartition _

中文:
定理 IsSubordinate.infPrepartition
  条件: [有限类型 ι] (h : IsSubordinate π r) (π' : 预分拆 I)
  证明: h.biUnionPrepartition _

Depends on / 依赖: biUnionPrepartition, h.biUnionPrepartition
-/
theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.biUnionPrepartition _

/--
theorem `IsSubordinate.mono'` / 定理 `IsSubordinate.mono'`

English:
theorem IsSubordinate.mono'
  statement: [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
  proof: fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)

中文:
定理 IsSubordinate.mono'
  结论: [有限类型 ι] {π : 标记预分拆 I} (hr₁ : π.IsSubordinate r₁)
  证明: fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)

Depends on / 依赖: closedBall_subset_closedBall
-/
theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : forall J in π, r₁ (π.tag J) <= r₂ (π.tag J)) : π.IsSubordinate r₂ :=
  fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)

/--
theorem `IsSubordinate.mono` / 定理 `IsSubordinate.mono`

English:
theorem IsSubordinate.mono
  statement: [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
  proof: hr₁.mono' fun J _ => h _ π.tag_mem_Icc J

中文:
定理 IsSubordinate.mono
  结论: [有限类型 ι] {π : 标记预分拆 I} (hr₁ : π.IsSubordinate r₁)
  证明: hr₁.mono' fun J _ => h _ π.tag_mem_Icc J

Depends on / 依赖: tag_mem_Icc
-/
theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : forall x in Box.Icc I, r₁ x <= r₂ x) : π.IsSubordinate r₂ :=
hr₁.mono' fun J _ => h _ π.tag_mem_Icc J

/--
theorem `IsSubordinate.diam_le` / 定理 `IsSubordinate.diam_le`

English:
theorem IsSubordinate.diam_le
  statement: [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
  proof: calc
    diam (Box.Icc J) <= diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) isBounded_closedBall
    _ <= 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)

中文:
定理 IsSubordinate.diam_le
  结论: [有限类型 ι] {π : 标记预分拆 I} (h : π.IsSubordinate r)
  证明: calc
    diam (Box.Icc J) <= diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) isBounded_closedBall
    _ <= 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)

Depends on / 依赖: Box.Icc, closedBall, diam_closedBall, diam_mono, isBounded_closedBall, le_of_lt
-/
theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J in π.boxes) : diam (Box.Icc J) <= 2 * r (π.tag J) :=
  calc
    diam (Box.Icc J) <= diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) isBounded_closedBall
    _ <= 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps! -fullyApplied]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (I J : Box ι) (hJ : J <= I) (x : ι -> Real) (h : x in Box.Icc I)
  body: ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩

@[simp]

中文:
定义 single
  签名: (I J : Box ι) (hJ : J <= I) (x : ι -> 实数) (h : x in Box.闭区间 I)
  定义体: ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩

@[simp]

Depends on / 依赖: Prepartition, Prepartition.single, single
-/
def single (I J : Box ι) (hJ : J <= I) (x : ι -> Real) (h : x in Box.Icc I) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩

@[simp]
/--
theorem `mem_single` / 定理 `mem_single`

English:
theorem mem_single
  given: {J'} (hJ : J <= I) (h : x in Box.Icc I)
  statement: J' in single I J hJ x h ↔ J' = J
  proof: Finset.mem_singleton

中文:
定理 mem_single
  条件: {J'} (hJ : J <= I) (h : x in Box.闭区间 I)
  结论: J' in single I J hJ x h ↔ J' = J
  证明: Finset.mem_singleton

Depends on / 依赖: Finset, Finset.mem_singleton, mem_singleton
-/
theorem mem_single {J'} (hJ : J <= I) (h : x in Box.Icc I) : J' in single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton

instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

/--
theorem `isPartition_single_iff` / 定理 `isPartition_single_iff`

English:
theorem isPartition_single_iff
  given: (hJ : J <= I) (h : x in Box.Icc I)
  proof: Prepartition.isPartition_single_iff hJ

中文:
定理 isPartition_single_iff
  条件: (hJ : J <= I) (h : x in Box.闭区间 I)
  证明: Prepartition.isPartition_single_iff hJ

Depends on / 依赖: Prepartition, Prepartition.isPartition_single_iff, isPartition_single_iff
-/
theorem isPartition_single_iff (hJ : J <= I) (h : x in Box.Icc I) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ

/--
theorem `isPartition_single` / 定理 `isPartition_single`

English:
theorem isPartition_single
  given: (h : x in Box.Icc I)
  statement: (single I I le_rfl x h).IsPartition
  proof: Prepartition.isPartitionTop I

中文:
定理 isPartition_single
  条件: (h : x in Box.闭区间 I)
  结论: (single I I le_rfl x h).IsPartition
  证明: Prepartition.isPartitionTop I

Depends on / 依赖: Prepartition, Prepartition.isPartitionTop, isPartitionTop
-/
theorem isPartition_single (h : x in Box.Icc I) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I

/--
theorem `forall_mem_single` / 定理 `forall_mem_single`

English:
theorem forall_mem_single
  given: (p : (ι -> Real) -> Box ι -> Prop) (hJ : J <= I) (h : x in Box.Icc I)
  proof: by simp

@[simp]

中文:
定理 对任意_mem_single
  条件: (p : (ι -> 实数) -> Box ι -> 命题) (hJ : J <= I) (h : x in Box.闭区间 I)
  证明: by simp

@[simp]
-/
theorem forall_mem_single (p : (ι -> Real) -> Box ι -> Prop) (hJ : J <= I) (h : x in Box.Icc I) :
    (forall J' in single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J := by simp

@[simp]
/--
theorem `isHenstock_single_iff` / 定理 `isHenstock_single_iff`

English:
theorem isHenstock_single_iff
  given: (hJ : J <= I) (h : x in Box.Icc I)
  proof: forall_mem_single (fun x J => x in Box.Icc J) hJ h

中文:
定理 isHenstock_single_iff
  条件: (hJ : J <= I) (h : x in Box.闭区间 I)
  证明: forall_mem_single (fun x J => x in Box.Icc J) hJ h

Depends on / 依赖: Box.Icc, forall_mem_single
-/
theorem isHenstock_single_iff (hJ : J <= I) (h : x in Box.Icc I) :
    IsHenstock (single I J hJ x h) ↔ x in Box.Icc J :=
  forall_mem_single (fun x J => x in Box.Icc J) hJ h

/--
theorem `isHenstock_single` / 定理 `isHenstock_single`

English:
theorem isHenstock_single
  given: (h : x in Box.Icc I)
  statement: IsHenstock (single I I le_rfl x h)
  proof: (isHenstock_single_iff (le_refl I) h).2 h

@[simp]

中文:
定理 isHenstock_single
  条件: (h : x in Box.闭区间 I)
  结论: IsHenstock (single I I le_rfl x h)
  证明: (isHenstock_single_iff (le_refl I) h).2 h

@[simp]

Depends on / 依赖: isHenstock_single_iff, le_refl
-/
theorem isHenstock_single (h : x in Box.Icc I) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h

@[simp]
/--
theorem `isSubordinate_single` / 定理 `isSubordinate_single`

English:
theorem isSubordinate_single
  given: [Fintype ι] (hJ : J <= I) (h : x in Box.Icc I)
  proof: forall_mem_single (fun x J => Box.Icc J subseteq closedBall x (r x)) hJ h

@[simp]

中文:
定理 isSubordinate_single
  条件: [有限类型 ι] (hJ : J <= I) (h : x in Box.闭区间 I)
  证明: forall_mem_single (fun x J => Box.Icc J subseteq closedBall x (r x)) hJ h

@[simp]

Depends on / 依赖: Box.Icc, closedBall, forall_mem_single, subseteq
-/
theorem isSubordinate_single [Fintype ι] (hJ : J <= I) (h : x in Box.Icc I) :
    IsSubordinate (single I J hJ x h) r ↔ Box.Icc J subseteq closedBall x (r x) :=
  forall_mem_single (fun x J => Box.Icc J subseteq closedBall x (r x)) hJ h

@[simp]
/--
theorem `iUnion_single` / 定理 `iUnion_single`

English:
theorem iUnion_single
  given: (hJ : J <= I) (h : x in Box.Icc I)
  statement: (single I J hJ x h).iUnion = J
  proof: Prepartition.iUnion_single hJ

中文:
定理 iUnion_single
  条件: (hJ : J <= I) (h : x in Box.闭区间 I)
  结论: (single I J hJ x h).iUnion = J
  证明: Prepartition.iUnion_single hJ

Depends on / 依赖: Prepartition, Prepartition.iUnion_single, iUnion_single
-/
theorem iUnion_single (hJ : J <= I) (h : x in Box.Icc I) : (single I J hJ x h).iUnion = J :=
  Prepartition.iUnion_single hJ

open scoped Classical in
/--
Definition of `disjUnion` / `disjUnion` 的定义

English:
definition disjUnion
  signature: (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion)
  body: π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]

中文:
定义 disjUnion
  签名: (π₁ π₂ : 标记预分拆 I) (h : Disjoint π₁.iUnion π₂.iUnion)
  定义体: π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]

Depends on / 依赖: disjUnion, toPrepartition, toPrepartition.disjUnion
-/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) :
    TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]

open scoped Classical in
@[simp]
/--
theorem `disjUnion_boxes` / 定理 `disjUnion_boxes`

English:
theorem disjUnion_boxes
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: rfl

@[simp]

中文:
定理 disjUnion_boxes
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: rfl

@[simp]
-/
theorem disjUnion_boxes (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes union π₂.boxes := rfl

@[simp]
/--
theorem `mem_disjUnion` / 定理 `mem_disjUnion`

English:
theorem mem_disjUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: by
  classical exact Finset.mem_union

@[simp]

中文:
定理 mem_disjUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: by
  classical exact Finset.mem_union

@[simp]

Depends on / 依赖: Finset, Finset.mem_union, classical, mem_union
-/
theorem mem_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    J in π₁.disjUnion π₂ h ↔ J in π₁ ∨ J in π₂ := by
  classical exact Finset.mem_union

@[simp]
/--
theorem `iUnion_disjUnion` / 定理 `iUnion_disjUnion`

English:
theorem iUnion_disjUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: Prepartition.iUnion_disjUnion h

中文:
定理 iUnion_disjUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: Prepartition.iUnion_disjUnion h

Depends on / 依赖: Prepartition, Prepartition.iUnion_disjUnion, iUnion_disjUnion
-/
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion union π₂.iUnion :=
  Prepartition.iUnion_disjUnion h

/--
theorem `disjUnion_tag_of_mem_left` / 定理 `disjUnion_tag_of_mem_left`

English:
theorem disjUnion_tag_of_mem_left
  given: (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁)
  proof: dif_pos hJ

中文:
定理 disjUnion_tag_of_mem_left
  条件: (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁)
  证明: dif_pos hJ

Depends on / 依赖: dif_pos
-/
theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₁) :
    (π₁.disjUnion π₂ h).tag J = π₁.tag J :=
  dif_pos hJ

/--
theorem `disjUnion_tag_of_mem_right` / 定理 `disjUnion_tag_of_mem_right`

English:
theorem disjUnion_tag_of_mem_right
  given: (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂)
  proof: dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩

中文:
定理 disjUnion_tag_of_mem_right
  条件: (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂)
  证明: dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩

Depends on / 依赖: J.upper_mem, dif_neg, h.le_bot, le_bot, subset_iUnion, upper_mem
-/
theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J in π₂) :
    (π₁.disjUnion π₂ h).tag J = π₂.tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩

/--
theorem `IsSubordinate.disjUnion` / 定理 `IsSubordinate.disjUnion`

English:
theorem IsSubordinate.disjUnion
  statement: [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
  proof: by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

中文:
定理 IsSubordinate.disjUnion
  结论: [有限类型 ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
  证明: by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

Depends on / 依赖: Finset, Finset.mem_union, classical, disjUnion_tag_of_mem_left, disjUnion_tag_of_mem_right, mem_union
-/
theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsSubordinate (π₁.disjUnion π₂ h) r := by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

/--
theorem `IsHenstock.disjUnion` / 定理 `IsHenstock.disjUnion`

English:
theorem IsHenstock.disjUnion
  statement: (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
  proof: by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

中文:
定理 IsHenstock.disjUnion
  结论: (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
  证明: by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

Depends on / 依赖: Finset, Finset.mem_union, classical, disjUnion_tag_of_mem_left, disjUnion_tag_of_mem_right, mem_union
-/
theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsHenstock (π₁.disjUnion π₂ h) := by
  classical
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ

/--
Definition of `embedBox` / `embedBox` 的定义

English:
definition embedBox
  signature: (I J : Box ι) (h : I <= J)
  body: { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H

中文:
定义 embedBox
  签名: (I J : Box ι) (h : I <= J)
  定义体: { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H

Depends on / 依赖: Box.le_iff_Icc, le_iff_Icc, le_of_mem, tag_mem_Icc
-/
def embedBox (I J : Box ι) (h : I <= J) : TaggedPrepartition I ↪ TaggedPrepartition J where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H

section Distortion

variable [Fintype ι] (π)

open Finset

/--
Definition of `distortion` / `distortion` 的定义

English:
definition distortion
  signature: : Real>=0
  body: π.toPrepartition.distortion

中文:
定义 distortion
  签名: : 实数>=0
  定义体: π.toPrepartition.distortion

Depends on / 依赖: distortion, toPrepartition, toPrepartition.distortion
-/
def distortion : Real>=0 :=
  π.toPrepartition.distortion

/--
theorem `distortion_le_of_mem` / 定理 `distortion_le_of_mem`

English:
theorem distortion_le_of_mem
  given: (h : J in π)
  statement: J.distortion <= π.distortion
  proof: le_sup h

中文:
定理 distortion_le_of_mem
  条件: (h : J in π)
  结论: J.distortion <= π.distortion
  证明: le_sup h

Depends on / 依赖: le_sup
-/
theorem distortion_le_of_mem (h : J in π) : J.distortion <= π.distortion :=
  le_sup h

/--
theorem `distortion_le_iff` / 定理 `distortion_le_iff`

English:
theorem distortion_le_iff
  given: {c : Real>=0}
  statement: π.distortion <= c ↔ forall J in π, Box.distortion J <= c
  proof: Finset.sup_le_iff

@[simp]

中文:
定理 distortion_le_iff
  条件: {c : 实数>=0}
  结论: π.distortion <= c ↔ 对任意 J in π, Box.distortion J <= c
  证明: Finset.sup_le_iff

@[simp]

Depends on / 依赖: Finset, Finset.sup_le_iff, sup_le_iff
-/
theorem distortion_le_iff {c : Real>=0} : π.distortion <= c ↔ forall J in π, Box.distortion J <= c :=
  Finset.sup_le_iff

@[simp]
/--
theorem `_root_.BoxIntegral.Prepartition.distortion_biUnionTagged` / 定理 `_root_.BoxIntegral.Prepartition.distortion_biUnionTagged`

English:
theorem _root_.BoxIntegral.Prepartition.distortion_biUnionTagged
  statement: (π : Prepartition I)
  proof: by
  classical exact sup_biUnion _ _

@[simp]

中文:
定理 _root_.Box整数egral.预分拆.distortion_biUnionTagged
  结论: (π : 预分拆 I)
  证明: by
  classical exact sup_biUnion _ _

@[simp]

Depends on / 依赖: classical, sup_biUnion
-/
theorem _root_.BoxIntegral.Prepartition.distortion_biUnionTagged (π : Prepartition I)
    (πi : forall J, TaggedPrepartition J) :
    (π.biUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/--
theorem `distortion_biUnionPrepartition` / 定理 `distortion_biUnionPrepartition`

English:
theorem distortion_biUnionPrepartition
  given: (π : TaggedPrepartition I) (πi : forall J, Prepartition J)
  proof: by
  classical exact sup_biUnion _ _

@[simp]

中文:
定理 distortion_biUnionPrepartition
  条件: (π : 标记预分拆 I) (πi : 对任意 J, 预分拆 J)
  证明: by
  classical exact sup_biUnion _ _

@[simp]

Depends on / 依赖: classical, sup_biUnion
-/
theorem distortion_biUnionPrepartition (π : TaggedPrepartition I) (πi : forall J, Prepartition J) :
    (π.biUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/--
theorem `distortion_disjUnion` / 定理 `distortion_disjUnion`

English:
theorem distortion_disjUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: by
  classical exact sup_union

中文:
定理 distortion_disjUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: by
  classical exact sup_union

Depends on / 依赖: classical, sup_union
-/
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion := by
  classical exact sup_union

/--
theorem `distortion_of_const` / 定理 `distortion_of_const`

English:
theorem distortion_of_const
  given: {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.distortion J = c)
  proof: (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]

中文:
定理 distortion_of_const
  条件: {c} (h₁ : π.boxes.非空) (h₂ : 对任意 J in π, Box.distortion J = c)
  证明: (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]

Depends on / 依赖: sup_congr, sup_const
-/
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
/--
theorem `distortion_single` / 定理 `distortion_single`

English:
theorem distortion_single
  given: (hJ : J <= I) (h : x in Box.Icc I)
  proof: sup_singleton

中文:
定理 distortion_single
  条件: (hJ : J <= I) (h : x in Box.闭区间 I)
  证明: sup_singleton

Depends on / 依赖: sup_singleton
-/
theorem distortion_single (hJ : J <= I) (h : x in Box.Icc I) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton

/--
theorem `distortion_filter_le` / 定理 `distortion_filter_le`

English:
theorem distortion_filter_le
  given: (p : Box ι -> Prop)
  statement: (π.filter p).distortion <= π.distortion
  proof: by
  classical exact sup_mono (filter_subset _ _)

中文:
定理 distortion_filter_le
  条件: (p : Box ι -> 命题)
  结论: (π.filter p).distortion <= π.distortion
  证明: by
  classical exact sup_mono (filter_subset _ _)

Depends on / 依赖: classical, filter_subset, sup_mono
-/
theorem distortion_filter_le (p : Box ι -> Prop) : (π.filter p).distortion <= π.distortion := by
  classical exact sup_mono (filter_subset _ _)

end Distortion

end TaggedPrepartition

end BoxIntegral
