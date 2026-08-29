/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Support of a Measure

This file develops the theory of the **support** of a measure `μ` on a
topological measurable space. The support is defined as the set of points whose every open
neighborhood has positive measure. We give equivalent characterizations, prove basic
measure-theoretic properties, and study interactions with sums, restrictions, and
absolute continuity. Under various Lindelöf or regularity conditions, the support is conull,
and various descriptions of the complement of the support are provided.

## Main definitions

* `Measure.support` : the support of a measure `μ`, defined as
  `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}` — equivalently, every neighborhood of `x`
  has positive `μ`-measure.

## Main results

* `compl_support_eq_sUnion` and `support_eq_sInter` : the complement of the support is the
  union of open measure-zero sets, and the support is the intersection of closed sets whose
  complements have measure zero.
* `isClosed_support` : the support is a closed set.
* `support_mem_ae_of_isLindelof` and `support_mem_ae` : under Lindelöf (or hereditarily
  Lindelöf) hypotheses, the support is conull.
* `support_mem_ae_of_innerRegularWRT_isCompact_isOpen` and
  `measure_compl_support_of_innerRegularWRT_isCompact_isOpen` : inner regularity by compact
  sets on open sets imply that the support is conull.

## Tags

measure, support, Lindelöf
-/

@[expose] public section

section Support

namespace MeasureTheory

namespace Measure

open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (μ : Measure X)
  body: {x : X | existsᶠ u in (𝓝 x).smallSets, 0 < μ u}

中文:
定义 support
  签名: (μ : 测度 X)
  定义体: {x : X | existsᶠ u in (𝓝 x).smallSets, 0 < μ u}
-/
protected def support (μ : Measure X) : Set X := {x : X | existsᶠ u in (𝓝 x).smallSets, 0 < μ u}

variable {μ : Measure X}

/--
theorem `_root_.Filter.HasBasis.mem_measureSupport` / 定理 `_root_.Filter.HasBasis.mem_measureSupport`

English:
theorem _root_.Filter.HasBasis.mem_measureSupport
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: hl.frequently_smallSets pos_mono

中文:
定理 _root_.滤子.有基.mem_measureSupport
  结论: {ι : 类型层*} {p : ι -> 命题}
  证明: hl.frequently_smallSets pos_mono

Depends on / 依赖: frequently_smallSets, hl.frequently_smallSets, pos_mono
-/
theorem _root_.Filter.HasBasis.mem_measureSupport {ι : Sort*} {p : ι -> Prop}
    {s : ι -> Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x in μ.support ↔ forall (i : ι), p i -> 0 < μ (s i) :=
  hl.frequently_smallSets pos_mono

/--
lemma `mem_support_iff` / 引理 `mem_support_iff`

English:
lemma mem_support_iff
  given: {x : X}
  statement: x in μ.support ↔
  proof: Iff.rfl

中文:
引理 mem_support_iff
  条件: {x : X}
  结论: x in μ.support ↔
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_support_iff {x : X} : x in μ.support ↔
    existsᶠ u in (𝓝 x).smallSets, 0 < μ u := Iff.rfl

/--
lemma `mem_support_iff_forall` / 引理 `mem_support_iff_forall`

English:
lemma mem_support_iff_forall
  given: (x : X)
  statement: x in μ.support ↔ forall U in 𝓝 x, 0 < μ U
  proof: (𝓝 x).basis_sets.mem_measureSupport

中文:
引理 mem_support_iff_对任意
  条件: (x : X)
  结论: x in μ.support ↔ 对任意 U in 𝓝 x, 0 < μ U
  证明: (𝓝 x).basis_sets.mem_measureSupport

Depends on / 依赖: basis_sets, basis_sets.mem_measureSupport, mem_measureSupport
-/
lemma mem_support_iff_forall (x : X) : x in μ.support ↔ forall U in 𝓝 x, 0 < μ U :=
  (𝓝 x).basis_sets.mem_measureSupport

/--
lemma `support_eq_univ` / 引理 `support_eq_univ`

English:
lemma support_eq_univ
  given: [μ.IsOpenPosMeasure]
  statement: μ.support = Set.univ
  proof: by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ => μ.measure_pos_of_mem_nhds

中文:
引理 support_eq_univ
  条件: [μ.是OpenPosMeasure]
  结论: μ.support = 集合.univ
  证明: by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ => μ.measure_pos_of_mem_nhds

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, measure_pos_of_mem_nhds, mem_support_iff_forall
-/
lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ := by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ => μ.measure_pos_of_mem_nhds

/--
lemma `AbsolutelyContinuous.support_mono` / 引理 `AbsolutelyContinuous.support_mono`

English:
lemma AbsolutelyContinuous.support_mono
  given: {μ ν : Measure X} (hμν : μ ≪ ν)
  proof: fun _ hx => hx.mp .of_forall hμν.pos_mono

中文:
引理 AbsolutelyContinuous.support_mono
  条件: {μ ν : 测度 X} (hμν : μ ≪ ν)
  证明: fun _ hx => hx.mp .of_forall hμν.pos_mono

Depends on / 依赖: hx.mp, of_forall, pos_mono
-/
lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
    μ.support subseteq ν.support :=
fun _ hx => hx.mp .of_forall hμν.pos_mono

/--
lemma `support_mono` / 引理 `support_mono`

English:
lemma support_mono
  given: {ν : Measure X} (h : μ <= ν)
  statement: μ.support subseteq ν.support
  proof: h.absolutelyContinuous.support_mono

中文:
引理 support_mono
  条件: {ν : 测度 X} (h : μ <= ν)
  结论: μ.support subseteq ν.support
  证明: h.absolutelyContinuous.support_mono

Depends on / 依赖: absolutelyContinuous, h.absolutelyContinuous.support_mono, support_mono
-/
lemma support_mono {ν : Measure X} (h : μ <= ν) : μ.support subseteq ν.support :=
  h.absolutelyContinuous.support_mono

/--
lemma `notMem_support_iff` / 引理 `notMem_support_iff`

English:
lemma notMem_support_iff
  given: {x : X}
  statement: x ∉ μ.support ↔ forallᶠ u in (𝓝 x).smallSets, μ u = 0
  proof: by
  simp [mem_support_iff]

中文:
引理 notMem_support_iff
  条件: {x : X}
  结论: x ∉ μ.support ↔ 对任意ᶠ u in (𝓝 x).smallSets, μ u = 0
  证明: by
  simp [mem_support_iff]

Depends on / 依赖: mem_support_iff
-/
lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ forallᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]

/--
theorem `_root_.Filter.HasBasis.notMem_measureSupport` / 定理 `_root_.Filter.HasBasis.notMem_measureSupport`

English:
theorem _root_.Filter.HasBasis.notMem_measureSupport
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: by
  simp [hl.mem_measureSupport]

@[simp]

中文:
定理 _root_.滤子.有基.notMem_measureSupport
  结论: {ι : 类型层*} {p : ι -> 命题}
  证明: by
  simp [hl.mem_measureSupport]

@[simp]

Depends on / 依赖: hl.mem_measureSupport, mem_measureSupport
-/
theorem _root_.Filter.HasBasis.notMem_measureSupport {ι : Sort*} {p : ι -> Prop}
    {s : ι -> Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∉ μ.support ↔ exists i, p i ∧ μ (s i) = 0 := by
  simp [hl.mem_measureSupport]

@[simp]
/--
lemma `support_zero` / 引理 `support_zero`

English:
lemma support_zero
  statement: (0 : Measure X).support = ∅
  proof: by simp [Measure.support]

中文:
引理 support_zero
  结论: (0 : 测度 X).support = ∅
  证明: by simp [Measure.support]

Depends on / 依赖: Measure, Measure.support, support
-/
lemma support_zero : (0 : Measure X).support = ∅ := by simp [Measure.support]

/--
lemma `support_add` / 引理 `support_add`

English:
lemma support_add
  given: (μ ν : Measure X)
  statement: (μ + ν).support = μ.support union ν.support
  proof: by
  ext; simp [mem_support_iff]

中文:
引理 support_add
  条件: (μ ν : 测度 X)
  结论: (μ + ν).support = μ.support union ν.support
  证明: by
  ext; simp [mem_support_iff]

Depends on / 依赖: mem_support_iff
-/
lemma support_add (μ ν : Measure X) : (μ + ν).support = μ.support union ν.support := by
  ext; simp [mem_support_iff]

/--
lemma `notMem_support_iff_exists` / 引理 `notMem_support_iff_exists`

English:
lemma notMem_support_iff_exists
  given: {x : X}
  statement: x ∉ μ.support ↔ exists U in 𝓝 x, μ U = 0
  proof: by
  simp [mem_support_iff_forall]

中文:
引理 notMem_support_iff_存在
  条件: {x : X}
  结论: x ∉ μ.support ↔ 存在 U in 𝓝 x, μ U = 0
  证明: by
  simp [mem_support_iff_forall]

Depends on / 依赖: mem_support_iff_forall
-/
lemma notMem_support_iff_exists {x : X} : x ∉ μ.support ↔ exists U in 𝓝 x, μ U = 0 := by
  simp [mem_support_iff_forall]

/--
lemma `support_eq_forall_isOpen` / 引理 `support_eq_forall_isOpen`

English:
lemma support_eq_forall_isOpen
  statement: μ.support =
  proof: by
  simp [Set.ext_iff, nhds_basis_opens _ |>.mem_measureSupport]

中文:
引理 support_eq_对任意_isOpen
  结论: μ.support =
  证明: by
  simp [Set.ext_iff, nhds_basis_opens _ |>.mem_measureSupport]

Depends on / 依赖: Set.ext_iff, ext_iff, mem_measureSupport, nhds_basis_opens
-/
lemma support_eq_forall_isOpen : μ.support =
    {x : X | forall u : Set X, x in u -> IsOpen u -> 0 < μ u} := by
  simp [Set.ext_iff, nhds_basis_opens _ |>.mem_measureSupport]

/--
lemma `isClosed_support` / 引理 `isClosed_support`

English:
lemma isClosed_support
  given: {μ : Measure X}
  statement: IsClosed μ.support
  proof: by
  simp_rw [isClosed_iff_frequently, nhds_basis_opens _ |>.mem_measureSupport,
.frequently_iff] nhds_basis_opens _
  grind

中文:
引理 isClosed_support
  条件: {μ : 测度 X}
  结论: 是闭集 μ.support
  证明: by
  simp_rw [isClosed_iff_frequently, nhds_basis_opens _ |>.mem_measureSupport,
.frequently_iff] nhds_basis_opens _
  grind

Depends on / 依赖: frequently_iff, isClosed_iff_frequently, mem_measureSupport, nhds_basis_opens, simp_rw
-/
lemma isClosed_support {μ : Measure X} : IsClosed μ.support := by
  simp_rw [isClosed_iff_frequently, nhds_basis_opens _ |>.mem_measureSupport,
.frequently_iff] nhds_basis_opens _
  grind

/--
lemma `isOpen_compl_support` / 引理 `isOpen_compl_support`

English:
lemma isOpen_compl_support
  given: {μ : Measure X}
  statement: IsOpen μ.supportᶜ
  proof: isOpen_compl_iff.mpr μ.isClosed_support

中文:
引理 isOpen_compl_support
  条件: {μ : 测度 X}
  结论: 是开集 μ.supportᶜ
  证明: isOpen_compl_iff.mpr μ.isClosed_support

Depends on / 依赖: isClosed_support, isOpen_compl_iff, isOpen_compl_iff.mpr
-/
lemma isOpen_compl_support {μ : Measure X} : IsOpen μ.supportᶜ :=
  isOpen_compl_iff.mpr μ.isClosed_support

/--
lemma `subset_compl_support_of_isOpen` / 引理 `subset_compl_support_of_isOpen`

English:
lemma subset_compl_support_of_isOpen
  given: {t : Set X} (ht : IsOpen t) (h : μ t = 0)
  proof: fun _ hx => notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

中文:
引理 subset_compl_support_of_isOpen
  条件: {t : 集合 X} (ht : 是开集 t) (h : μ t = 0)
  证明: fun _ hx => notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

Depends on / 依赖: Fintype, Fintype.toBoundedOrder, ht.mem_nhds, mem_nhds, notMem_support_iff_exists, notMem_support_iff_exists.mpr, toBoundedOrder
-/
lemma subset_compl_support_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) :
    t subseteq μ.supportᶜ :=
  fun _ hx => notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

/--
lemma `support_subset_of_isClosed` / 引理 `support_subset_of_isClosed`

English:
lemma support_subset_of_isClosed
  given: {t : Set X} (ht : IsClosed t) (h : t in ae μ)
  proof: Set.compl_subset_compl.mp subset_compl_support_of_isOpen ht.isOpen_compl h

中文:
引理 support_subset_of_isClosed
  条件: {t : 集合 X} (ht : 是闭集 t) (h : t in ae μ)
  证明: Set.compl_subset_compl.mp subset_compl_support_of_isOpen ht.isOpen_compl h

Depends on / 依赖: Set.compl_subset_compl.mp, compl_subset_compl, ht.isOpen_compl, isOpen_compl, subset_compl_support_of_isOpen
-/
lemma support_subset_of_isClosed {t : Set X} (ht : IsClosed t) (h : t in ae μ) :
    μ.support subseteq t :=
Set.compl_subset_compl.mp subset_compl_support_of_isOpen ht.isOpen_compl h

/--
lemma `compl_support_eq_sUnion` / 引理 `compl_support_eq_sUnion`

English:
lemma compl_support_eq_sUnion
  statement: μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0}
  proof: by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, and_right_comm,
.notMem_measureSupport, fun t => and_comm (b := x in t)] nhds_basis_opens x

中文:
引理 compl_support_eq_sUnion
  结论: μ.supportᶜ = ⋃₀ {t : 集合 X | 是开集 t ∧ μ t = 0}
  证明: by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, and_right_comm,
.notMem_measureSupport, fun t => and_comm (b := x in t)] nhds_basis_opens x

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sUnion, and_comm, and_right_comm, mem_compl_iff, mem_ofPred_eq, mem_sUnion, nhds_basis_opens, notMem_measureSupport
-/
lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, and_right_comm,
.notMem_measureSupport, fun t => and_comm (b := x in t)] nhds_basis_opens x

/--
lemma `support_eq_sInter` / 引理 `support_eq_sInter`

English:
lemma support_eq_sInter
  statement: μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0}
  proof: by
  convert! congr($(compl_support_eq_sUnion (μ := μ))ᶜ)
  all_goals simp [Set.compl_sUnion, compl_involutive.image_eq_preimage_symm]

中文:
引理 support_eq_s整数er
  结论: μ.support = ⋂₀ {t : 集合 X | 是闭集 t ∧ μ tᶜ = 0}
  证明: by
  convert! congr($(compl_support_eq_sUnion (μ := μ))ᶜ)
  all_goals simp [Set.compl_sUnion, compl_involutive.image_eq_preimage_symm]

Depends on / 依赖: Set.compl_sUnion, all_goals, compl_involutive, compl_involutive.image_eq_preimage_symm, compl_sUnion, compl_support_eq_sUnion, convert, image_eq_preimage_symm
-/
lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  convert! congr($(compl_support_eq_sUnion (μ := μ))ᶜ)
  all_goals simp [Set.compl_sUnion, compl_involutive.image_eq_preimage_symm]

section Regular

/--
lemma `measure_eq_zero_of_isCompact_subset_compl_support` / 引理 `measure_eq_zero_of_isCompact_subset_compl_support`

English:
lemma measure_eq_zero_of_isCompact_subset_compl_support
  statement: {K : Set X} (hK : IsCompact K)
  proof: by
  refine hK.induction_on measure_empty ?_ ?_ ?_
  · exact fun _ _ hst ht => measure_mono_null hst ht
  · exact fun _ _ hs ht => measure_union_null hs ht
  · intro x hxK
    obtain ⟨U, hUnhds, hU0⟩ := notMem_support_iff_exists.1 (hKsub hxK)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hUnhds, hU0⟩

中文:
引理 measure_eq_zero_of_isCompact_subset_compl_support
  结论: {K : 集合 X} (hK : 是紧集 K)
  证明: by
  refine hK.induction_on measure_empty ?_ ?_ ?_
  · exact fun _ _ hst ht => measure_mono_null hst ht
  · exact fun _ _ hs ht => measure_union_null hs ht
  · intro x hxK
    obtain ⟨U, hUnhds, hU0⟩ := notMem_support_iff_exists.1 (hKsub hxK)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hUnhds, hU0⟩

Depends on / 依赖: hK.induction_on, hUnhds, induction_on, measure_empty, measure_mono_null, measure_union_null, mem_nhdsWithin_of_mem_nhds, notMem_support_iff_exists
-/
lemma measure_eq_zero_of_isCompact_subset_compl_support {K : Set X} (hK : IsCompact K)
    (hKsub : K subseteq μ.supportᶜ) : μ K = 0 := by
  refine hK.induction_on measure_empty ?_ ?_ ?_
  · exact fun _ _ hst ht => measure_mono_null hst ht
  · exact fun _ _ hs ht => measure_union_null hs ht
  · intro x hxK
    obtain ⟨U, hUnhds, hU0⟩ := notMem_support_iff_exists.1 (hKsub hxK)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hUnhds, hU0⟩

/--
lemma `support_mem_ae_of_innerRegularWRT_isCompact_isOpen` / 引理 `support_mem_ae_of_innerRegularWRT_isCompact_isOpen`

English:
lemma support_mem_ae_of_innerRegularWRT_isCompact_isOpen
  proof: by
  by_contra hne
  obtain ⟨K, hKsub, hKcompact, hKpos⟩ := hμ isOpen_compl_support 0 (pos_iff_ne_zero.2 hne)
  simp [measure_eq_zero_of_isCompact_subset_compl_support hKcompact hKsub] at hKpos

中文:
引理 support_mem_ae_of_innerRegularWRT_isCompact_isOpen
  证明: by
  by_contra hne
  obtain ⟨K, hKsub, hKcompact, hKpos⟩ := hμ isOpen_compl_support 0 (pos_iff_ne_zero.2 hne)
  simp [measure_eq_zero_of_isCompact_subset_compl_support hKcompact hKsub] at hKpos

Depends on / 依赖: hKcompact, isOpen_compl_support, measure_eq_zero_of_isCompact_subset_compl_support, pos_iff_ne_zero
-/
lemma support_mem_ae_of_innerRegularWRT_isCompact_isOpen
    (hμ : μ.InnerRegularWRT IsCompact IsOpen) : μ.support in ae μ := by
  by_contra hne
  obtain ⟨K, hKsub, hKcompact, hKpos⟩ := hμ isOpen_compl_support 0 (pos_iff_ne_zero.2 hne)
  simp [measure_eq_zero_of_isCompact_subset_compl_support hKcompact hKsub] at hKpos

/-- A measure which is compact-inner-regular on open sets has conull support. -/
@[simp]
/--
lemma `measure_compl_support_of_innerRegularWRT_isCompact_isOpen` / 引理 `measure_compl_support_of_innerRegularWRT_isCompact_isOpen`

English:
lemma measure_compl_support_of_innerRegularWRT_isCompact_isOpen
  proof: support_mem_ae_of_innerRegularWRT_isCompact_isOpen hμ

中文:
引理 measure_compl_support_of_innerRegularWRT_isCompact_isOpen
  证明: support_mem_ae_of_innerRegularWRT_isCompact_isOpen hμ

Depends on / 依赖: support_mem_ae_of_innerRegularWRT_isCompact_isOpen
-/
lemma measure_compl_support_of_innerRegularWRT_isCompact_isOpen
    (hμ : μ.InnerRegularWRT IsCompact IsOpen) : μ μ.supportᶜ = 0 :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen hμ

/--
lemma `support_mem_ae_of_innerRegular` / 引理 `support_mem_ae_of_innerRegular`

English:
lemma support_mem_ae_of_innerRegular
  given: [OpensMeasurableSpace X] [μ.InnerRegular]
  proof: support_mem_ae_of_innerRegularWRT_isCompact_isOpen fun _ hU r hr =>
    InnerRegular.innerRegular hU.measurableSet r hr

中文:
引理 support_mem_ae_of_innerRegular
  条件: [OpensMeasurable空间 X] [μ.内正则]
  证明: support_mem_ae_of_innerRegularWRT_isCompact_isOpen fun _ hU r hr =>
    InnerRegular.innerRegular hU.measurableSet r hr

Depends on / 依赖: InnerRegular, InnerRegular.innerRegular, hU.measurableSet, innerRegular, measurableSet, support_mem_ae_of_innerRegularWRT_isCompact_isOpen
-/
lemma support_mem_ae_of_innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] :
    μ.support in ae μ :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen fun _ hU r hr =>
    InnerRegular.innerRegular hU.measurableSet r hr

/-- An inner regular measure has conull support when open sets are measurable. -/
@[simp]
/--
lemma `measure_compl_support_of_innerRegular` / 引理 `measure_compl_support_of_innerRegular`

English:
lemma measure_compl_support_of_innerRegular
  given: [OpensMeasurableSpace X] [μ.InnerRegular]
  proof: support_mem_ae_of_innerRegular

中文:
引理 measure_compl_support_of_innerRegular
  条件: [OpensMeasurable空间 X] [μ.内正则]
  证明: support_mem_ae_of_innerRegular

Depends on / 依赖: support_mem_ae_of_innerRegular
-/
lemma measure_compl_support_of_innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] :
    μ μ.supportᶜ = 0 := support_mem_ae_of_innerRegular

/--
lemma `support_mem_ae_of_regular` / 引理 `support_mem_ae_of_regular`

English:
lemma support_mem_ae_of_regular
  given: [μ.Regular]
  statement: μ.support in ae μ
  proof: support_mem_ae_of_innerRegularWRT_isCompact_isOpen Regular.innerRegular

中文:
引理 support_mem_ae_of_regular
  条件: [μ.正则]
  结论: μ.support in ae μ
  证明: support_mem_ae_of_innerRegularWRT_isCompact_isOpen Regular.innerRegular

Depends on / 依赖: Regular, Regular.innerRegular, innerRegular, support_mem_ae_of_innerRegularWRT_isCompact_isOpen
-/
lemma support_mem_ae_of_regular [μ.Regular] : μ.support in ae μ :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen Regular.innerRegular

/-- A regular measure has conull support. -/
@[simp]
/--
lemma `measure_compl_support_of_regular` / 引理 `measure_compl_support_of_regular`

English:
lemma measure_compl_support_of_regular
  given: [μ.Regular]
  statement: μ μ.supportᶜ = 0
  proof: support_mem_ae_of_regular

中文:
引理 measure_compl_support_of_regular
  条件: [μ.正则]
  结论: μ μ.supportᶜ = 0
  证明: support_mem_ae_of_regular

Depends on / 依赖: support_mem_ae_of_regular
-/
lemma measure_compl_support_of_regular [μ.Regular] : μ μ.supportᶜ = 0 :=
  support_mem_ae_of_regular

end Regular

section Lindelof

/--
lemma `support_mem_ae_of_isLindelof` / 引理 `support_mem_ae_of_isLindelof`

English:
lemma support_mem_ae_of_isLindelof
  given: (h : IsLindelof μ.supportᶜ)
  statement: μ.support in ae μ
  proof: by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs => ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

中文:
引理 support_mem_ae_of_isLindelof
  条件: (h : IsLindelof μ.supportᶜ)
  结论: μ.support in ae μ
  证明: by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs => ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

Depends on / 依赖: compl_compl, compl_mem_ae_iff, compl_mem_sets_of_nhdsWithin, h.compl_mem_sets_of_nhdsWithin, isOpen_compl_support, isOpen_compl_support.nhdsWithin_eq, nhdsWithin_eq, notMem_support_iff_exists, notMem_support_iff_exists.mp, support
-/
lemma support_mem_ae_of_isLindelof (h : IsLindelof μ.supportᶜ) : μ.support in ae μ := by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs => ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

variable [HereditarilyLindelofSpace X]

/--
lemma `support_mem_ae` / 引理 `support_mem_ae`

English:
lemma support_mem_ae
  statement: μ.support in ae μ
  proof: support_mem_ae_of_isLindelof HereditarilyLindelofSpace.isLindelof μ.supportᶜ

@[simp]

中文:
引理 support_mem_ae
  结论: μ.support in ae μ
  证明: support_mem_ae_of_isLindelof HereditarilyLindelofSpace.isLindelof μ.supportᶜ

@[simp]

Depends on / 依赖: HereditarilyLindelofSpace, HereditarilyLindelofSpace.isLindelof, isLindelof, support_mem_ae_of_isLindelof
-/
lemma support_mem_ae : μ.support in ae μ :=
support_mem_ae_of_isLindelof HereditarilyLindelofSpace.isLindelof μ.supportᶜ

@[simp]
/--
lemma `measure_compl_support` / 引理 `measure_compl_support`

English:
lemma measure_compl_support
  statement: μ μ.supportᶜ = 0
  proof: support_mem_ae

中文:
引理 measure_compl_support
  结论: μ μ.supportᶜ = 0
  证明: support_mem_ae

Depends on / 依赖: support_mem_ae
-/
lemma measure_compl_support : μ μ.supportᶜ = 0 := support_mem_ae

open Set

/--
lemma `nonempty_inter_support_of_pos` / 引理 `nonempty_inter_support_of_pos`

English:
lemma nonempty_inter_support_of_pos
  given: {s : Set X} (hμ : 0 < μ s)
  proof: by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! hμ
.trans by simp exact μ.mono hμ.subset_compl_right

中文:
引理 nonempty_inter_support_of_pos
  条件: {s : 集合 X} (hμ : 0 < μ s)
  证明: by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! hμ
.trans by simp exact μ.mono hμ.subset_compl_right

Depends on / 依赖: Set.not_disjoint_iff_nonempty_inter, contrapose, not_disjoint_iff_nonempty_inter, subset_compl_right
-/
lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s inter μ.support).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! hμ
.trans by simp exact μ.mono hμ.subset_compl_right

/--
lemma `nullMeasurableSet_compl_support` / 引理 `nullMeasurableSet_compl_support`

English:
lemma nullMeasurableSet_compl_support
  statement: NullMeasurableSet (μ.supportᶜ) μ
  proof: NullMeasurableSet.of_null measure_compl_support

中文:
引理 nullMeasurableSet_compl_support
  结论: NullMeasurableSet (μ.supportᶜ) μ
  证明: NullMeasurableSet.of_null measure_compl_support

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.of_null, measure_compl_support, of_null
-/
lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ :=
  NullMeasurableSet.of_null measure_compl_support

/--
lemma `nullMeasurableSet_support` / 引理 `nullMeasurableSet_support`

English:
lemma nullMeasurableSet_support
  statement: NullMeasurableSet μ.support μ
  proof: NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support

中文:
引理 nullMeasurableSet_support
  结论: NullMeasurableSet μ.support μ
  证明: NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.compl_iff.mp, compl_iff, nullMeasurableSet_compl_support
-/
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ :=
  NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support

/--
lemma `nonempty_support` / 引理 `nonempty_support`

English:
lemma nonempty_support
  given: (hμ : μ != 0)
  statement: μ.support.Nonempty
  proof: Nonempty.right nonempty_inter_support_of_pos measure_univ_pos.mpr hμ

中文:
引理 nonempty_support
  条件: (hμ : μ != 0)
  结论: μ.support.非空
  证明: Nonempty.right nonempty_inter_support_of_pos measure_univ_pos.mpr hμ

Depends on / 依赖: Nonempty, Nonempty.right, measure_univ_pos, measure_univ_pos.mpr, nonempty_inter_support_of_pos
-/
lemma nonempty_support (hμ : μ != 0) : μ.support.Nonempty :=
Nonempty.right nonempty_inter_support_of_pos measure_univ_pos.mpr hμ

/--
lemma `nonempty_support_iff` / 引理 `nonempty_support_iff`

English:
lemma nonempty_support_iff
  statement: μ.support.Nonempty ↔ μ != 0
  proof: ⟨fun h e => (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e |>.trans
 support_zero) h, fun h => nonempty_support h⟩

@[simp]

中文:
引理 nonempty_support_iff
  结论: μ.support.非空 ↔ μ != 0
  证明: ⟨fun h e => (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e |>.trans
 support_zero) h, fun h => nonempty_support h⟩

@[simp]

Depends on / 依赖: Measure, Measure.support, nonempty_support, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.mpr, support, support_zero
-/
lemma nonempty_support_iff : μ.support.Nonempty ↔ μ != 0 :=
  ⟨fun h e => (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e |>.trans
 support_zero) h, fun h => nonempty_support h⟩

@[simp]
/--
lemma `support_eq_empty_iff` / 引理 `support_eq_empty_iff`

English:
lemma support_eq_empty_iff
  statement: μ.support = ∅ ↔ μ = 0
  proof: by
  simp [← Set.not_nonempty_iff_eq_empty, not_congr nonempty_support_iff]

中文:
引理 support_eq_empty_iff
  结论: μ.support = ∅ ↔ μ = 0
  证明: by
  simp [← Set.not_nonempty_iff_eq_empty, not_congr nonempty_support_iff]

Depends on / 依赖: Set.not_nonempty_iff_eq_empty, nonempty_support_iff, not_congr, not_nonempty_iff_eq_empty
-/
lemma support_eq_empty_iff : μ.support = ∅ ↔ μ = 0 := by
  simp [← Set.not_nonempty_iff_eq_empty, not_congr nonempty_support_iff]

end Lindelof

section Restrict

variable [OpensMeasurableSpace X]

/--
lemma `mem_support_restrict` / 引理 `mem_support_restrict`

English:
lemma mem_support_restrict
  given: {s : Set X} {x : X}
  proof: by
  rw [nhds_basis_opens x |>.mem_measureSupport]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  grind [IsOpen.measurableSet, restrict_apply]

中文:
引理 mem_support_restrict
  条件: {s : 集合 X} {x : X}
  证明: by
  rw [nhds_basis_opens x |>.mem_measureSupport]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  grind [IsOpen.measurableSet, restrict_apply]

Depends on / 依赖: IsOpen, IsOpen.measurableSet, frequently_smallSets, measurableSet, mem_measureSupport, nhdsWithin_basis_open, nhds_basis_opens, pos_mono, restrict_apply
-/
lemma mem_support_restrict {s : Set X} {x : X} :
    x in (μ.restrict s).support ↔ existsᶠ u in (𝓝[s] x).smallSets, 0 < μ u := by
  rw [nhds_basis_opens x |>.mem_measureSupport]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  grind [IsOpen.measurableSet, restrict_apply]

/--
lemma `interior_inter_support` / 引理 `interior_inter_support`

English:
lemma interior_inter_support
  given: {s : Set X}
  proof: by
  rintro x ⟨hxs, hxμ⟩
  rw [mem_support_restrict]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  rw [(nhds_basis_opens x).mem_measureSupport] at hxμ
  rintro u ⟨hxu, hu⟩
.trans_le apply hxμ (u inter interior s) ⟨⟨hxu, hxs⟩, hu.inter isOpen_interior⟩
  gcongr
  exact interior_su

中文:
引理 interior_inter_support
  条件: {s : 集合 X}
  证明: by
  rintro x ⟨hxs, hxμ⟩
  rw [mem_support_restrict]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  rw [(nhds_basis_opens x).mem_measureSupport] at hxμ
  rintro u ⟨hxu, hu⟩
.trans_le apply hxμ (u inter interior s) ⟨⟨hxu, hxs⟩, hu.inter isOpen_interior⟩
  gcongr
  exact interior_su

Depends on / 依赖: frequently_smallSets, hu.inter, interior, interior_subset, isOpen_interior, mem_measureSupport, mem_support_restrict, nhdsWithin_basis_open, nhds_basis_opens, pos_mono, trans_le
-/
lemma interior_inter_support {s : Set X} :
    interior s inter μ.support subseteq (μ.restrict s).support := by
  rintro x ⟨hxs, hxμ⟩
  rw [mem_support_restrict]; rw [(nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  rw [(nhds_basis_opens x).mem_measureSupport] at hxμ
  rintro u ⟨hxu, hu⟩
.trans_le apply hxμ (u inter interior s) ⟨⟨hxu, hxs⟩, hu.inter isOpen_interior⟩
  gcongr
  exact interior_subset

/--
lemma `support_restrict_subset` / 引理 `support_restrict_subset`

English:
lemma support_restrict_subset
  given: {s : Set X}
  proof: by
  refine Set.subset_inter (support_subset_of_isClosed isClosed_closure ?_)
    (support_mono restrict_le_self)
  rw [mem_ae_iff]; rw [μ.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  convert! μ.empty
  exact subset_closure.disjoint_compl_left.eq_bot

中文:
引理 support_restrict_subset
  条件: {s : 集合 X}
  证明: by
  refine Set.subset_inter (support_subset_of_isClosed isClosed_closure ?_)
    (support_mono restrict_le_self)
  rw [mem_ae_iff]; rw [μ.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  convert! μ.empty
  exact subset_closure.disjoint_compl_left.eq_bot

Depends on / 依赖: Set.subset_inter, convert, disjoint_compl_left, eq_bot, isClosed_closure, isClosed_closure.isOpen_compl.measurableSet, isOpen_compl, measurableSet, mem_ae_iff, restrict_apply, restrict_le_self, subset_closure, subset_closure.disjoint_compl_left.eq_bot, subset_inter, support_mono, support_subset_of_isClosed
-/
lemma support_restrict_subset {s : Set X} :
    (μ.restrict s).support subseteq closure s inter μ.support := by
  refine Set.subset_inter (support_subset_of_isClosed isClosed_closure ?_)
    (support_mono restrict_le_self)
  rw [mem_ae_iff]; rw [μ.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  convert! μ.empty
  exact subset_closure.disjoint_compl_left.eq_bot

end Restrict

end Measure

end MeasureTheory

end Support
