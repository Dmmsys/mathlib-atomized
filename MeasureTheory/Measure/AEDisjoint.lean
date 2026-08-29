/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `MeasureTheory.AEDisjoint`) if their
intersection has measure zero. This assumption can be used instead of `Disjoint` in most theorems in
measure theory.
-/

@[expose] public section


open Set Function

namespace MeasureTheory

variable {ι α : Type*} {m : MeasurableSpace α} (μ : Measure α)

/--
Definition of `AEDisjoint` / `AEDisjoint` 的定义

English:
definition AEDisjoint
  signature: (s t : Set α)
  body: μ (s inter t) = 0

中文:
定义 AEDisjoint
  签名: (s t : Set α)
  定义体: μ (s inter t) = 0
-/
def AEDisjoint (s t : Set α) :=
  μ (s inter t) = 0

variable {μ} {s t u v : Set α}

/--
theorem `exists_null_pairwise_disjoint_sdiff` / 定理 `exists_null_pairwise_disjoint_sdiff`

English:
theorem exists_null_pairwise_disjoint_sdiff
  statement: [Countable ι] {s : ι -> Set α}
  proof: by
  refine ⟨fun i => toMeasurable μ (s i inter ⋃ j in ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, 

中文:
定理 exists_null_pairwise_disjoint_sdiff
  结论: [Countable ι] {s : ι -> Set α}
  证明: by
  refine ⟨fun i => toMeasurable μ (s i inter ⋃ j in ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, 

Depends on / 依赖: Classical, Classical.not_not, Ne.symm, Pairwise, and_imp, disjoint_left, iUnion, inter_iUnion, measurableSet_toMeasurable, measure_biUnion_null_iff, measure_toMeasurable, mem_sdiff, not_and, not_not, replace, subset_toMeasurable, toMeasurable, to_countable
-/
theorem exists_null_pairwise_disjoint_sdiff [Countable ι] {s : ι -> Set α}
    (hd : Pairwise (AEDisjoint μ on s)) : exists t : ι -> Set α, (forall i, MeasurableSet (t i)) ∧
    (forall i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) := by
  refine ⟨fun i => toMeasurable μ (s i inter ⋃ j in ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, onFun, mem_sdiff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i inter iUnion fun j => iUnion fun _ => s j :=
      fun h => hU (subset_toMeasurable _ _ h)
    simp only [mem_inter_iff, mem_iUnion, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim

@[deprecated (since := "2026-06-03")]
alias exists_null_pairwise_disjoint_diff := exists_null_pairwise_disjoint_sdiff

namespace AEDisjoint

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : AEDisjoint μ s t)
  statement: μ (s inter t) = 0
  proof: h

@[symm]

中文:
定理 eq
  条件: (h : AEDisjoint μ s t)
  结论: μ (s inter t) = 0
  证明: h

@[symm]
-/
protected theorem eq (h : AEDisjoint μ s t) : μ (s inter t) = 0 :=
  h

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : AEDisjoint μ s t)
  statement: AEDisjoint μ t s
  proof: by rwa [AEDisjoint, inter_comm]

中文:
定理 symm
  条件: (h : AEDisjoint μ s t)
  结论: AEDisjoint μ t s
  证明: by rwa [AEDisjoint, inter_comm]
-/
protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [AEDisjoint, inter_comm]

/--
Instance `stdSymm` / 实例 `stdSymm`

English:
instance stdSymm
  signature: : Std.Symm (AEDisjoint μ) where
  body: AEDisjoint.symm

@[deprecated (since := "2026-06-10")] protected alias symmetric := AEDisjoint.stdSymm

中文:
实例 stdSymm
  签名: : Std.Symm (AEDisjoint μ) where
  定义体: AEDisjoint.symm

@[deprecated (since := "2026-06-10")] protected alias symmetric := AEDisjoint.stdSymm

Depends on / 依赖: AEDisjoint, AEDisjoint.symm
-/
instance stdSymm : Std.Symm (AEDisjoint μ) where
  symm _ _ := AEDisjoint.symm

@[deprecated (since := "2026-06-10")] protected alias symmetric := AEDisjoint.stdSymm

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  statement: AEDisjoint μ s t ↔ AEDisjoint μ t s
  proof: ⟨AEDisjoint.symm, AEDisjoint.symm⟩

中文:
定理 comm
  结论: AEDisjoint μ s t ↔ AEDisjoint μ t s
  证明: ⟨AEDisjoint.symm, AEDisjoint.symm⟩
-/
protected theorem comm : AEDisjoint μ s t ↔ AEDisjoint μ t s :=
  ⟨AEDisjoint.symm, AEDisjoint.symm⟩

/--
theorem `_root_.Disjoint.aedisjoint` / 定理 `_root_.Disjoint.aedisjoint`

English:
theorem _root_.Disjoint.aedisjoint
  given: (h : Disjoint s t)
  statement: AEDisjoint μ s t
  proof: by
  rw [AEDisjoint]; rw [disjoint_iff_inter_eq_empty.1 h]; rw [measure_empty]

中文:
定理 _root_.Disjoint.aedisjoint
  条件: (h : Disjoint s t)
  结论: AEDisjoint μ s t
  证明: by
  rw [AEDisjoint]; rw [disjoint_iff_inter_eq_empty.1 h]; rw [measure_empty]
-/
protected theorem _root_.Disjoint.aedisjoint (h : Disjoint s t) : AEDisjoint μ s t := by
  rw [AEDisjoint]; rw [disjoint_iff_inter_eq_empty.1 h]; rw [measure_empty]

/--
theorem `_root_.Pairwise.aedisjoint` / 定理 `_root_.Pairwise.aedisjoint`

English:
theorem _root_.Pairwise.aedisjoint
  given: {f : ι -> Set α} (hf : Pairwise (Disjoint on f))
  proof: hf.mono fun _i _j h => h.aedisjoint

中文:
定理 _root_.Pairwise.aedisjoint
  条件: {f : ι -> Set α} (hf : Pairwise (Disjoint on f))
  证明: hf.mono fun _i _j h => h.aedisjoint
-/
protected theorem _root_.Pairwise.aedisjoint {f : ι -> Set α} (hf : Pairwise (Disjoint on f)) :
    Pairwise (AEDisjoint μ on f) :=
  hf.mono fun _i _j h => h.aedisjoint

/--
theorem `_root_.Set.PairwiseDisjoint.aedisjoint` / 定理 `_root_.Set.PairwiseDisjoint.aedisjoint`

English:
theorem _root_.Set.PairwiseDisjoint.aedisjoint
  statement: {f : ι -> Set α} {s : Set ι}
  proof: hf.mono' fun _i _j h => h.aedisjoint

中文:
定理 _root_.Set.PairwiseDisjoint.aedisjoint
  结论: {f : ι -> Set α} {s : Set ι}
  证明: hf.mono' fun _i _j h => h.aedisjoint
-/
protected theorem _root_.Set.PairwiseDisjoint.aedisjoint {f : ι -> Set α} {s : Set ι}
    (hf : s.PairwiseDisjoint f) : s.Pairwise (AEDisjoint μ on f) :=
  hf.mono' fun _i _j h => h.aedisjoint

/--
theorem `mono_ae` / 定理 `mono_ae`

English:
theorem mono_ae
  given: (h : AEDisjoint μ s t) (hu : u <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t)
  statement: AEDisjoint μ u v
  proof: measure_mono_null_ae (hu.inter hv) h

中文:
定理 mono_ae
  条件: (h : AEDisjoint μ s t) (hu : u <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t)
  结论: AEDisjoint μ u v
  证明: measure_mono_null_ae (hu.inter hv) h

Depends on / 依赖: hu.inter, measure_mono_null_ae
-/
theorem mono_ae (h : AEDisjoint μ s t) (hu : u <=ᵐ[μ] s) (hv : v <=ᵐ[μ] t) : AEDisjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : AEDisjoint μ s t) (hu : u subseteq s) (hv : v subseteq t)
  statement: AEDisjoint μ u v
  proof: mono_ae h (LE.le.eventuallyLE hu) (LE.le.eventuallyLE hv)

中文:
定理 mono
  条件: (h : AEDisjoint μ s t) (hu : u subseteq s) (hv : v subseteq t)
  结论: AEDisjoint μ u v
  证明: mono_ae h (LE.le.eventuallyLE hu) (LE.le.eventuallyLE hv)
-/
protected theorem mono (h : AEDisjoint μ s t) (hu : u subseteq s) (hv : v subseteq t) : AEDisjoint μ u v :=
  mono_ae h (LE.le.eventuallyLE hu) (LE.le.eventuallyLE hv)

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t)
  proof: mono_ae h (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)

@[simp]

中文:
定理 congr
  条件: (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t)
  证明: mono_ae h (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)

@[simp]
-/
protected theorem congr (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
    AEDisjoint μ u v :=
  mono_ae h (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)

@[simp]
/--
theorem `iUnion_left_iff` / 定理 `iUnion_left_iff`

English:
theorem iUnion_left_iff
  given: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  proof: by
  simp only [AEDisjoint, iUnion_inter, measure_iUnion_null_iff]

@[simp]

中文:
定理 iUnion_left_iff
  条件: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  证明: by
  simp only [AEDisjoint, iUnion_inter, measure_iUnion_null_iff]

@[simp]

Depends on / 依赖: AEDisjoint, iUnion_inter, measure_iUnion_null_iff
-/
theorem iUnion_left_iff {ι : Sort*} [Countable ι] {s : ι -> Set α} :
    AEDisjoint μ (⋃ i, s i) t ↔ forall i, AEDisjoint μ (s i) t := by
  simp only [AEDisjoint, iUnion_inter, measure_iUnion_null_iff]

@[simp]
/--
theorem `iUnion_right_iff` / 定理 `iUnion_right_iff`

English:
theorem iUnion_right_iff
  given: {ι : Sort*} [Countable ι] {t : ι -> Set α}
  proof: by
  simp only [AEDisjoint, inter_iUnion, measure_iUnion_null_iff]

@[simp]

中文:
定理 iUnion_right_iff
  条件: {ι : Sort*} [Countable ι] {t : ι -> Set α}
  证明: by
  simp only [AEDisjoint, inter_iUnion, measure_iUnion_null_iff]

@[simp]

Depends on / 依赖: AEDisjoint, inter_iUnion, measure_iUnion_null_iff
-/
theorem iUnion_right_iff {ι : Sort*} [Countable ι] {t : ι -> Set α} :
    AEDisjoint μ s (⋃ i, t i) ↔ forall i, AEDisjoint μ s (t i) := by
  simp only [AEDisjoint, inter_iUnion, measure_iUnion_null_iff]

@[simp]
/--
theorem `union_left_iff` / 定理 `union_left_iff`

English:
theorem union_left_iff
  statement: AEDisjoint μ (s union t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u
  proof: by
  simp [union_eq_iUnion, and_comm]

@[simp]

中文:
定理 union_left_iff
  结论: AEDisjoint μ (s union t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u
  证明: by
  simp [union_eq_iUnion, and_comm]

@[simp]

Depends on / 依赖: and_comm, union_eq_iUnion
-/
theorem union_left_iff : AEDisjoint μ (s union t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u := by
  simp [union_eq_iUnion, and_comm]

@[simp]
/--
theorem `union_right_iff` / 定理 `union_right_iff`

English:
theorem union_right_iff
  statement: AEDisjoint μ s (t union u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u
  proof: by
  simp [union_eq_iUnion, and_comm]

中文:
定理 union_right_iff
  结论: AEDisjoint μ s (t union u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u
  证明: by
  simp [union_eq_iUnion, and_comm]

Depends on / 依赖: and_comm, union_eq_iUnion
-/
theorem union_right_iff : AEDisjoint μ s (t union u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u := by
  simp [union_eq_iUnion, and_comm]

/--
theorem `union_left` / 定理 `union_left`

English:
theorem union_left
  given: (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u)
  statement: AEDisjoint μ (s union t) u
  proof: union_left_iff.mpr ⟨hs, ht⟩

中文:
定理 union_left
  条件: (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u)
  结论: AEDisjoint μ (s union t) u
  证明: union_left_iff.mpr ⟨hs, ht⟩

Depends on / 依赖: union_left_iff, union_left_iff.mpr
-/
theorem union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ (s union t) u :=
  union_left_iff.mpr ⟨hs, ht⟩

/--
theorem `union_right` / 定理 `union_right`

English:
theorem union_right
  given: (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u)
  statement: AEDisjoint μ s (t union u)
  proof: union_right_iff.2 ⟨ht, hu⟩

中文:
定理 union_right
  条件: (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u)
  结论: AEDisjoint μ s (t union u)
  证明: union_right_iff.2 ⟨ht, hu⟩

Depends on / 依赖: union_right_iff
-/
theorem union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ s (t union u) :=
  union_right_iff.2 ⟨ht, hu⟩

/--
theorem `sdiff_ae_eq_left` / 定理 `sdiff_ae_eq_left`

English:
theorem sdiff_ae_eq_left
  given: (h : AEDisjoint μ s t)
  statement: (s \ t : Set α) =ᵐ[μ] s
  proof: @sdiff_self_inter _ s t ▸ sdiff_null_ae_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_left := sdiff_ae_eq_left

中文:
定理 sdiff_ae_eq_left
  条件: (h : AEDisjoint μ s t)
  结论: (s \ t : Set α) =ᵐ[μ] s
  证明: @sdiff_self_inter _ s t ▸ sdiff_null_ae_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_left := sdiff_ae_eq_left

Depends on / 依赖: sdiff_null_ae_eq_self, sdiff_self_inter
-/
theorem sdiff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @sdiff_self_inter _ s t ▸ sdiff_null_ae_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_left := sdiff_ae_eq_left

/--
theorem `sdiff_ae_eq_right` / 定理 `sdiff_ae_eq_right`

English:
theorem sdiff_ae_eq_right
  given: (h : AEDisjoint μ s t)
  statement: (t \ s : Set α) =ᵐ[μ] t
  proof: sdiff_ae_eq_left AEDisjoint.symm h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_right := sdiff_ae_eq_right

中文:
定理 sdiff_ae_eq_right
  条件: (h : AEDisjoint μ s t)
  结论: (t \ s : Set α) =ᵐ[μ] t
  证明: sdiff_ae_eq_left AEDisjoint.symm h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_right := sdiff_ae_eq_right

Depends on / 依赖: AEDisjoint, AEDisjoint.symm, sdiff_ae_eq_left
-/
theorem sdiff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
sdiff_ae_eq_left AEDisjoint.symm h

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_right := sdiff_ae_eq_right

/--
theorem `measure_sdiff_left` / 定理 `measure_sdiff_left`

English:
theorem measure_sdiff_left
  given: (h : AEDisjoint μ s t)
  statement: μ (s \ t) = μ s
  proof: measure_congr AEDisjoint.sdiff_ae_eq_left h

@[deprecated (since := "2026-06-03")] alias measure_diff_left := measure_sdiff_left

中文:
定理 measure_sdiff_left
  条件: (h : AEDisjoint μ s t)
  结论: μ (s \ t) = μ s
  证明: measure_congr AEDisjoint.sdiff_ae_eq_left h

@[deprecated (since := "2026-06-03")] alias measure_diff_left := measure_sdiff_left

Depends on / 依赖: AEDisjoint, AEDisjoint.sdiff_ae_eq_left, measure_congr, sdiff_ae_eq_left
-/
theorem measure_sdiff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s :=
measure_congr AEDisjoint.sdiff_ae_eq_left h

@[deprecated (since := "2026-06-03")] alias measure_diff_left := measure_sdiff_left

/--
theorem `measure_sdiff_right` / 定理 `measure_sdiff_right`

English:
theorem measure_sdiff_right
  given: (h : AEDisjoint μ s t)
  statement: μ (t \ s) = μ t
  proof: measure_congr AEDisjoint.sdiff_ae_eq_right h

@[deprecated (since := "2026-06-03")] alias measure_diff_right := measure_sdiff_right

中文:
定理 measure_sdiff_right
  条件: (h : AEDisjoint μ s t)
  结论: μ (t \ s) = μ t
  证明: measure_congr AEDisjoint.sdiff_ae_eq_right h

@[deprecated (since := "2026-06-03")] alias measure_diff_right := measure_sdiff_right

Depends on / 依赖: AEDisjoint, AEDisjoint.sdiff_ae_eq_right, measure_congr, sdiff_ae_eq_right
-/
theorem measure_sdiff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t :=
measure_congr AEDisjoint.sdiff_ae_eq_right h

@[deprecated (since := "2026-06-03")] alias measure_diff_right := measure_sdiff_right

/--
theorem `exists_disjoint_diff` / 定理 `exists_disjoint_diff`

English:
theorem exists_disjoint_diff
  given: (h : AEDisjoint μ s t)
  proof: ⟨toMeasurable μ (s inter t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left (b := s \ t) fun x hx => by
simpa using ⟨hx.1, fun hxt => hx.2 subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩

中文:
定理 exists_disjoint_diff
  条件: (h : AEDisjoint μ s t)
  证明: ⟨toMeasurable μ (s inter t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left (b := s \ t) fun x hx => by
simpa using ⟨hx.1, fun hxt => hx.2 subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩

Depends on / 依赖: disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono_left, measurableSet_toMeasurable, measure_toMeasurable, mono_left, subset_toMeasurable, toMeasurable
-/
theorem exists_disjoint_diff (h : AEDisjoint μ s t) :
    exists u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨toMeasurable μ (s inter t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left (b := s \ t) fun x hx => by
simpa using ⟨hx.1, fun hxt => hx.2 subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩

/--
theorem `of_null_right` / 定理 `of_null_right`

English:
theorem of_null_right
  given: (h : μ t = 0)
  statement: AEDisjoint μ s t
  proof: measure_mono_null inter_subset_right h

中文:
定理 of_null_right
  条件: (h : μ t = 0)
  结论: AEDisjoint μ s t
  证明: measure_mono_null inter_subset_right h

Depends on / 依赖: inter_subset_right, measure_mono_null
-/
theorem of_null_right (h : μ t = 0) : AEDisjoint μ s t :=
  measure_mono_null inter_subset_right h

/--
theorem `of_null_left` / 定理 `of_null_left`

English:
theorem of_null_left
  given: (h : μ s = 0)
  statement: AEDisjoint μ s t
  proof: AEDisjoint.symm (of_null_right h)

中文:
定理 of_null_left
  条件: (h : μ s = 0)
  结论: AEDisjoint μ s t
  证明: AEDisjoint.symm (of_null_right h)

Depends on / 依赖: AEDisjoint, AEDisjoint.symm, of_null_right
-/
theorem of_null_left (h : μ s = 0) : AEDisjoint μ s t :=
  AEDisjoint.symm (of_null_right h)

end AEDisjoint

/--
theorem `aedisjoint_compl_left` / 定理 `aedisjoint_compl_left`

English:
theorem aedisjoint_compl_left
  statement: AEDisjoint μ sᶜ s
  proof: (@disjoint_compl_left _ _ s).aedisjoint

中文:
定理 aedisjoint_compl_left
  结论: AEDisjoint μ sᶜ s
  证明: (@disjoint_compl_left _ _ s).aedisjoint

Depends on / 依赖: aedisjoint, disjoint_compl_left
-/
theorem aedisjoint_compl_left : AEDisjoint μ sᶜ s :=
  (@disjoint_compl_left _ _ s).aedisjoint

/--
theorem `aedisjoint_compl_right` / 定理 `aedisjoint_compl_right`

English:
theorem aedisjoint_compl_right
  statement: AEDisjoint μ s sᶜ
  proof: (@disjoint_compl_right _ _ s).aedisjoint

中文:
定理 aedisjoint_compl_right
  结论: AEDisjoint μ s sᶜ
  证明: (@disjoint_compl_right _ _ s).aedisjoint

Depends on / 依赖: aedisjoint, disjoint_compl_right
-/
theorem aedisjoint_compl_right : AEDisjoint μ s sᶜ :=
  (@disjoint_compl_right _ _ s).aedisjoint

end MeasureTheory
