/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Monotone

/-!
# Points in sight

This file defines the relation of visibility with respect to a set, and lower bounds how many
elements of a set a point sees in terms of the dimension of that set.

## TODO

The art gallery problem can be stated using the visibility predicate: A set `A` (the art gallery) is
guarded by a finite set `G` (the guards) iff `∀ a ∈ A, ∃ g ∈ G, IsVisible ℝ sᶜ a g`.
-/

@[expose] public section

open AffineMap Filter Finset Set
open scoped Cardinal Pointwise Topology

variable {𝕜 V P : Type*}

section AddTorsor
variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  {s t : Set P} {x y z : P}

omit [IsOrderedRing 𝕜] in
variable (𝕜) in
/--
Definition of `IsVisible` / `IsVisible` 的定义

English:
definition IsVisible
  signature: (s : Set P) (x y : P)
  body: forall ⦃z⦄, z in s -> ¬ Sbtw 𝕜 x z y

@[simp, refl]

中文:
定义 IsVisible
  签名: (s : 集合 P) (x y : P)
  定义体: forall ⦃z⦄, z in s -> ¬ Sbtw 𝕜 x z y

@[simp, refl]
-/
def IsVisible (s : Set P) (x y : P) : Prop := forall ⦃z⦄, z in s -> ¬ Sbtw 𝕜 x z y

@[simp, refl]
/--
lemma `IsVisible.rfl` / 引理 `IsVisible.rfl`

English:
lemma IsVisible.rfl
  statement: IsVisible 𝕜 s x x
  proof: by simp [IsVisible]

中文:
引理 IsVisible.rfl
  结论: IsVisible 𝕜 s x x
  证明: by simp [IsVisible]

Depends on / 依赖: IsVisible
-/
lemma IsVisible.rfl : IsVisible 𝕜 s x x := by simp [IsVisible]

/--
lemma `isVisible_comm` / 引理 `isVisible_comm`

English:
lemma isVisible_comm
  statement: IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x
  proof: by
  simp [IsVisible, sbtw_comm]

@[symm] alias ⟨IsVisible.symm, _⟩ := isVisible_comm

omit [IsOrderedRing 𝕜] in

中文:
引理 isVisible_comm
  结论: IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x
  证明: by
  simp [IsVisible, sbtw_comm]

@[symm] alias ⟨IsVisible.symm, _⟩ := isVisible_comm

omit [IsOrderedRing 𝕜] in

Depends on / 依赖: IsVisible, sbtw_comm
-/
lemma isVisible_comm : IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x := by
  simp [IsVisible, sbtw_comm]

@[symm] alias ⟨IsVisible.symm, _⟩ := isVisible_comm

omit [IsOrderedRing 𝕜] in
/--
lemma `IsVisible.mono` / 引理 `IsVisible.mono`

English:
lemma IsVisible.mono
  given: (hst : s subseteq t) (ht : IsVisible 𝕜 t x y)
  statement: IsVisible 𝕜 s x y
  proof: fun _z hz => ht hst hz

中文:
引理 IsVisible.mono
  条件: (hst : s subseteq t) (ht : IsVisible 𝕜 t x y)
  结论: IsVisible 𝕜 s x y
  证明: fun _z hz => ht hst hz
-/
lemma IsVisible.mono (hst : s subseteq t) (ht : IsVisible 𝕜 t x y) : IsVisible 𝕜 s x y :=
fun _z hz => ht hst hz

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isVisible_iff_lineMap` / 引理 `isVisible_iff_lineMap`

English:
lemma isVisible_iff_lineMap
  given: (hxy : x != y)
  proof: by
  simp [IsVisible, sbtw_iff_mem_image_Ioo_and_ne, hxy]
  aesop

中文:
引理 isVisible_iff_lineMap
  条件: (hxy : x != y)
  证明: by
  simp [IsVisible, sbtw_iff_mem_image_Ioo_and_ne, hxy]
  aesop

Depends on / 依赖: IsVisible, sbtw_iff_mem_image_Ioo_and_ne
-/
lemma isVisible_iff_lineMap (hxy : x != y) :
    IsVisible 𝕜 s x y ↔ forall δ in Set.Ioo (0 : 𝕜) 1, lineMap x y δ ∉ s := by
  simp [IsVisible, sbtw_iff_mem_image_Ioo_and_ne, hxy]
  aesop

end AddTorsor

section Module
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {s : Set V} {x y z : V}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsVisible.of_convexHull_of_pos` / 引理 `IsVisible.of_convexHull_of_pos`

English:
lemma IsVisible.of_convexHull_of_pos
  statement: {ι : Type*} {t : Finset ι} {a : ι -> V} {w : ι -> 𝕜}
  proof: by
  classical
obtain hwi | hwi : w i = 1 ∨ w i < 1 := eq_or_lt_of_le (single_le_sum hw₀ hi).trans_eq hw₁
  · convert! hw
    rw [← one_smul 𝕜 (a i)]; rw [← hwi]; rw [eq_comm]
    rw [← hwi]; rw [← sub_eq_zero]; rw [← sum_erase_eq_sub hi]; rw [sum_eq_zero_iff_of_nonneg fun j hj => hw₀ _ erase_subset

中文:
引理 IsVisible.of_convexHull_of_pos
  结论: {ι : 类型} {t : 有限集 ι} {a : ι -> V} {w : ι -> 𝕜}
  证明: by
  classical
obtain hwi | hwi : w i = 1 ∨ w i < 1 := eq_or_lt_of_le (single_le_sum hw₀ hi).trans_eq hw₁
  · convert! hw
    rw [← one_smul 𝕜 (a i)]; rw [← hwi]; rw [eq_comm]
    rw [← hwi]; rw [← sub_eq_zero]; rw [← sum_erase_eq_sub hi]; rw [sum_eq_zero_iff_of_nonneg fun j hj => hw₀ _ erase_subset

Depends on / 依赖: classical, convert, eq_comm, eq_or_lt_of_le, erase_subset, lt_of_ne, mem_erase, one_smul, replace, single_le_sum, sub_eq_zero, sum_eq_single, sum_eq_zero_iff_of_nonneg, sum_erase_eq_sub, trans_eq, zero_smul
-/
lemma IsVisible.of_convexHull_of_pos {ι : Type*} {t : Finset ι} {a : ι -> V} {w : ι -> 𝕜}
    (hw₀ : forall i in t, 0 <= w i) (hw₁ : ∑ i in t, w i = 1) (ha : forall i in t, a i in s)
    (hx : x ∉ convexHull 𝕜 s) (hw : IsVisible 𝕜 (convexHull 𝕜 s) x (∑ i in t, w i • a i)) {i : ι}
    (hi : i in t) (hwi : 0 < w i) : IsVisible 𝕜 (convexHull 𝕜 s) x (a i) := by
  classical
obtain hwi | hwi : w i = 1 ∨ w i < 1 := eq_or_lt_of_le (single_le_sum hw₀ hi).trans_eq hw₁
  · convert! hw
    rw [← one_smul 𝕜 (a i)]; rw [← hwi]; rw [eq_comm]
    rw [← hwi]; rw [← sub_eq_zero]; rw [← sum_erase_eq_sub hi]; rw [sum_eq_zero_iff_of_nonneg fun j hj => hw₀ _ erase_subset _ _ hj] at hw₁
    refine sum_eq_single _ (fun j hj hji => ?_) (by simp [hi])
    rw [hw₁ _ <| mem_erase.2 ⟨hji]; rw [hj⟩]; rw [zero_smul]
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, h⟩
replace hε₀ : 0 < ε := hε₀.lt_of_ne by rintro rfl; simp at h
replace hε₁ : ε < 1 := hε₁.lt_of_ne by rintro rfl; simp at h
  have : 0 < 1 - ε := by linarith
  have hwi : 0 < 1 - w i := by linarith
  refine hw (z := lineMap x (∑ j in t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
?_ sbtw_lineMap_iff.2 ⟨(ne_of_mem_of_not_mem ((convex_convexHull ..).sum_mem hw₀ hw₁
fun i hi => subset_convexHull _ _ ha _ hi) hx).symm, by positivity,
    (div_lt_one <| by positivity).2 ?_⟩
  · have : Wbtw 𝕜
      (lineMap x (a i) ε)
      (lineMap x (∑ j in t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
      (∑ j in t.erase i, (w j / (1 - w i)) • a j) := by
      refine ⟨((1 - w i) / w i) / ((1 - ε) / ε + (1 - w i) / w i + 1), ⟨by positivity, ?_⟩, ?_⟩
      · refine (div_le_one <| by positivity).2 ?_
        calc
          (1 - w i) / w i = 0 + (1 - w i) / w i + 0 := by simp
          _ <= (1 - ε) / ε + (1 - w i) / w i + 1 := by gcongr <;> positivity
      have :
        w i • a i + (1 - w i) • ∑ j in t.erase i, (w j / (1 - w i)) • a j = ∑ j in t, w j • a j := by
        rw [smul_sum]
        simp_rw [smul_smul, mul_div_cancel₀ _ hwi.ne']
        exact add_sum_erase _ (fun i => w i • a i) hi
      simp_rw [lineMap_apply_module, ← this]
      match_scalars <;> field
refine (convex_convexHull _ _).mem_of_wbtw this hε (convex_convexHull _ _).sum_mem ?_ ?_ ?_
    · intro j hj
      positivity [hw₀ j <| erase_subset _ _ hj]
    · rw [← sum_div, sum_erase_eq_sub hi, hw₁, div_self hwi.ne']
· exact fun j hj => subset_convexHull _ _ ha _ erase_subset _ _ hj
· exact lt_add_of_pos_left _ by positivity

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsVisible.eq_of_mem_interior` / 引理 `IsVisible.eq_of_mem_interior`

English:
lemma IsVisible.eq_of_mem_interior
  given: (hsxy : IsVisible 𝕜 s x y) (hy : y in interior s)
  proof: by
  by_contra! hxy
  suffices h : forallᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  have hmem : forallᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap y x δ in s :=
    lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  filter_upwards [hmem, Ioo

中文:
引理 IsVisible.eq_of_mem_interior
  条件: (hsxy : IsVisible 𝕜 s x y) (hy : y in interior s)
  证明: by
  by_contra! hxy
  suffices h : forallᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  have hmem : forallᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap y x δ in s :=
    lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  filter_upwards [hmem, Ioo

Depends on / 依赖: Ioo_mem_nhdsGT, continuousWithinAt, eventually_mem, filter_upwards, h.exists, hsxy.symm, lineMap, lineMap_continuous, lineMap_continuous.continuousWithinAt.eventually_mem, mem_interior_iff_mem_nhds, zero_lt_one
-/
lemma IsVisible.eq_of_mem_interior (hsxy : IsVisible 𝕜 s x y) (hy : y in interior s) :
    x = y := by
  by_contra! hxy
  suffices h : forallᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  have hmem : forallᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap y x δ in s :=
    lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  filter_upwards [hmem, Ioo_mem_nhdsGT zero_lt_one] with δ hmem hsbt using hsxy.symm hmem (by aesop)

/--
lemma `IsOpen.eq_of_isVisible_of_left_mem` / 引理 `IsOpen.eq_of_isVisible_of_left_mem`

English:
lemma IsOpen.eq_of_isVisible_of_left_mem
  given: (hs : IsOpen s) (hsxy : IsVisible 𝕜 s x y) (hy : y in s)
  proof: hsxy.eq_of_mem_interior (by simpa [hs.interior_eq])

中文:
引理 是开集.eq_of_isVisible_of_left_mem
  条件: (hs : 是开集 s) (hsxy : IsVisible 𝕜 s x y) (hy : y in s)
  证明: hsxy.eq_of_mem_interior (by simpa [hs.interior_eq])

Depends on / 依赖: eq_of_mem_interior, hs.interior_eq, hsxy.eq_of_mem_interior, interior_eq
-/
lemma IsOpen.eq_of_isVisible_of_left_mem (hs : IsOpen s) (hsxy : IsVisible 𝕜 s x y) (hy : y in s) :
    x = y :=
  hsxy.eq_of_mem_interior (by simpa [hs.interior_eq])

end Module

section Real
variable [AddCommGroup V] [Module Real V] {s : Set V} {x y z : V}

/--
lemma `IsVisible.mem_convexHull_isVisible` / 引理 `IsVisible.mem_convexHull_isVisible`

English:
lemma IsVisible.mem_convexHull_isVisible
  statement: (hx : x ∉ convexHull Real s) (hy : y in convexHull Real s)
  proof: by
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i != 0})
    fun i hi => mem_filter.2 ⟨mem_univ _]; rw [left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ => hw₀ _) (by rwa [sum_filter_ne_zero])
    

中文:
引理 IsVisible.mem_convexHull_isVisible
  结论: (hx : x ∉ convexHull 实数 s) (hy : y in convexHull 实数 s)
  证明: by
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i != 0})
    fun i hi => mem_filter.2 ⟨mem_univ _]; rw [left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ => hw₀ _) (by rwa [sum_filter_ne_zero])
    

Depends on / 依赖: Fintype, Fintype.sum_subset, IsVisible, IsVisible.of_convexHull_of_pos, convex_convexHull, left_ne_zero_of_smul, lt_of_ne, mem_convexHull_iff_exists_fintype, mem_filter, mem_univ, of_convexHull_of_pos, subset_convexHull, sum_filter_ne_zero, sum_mem, sum_subset
-/
lemma IsVisible.mem_convexHull_isVisible (hx : x ∉ convexHull Real s) (hy : y in convexHull Real s)
    (hxy : IsVisible Real (convexHull Real s) x y) :
    y in convexHull Real {z in s | IsVisible Real (convexHull Real s) x z} := by
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i != 0})
    fun i hi => mem_filter.2 ⟨mem_univ _]; rw [left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ => hw₀ _) (by rwa [sum_filter_ne_zero])
    fun i hi => subset_convexHull _ _ ⟨ha _, IsVisible.of_convexHull_of_pos (fun _ _ => hw₀ _) hw₁
(by simpa) hx hxy (mem_univ _) (hw₀ _).lt_of_ne' (mem_filter.1 hi).2⟩

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul Real V]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsClosed.exists_wbtw_isVisible` / 引理 `IsClosed.exists_wbtw_isVisible`

English:
lemma IsClosed.exists_wbtw_isVisible
  given: (hs : IsClosed s) (hy : y in s) (x : V)
  proof: by
  let t : Set Real := Ici 0 inter lineMap x y ⁻¹' s
  have ht₁ : 1 in t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : Real := sInf t
  have hδ₁ : δ <= 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 <= δ ∧ lineMap x y δ in s :=
    (isClosed_Ici.inter <| hs.preimage l

中文:
引理 是闭集.存在_wbtw_isVisible
  条件: (hs : 是闭集 s) (hy : y in s) (x : V)
  证明: by
  let t : Set Real := Ici 0 inter lineMap x y ⁻¹' s
  have ht₁ : 1 in t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : Real := sInf t
  have hδ₁ : δ <= 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 <= δ ∧ lineMap x y δ in s :=
    (isClosed_Ici.inter <| hs.preimage l

Depends on / 依赖: BddBelow, bddBelow_Ici, bddBelow_Ici.inter_of_left, csInf_le, csInf_mem, hs.preimage, inter_of_left, isClosed_Ici, isClosed_Ici.inter, lineMap, lineMap_continuous, lt_of_ne, preimage, replace, wbtw_lineMap_iff
-/
lemma IsClosed.exists_wbtw_isVisible (hs : IsClosed s) (hy : y in s) (x : V) :
    exists z in s, Wbtw Real x z y ∧ IsVisible Real s x z := by
  let t : Set Real := Ici 0 inter lineMap x y ⁻¹' s
  have ht₁ : 1 in t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : Real := sInf t
  have hδ₁ : δ <= 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 <= δ ∧ lineMap x y δ in s :=
    (isClosed_Ici.inter <| hs.preimage lineMap_continuous).csInf_mem ⟨1, ht₁⟩ ht
refine ⟨lineMap x y δ, hδ, wbtw_lineMap_iff.2 .inr ⟨hδ₀, hδ₁⟩, ?_⟩
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, -, h⟩
replace hδ₀ : 0 < δ := hδ₀.lt_of_ne' by rintro hδ₀; simp [hδ₀] at h
replace hε₁ : ε < 1 := hε₁.lt_of_ne by rintro rfl; simp at h
  rw [lineMap_lineMap_right] at hε
exact (csInf_le ht ⟨mul_nonneg hε₀ hδ₀.le, hε⟩).not_gt mul_lt_of_lt_one_left hδ₀ hε₁

-- TODO: Once we have cone hulls, the RHS can be strengthened to
-- `coneHull ℝ x {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}`
/--
lemma `IsClosed.convexHull_subset_affineSpan_isVisible` / 引理 `IsClosed.convexHull_subset_affineSpan_isVisible`

English:
lemma IsClosed.convexHull_subset_affineSpan_isVisible
  statement: (hs : IsClosed (convexHull Real s))
  proof: by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isVisible hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
     

中文:
引理 是闭集.convexHull_subset_affineSpan_isVisible
  结论: (hs : 是闭集 (convexHull 实数 s))
  证明: by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isVisible hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
     

Depends on / 依赖: exists_wbtw_isVisible, hs.exists_wbtw_isVisible
-/
lemma IsClosed.convexHull_subset_affineSpan_isVisible (hs : IsClosed (convexHull Real s))
    (hx : x ∉ convexHull Real s) :
    convexHull Real s subseteq affineSpan Real ({x} union {y in s | IsVisible Real (convexHull Real s) x y}) := by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isVisible hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
      hxz.mem_convexHull_isVisible hx hz) (ne_of_mem_of_not_mem hz hx).symm

open Submodule in
/--
lemma `rank_le_card_isVisible` / 引理 `rank_le_card_isVisible`

English:
lemma rank_le_card_isVisible
  given: (hs : IsClosed (convexHull Real s)) (hx : x ∉ convexHull Real s)
  proof: by
  calc
    Module.rank Real (span Real (-x +ᵥ s)) <=
      Module.rank Real (span Real
        (-x +ᵥ affineSpan Real ({x} union {y in s | IsVisible Real (convexHull Real s) x y}) : Set V)) := by
      push_cast
      refine Submodule.rank_mono ?_
      gcongr
exact (subset_convexHull ..).trans h

中文:
引理 rank_le_card_isVisible
  条件: (hs : 是闭集 (convexHull 实数 s)) (hx : x ∉ convexHull 实数 s)
  证明: by
  calc
    Module.rank Real (span Real (-x +ᵥ s)) <=
      Module.rank Real (span Real
        (-x +ᵥ affineSpan Real ({x} union {y in s | IsVisible Real (convexHull Real s) x y}) : Set V)) := by
      push_cast
      refine Submodule.rank_mono ?_
      gcongr
exact (subset_convexHull ..).trans h

Depends on / 依赖: IsVisible, Module, Module.rank, Submodule, Submodule.rank_mono, affineSpan, convexHull, convexHull_subset_affineSpan_isVisible, hs.convexHull_subset_affineSpan_isVisible, rank_mono, subset_convexHull
-/
lemma rank_le_card_isVisible (hs : IsClosed (convexHull Real s)) (hx : x ∉ convexHull Real s) :
    Module.rank Real (span Real (-x +ᵥ s)) <= #{y in s | IsVisible Real (convexHull Real s) x y} := by
  calc
    Module.rank Real (span Real (-x +ᵥ s)) <=
      Module.rank Real (span Real
        (-x +ᵥ affineSpan Real ({x} union {y in s | IsVisible Real (convexHull Real s) x y}) : Set V)) := by
      push_cast
      refine Submodule.rank_mono ?_
      gcongr
exact (subset_convexHull ..).trans hs.convexHull_subset_affineSpan_isVisible hx
    _ = Module.rank Real (span Real (-x +ᵥ {y in s | IsVisible Real (convexHull Real s) x y})) := by
      suffices h :
        -x +ᵥ (affineSpan Real ({x} union {y in s | IsVisible Real (convexHull Real s) x y}) : Set V) =
          span Real (-x +ᵥ {y in s | IsVisible Real (convexHull Real s) x y}) by
        rw [AffineSubspace.coe_pointwise_vadd]; rw [h]; rw [span_span]
      simp [← AffineSubspace.coe_pointwise_vadd, AffineSubspace.pointwise_vadd_span,
        vadd_set_insert, affineSpan_insert_zero]
    _ <= #(-x +ᵥ {y in s | IsVisible Real (convexHull Real s) x y}) := rank_span_le _
    _ = #{y in s | IsVisible Real (convexHull Real s) x y} := by simp

end Real
