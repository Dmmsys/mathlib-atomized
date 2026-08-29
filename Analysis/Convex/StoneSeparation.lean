/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Join

/-!
# Stone's separation theorem

This file proves Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

In locally convex real topological vector spaces, the Hahn-Banach separation theorems provide
stronger statements: one may find a separating hyperplane, instead of merely a convex set whose
complement is convex.
-/

public section


open Set

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/--
theorem `not_disjoint_segment_convexHull_triple` / 定理 `not_disjoint_segment_convexHull_triple`

English:
theorem not_disjoint_segment_convexHull_triple
  statement: {p q u v x y z : E} (hz : z in segment 𝕜 x y)
  proof: by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz
    rw [zero_smul]; rw [zero_add]; rw [habz]; rw [one_smul]
    refine ⟨v, by apply right_mem_segment, segment_subset_convexHull ?_ ?_ hv⟩ <;> simp
  obtain ⟨av, bv, 

中文:
定理 not_disjoint_segment_convexHull_triple
  结论: {p q u v x y z : E} (hz : z in segment 𝕜 x y)
  证明: by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz
    rw [zero_smul]; rw [zero_add]; rw [habz]; rw [one_smul]
    refine ⟨v, by apply right_mem_segment, segment_subset_convexHull ?_ ?_ hv⟩ <;> simp
  obtain ⟨av, bv, 

Depends on / 依赖: eq_or_lt, hav.eq_or_lt, haz.eq_or_lt, not_disjoint_iff, one_smul, right_mem_segment, segment_subset_convexHull, subset_convexHull, zero_add, zero_smul
-/
theorem not_disjoint_segment_convexHull_triple {p q u v x y z : E} (hz : z in segment 𝕜 x y)
    (hu : u in segment 𝕜 x p) (hv : v in segment 𝕜 y q) :
    ¬Disjoint (segment 𝕜 u v) (convexHull 𝕜 {p, q, z}) := by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz
    rw [zero_smul]; rw [zero_add]; rw [habz]; rw [one_smul]
    refine ⟨v, by apply right_mem_segment, segment_subset_convexHull ?_ ?_ hv⟩ <;> simp
  obtain ⟨av, bv, hav, hbv, habv, rfl⟩ := hv
  obtain rfl | hav' := hav.eq_or_lt
  · rw [zero_add] at habv
    rw [zero_smul]; rw [zero_add]; rw [habv]; rw [one_smul]
exact ⟨q, right_mem_segment _ _ _, subset_convexHull _ _ by simp⟩
  obtain ⟨au, bu, hau, hbu, habu, rfl⟩ := hu
  have hab : 0 < az * av + bz * au := by positivity
  refine ⟨(az * av / (az * av + bz * au)) • (au • x + bu • p) +
    (bz * au / (az * av + bz * au)) • (av • y + bv • q), ⟨_, _, ?_, ?_, ?_, rfl⟩, ?_⟩
  · positivity
  · positivity
  · rw [← add_div, div_self]; positivity
  classical
    let w : Fin 3 -> 𝕜 := ![az * av * bu, bz * au * bv, au * av]
    let z : Fin 3 -> E := ![p, q, az • x + bz • y]
    have hw₀ : forall i, 0 <= w i := by
      rintro i
      fin_cases i
      · exact mul_nonneg (mul_nonneg haz hav) hbu
      · exact mul_nonneg (mul_nonneg hbz hau) hbv
      · exact mul_nonneg hau hav
    have hw : ∑ i, w i = az * av + bz * au := by
      trans az * av * bu + (bz * au * bv + au * av)
      · simp [w, Fin.sum_univ_succ]
      linear_combination (au * bv - 1 * au) * habz + (-(1 * az * au) + au) * habv + az * av * habu
    have hz : forall i, z i in ({p, q, az • x + bz • y} : Set E) := fun i => by fin_cases i <;> simp [z]
    convert!
      (Finset.centerMass_mem_convexHull (Finset.univ : Finset (Fin 3)) (fun i _ => hw₀ i)
          (by rwa [hw]) fun i _ => hz i :
        Finset.univ.centerMass w z in _)
    rw [Finset.centerMass]; rw [hw]
    trans (az * av + bz * au)⁻¹ •
      ((az * av * bu) • p + ((bz * au * bv) • q + (au * av) • (az • x + bz • y)))
    · module
    congr 3
    simp [w, z]

/--
theorem `exists_convex_convex_compl_subset` / 定理 `exists_convex_convex_compl_subset`

English:
theorem exists_convex_convex_compl_subset
  given: (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t)
  proof: by
  let S : Set (Set E) := { C | Convex 𝕜 C ∧ Disjoint C t }
  obtain ⟨C, hsC, hmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨_, _⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directedOn.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s 

中文:
定理 存在_convex_convex_compl_subset
  条件: (hs : 凸 𝕜 s) (ht : 凸 𝕜 t) (hst : Disjoint s t)
  证明: by
  let S : Set (Set E) := { C | Convex 𝕜 C ∧ Disjoint C t }
  obtain ⟨C, hsC, hmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨_, _⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directedOn.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s 

Depends on / 依赖: Convex, Disjoint, Nonempty, convex_iff_segment_subset, convex_sUnion, directedOn, disjoint_sUnion_left, hc.directedOn.convex_sUnion, hmax.prop, segment, subset_compl_left, subset_sUnion_of_mem, zorn_subset_nonempty
-/
theorem exists_convex_convex_compl_subset (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    exists C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s subseteq C ∧ t subseteq Cᶜ := by
  let S : Set (Set E) := { C | Convex 𝕜 C ∧ Disjoint C t }
  obtain ⟨C, hsC, hmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨_, _⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directedOn.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s => subset_sUnion_of_mem⟩)
      s ⟨hs, hst⟩
  obtain hC : _ ∧ _ := hmax.prop
  refine
    ⟨C, hC.1, convex_iff_segment_subset.2 fun x hx y hy z hz hzC => ?_, hsC, hC.2.subset_compl_left⟩
  suffices h : forall c in Cᶜ, exists a in C, (segment 𝕜 c a inter t).Nonempty by
    obtain ⟨p, hp, u, hu, hut⟩ := h x hx
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy
    refine
      not_disjoint_segment_convexHull_triple hz hu hv
        (hC.2.symm.mono (ht.segment_subset hut hvt) <| convexHull_min ?_ hC.1)
    simp [insert_subset_iff, hp, hq, singleton_subset_iff.2 hzC]
  rintro c hc
  by_contra! h
  suffices h : Disjoint (convexHull 𝕜 (insert c C)) t by
    rw [hmax.eq_of_subset ⟨convex_convexHull _ _]; rw [h⟩ <|
(subset_insert ..).trans subset_convexHull ..] at hc
    exact hc (subset_convexHull _ _ <| mem_insert _ _)
  rw [convexHull_insert ⟨z]; rw [hzC⟩]; rw [convexJoin_singleton_left]
  refine disjoint_iUnion₂_left.2 fun a ha => disjoint_iff_inter_eq_empty.2 (h a ?_)
  rwa [← hC.1.convexHull_eq]
