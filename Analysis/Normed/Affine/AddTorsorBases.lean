/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

* `continuous_barycentric_coord`
* `isOpenMap_barycentric_coord`
* `AffineBasis.interior_convexHull`
* `IsOpen.exists_subset_affineIndependent_span_eq_top`
* `interior_convexHull_nonempty_iff_affineSpan_eq_top`
-/

public section

assert_not_exists HasFDerivAt

section Barycentric

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]

/--
theorem `isOpenMap_barycentric_coord` / 定理 `isOpenMap_barycentric_coord`

English:
theorem isOpenMap_barycentric_coord
  given: [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι)
  proof: AffineMap.isOpenMap_linear_iff.mp
(b.coord i).linear.isOpenMap_of_finiteDimensional
      (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

中文:
定理 isOpenMap_barycentric_coord
  条件: [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι)
  证明: AffineMap.isOpenMap_linear_iff.mp
(b.coord i).linear.isOpenMap_of_finiteDimensional
      (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

Depends on / 依赖: AffineMap, AffineMap.isOpenMap_linear_iff.mp, b.coord, b.surjective_coord, isOpenMap_linear_iff, isOpenMap_of_finiteDimensional, linear, linear.isOpenMap_of_finiteDimensional, linear_surjective_iff, linear_surjective_iff.mpr, surjective_coord
-/
theorem isOpenMap_barycentric_coord [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι) :
    IsOpenMap (b.coord i) :=
AffineMap.isOpenMap_linear_iff.mp
(b.coord i).linear.isOpenMap_of_finiteDimensional
      (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

variable [FiniteDimensional 𝕜 E] (b : AffineBasis ι 𝕜 P)

@[continuity]
/--
theorem `continuous_barycentric_coord` / 定理 `continuous_barycentric_coord`

English:
theorem continuous_barycentric_coord
  given: (i : ι)
  statement: Continuous (b.coord i)
  proof: (b.coord i).continuous_of_finiteDimensional

中文:
定理 continuous_barycentric_coord
  条件: (i : ι)
  结论: Continuous (b.coord i)
  证明: (b.coord i).continuous_of_finiteDimensional

Depends on / 依赖: b.coord, continuous_of_finiteDimensional
-/
theorem continuous_barycentric_coord (i : ι) : Continuous (b.coord i) :=
  (b.coord i).continuous_of_finiteDimensional

end Barycentric

open Set

/--
theorem `AffineBasis.interior_convexHull` / 定理 `AffineBasis.interior_convexHull`

English:
theorem AffineBasis.interior_convexHull
  statement: {ι E : Type*} [Finite ι] [NormedAddCommGroup E]
  proof: by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    have : range b = univ :=
      AffineSubspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot
    simp [this]
  · -- The positive-dimensional case.
    have : FiniteDimensional Real E := b.finiteDimensiona

中文:
定理 AffineBasis.interior_convexHull
  结论: {ι E : 类型} [Finite ι] [NormedAddCommGroup E]
  证明: by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    have : range b = univ :=
      AffineSubspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot
    simp [this]
  · -- The positive-dimensional case.
    have : FiniteDimensional Real E := b.finiteDimensiona

Depends on / 依赖: AffineSubspace, AffineSubspace.eq_univ_of_subsingleton_span_eq_top, FiniteDimensional, IsOpenMap, IsOpenMap.preimage_interior_eq_interior_preimag, b.convexHull_eq_nonneg_coord, b.coord, b.finiteDimensional, b.tot, convexHull, convexHull_eq_nonneg_coord, dimensional, eq_univ_of_subsingleton_span_eq_top, finiteDimensional, interior_iInter_of_finite, ofPred_forall, positive, preimage_interior_eq_interior_preimag, subsingleton_or_nontrivial, subsingleton_range
-/
theorem AffineBasis.interior_convexHull {ι E : Type*} [Finite ι] [NormedAddCommGroup E]
    [NormedSpace Real E] (b : AffineBasis ι Real E) :
    interior (convexHull Real (range b)) = {x | forall i, 0 < b.coord i x} := by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    have : range b = univ :=
      AffineSubspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot
    simp [this]
  · -- The positive-dimensional case.
    have : FiniteDimensional Real E := b.finiteDimensional
    have : convexHull Real (range b) = ⋂ i, b.coord i ⁻¹' Ici 0 := by
      rw [b.convexHull_eq_nonneg_coord]; rw [ofPred_forall]; rfl
    ext
    simp only [this, interior_iInter_of_finite, ←
      IsOpenMap.preimage_interior_eq_interior_preimage (isOpenMap_barycentric_coord b _)
        (continuous_barycentric_coord b _),
      interior_Ici, mem_iInter, mem_ofPred_eq, mem_Ioi, mem_preimage]

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsOpen.exists_between_affineIndependent_span_eq_top` / 定理 `IsOpen.exists_between_affineIndependent_span_eq_top`

English:
theorem IsOpen.exists_between_affineIndependent_span_eq_top
  statement: {s u : Set P} (hu : IsOpen u)
  proof: by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, ε0, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds <| hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affineIndependent_affineSpan_eq_top h
  let f : P -> P := fun y => lineMap q y (ε / dist y q)
  have hf : forall y, f y in u := by
    refin

中文:
定理 IsOpen.exists_between_affineIndependent_span_eq_top
  结论: {s u : Set P} (hu : IsOpen u)
  证明: by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, ε0, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds <| hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affineIndependent_affineSpan_eq_top h
  let f : P -> P := fun y => lineMap q y (ε / dist y q)
  have hf : forall y, f y in u := by
    refin

Depends on / 依赖: Metric, Metric.mem_closedBall, Metric.nhds_basis_closedBall.mem_iff, Real.norm_eq_abs, abs_div, abs_of, abs_of_pos, dist_eq_norm_vsub, dist_vadd_left, exists_subset_affineIndependent_affineSpan_eq_top, hu.mem_nhds, lineMap, lineMap_apply, mem_closedBall, mem_iff, mem_nhds, nhds_basis_closedBall, norm_eq_abs, norm_smul
-/
theorem IsOpen.exists_between_affineIndependent_span_eq_top {s u : Set P} (hu : IsOpen u)
    (hsu : s subseteq u) (hne : s.Nonempty) (h : AffineIndependent Real ((↑) : s -> P)) :
    exists t : Set P, s subseteq t ∧ t subseteq u ∧ AffineIndependent Real ((↑) : t -> P) ∧ affineSpan Real t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, ε0, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds <| hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affineIndependent_affineSpan_eq_top h
  let f : P -> P := fun y => lineMap q y (ε / dist y q)
  have hf : forall y, f y in u := by
    refine fun y => hεu ?_
    simp only [f]
    rw [Metric.mem_closedBall]; rw [lineMap_apply]; rw [dist_vadd_left]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [dist_eq_norm_vsub V y q]; rw [abs_div]; rw [abs_of_pos ε0]; rw [abs_of_nonneg (norm_nonneg _)]; rw [div_mul_comm]
    exact mul_le_of_le_one_left ε0.le (div_self_le_one _)
  have hεyq : forall y ∉ s, ε / dist y q != 0 := fun y hy =>
    div_ne_zero ε0.ne' (dist_ne_zero.2 (ne_of_mem_of_not_mem hq hy).symm)
  classical
  let w : t -> Realˣ := fun p => if hp : (p : P) in s then 1 else Units.mk0 _ (hεyq (↑p) hp)
  refine ⟨Set.range fun p : t => lineMap q p (w p : Real), ?_, ?_, ?_, ?_⟩
  · intro p hp; use ⟨p, ht₁ hp⟩; simp [w, hp]
  · rintro y ⟨⟨p, hp⟩, rfl⟩
    by_cases hps : p in s <;>
    simp only [w, hps, lineMap_apply_one, Units.val_mk0, dif_neg, dif_pos, not_false_iff,
      Units.val_one] <;>
    [exact hsu hps; exact hf p]
  · exact (ht₂.units_lineMap ⟨q, ht₁ hq⟩ w).range
  · rw [affineSpan_eq_affineSpan_lineMap_units (ht₁ hq) w, ht₃]

/--
theorem `IsOpen.exists_subset_affineIndependent_span_eq_top` / 定理 `IsOpen.exists_subset_affineIndependent_span_eq_top`

English:
theorem IsOpen.exists_subset_affineIndependent_span_eq_top
  statement: {u : Set P} (hu : IsOpen u)
  proof: by
  rcases hne with ⟨x, hx⟩
  rcases hu.exists_between_affineIndependent_span_eq_top (singleton_subset_iff.mpr hx)
    (singleton_nonempty _) (affineIndependent_of_subsingleton _ _) with ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩

中文:
定理 IsOpen.exists_subset_affineIndependent_span_eq_top
  结论: {u : Set P} (hu : IsOpen u)
  证明: by
  rcases hne with ⟨x, hx⟩
  rcases hu.exists_between_affineIndependent_span_eq_top (singleton_subset_iff.mpr hx)
    (singleton_nonempty _) (affineIndependent_of_subsingleton _ _) with ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩

Depends on / 依赖: affineIndependent_of_subsingleton, exists_between_affineIndependent_span_eq_top, hu.exists_between_affineIndependent_span_eq_top, singleton_nonempty, singleton_subset_iff, singleton_subset_iff.mpr
-/
theorem IsOpen.exists_subset_affineIndependent_span_eq_top {u : Set P} (hu : IsOpen u)
    (hne : u.Nonempty) : exists s subseteq u, AffineIndependent Real ((↑) : s -> P) ∧ affineSpan Real s = ⊤ := by
  rcases hne with ⟨x, hx⟩
  rcases hu.exists_between_affineIndependent_span_eq_top (singleton_subset_iff.mpr hx)
    (singleton_nonempty _) (affineIndependent_of_subsingleton _ _) with ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩

/--
theorem `IsOpen.affineSpan_eq_top` / 定理 `IsOpen.affineSpan_eq_top`

English:
theorem IsOpen.affineSpan_eq_top
  given: {u : Set P} (hu : IsOpen u) (hne : u.Nonempty)
  proof: let ⟨_, hsu, _, hs'⟩ := hu.exists_subset_affineIndependent_span_eq_top hne
top_unique hs' ▸ affineSpan_mono _ hsu

中文:
定理 IsOpen.affineSpan_eq_top
  条件: {u : Set P} (hu : IsOpen u) (hne : u.Nonempty)
  证明: let ⟨_, hsu, _, hs'⟩ := hu.exists_subset_affineIndependent_span_eq_top hne
top_unique hs' ▸ affineSpan_mono _ hsu

Depends on / 依赖: affineSpan_mono, exists_subset_affineIndependent_span_eq_top, hu.exists_subset_affineIndependent_span_eq_top, top_unique
-/
theorem IsOpen.affineSpan_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) :
    affineSpan Real u = ⊤ :=
  let ⟨_, hsu, _, hs'⟩ := hu.exists_subset_affineIndependent_span_eq_top hne
top_unique hs' ▸ affineSpan_mono _ hsu

/--
theorem `affineSpan_eq_top_of_nonempty_interior` / 定理 `affineSpan_eq_top_of_nonempty_interior`

English:
theorem affineSpan_eq_top_of_nonempty_interior
  statement: {s : Set V}
  proof: top_unique isOpen_interior.affineSpan_eq_top hs ▸
    (affineSpan_mono _ interior_subset).trans_eq (affineSpan_convexHull _)

中文:
定理 affineSpan_eq_top_of_nonempty_interior
  结论: {s : Set V}
  证明: top_unique isOpen_interior.affineSpan_eq_top hs ▸
    (affineSpan_mono _ interior_subset).trans_eq (affineSpan_convexHull _)

Depends on / 依赖: affineSpan_convexHull, affineSpan_eq_top, affineSpan_mono, interior_subset, isOpen_interior, isOpen_interior.affineSpan_eq_top, top_unique, trans_eq
-/
theorem affineSpan_eq_top_of_nonempty_interior {s : Set V}
    (hs : (interior <| convexHull Real s).Nonempty) : affineSpan Real s = ⊤ :=
top_unique isOpen_interior.affineSpan_eq_top hs ▸
    (affineSpan_mono _ interior_subset).trans_eq (affineSpan_convexHull _)

/--
theorem `AffineBasis.centroid_mem_interior_convexHull` / 定理 `AffineBasis.centroid_mem_interior_convexHull`

English:
theorem AffineBasis.centroid_mem_interior_convexHull
  given: {ι} [Fintype ι] (b : AffineBasis ι Real V)
  proof: by
  have := b.nonempty
  simp only [b.interior_convexHull, mem_ofPred_eq, b.coord_apply_centroid (Finset.mem_univ _),
    inv_pos, Nat.cast_pos, Finset.card_pos, Finset.univ_nonempty, forall_true_iff]

中文:
定理 AffineBasis.centroid_mem_interior_convexHull
  条件: {ι} [Fintype ι] (b : AffineBasis ι 实数 V)
  证明: by
  have := b.nonempty
  simp only [b.interior_convexHull, mem_ofPred_eq, b.coord_apply_centroid (Finset.mem_univ _),
    inv_pos, Nat.cast_pos, Finset.card_pos, Finset.univ_nonempty, forall_true_iff]

Depends on / 依赖: Finset, Finset.card_pos, Finset.mem_univ, Finset.univ_nonempty, Nat.cast_pos, b.coord_apply_centroid, b.interior_convexHull, b.nonempty, card_pos, cast_pos, coord_apply_centroid, forall_true_iff, interior_convexHull, inv_pos, mem_ofPred_eq, mem_univ, nonempty, univ_nonempty
-/
theorem AffineBasis.centroid_mem_interior_convexHull {ι} [Fintype ι] (b : AffineBasis ι Real V) :
    Finset.univ.centroid Real b in interior (convexHull Real (range b)) := by
  have := b.nonempty
  simp only [b.interior_convexHull, mem_ofPred_eq, b.coord_apply_centroid (Finset.mem_univ _),
    inv_pos, Nat.cast_pos, Finset.card_pos, Finset.univ_nonempty, forall_true_iff]

/--
theorem `interior_convexHull_nonempty_iff_affineSpan_eq_top` / 定理 `interior_convexHull_nonempty_iff_affineSpan_eq_top`

English:
theorem interior_convexHull_nonempty_iff_affineSpan_eq_top
  given: [FiniteDimensional Real V] {s : Set V}
  proof: by
  refine ⟨affineSpan_eq_top_of_nonempty_interior, fun h => ?_⟩
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
  suffices (interior (convexHull Real (range b))).Nonempty by
    rw [hb]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq] at this
    refine this.mono (by gcongr)
  

中文:
定理 interior_convexHull_nonempty_iff_affineSpan_eq_top
  条件: [FiniteDimensional 实数 V] {s : Set V}
  证明: by
  refine ⟨affineSpan_eq_top_of_nonempty_interior, fun h => ?_⟩
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
  suffices (interior (convexHull Real (range b))).Nonempty by
    rw [hb]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq] at this
    refine this.mono (by gcongr)
  

Depends on / 依赖: AffineBasis, AffineBasis.exists_affine_subbasis, Finset, Nonempty, Subtype, Subtype.range_coe_subtype, affineSpan_eq_top_of_nonempty_interior, b.centroid_mem_interior_convexHull, b.finite_set, centroid_mem_interior_convexHull, convexHull, exists_affine_subbasis, finite_set, interior, ofPred_mem_eq, range_coe_subtype, this.mono
-/
theorem interior_convexHull_nonempty_iff_affineSpan_eq_top [FiniteDimensional Real V] {s : Set V} :
    (interior (convexHull Real s)).Nonempty ↔ affineSpan Real s = ⊤ := by
  refine ⟨affineSpan_eq_top_of_nonempty_interior, fun h => ?_⟩
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
  suffices (interior (convexHull Real (range b))).Nonempty by
    rw [hb]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq] at this
    refine this.mono (by gcongr)
  lift t to Finset V using b.finite_set
  exact ⟨_, b.centroid_mem_interior_convexHull⟩

/--
theorem `Convex.interior_nonempty_iff_affineSpan_eq_top` / 定理 `Convex.interior_nonempty_iff_affineSpan_eq_top`

English:
theorem Convex.interior_nonempty_iff_affineSpan_eq_top
  statement: [FiniteDimensional Real V] {s : Set V}
  proof: by
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top]; rw [hs.convexHull_eq]

中文:
定理 Convex.interior_nonempty_iff_affineSpan_eq_top
  结论: [FiniteDimensional 实数 V] {s : Set V}
  证明: by
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top]; rw [hs.convexHull_eq]

Depends on / 依赖: convexHull_eq, hs.convexHull_eq, interior_convexHull_nonempty_iff_affineSpan_eq_top
-/
theorem Convex.interior_nonempty_iff_affineSpan_eq_top [FiniteDimensional Real V] {s : Set V}
    (hs : Convex Real s) : (interior s).Nonempty ↔ affineSpan Real s = ⊤ := by
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top]; rw [hs.convexHull_eq]
