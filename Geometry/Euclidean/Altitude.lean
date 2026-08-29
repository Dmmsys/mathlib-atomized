/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Affine

/-!
# Altitudes of a simplex

This file defines the altitudes of a simplex and their feet.

## Main definitions

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `altitudeFoot` is the orthogonal projection of a vertex of a simplex onto the opposite face.

* `height` is the distance between a vertex of a simplex and its `altitudeFoot`.

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>

-/

@[expose] public section

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

/--
Definition of `altitude` / `altitude` 的定义

English:
definition altitude
  signature: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  body: mk' (s.points i) (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan Real (Set.range s.points)

中文:
定义 altitude
  签名: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  定义体: mk' (s.points i) (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan Real (Set.range s.points)

Depends on / 依赖: Set.range, affineSpan, points, s.points
-/
def altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : AffineSubspace Real P :=
  mk' (s.points i) (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan Real (Set.range s.points)

/--
theorem `altitude_def` / 定理 `altitude_def`

English:
theorem altitude_def
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: rfl

中文:
定理 altitude_def
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: rfl
-/
theorem altitude_def {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.altitude i =
      mk' (s.points i) (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ ⊓
        affineSpan Real (Set.range s.points) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `altitude_reindex` / 引理 `altitude_reindex`

English:
lemma altitude_reindex
  given: {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  ext i
  simp_rw [altitude, reindex_points, Set.image_comp, Equiv.image_compl]
  simp [altitude]

中文:
引理 altitude_reindex
  条件: {m n : 自然数} (s : Simplex 实数 P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  证明: by
  ext i
  simp_rw [altitude, reindex_points, Set.image_comp, Equiv.image_compl]
  simp [altitude]
-/
@[simp] lemma altitude_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).altitude = s.altitude ∘ e.symm := by
  ext i
  simp_rw [altitude, reindex_points, Set.image_comp, Equiv.image_compl]
  simp [altitude]

/--
theorem `mem_altitude` / 定理 `mem_altitude`

English:
theorem mem_altitude
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan Real (Set.mem_range_self _)⟩

中文:
定理 mem_altitude
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan Real (Set.mem_range_self _)⟩

Depends on / 依赖: Set.mem_range_self, mem_affineSpan, mem_inf_iff, mem_range_self, self_mem_mk
-/
theorem mem_altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.points i in s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan Real (Set.mem_range_self _)⟩

/--
theorem `direction_altitude` / 定理 `direction_altitude`

English:
theorem direction_altitude
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [altitude_def]; rw [direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan Real (Set.mem_range_self _))]; rw [direction_mk']; rw [direction_affineSpan]; rw [direction_affineSpan]

中文:
定理 direction_altitude
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  rw [altitude_def]; rw [direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan Real (Set.mem_range_self _))]; rw [direction_mk']; rw [direction_affineSpan]; rw [direction_affineSpan]

Depends on / 依赖: Set.mem_range_self, altitude_def, direction_affineSpan, direction_inf_of_mem, direction_mk, mem_affineSpan, mem_range_self, points, s.points, self_mem_mk
-/
theorem direction_altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    (s.altitude i).direction =
      (vectorSpan Real (s.points '' {i}ᶜ))ᗮ ⊓ vectorSpan Real (Set.range s.points) := by
  rw [altitude_def]; rw [direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan Real (Set.mem_range_self _))]; rw [direction_mk']; rw [direction_affineSpan]; rw [direction_affineSpan]

/--
theorem `vectorSpan_isOrtho_altitude_direction` / 定理 `vectorSpan_isOrtho_altitude_direction`

English:
theorem vectorSpan_isOrtho_altitude_direction
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left

中文:
定理 vectorSpan_isOrtho_altitude_direction
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left

Depends on / 依赖: Submodule, Submodule.isOrtho_orthogonal_right, direction_altitude, inf_le_left, isOrtho_orthogonal_right, mono_right
-/
theorem vectorSpan_isOrtho_altitude_direction {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    vectorSpan Real (s.points '' {i}ᶜ) ⟂ (s.altitude i).direction := by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left

/--
lemma `altitude_map` / 引理 `altitude_map`

English:
lemma altitude_map
  given: {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1))
  proof: by
  refine (eq_iff_direction_eq_of_mem (p := f (s.points i)) ?_ ?_).mpr ?_
  · exact (s.map f.toAffineMap f.injective).mem_altitude i
  · exact mem_map_of_mem f.toAffineMap (s.mem_altitude i)
  have hf : Function.Injective f.linear := f.linearIsometry.injective
  rw [map_direction]; rw [direction_a

中文:
引理 altitude_map
  条件: {n : 自然数} (s : Simplex 实数 P n) (f : P ->ᵃⁱ[实数] P₂) (i : Fin (n + 1))
  证明: by
  refine (eq_iff_direction_eq_of_mem (p := f (s.points i)) ?_ ?_).mpr ?_
  · exact (s.map f.toAffineMap f.injective).mem_altitude i
  · exact mem_map_of_mem f.toAffineMap (s.mem_altitude i)
  have hf : Function.Injective f.linear := f.linearIsometry.injective
  rw [map_direction]; rw [direction_a

Depends on / 依赖: AffineIsometry, AffineIsometry.linear_eq_linearIsometry, Function, Function.Injective, Injective, Submodule, Submodule.map_inf, Submodule.map_orthogonal, direction_altitude, eq_iff_direction_eq_of_mem, f.injective, f.linear, f.linearIsometry.injective, f.toAffineMap, injective, linear, linearIsometry, linear_eq_linearIsometry, map_direction, map_inf
-/
lemma altitude_map {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).altitude i = (s.altitude i).map f.toAffineMap := by
  refine (eq_iff_direction_eq_of_mem (p := f (s.points i)) ?_ ?_).mpr ?_
  · exact (s.map f.toAffineMap f.injective).mem_altitude i
  · exact mem_map_of_mem f.toAffineMap (s.mem_altitude i)
  have hf : Function.Injective f.linear := f.linearIsometry.injective
  rw [map_direction]; rw [direction_altitude]; rw [direction_altitude]; rw [Submodule.map_inf _ hf]; rw [AffineIsometry.linear_eq_linearIsometry]; rw [Submodule.map_orthogonal]; rw [← AffineIsometry.linear_eq_linearIsometry]; rw [map_points]; rw [Set.range_comp]; rw [Set.image_comp]; rw [← AffineMap.map_vectorSpan]; rw [inf_assoc]; rw [← Submodule.map_top]; rw [← Submodule.map_inf _ hf]; rw [top_inf_eq]; rw [← AffineMap.map_vectorSpan]

/--
lemma `map_altitude_restrict` / 引理 `map_altitude_restrict`

English:
lemma map_altitude_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).altitude i).map S.subtype = s.altitude i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitude_map S.subtypeₐᵢ i

中文:
引理 map_altitude_restrict
  结论: {n : 自然数} (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).altitude i).map S.subtype = s.altitude i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitude_map S.subtypeₐᵢ i
-/
@[simp] lemma map_altitude_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).altitude i).map S.subtype = s.altitude i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitude_map S.subtypeₐᵢ i

/--
lemma `altitude_restrict_eq_comap_subtype` / 引理 `altitude_restrict_eq_comap_subtype`

English:
lemma altitude_restrict_eq_comap_subtype
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitude i = (s.altitude i).comap S.subtype := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← s.map_altitude_restrict S hS]; rw [comap_map_eq_of_injective S.subtype_injective]

中文:
引理 altitude_restrict_eq_comap_subtype
  结论: {n : 自然数} (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitude i = (s.altitude i).comap S.subtype := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← s.map_altitude_restrict S hS]; rw [comap_map_eq_of_injective S.subtype_injective]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma altitude_restrict_eq_comap_subtype {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitude i = (s.altitude i).comap S.subtype := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← s.map_altitude_restrict S hS]; rw [comap_map_eq_of_injective S.subtype_injective]

open Module

/--
Instance `finiteDimensional_direction_altitude` / 实例 `finiteDimensional_direction_altitude`

English:
instance finiteDimensional_direction_altitude
  signature: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  body: by
  rw [direction_altitude]
  infer_instance

中文:
实例 finiteDimensional_direction_altitude
  签名: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  定义体: by
  rw [direction_altitude]
  infer_instance

Depends on / 依赖: direction_altitude, infer_instance
-/
instance finiteDimensional_direction_altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    FiniteDimensional Real (s.altitude i).direction := by
  rw [direction_altitude]
  infer_instance

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
/--
theorem `finrank_direction_altitude` / 定理 `finrank_direction_altitude`

English:
theorem finrank_direction_altitude
  given: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono Real (Set.image_subset_range s.points {i}ᶜ))
  have hn : (n - 1) + 1 = n := by
    have := NeZero.ne n
    cases n <;> lia
  have hc : #({i}ᶜ) = (n - 1) + 1 := by
    rw [card_compl]; rw [card_

中文:
定理 finrank_direction_altitude
  条件: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono Real (Set.image_subset_range s.points {i}ᶜ))
  have hn : (n - 1) + 1 = n := by
    have := NeZero.ne n
    cases n <;> lia
  have hc : #({i}ᶜ) = (n - 1) + 1 := by
    rw [card_compl]; rw [card_

Depends on / 依赖: Finset, Finset.coe_singleton, Fintype, Fintype.card_fin, NeZero, NeZero.ne, Set.image_subset_range, Submodule, Submodule.finrank_add_inf_finrank_orthogonal, _root_, _root_.trans, add_left_cancel, add_tsub_cancel_right, card_compl, card_fin, card_singleton, classical, coe_singleton, direction_altitude, finrank_add_inf_finrank_orthogonal
-/
theorem finrank_direction_altitude {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    finrank Real (s.altitude i).direction = 1 := by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono Real (Set.image_subset_range s.points {i}ᶜ))
  have hn : (n - 1) + 1 = n := by
    have := NeZero.ne n
    cases n <;> lia
  have hc : #({i}ᶜ) = (n - 1) + 1 := by
    rw [card_compl]; rw [card_singleton]; rw [Fintype.card_fin]; rw [hn]; rw [add_tsub_cancel_right]
  refine add_left_cancel (_root_.trans h ?_)
  classical
  rw [s.independent.finrank_vectorSpan (Fintype.card_fin _)]; rw [← Finset.coe_singleton]; rw [← Finset.coe_compl]; rw [← Finset.coe_image]; rw [s.independent.finrank_vectorSpan_image_finset hc]; rw [hn]

/--
theorem `affineSpan_pair_eq_altitude_iff` / 定理 `affineSpan_pair_eq_altitude_iff`

English:
theorem affineSpan_pair_eq_altitude_iff
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan Real (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _)]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan Real (Set.mem_range_self i)) p]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [direction_affineSpan]

中文:
定理 affineSpan_pair_eq_altitude_iff
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan Real (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _)]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan Real (Set.mem_range_self i)) p]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [direction_affineSpan]

Depends on / 依赖: Set.mem_insert_of_mem, Set.mem_range_self, Set.mem_singleton, Set.pair_eq_singleton, altitude, direction, direction_affineSpan, eq_iff_direction_eq_of_mem, finrank, finrank_bot, mem_affineSpan, mem_altitude, mem_insert_of_mem, mem_range_self, mem_singleton, pair_eq_singleton, s.altitude, s.mem_altitude, vectorSpan_singleton, vsub_right_mem_direction_iff_mem
-/
theorem affineSpan_pair_eq_altitude_iff {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
    (p : P) :
    line[Real, p, s.points i] = s.altitude i ↔
      p != s.points i ∧
        p in affineSpan Real (Set.range s.points) ∧
          p -ᵥ s.points i in (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ := by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan Real (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _)]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan Real (Set.mem_range_self i)) p]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [direction_affineSpan]
  constructor
  · intro h
    constructor
    · intro heq
      rw [heq]; rw [Set.pair_eq_singleton]; rw [vectorSpan_singleton] at h
      have hd : finrank Real (s.altitude i).direction = 0 := by rw [← h, finrank_bot]
      simp at hd
    · rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude, ← h]
      exact
        vsub_mem_vectorSpan Real (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hne, h⟩
    rw [← Submodule.mem_inf]; rw [_root_.inf_comm]; rw [← direction_altitude] at h
    rw [vectorSpan_eq_span_vsub_set_left_ne Real (Set.mem_insert _ _)]; rw [Set.insert_sdiff_of_mem _ (Set.mem_singleton _)]; rw [Set.sdiff_singleton_eq_self fun h => hne (Set.mem_singleton_iff.1 h)]; rw [Set.image_singleton]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      simpa using h
    · rw [finrank_direction_altitude, finrank_span_set_eq_card]
      · simp
· exact .singleton by simpa using hne

/--
Definition of `altitudeFoot` / `altitudeFoot` 的定义

English:
definition altitudeFoot
  signature: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  body: (s.faceOpposite i).orthogonalProjectionSpan (s.points i)

中文:
定义 altitudeFoot
  签名: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  定义体: (s.faceOpposite i).orthogonalProjectionSpan (s.points i)

Depends on / 依赖: faceOpposite, orthogonalProjectionSpan, points, s.faceOpposite, s.points
-/
def altitudeFoot {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).orthogonalProjectionSpan (s.points i)

/--
lemma `altitudeFoot_reindex` / 引理 `altitudeFoot_reindex`

English:
lemma altitudeFoot_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n] (s : Simplex Real P n)
  proof: by
  ext i
  simp only [altitudeFoot, reindex_points, Function.comp_apply]
  exact orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex e i) rfl

中文:
引理 altitudeFoot_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n] (s : Simplex 实数 P n)
  证明: by
  ext i
  simp only [altitudeFoot, reindex_points, Function.comp_apply]
  exact orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex e i) rfl
-/
@[simp] lemma altitudeFoot_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex Real P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).altitudeFoot = s.altitudeFoot ∘ e.symm := by
  ext i
  simp only [altitudeFoot, reindex_points, Function.comp_apply]
  exact orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex e i) rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `altitudeFoot_map` / 引理 `altitudeFoot_map`

English:
lemma altitudeFoot_map
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  simp [altitudeFoot, ← orthogonalProjectionSpan_map]

中文:
引理 altitudeFoot_map
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  simp [altitudeFoot, ← orthogonalProjectionSpan_map]
-/
@[simp] lemma altitudeFoot_map {n : Nat} [NeZero n] (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂)
    (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).altitudeFoot i = f (s.altitudeFoot i) := by
  simp [altitudeFoot, ← orthogonalProjectionSpan_map]

/--
lemma `altitudeFoot_restrict` / 引理 `altitudeFoot_restrict`

English:
lemma altitudeFoot_restrict
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitudeFoot i = s.altitudeFoot i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitudeFoot_map S.subtypeₐᵢ i

中文:
引理 altitudeFoot_restrict
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitudeFoot i = s.altitudeFoot i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitudeFoot_map S.subtypeₐᵢ i
-/
@[simp] lemma altitudeFoot_restrict {n : Nat} [NeZero n] (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitudeFoot i = s.altitudeFoot i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitudeFoot_map S.subtypeₐᵢ i

/--
lemma `ne_altitudeFoot` / 引理 `ne_altitudeFoot`

English:
lemma ne_altitudeFoot
  given: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  intro h
  rw [eq_comm]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]; rw [orthogonalProjection_eq_self_iff] at h
  simp at h

中文:
引理 ne_altitudeFoot
  条件: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  intro h
  rw [eq_comm]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]; rw [orthogonalProjection_eq_self_iff] at h
  simp at h
-/
@[simp] lemma ne_altitudeFoot {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.points i != s.altitudeFoot i := by
  intro h
  rw [eq_comm]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]; rw [orthogonalProjection_eq_self_iff] at h
  simp at h

/--
lemma `altitudeFoot_mem_affineSpan_image_compl` / 引理 `altitudeFoot_mem_affineSpan_image_compl`

English:
lemma altitudeFoot_mem_affineSpan_image_compl
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: by
  rw [← range_faceOpposite_points]
  exact orthogonalProjection_mem _

中文:
引理 altitudeFoot_mem_affineSpan_image_compl
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n)
  证明: by
  rw [← range_faceOpposite_points]
  exact orthogonalProjection_mem _
-/
@[simp] lemma altitudeFoot_mem_affineSpan_image_compl {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) : s.altitudeFoot i in affineSpan Real (s.points '' {i}ᶜ) := by
  rw [← range_faceOpposite_points]
  exact orthogonalProjection_mem _

/--
lemma `altitudeFoot_mem_affineSpan_faceOpposite` / 引理 `altitudeFoot_mem_affineSpan_faceOpposite`

English:
lemma altitudeFoot_mem_affineSpan_faceOpposite
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: orthogonalProjection_mem _

中文:
引理 altitudeFoot_mem_affineSpan_faceOpposite
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n)
  证明: orthogonalProjection_mem _

Depends on / 依赖: orthogonalProjection_mem
-/
lemma altitudeFoot_mem_affineSpan_faceOpposite {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) : s.altitudeFoot i in affineSpan Real (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _

/--
lemma `altitudeFoot_mem_affineSpan` / 引理 `altitudeFoot_mem_affineSpan`

English:
lemma altitudeFoot_mem_affineSpan
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp

中文:
引理 altitudeFoot_mem_affineSpan
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n)
  证明: by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp

Depends on / 依赖: SetLike, SetLike.le_def, affineSpan_mono, altitudeFoot_mem_affineSpan_faceOpposite, le_def, s.altitudeFoot_mem_affineSpan_faceOpposite
-/
lemma altitudeFoot_mem_affineSpan {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) : s.altitudeFoot i in affineSpan Real (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp

/--
lemma `affineSpan_pair_altitudeFoot_eq_altitude` / 引理 `affineSpan_pair_altitudeFoot_eq_altitude`

English:
lemma affineSpan_pair_altitudeFoot_eq_altitude
  proof: by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot]; rw [orthogonalProjectionSpan]
  simp_rw [range_faceOpposite_points]
  exact orthogonalProjection_vsub_mem_direction_orthogonal _ _

中文:
引理 affineSpan_pair_altitudeFoot_eq_altitude
  证明: by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot]; rw [orthogonalProjectionSpan]
  simp_rw [range_faceOpposite_points]
  exact orthogonalProjection_vsub_mem_direction_orthogonal _ _

Depends on / 依赖: affineSpan_pair_eq_altitude_iff, altitudeFoot, altitudeFoot_mem_affineSpan, ne_altitudeFoot, orthogonalProjectionSpan, orthogonalProjection_vsub_mem_direction_orthogonal, range_faceOpposite_points, s.altitudeFoot_mem_affineSpan, s.ne_altitudeFoot, simp_rw
-/
lemma affineSpan_pair_altitudeFoot_eq_altitude
    {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    line[Real, s.altitudeFoot i, s.points i] = s.altitude i := by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot]; rw [orthogonalProjectionSpan]
  simp_rw [range_faceOpposite_points]
  exact orthogonalProjection_vsub_mem_direction_orthogonal _ _

/--
lemma `altitudeFoot_mem_altitude` / 引理 `altitudeFoot_mem_altitude`

English:
lemma altitudeFoot_mem_altitude
  given: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _

中文:
引理 altitudeFoot_mem_altitude
  条件: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _

Depends on / 依赖: affineSpan_pair_altitudeFoot_eq_altitude, left_mem_affineSpan_pair
-/
lemma altitudeFoot_mem_altitude {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.altitudeFoot i in s.altitude i := by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _

/--
lemma `altitudeFoot_eq_point_rev` / 引理 `altitudeFoot_eq_point_rev`

English:
lemma altitudeFoot_eq_point_rev
  given: (s : Simplex Real P 1) (i : Fin 2)
  proof: by
  simp [altitudeFoot, faceOpposite_point_eq_point_rev]

中文:
引理 altitudeFoot_eq_point_rev
  条件: (s : Simplex 实数 P 1) (i : Fin 2)
  证明: by
  simp [altitudeFoot, faceOpposite_point_eq_point_rev]
-/
@[simp] lemma altitudeFoot_eq_point_rev (s : Simplex Real P 1) (i : Fin 2) :
    s.altitudeFoot i = s.points i.rev := by
  simp [altitudeFoot, faceOpposite_point_eq_point_rev]

/--
Definition of `height` / `height` 的定义

English:
definition height
  signature: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  body: dist (s.points i) (s.altitudeFoot i)

中文:
定义 height
  签名: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  定义体: dist (s.points i) (s.altitudeFoot i)

Depends on / 依赖: altitudeFoot, points, s.altitudeFoot, s.points
-/
def height {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : Real :=
  dist (s.points i) (s.altitudeFoot i)

/--
lemma `height_reindex` / 引理 `height_reindex`

English:
lemma height_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n] (s : Simplex Real P n)
  proof: by
  ext i
  simp [height]

中文:
引理 height_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n] (s : Simplex 实数 P n)
  证明: by
  ext i
  simp [height]
-/
@[simp] lemma height_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex Real P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).height = s.height ∘ e.symm := by
  ext i
  simp [height]

/--
lemma `height_map` / 引理 `height_map`

English:
lemma height_map
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  simp [height]

中文:
引理 height_map
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  simp [height]
-/
@[simp] lemma height_map {n : Nat} [NeZero n] (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂)
    (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).height i = s.height i := by
  simp [height]

/--
lemma `height_restrict` / 引理 `height_restrict`

English:
lemma height_restrict
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).height i = s.height i := by
  rw [eq_comm]
  convert! (s.restrict S hS).height_map S.subtypeₐᵢ i

@[simp]

中文:
引理 height_restrict
  结论: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).height i = s.height i := by
  rw [eq_comm]
  convert! (s.restrict S hS).height_map S.subtypeₐᵢ i

@[simp]
-/
@[simp] lemma height_restrict {n : Nat} [NeZero n] (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).height i = s.height i := by
  rw [eq_comm]
  convert! (s.restrict S hS).height_map S.subtypeₐᵢ i

@[simp]
/--
lemma `height_pos` / 引理 `height_pos`

English:
lemma height_pos
  given: {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  statement: 0 < s.height i
  proof: by
  simp [height]

中文:
引理 height_pos
  条件: {n : 自然数} [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  结论: 0 < s.height i
  证明: by
  simp [height]

Depends on / 依赖: height
-/
lemma height_pos {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : 0 < s.height i := by
  simp [height]

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the height of a simplex is always positive. -/
@[positivity height _ _]
meta def evalHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@height $V $P $i1 $i2 $i3 $i4 $n $hn $s $i) =>
    assertInstancesCommute
    return .positive q(height_pos $s $i)
  | _, _, _ => throwError "not Simplex.height"

example {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : 0 < s.height i := by
  positivity

/--
lemma `height_eq_dist` / 引理 `height_eq_dist`

English:
lemma height_eq_dist
  given: (s : Simplex Real P 1) (i : Fin 2)
  proof: by
  fin_cases i
  · simp [height]
  · rw [dist_comm]
    simp [height]

中文:
引理 height_eq_dist
  条件: (s : Simplex 实数 P 1) (i : Fin 2)
  证明: by
  fin_cases i
  · simp [height]
  · rw [dist_comm]
    simp [height]
-/
@[simp] lemma height_eq_dist (s : Simplex Real P 1) (i : Fin 2) :
    s.height i = dist (s.points 0) (s.points 1) := by
  fin_cases i
  · simp [height]
  · rw [dist_comm]
    simp [height]

open scoped RealInnerProductSpace

variable {n : Nat} (s : Simplex Real P n)

/--
lemma `inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero` / 引理 `inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero`

English:
lemma inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
  given: {i j : Fin (n + 1)} (h : i != j)
  proof: by grind [neZero_iff]
    ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 := by
  have : NeZero n := by grind [neZero_iff]
  refine Submodule.inner_right_of_mem_orthogonal
    (K := vectorSpan Real (s.points '' {i}ᶜ))
    (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan


中文:
引理 inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
  条件: {i j : Fin (n + 1)} (h : i != j)
  证明: by grind [neZero_iff]
    ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 := by
  have : NeZero n := by grind [neZero_iff]
  refine Submodule.inner_right_of_mem_orthogonal
    (K := vectorSpan Real (s.points '' {i}ᶜ))
    (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan


Depends on / 依赖: Affine, Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl, Affine.Simplex.range_faceOpposite_points, NeZero, Simplex, Submodule, Submodule.inner_right_of_mem_orthogonal, altitudeFoot, altitudeFoot_mem_affineSpan_image_compl, direction_affineSpan, h.symm, inner_right_of_mem_orthogonal, mem_affineSpan_image_iff, neZero_iff, points, range_faceOpposite_points, s.altitudeFoot, s.mem_affineSpan_image_iff, s.points, vectorSpan
-/
lemma inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero {i j : Fin (n + 1)} (h : i != j) :
    have : NeZero n := by grind [neZero_iff]
    ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 := by
  have : NeZero n := by grind [neZero_iff]
  refine Submodule.inner_right_of_mem_orthogonal
    (K := vectorSpan Real (s.points '' {i}ᶜ))
    (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (s.mem_affineSpan_image_iff.2 h.symm)
      (Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl _ _))
    ?_
  rw [← direction_affineSpan]; rw [← Affine.Simplex.range_faceOpposite_points]
  exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
lemma `inner_vsub_vsub_altitudeFoot_eq_height_sq` / 引理 `inner_vsub_vsub_altitudeFoot_eq_height_sq`

English:
lemma inner_vsub_vsub_altitudeFoot_eq_height_sq
  given: [NeZero n] {i j : Fin (n + 1)} (h : i != j)
  proof: by
  suffices ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 by
    rwa [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, inner_vsub_left_eq_zero_symm]
  exact s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero h

中文:
引理 inner_vsub_vsub_altitudeFoot_eq_height_sq
  条件: [NeZero n] {i j : Fin (n + 1)} (h : i != j)
  证明: by
  suffices ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 by
    rwa [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, inner_vsub_left_eq_zero_symm]
  exact s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero h

Depends on / 依赖: altitudeFoot, height, inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero, inner_vsub_left_eq_zero_symm, inner_vsub_vsub_left_eq_dist_sq_right_iff, points, s.altitudeFoot, s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero, s.points
-/
lemma inner_vsub_vsub_altitudeFoot_eq_height_sq [NeZero n] {i j : Fin (n + 1)} (h : i != j) :
    ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.altitudeFoot i⟫ = s.height i ^ 2 := by
  suffices ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 by
    rwa [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, inner_vsub_left_eq_zero_symm]
  exact s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero h

variable [Nat.AtLeastTwo n]

/--
lemma `abs_inner_vsub_altitudeFoot_lt_mul` / 引理 `abs_inner_vsub_altitudeFoot_lt_mul`

English:
lemma abs_inner_vsub_altitudeFoot_lt_mul
  given: {i j : Fin (n + 1)} (hij : i != j)
  proof: by
  apply lt_of_le_of_ne
  · convert! abs_real_inner_le_norm _ _ using 1
    simp only [dist_eq_norm_vsub, height]
  · simp_rw [height, dist_eq_norm_vsub]
    rw [← Real.norm_eq_abs]; rw [ne_eq]; rw [norm_inner_eq_norm_iff (by simp) (by simp)]
    rintro ⟨r, hr, h⟩
    suffices s.points j -ᵥ s.alti

中文:
引理 abs_inner_vsub_altitudeFoot_lt_mul
  条件: {i j : Fin (n + 1)} (hij : i != j)
  证明: by
  apply lt_of_le_of_ne
  · convert! abs_real_inner_le_norm _ _ using 1
    simp only [dist_eq_norm_vsub, height]
  · simp_rw [height, dist_eq_norm_vsub]
    rw [← Real.norm_eq_abs]; rw [ne_eq]; rw [norm_inner_eq_norm_iff (by simp) (by simp)]
    rintro ⟨r, hr, h⟩
    suffices s.points j -ᵥ s.alti

Depends on / 依赖: Real.norm_eq_abs, Set.range, Submodule, Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, abs_real_inner_le_norm, altitudeFoot, convert, dist_eq_norm_vsub, height, inf_orthogonal_eq_bot, lt_of_le_of_ne, mem_affineSpan, mem_bot, ne_eq, norm_eq_abs, norm_inner_eq_norm_iff, points, s.altitudeFoot, s.points
-/
lemma abs_inner_vsub_altitudeFoot_lt_mul {i j : Fin (n + 1)} (hij : i != j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫|
      < s.height i * s.height j := by
  apply lt_of_le_of_ne
  · convert! abs_real_inner_le_norm _ _ using 1
    simp only [dist_eq_norm_vsub, height]
  · simp_rw [height, dist_eq_norm_vsub]
    rw [← Real.norm_eq_abs]; rw [ne_eq]; rw [norm_inner_eq_norm_iff (by simp) (by simp)]
    rintro ⟨r, hr, h⟩
    suffices s.points j -ᵥ s.altitudeFoot j = 0 by
      simp at this
    rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
    refine ⟨vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (mem_affineSpan _ (Set.mem_range_self _)) ?_, ?_⟩
    · refine SetLike.le_def.1 (affineSpan_mono _ ?_) (Subtype.property _)
      simp
    · rw [SetLike.mem_coe]
      have hk : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j
        (by linarith only [Nat.AtLeastTwo.one_lt (n := n)])
      have hs : vectorSpan Real (Set.range s.points) =
          vectorSpan Real (Set.range (s.faceOpposite i).points) ⊔
            vectorSpan Real (Set.range (s.faceOpposite j).points) := by
        rcases hk with ⟨k, hki, hkj⟩
        have hki' : s.points k in Set.range (s.faceOpposite i).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hki
        have hkj' : s.points k in Set.range (s.faceOpposite j).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hkj
        have hs :
            Set.range s.points =
              Set.range (s.faceOpposite i).points union Set.range (s.faceOpposite j).points := by
          simp only [range_faceOpposite_points, ← Set.image_union]
          simp_rw [← Set.image_univ, ← Set.compl_inter]
          rw [Set.inter_singleton_eq_empty.mpr ?_]; rw [Set.compl_empty]
          simpa using hij.symm
        convert! AffineSubspace.vectorSpan_union_of_mem_of_mem Real hki' hkj'
      rw [hs]; rw [← Submodule.inf_orthogonal]; rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [h, ← direction_affineSpan]
        exact Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
      · rw [← direction_affineSpan]
        exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
lemma `neg_mul_lt_inner_vsub_altitudeFoot` / 引理 `neg_mul_lt_inner_vsub_altitudeFoot`

English:
lemma neg_mul_lt_inner_vsub_altitudeFoot
  given: (i j : Fin (n + 1))
  proof: by
  obtain rfl | hij := eq_or_ne i j
  · rw [real_inner_self_eq_norm_sq]
    refine lt_of_lt_of_le (b := 0) ?_ ?_
    · rw [neg_lt_zero]
      positivity
    · positivity
  rw [neg_lt]
  refine lt_of_abs_lt ?_
  rw [abs_neg]
  exact abs_inner_vsub_altitudeFoot_lt_mul s hij

中文:
引理 neg_mul_lt_inner_vsub_altitudeFoot
  条件: (i j : Fin (n + 1))
  证明: by
  obtain rfl | hij := eq_or_ne i j
  · rw [real_inner_self_eq_norm_sq]
    refine lt_of_lt_of_le (b := 0) ?_ ?_
    · rw [neg_lt_zero]
      positivity
    · positivity
  rw [neg_lt]
  refine lt_of_abs_lt ?_
  rw [abs_neg]
  exact abs_inner_vsub_altitudeFoot_lt_mul s hij

Depends on / 依赖: abs_inner_vsub_altitudeFoot_lt_mul, abs_neg, eq_or_ne, lt_of_abs_lt, lt_of_lt_of_le, neg_lt, neg_lt_zero, real_inner_self_eq_norm_sq
-/
lemma neg_mul_lt_inner_vsub_altitudeFoot (i j : Fin (n + 1)) :
    -(s.height i * s.height j)
      < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ := by
  obtain rfl | hij := eq_or_ne i j
  · rw [real_inner_self_eq_norm_sq]
    refine lt_of_lt_of_le (b := 0) ?_ ?_
    · rw [neg_lt_zero]
      positivity
    · positivity
  rw [neg_lt]
  refine lt_of_abs_lt ?_
  rw [abs_neg]
  exact abs_inner_vsub_altitudeFoot_lt_mul s hij

/--
lemma `abs_inner_vsub_altitudeFoot_div_lt_one` / 引理 `abs_inner_vsub_altitudeFoot_div_lt_one`

English:
lemma abs_inner_vsub_altitudeFoot_div_lt_one
  given: {i j : Fin (n + 1)} (hij : i != j)
  proof: by
  rw [abs_div]; rw [div_lt_one (by simp [height])]
  nth_rw 2 [abs_eq_self.2]
  · exact abs_inner_vsub_altitudeFoot_lt_mul _ hij
  · simp only [height]
    positivity

中文:
引理 abs_inner_vsub_altitudeFoot_div_lt_one
  条件: {i j : Fin (n + 1)} (hij : i != j)
  证明: by
  rw [abs_div]; rw [div_lt_one (by simp [height])]
  nth_rw 2 [abs_eq_self.2]
  · exact abs_inner_vsub_altitudeFoot_lt_mul _ hij
  · simp only [height]
    positivity

Depends on / 依赖: abs_div, abs_eq_self, abs_inner_vsub_altitudeFoot_lt_mul, div_lt_one, height, nth_rw
-/
lemma abs_inner_vsub_altitudeFoot_div_lt_one {i j : Fin (n + 1)} (hij : i != j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j)| < 1 := by
  rw [abs_div]; rw [div_lt_one (by simp [height])]
  nth_rw 2 [abs_eq_self.2]
  · exact abs_inner_vsub_altitudeFoot_lt_mul _ hij
  · simp only [height]
    positivity

/--
lemma `neg_one_lt_inner_vsub_altitudeFoot_div` / 引理 `neg_one_lt_inner_vsub_altitudeFoot_div`

English:
lemma neg_one_lt_inner_vsub_altitudeFoot_div
  given: (s : Simplex Real P n) (i j : Fin (n + 1))
  proof: by
  rw [neg_lt]; rw [neg_div']; rw [div_lt_one (by simp [height]), neg_lt]
  exact neg_mul_lt_inner_vsub_altitudeFoot _ _ _

中文:
引理 neg_one_lt_inner_vsub_altitudeFoot_div
  条件: (s : Simplex 实数 P n) (i j : Fin (n + 1))
  证明: by
  rw [neg_lt]; rw [neg_div']; rw [div_lt_one (by simp [height]), neg_lt]
  exact neg_mul_lt_inner_vsub_altitudeFoot _ _ _

Depends on / 依赖: div_lt_one, height, neg_div, neg_lt, neg_mul_lt_inner_vsub_altitudeFoot
-/
lemma neg_one_lt_inner_vsub_altitudeFoot_div (s : Simplex Real P n) (i j : Fin (n + 1)) :
    -1 < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j) := by
  rw [neg_lt]; rw [neg_div']; rw [div_lt_one (by simp [height]), neg_lt]
  exact neg_mul_lt_inner_vsub_altitudeFoot _ _ _

end Simplex

end Affine
