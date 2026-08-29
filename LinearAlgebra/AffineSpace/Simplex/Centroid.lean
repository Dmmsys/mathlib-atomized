/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Chu Zheng
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Centroid of a simplex in affine space

This file proves some basic properties of the centroid of a simplex in affine space.
The definition of the centroid is based on `Finset.univ.centroid` applied to the set of vertices.
For convenience, we use `Simplex.centroid` as an abbreviation.

This file also defines `faceOppositeCentroid`, which is the centroid of the facet of the simplex
obtained by removing one vertex.

We prove several relations among the `centroid`, the `faceOppositeCentroid`, and the vertices of
the simplex. In particular, we prove a version of Commandino's theorem in arbitrary dimensions:
the centroid lies on each median, dividing it in a ratio of `n : 1`, where `n` is the dimension
of the simplex.

## Main definitions

* `centroid` is the centroid of a simplex, defined via `Finset.univ.centroid` on its vertices.

* `faceOppositeCentroid` is the centroid of the facet obtained by removing one vertex from the
  simplex.

* `median` is the line connecting a vertex to the corresponding faceOppositeCentroid.

* `medial` is the simplex formed by all `faceOppositeCentroid`.

## References

* https://en.wikipedia.org/wiki/Median_(geometry)
* https://en.wikipedia.org/wiki/Commandino%27s_theorem

-/

@[expose] public section

noncomputable section

open Finset AffineSubspace

namespace Affine

namespace Simplex

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {n : Nat}

/--
Definition of `centroid` / `centroid` 的定义

English:
abbreviation centroid
  signature: (t : Affine.Simplex k P n)
  body: Finset.univ.centroid k t.points

中文:
缩写 centroid
  签名: (t : 仿射.单纯形 k P n)
  定义体: Finset.univ.centroid k t.points

Depends on / 依赖: Finset, Finset.univ.centroid, centroid, points, t.points
-/
abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points

/--
theorem `univ_centroid_eq` / 定理 `univ_centroid_eq`

English:
theorem univ_centroid_eq
  given: (s : Simplex k P n)
  proof: rfl

中文:
定理 univ_centroid_eq
  条件: (s : 单纯形 k P n)
  证明: rfl
-/
theorem univ_centroid_eq (s : Simplex k P n) :
    Finset.univ.centroid k s.points = s.centroid := rfl

/--
theorem `centroid_mem_affineSpan` / 定理 `centroid_mem_affineSpan`

English:
theorem centroid_mem_affineSpan
  given: [CharZero k] {n : Nat} (s : Simplex k P n)
  proof: centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

中文:
定理 centroid_mem_affineSpan
  条件: [特征零 k] {n : 自然数} (s : 单纯形 k P n)
  证明: centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

Depends on / 依赖: card_fin, centroid_mem_affineSpan_of_card_eq_add_one
-/
theorem centroid_mem_affineSpan [CharZero k] {n : Nat} (s : Simplex k P n) :
    s.centroid in affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

/--
theorem `centroid_eq_affineCombination` / 定理 `centroid_eq_affineCombination`

English:
theorem centroid_eq_affineCombination
  given: (s : Simplex k P n)
  proof: by rfl

中文:
定理 centroid_eq_affineCombination
  条件: (s : 单纯形 k P n)
  证明: by rfl
-/
theorem centroid_eq_affineCombination (s : Simplex k P n) :
    s.centroid = affineCombination k univ s.points (centroidWeights k univ) := by rfl

/--
theorem `centroid_notMem_affineSpan_of_ne_univ` / 定理 `centroid_notMem_affineSpan_of_ne_univ`

English:
theorem centroid_notMem_affineSpan_of_ne_univ
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ 

中文:
定理 centroid_notMem_affineSpan_of_ne_univ
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ 

Depends on / 依赖: AffineIndependent, AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan, Finset, Fintype, Set.exists_of_ssubset, Set.univ, card_univ, centroidWeights, centroidWeights_apply, centroid_eq_affineCombination, eq_zero_of_affineCombination_mem_affineSpan, exists_of_ssubset, hssubset, independent, s.centroid_eq_affineCombination, s.independent, sum_centroidWeights_eq_one_of_nonempty
-/
theorem centroid_notMem_affineSpan_of_ne_univ [CharZero k] (s : Simplex k P n)
    {t : Set (Fin (n + 1))} (ht : t != Set.univ) :
    s.centroid ∉ affineSpan k (s.points '' t) := by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ (by simp)]
  have h1 := AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan s.independent hw h
    (by simp) hi.2
  have h2 : w i = (1 : k) / (n + 1) := by
    simp [wdef, centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
  simp only [h2, one_div, inv_eq_zero] at h1
  norm_cast at h1

/--
theorem `centroid_vsub_eq` / 定理 `centroid_vsub_eq`

English:
theorem centroid_vsub_eq
  given: {n : Nat} [CharZero k] (s : Simplex k P n) (p : P)
  proof: by
  rw [centroid_vsub_const _ _ (by simp)]; rw [centroid_def]; rw [affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]

中文:
定理 centroid_vsub_eq
  条件: {n : 自然数} [特征零 k] (s : 单纯形 k P n) (p : P)
  证明: by
  rw [centroid_vsub_const _ _ (by simp)]; rw [centroid_def]; rw [affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]

Depends on / 依赖: affineCombination_eq_linear_combination, centroid_def, centroid_vsub_const, smul_sum, sum_centroidWeights_eq_one_of_nonempty
-/
theorem centroid_vsub_eq {n : Nat} [CharZero k] (s : Simplex k P n) (p : P) :
    s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid_vsub_const _ _ (by simp)]; rw [centroid_def]; rw [affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]

/--
theorem `centroid_eq_smul_sum_vsub_vadd` / 定理 `centroid_eq_smul_sum_vsub_vadd`

English:
theorem centroid_eq_smul_sum_vsub_vadd
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  rw [← s.centroid_vsub_eq]; rw [vsub_vadd]

中文:
定理 centroid_eq_smul_sum_vsub_vadd
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  rw [← s.centroid_vsub_eq]; rw [vsub_vadd]

Depends on / 依赖: centroid_vsub_eq, s.centroid_vsub_eq, vsub_vadd
-/
theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← s.centroid_vsub_eq]; rw [vsub_vadd]

/--
theorem `smul_centroid_vsub_point_eq_sum_vsub` / 定理 `smul_centroid_vsub_point_eq_sum_vsub`

English:
theorem smul_centroid_vsub_point_eq_sum_vsub
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  rw [centroid_eq_smul_sum_vsub_vadd s i]; rw [vadd_vsub]; rw [smul_smul]; rw [mul_inv_cancel₀]; rw [one_smul]
  norm_cast

中文:
定理 smul_centroid_vsub_point_eq_sum_vsub
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  rw [centroid_eq_smul_sum_vsub_vadd s i]; rw [vadd_vsub]; rw [smul_smul]; rw [mul_inv_cancel₀]; rw [one_smul]
  norm_cast

Depends on / 依赖: centroid_eq_smul_sum_vsub_vadd, one_smul, smul_smul, vadd_vsub
-/
theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid_eq_smul_sum_vsub_vadd s i]; rw [vadd_vsub]; rw [smul_smul]; rw [mul_inv_cancel₀]; rw [one_smul]
  norm_cast

/--
theorem `centroid_weighted_vsub_eq_zero` / 定理 `centroid_weighted_vsub_eq_zero`

English:
theorem centroid_weighted_vsub_eq_zero
  given: [CharZero k] (s : Simplex k P n)
  proof: by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

中文:
定理 centroid_weighted_vsub_eq_zero
  条件: [特征零 k] (s : 单纯形 k P n)
  证明: by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

Depends on / 依赖: centroid, centroid_vsub_eq, inv_ne_zero, s.centroid, smul_eq_zero_iff_right, vsub_self
-/
theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

/--
theorem `eq_centroid_iff_sum_vsub_eq_zero` / 定理 `eq_centroid_iff_sum_vsub_eq_zero`

English:
theorem eq_centroid_iff_sum_vsub_eq_zero
  given: [CharZero k] {s : Simplex k P n} {p : P}
  proof: by
  constructor
  · intro h
    rw [h]; rw [centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ 

中文:
定理 eq_centroid_iff_sum_vsub_eq_zero
  条件: [特征零 k] {s : 单纯形 k P n} {p : P}
  证明: by
  constructor
  · intro h
    rw [h]; rw [centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ 

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, card_univ, centroid, centroid_weighted_vsub_eq_zero, neg_eq_zero, points, s.centroid, s.points, sum_congr, sum_const, sum_sub_distrib, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right, zero_sub
-/
theorem eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Simplex k P n} {p : P} :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h]; rw [centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this]; rw [sum_sub_distrib]; rw [centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n : k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

/--
theorem `face_centroid_eq_centroid` / 定理 `face_centroid_eq_centroid`

English:
theorem face_centroid_eq_centroid
  statement: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
  proof: by
  convert! (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj]; rw [Finset.coe_map]; rw [Finset.coe_univ]; rw [Set.image_univ]
  simp

中文:
定理 face_centroid_eq_centroid
  结论: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数}
  证明: by
  convert! (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj]; rw [Finset.coe_map]; rw [Finset.coe_univ]; rw [Set.image_univ]
  simp

Depends on / 依赖: Finset, Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Finset.univ.centroid_map, Set.image_univ, centroid_map, coe_inj, coe_map, coe_univ, convert, fs.orderEmbOfFin, image_univ, orderEmbOfFin, points, s.points, toEmbedding
-/
theorem face_centroid_eq_centroid {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert! (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj]; rw [Finset.coe_map]; rw [Finset.coe_univ]; rw [Set.image_univ]
  simp

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
/--
theorem `centroid_eq_iff` / 定理 `centroid_eq_iff`

English:
theorem centroid_eq_iff
  statement: [CharZero k] {n : Nat} (s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
  proof: by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype]; rw [Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independen

中文:
定理 centroid_eq_iff
  结论: [特征零 k] {n : 自然数} (s : 单纯形 k P n) {fs₁ fs₂ : 有限集 (有限集 (n + 1))}
  证明: by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype]; rw [Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independen

Depends on / 依赖: Finset, Finset.c, Finset.centroid, Finset.centroid_eq_affineCombination_fintype, Finset.coe_univ, Set.indicator_univ, affineIndependent_iff_indicator_eq_of_affineCombination_eq, centroid, centroid_eq_affineCombination_fintype, coe_univ, funext_iff, independent, indicator_univ, points, s.independent, s.points, simp_rw, sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one
-/
theorem centroid_eq_iff [CharZero k] {n : Nat} (s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
    {m₁ m₂ : Nat} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ := by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype]; rw [Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, funext_iff,
    Finset.centroidWeightsIndicator_def, Finset.centroidWeights, h₁, h₂] at ha
  ext i
  specialize ha i
  have key : forall n : Nat, (n : k) + 1 != 0 := fun n h => by norm_cast at h
  -- we should be able to golf this to
  -- `refine ⟨fun hi ↦ decidable.by_contradiction (fun hni ↦ ?_), ...⟩`,
  -- but for some unknown reason it doesn't work.
  constructor <;> intro hi <;> by_contra hni
  · simp [hni, hi, key] at ha
  · simpa [hni, hi, key] using ha.symm

/--
theorem `face_centroid_eq_iff` / 定理 `face_centroid_eq_iff`

English:
theorem face_centroid_eq_iff
  statement: [CharZero k] {n : Nat} (s : Simplex k P n)
  proof: by
  rw [face_centroid_eq_centroid]; rw [face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

中文:
定理 face_centroid_eq_iff
  结论: [特征零 k] {n : 自然数} (s : 单纯形 k P n)
  证明: by
  rw [face_centroid_eq_centroid]; rw [face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

Depends on / 依赖: centroid_eq_iff, face_centroid_eq_centroid, s.centroid_eq_iff
-/
theorem face_centroid_eq_iff [CharZero k] {n : Nat} (s : Simplex k P n)
    {fs₁ fs₂ : Finset (Fin (n + 1))} {m₁ m₂ : Nat} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).points ↔
      fs₁ = fs₂ := by
  rw [face_centroid_eq_centroid]; rw [face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

/--
theorem `centroid_eq_of_range_eq` / 定理 `centroid_eq_of_range_eq`

English:
theorem centroid_eq_of_range_eq
  statement: {n : Nat} {s₁ s₂ : Simplex k P n}
  proof: by
  rw [← Set.image_univ]; rw [← Set.image_univ]; rw [← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

中文:
定理 centroid_eq_of_range_eq
  结论: {n : 自然数} {s₁ s₂ : 单纯形 k P n}
  证明: by
  rw [← Set.image_univ]; rw [← Set.image_univ]; rw [← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

Depends on / 依赖: AffineIndependent, AffineIndependent.injective, Finset, Finset.coe_univ, Finset.univ.centroid_eq_of_inj_on_of_image_eq, Set.image_univ, centroid_eq_of_inj_on_of_image_eq, coe_univ, image_univ, independent, injective
-/
theorem centroid_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points := by
  rw [← Set.image_univ]; rw [← Set.image_univ]; rw [← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

/--
theorem `affineIndependent_points_update_centroid` / 定理 `affineIndependent_points_update_centroid`

English:
theorem affineIndependent_points_update_centroid
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    s.centroid_notMem_affineSpan_of_ne_univ (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this

中文:
定理 affineIndependent_points_update_centroid
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    s.centroid_notMem_affineSpan_of_ne_univ (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this

Depends on / 依赖: AffineIndependent, AffineIndependent.affineIndependent_update_of_notMem_affineSpan, affineIndependent_update_of_notMem_affineSpan, affineSpan, centroid, centroid_notMem_affineSpan_of_ne_univ, independent, points, s.centroid, s.centroid_notMem_affineSpan_of_ne_univ, s.independent, s.points
-/
theorem affineIndependent_points_update_centroid [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    s.centroid_notMem_affineSpan_of_ne_univ (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this

/--
theorem `centroid_map` / 定理 `centroid_map`

English:
theorem centroid_map
  statement: [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
  proof: by
  rw [centroid]; rw [map_points]; rw [centroid_eq_affineCombination]; rw [Finset.map_affineCombination]
  · rw [Finset.centroid]
  · rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp

中文:
定理 centroid_map
  结论: [特征零 k] {V₂ P₂ : 类型} [加法交换群 V₂] [模 k V₂]
  证明: by
  rw [centroid]; rw [map_points]; rw [centroid_eq_affineCombination]; rw [Finset.map_affineCombination]
  · rw [Finset.centroid]
  · rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp

Depends on / 依赖: Finset, Finset.centroid, Finset.map_affineCombination, centroid, centroid_eq_affineCombination, map_affineCombination, map_points, sum_centroidWeights_eq_one_of_card_ne_zero
-/
theorem centroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    [AffineSpace V₂ P₂] {n : Nat} (s : Simplex k P n) (f : P ->ᵃ[k] P₂)
    (hf : Function.Injective f) :
    (s.map f hf).centroid = f (s.centroid) := by
  rw [centroid]; rw [map_points]; rw [centroid_eq_affineCombination]; rw [Finset.map_affineCombination]
  · rw [Finset.centroid]
  · rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp

/--
theorem `centroid_reindex` / 定理 `centroid_reindex`

English:
theorem centroid_reindex
  statement: {m n : Nat} (s : Simplex k P m)
  proof: by
  rw [centroid]; rw [centroid]
  simp only [centroid_eq_affineCombination]
  simp only [reindex]
  have h_eq : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  subst h_eq
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

中文:
定理 centroid_reindex
  结论: {m n : 自然数} (s : 单纯形 k P m)
  证明: by
  rw [centroid]; rw [centroid]
  simp only [centroid_eq_affineCombination]
  simp only [reindex]
  have h_eq : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  subst h_eq
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

Depends on / 依赖: Finset, Finset.univ.affineCombination_map, Fintype, Fintype.card_eq, Function, Function.comp_assoc, affineCombination_map, card_eq, centroid, centroid_eq_affineCombination, comp_assoc, convert, e.toEmbedding, h_eq, reindex, toEmbedding
-/
theorem centroid_reindex {m n : Nat} (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).centroid = s.centroid := by
  rw [centroid]; rw [centroid]
  simp only [centroid_eq_affineCombination]
  simp only [reindex]
  have h_eq : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  subst h_eq
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

/--
theorem `centroid_restrict` / 定理 `centroid_restrict`

English:
theorem centroid_restrict
  statement: [CharZero k] {n : Nat} (s : Simplex k P n) (S : AffineSubspace k P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).centroid = s.centroid := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.

中文:
定理 centroid_restrict
  结论: [特征零 k] {n : 自然数} (s : 单纯形 k P n) (S : 仿射子空间 k P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).centroid = s.centroid := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem centroid_restrict [CharZero k] {n : Nat} (s : Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).centroid = s.centroid := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.restrict S hS).centroid_map S.subtype hf

variable [NeZero n]

/--
Definition of `faceOppositeCentroid` / `faceOppositeCentroid` 的定义

English:
definition faceOppositeCentroid
  signature: (s : Affine.Simplex k P n) (i : Fin (n + 1))
  body: (s.faceOpposite i).centroid

中文:
定义 faceOppositeCentroid
  签名: (s : 仿射.单纯形 k P n) (i : 有限集 (n + 1))
  定义体: (s.faceOpposite i).centroid

Depends on / 依赖: centroid, faceOpposite, s.faceOpposite
-/
def faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).centroid

/--
theorem `faceOppositeCentroid_mem_affineSpan_face` / 定理 `faceOppositeCentroid_mem_affineSpan_face`

English:
theorem faceOppositeCentroid_mem_affineSpan_face
  statement: [CharZero k] (s : Simplex k P n)
  proof: centroid_mem_affineSpan (s.faceOpposite i)

中文:
定理 faceOppositeCentroid_mem_affineSpan_face
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: centroid_mem_affineSpan (s.faceOpposite i)

Depends on / 依赖: centroid_mem_affineSpan, faceOpposite, s.faceOpposite
-/
theorem faceOppositeCentroid_mem_affineSpan_face [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i in affineSpan k (Set.range (s.faceOpposite i).points) :=
  centroid_mem_affineSpan (s.faceOpposite i)

/--
theorem `faceOppositeCentroid_eq_affineCombination` / 定理 `faceOppositeCentroid_eq_affineCombination`

English:
theorem faceOppositeCentroid_eq_affineCombination
  given: (s : Affine.Simplex k P n) (i : Fin (n + 1))
  proof: by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid]; rw [centroid_def]; rw [centroidWeights_eq_const]; rw [card_compl]
  simp only [Fintype.card_fin, card_singl

中文:
定理 faceOppositeCentroid_eq_affineCombination
  条件: (s : 仿射.单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid]; rw [centroid_def]; rw [centroidWeights_eq_const]; rw [card_compl]
  simp only [Fintype.card_fin, card_singl

Depends on / 依赖: Fintype, Fintype.card_fin, NeZero, NeZero.one_le, add_tsub_cancel_right, card_compl, card_fin, card_singleton, centroid, centroidWeights_eq_const, centroid_def, faceOpposite, faceOppositeCentroid, face_centroid_eq_centroid, one_le, s.face, s.faceOpposite
-/
theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) fun _ => (↑n)⁻¹) := by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid]; rw [centroid_def]; rw [centroidWeights_eq_const]; rw [card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

/--
theorem `faceOppositeCentroid_vsub_point_eq_smul_sum_vsub` / 定理 `faceOppositeCentroid_vsub_point_eq_smul_sum_vsub`

English:
theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub
  statement: [CharZero k] (s : Affine.Simplex k P n)
  proof: by
  rw [faceOppositeCentroid_eq_affineCombination]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n + 1)) : ∑ j in {i}ᶜ, (n : k)⁻¹ • (s.points j -ᵥ s.points i) =
      ∑ j : (Fin (n + 

中文:
定理 faceOppositeCentroid_vsub_point_eq_smul_sum_vsub
  结论: [特征零 k] (s : 仿射.单纯形 k P n)
  证明: by
  rw [faceOppositeCentroid_eq_affineCombination]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n + 1)) : ∑ j in {i}ᶜ, (n : k)⁻¹ • (s.points j -ᵥ s.points i) =
      ∑ j : (Fin (n + 

Depends on / 依赖: Finset, Finset.sum_compl_add_sum, Fintype, Fintype.card_fin, add_tsub_cancel_right, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, card_compl, card_fin, card_singleton, faceOppositeCentroid_eq_affineCombination, points, s.points, smul_sum, sum_compl_add_sum, sum_const, vadd_vsub, weightedVSubOfPoint_apply
-/
theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ (s.points i) = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_affineCombination]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n + 1)) : ∑ j in {i}ᶜ, (n : k)⁻¹ • (s.points j -ᵥ s.points i) =
      ∑ j : (Fin (n + 1)), ((n : k)⁻¹ • (s.points j -ᵥ s.points i)) := by
      rw [← Finset.sum_compl_add_sum {i}]
      simp
    rw [h i]; rw [smul_sum]
  · simp only [sum_const, card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right,
      nsmul_eq_mul]
    rw [mul_inv_cancel₀ (NeZero.ne (n : k))]

/--
theorem `faceOppositeCentroid_eq_sum_vsub_vadd` / 定理 `faceOppositeCentroid_eq_sum_vsub_vadd`

English:
theorem faceOppositeCentroid_eq_sum_vsub_vadd
  statement: [CharZero k] (s : Affine.Simplex k P n)
  proof: by
  rw [← faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i]; rw [vsub_vadd]

中文:
定理 faceOppositeCentroid_eq_sum_vsub_vadd
  结论: [特征零 k] (s : 仿射.单纯形 k P n)
  证明: by
  rw [← faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i]; rw [vsub_vadd]

Depends on / 依赖: faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, vsub_vadd
-/
theorem faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [← faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i]; rw [vsub_vadd]

/--
theorem `point_vsub_faceOppositeCentroid_eq_smul_sum_vsub` / 定理 `point_vsub_faceOppositeCentroid_eq_smul_sum_vsub`

English:
theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub
  statement: [CharZero k] (s : Affine.Simplex k P n)
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [← neg_smul]; rw [Lean.Grind.Ring.neg_eq_mul_neg_one]; rw [← smul_smul]; rw [smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

中文:
定理 point_vsub_faceOppositeCentroid_eq_smul_sum_vsub
  结论: [特征零 k] (s : 仿射.单纯形 k P n)
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [← neg_smul]; rw [Lean.Grind.Ring.neg_eq_mul_neg_one]; rw [← smul_smul]; rw [smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

Depends on / 依赖: Lean.Grind.Ring.neg_eq_mul_neg_one, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, neg_eq_mul_neg_one, neg_smul, neg_vsub_eq_vsub_rev, one_smul, smul_smul, smul_sum
-/
theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [← neg_smul]; rw [Lean.Grind.Ring.neg_eq_mul_neg_one]; rw [← smul_smul]; rw [smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

/--
theorem `smul_faceOppositeCentroid_vsub_point_eq_sum_vsub` / 定理 `smul_faceOppositeCentroid_vsub_point_eq_sum_vsub`

English:
theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub
  statement: [CharZero k] (s : Affine.Simplex k P n)
  proof: by
  simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]

中文:
定理 smul_faceOppositeCentroid_vsub_point_eq_sum_vsub
  结论: [特征零 k] (s : 仿射.单纯形 k P n)
  证明: by
  simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]

Depends on / 依赖: NeZero, NeZero.ne, faceOppositeCentroid_eq_sum_vsub_vadd, one_smul, smul_smul
-/
theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]

/--
theorem `smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point` / 定理 `smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point`

English:
theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point
  statement: [CharZero k]
  proof: by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i]; rw [smul_centroid_vsub_point_eq_sum_vsub s i]

中文:
定理 smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point
  结论: [特征零 k]
  证明: by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i]; rw [smul_centroid_vsub_point_eq_sum_vsub s i]

Depends on / 依赖: smul_centroid_vsub_point_eq_sum_vsub, smul_faceOppositeCentroid_vsub_point_eq_sum_vsub
-/
theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    (n + 1 : k) • (s.centroid -ᵥ s.points i) =
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i]; rw [smul_centroid_vsub_point_eq_sum_vsub s i]

/--
theorem `faceOppositeCentroid_vsub_faceOppositeCentroid` / 定理 `faceOppositeCentroid_vsub_faceOppositeCentroid`

English:
theorem faceOppositeCentroid_vsub_faceOppositeCentroid
  statement: [CharZero k] (s : Affine.Simplex k P n)
  proof: by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i]; rw [faceOppositeCentroid_eq_sum_vsub_vadd s j]; rw [vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n + 1)) : ∑ x, (s.points x -ᵥ s.points i) =
      ∑ x, (s.points x -ᵥ s.points 0 - (s.points i -ᵥ s.points 0)) := by
    app

中文:
定理 faceOppositeCentroid_vsub_faceOppositeCentroid
  结论: [特征零 k] (s : 仿射.单纯形 k P n)
  证明: by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i]; rw [faceOppositeCentroid_eq_sum_vsub_vadd s j]; rw [vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n + 1)) : ∑ x, (s.points x -ᵥ s.points i) =
      ∑ x, (s.points x -ᵥ s.points 0 - (s.points i -ᵥ s.points 0)) := by
    app

Depends on / 依赖: faceOppositeCentroid_eq_sum_vsub_vadd, points, s.points, simp_rw, smul_sub, sub_sub_sub_cancel_left, sum_congr, sum_const, sum_sub_distrib, vadd_vsub_vadd_comm, vsub_sub_vsub_cancel_right
-/
theorem faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n)
    (i j : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    (n : k)⁻¹ • (s.points j -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i]; rw [faceOppositeCentroid_eq_sum_vsub_vadd s j]; rw [vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n + 1)) : ∑ x, (s.points x -ᵥ s.points i) =
      ∑ x, (s.points x -ᵥ s.points 0 - (s.points i -ᵥ s.points 0)) := by
    apply sum_congr rfl
    simp
  simp_rw [h1 i, h1 j, sum_sub_distrib]
  rw [smul_sub]; rw [smul_sub]; rw [sub_sub_sub_cancel_left]; rw [← smul_sub]; rw [← sum_sub_distrib]; rw [vsub_sub_vsub_cancel_right]; rw [sum_const]; rw [card_univ]; rw [Fintype.card_fin]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this]; rw [← sub_eq_add_neg]; rw [add_smul]; rw [sub_eq_iff_eq_add]; rw [one_smul]; rw [smul_add]; rw [add_comm]
  have : (n : k)⁻¹ • n • (s.points j -ᵥ s.points i) =
      (n : k)⁻¹ • (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
  rw [this]; rw [smul_smul]; rw [inv_eq_one_div]; rw [one_div_mul_cancel (NeZero.ne (n : k))]; rw [one_smul]

/--
theorem `faceOppositeCentroid_vsub_point_eq_smul_vsub` / 定理 `faceOppositeCentroid_vsub_point_eq_smul_vsub`

English:
theorem faceOppositeCentroid_vsub_point_eq_smul_vsub
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]
  congr
  rw [mul_sub]; rw [add_mul]; rw [mul_inv_cancel₀ (NeZero.ne (n : k))]; rw [mul_inv_cancel₀ (by norm_cast)]; rw [o

中文:
定理 faceOppositeCentroid_vsub_point_eq_smul_vsub
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]
  congr
  rw [mul_sub]; rw [add_mul]; rw [mul_inv_cancel₀ (NeZero.ne (n : k))]; rw [mul_inv_cancel₀ (by norm_cast)]; rw [o

Depends on / 依赖: NeZero, NeZero.ne, add_mul, centroid, centroid_vsub_eq, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, mul_sub, one_mul, points, s.centroid, s.points, smul_smul, sub_smul, vsub_sub_vsub_cancel_right
-/
theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    (n + 1 : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]
  congr
  rw [mul_sub]; rw [add_mul]; rw [mul_inv_cancel₀ (NeZero.ne (n : k))]; rw [mul_inv_cancel₀ (by norm_cast)]; rw [one_mul]
  grind

/--
theorem `point_vsub_faceOppositeCentroid_eq_smul_vsub` / 定理 `point_vsub_faceOppositeCentroid_eq_smul_vsub`

English:
theorem point_vsub_faceOppositeCentroid_eq_smul_vsub
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [← neg_smul]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_neg]

中文:
定理 point_vsub_faceOppositeCentroid_eq_smul_vsub
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [← neg_smul]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_neg]

Depends on / 依赖: faceOppositeCentroid_vsub_point_eq_smul_vsub, neg_neg, neg_smul, neg_smul_neg, neg_vsub_eq_vsub_rev
-/
theorem point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i =
    (n + 1 : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [← neg_smul]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_neg]

/--
theorem `point_vsub_centroid_eq_smul_vsub` / 定理 `point_vsub_centroid_eq_smul_vsub`

English:
theorem point_vsub_centroid_eq_smul_vsub
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]; rw [← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq

中文:
定理 point_vsub_centroid_eq_smul_vsub
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]; rw [← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq

Depends on / 依赖: NeZero, NeZero.ne, add_mul, centroid_vsub_eq, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, mul_sub, neg_add_eq_sub, neg_smul, neg_vsub_eq_vsub_rev, nth_rw, points, s.points, simp_rw, smul_smul, sub_eq_iff_eq_add, sub_smul, vsub_sub_vsub_cancel_right
-/
theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i)]; rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub]; rw [centroid_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [centroid_vsub_eq]; rw [← sub_smul]; rw [smul_smul]; rw [← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  rw [sub_eq_iff_eq_add]; rw [mul_inv_cancel₀ (NeZero.ne (n : k))]
  have : (↑n + (1 : k))⁻¹ = 1 * (↑n + (1 : k))⁻¹ := by simp
  nth_rw 2 [this]
  rw [← add_mul]; rw [mul_inv_cancel₀ (by norm_cast)]

/--
theorem `centroid_vsub_point_eq_smul_vsub` / 定理 `centroid_vsub_point_eq_smul_vsub`

English:
theorem centroid_vsub_point_eq_smul_vsub
  statement: [CharZero k]
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [point_vsub_centroid_eq_smul_vsub]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [← neg_smul]; rw [neg_neg]

中文:
定理 centroid_vsub_point_eq_smul_vsub
  结论: [特征零 k]
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [point_vsub_centroid_eq_smul_vsub]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [← neg_smul]; rw [neg_neg]

Depends on / 依赖: neg_neg, neg_smul, neg_smul_neg, neg_vsub_eq_vsub_rev, point_vsub_centroid_eq_smul_vsub
-/
theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [point_vsub_centroid_eq_smul_vsub]; rw [← neg_smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [← neg_smul]; rw [neg_neg]

/--
theorem `faceOppositeCentroid_vsub_centroid_eq_smul_vsub` / 定理 `faceOppositeCentroid_vsub_centroid_eq_smul_vsub`

English:
theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub
  statement: [CharZero k]
  proof: by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

中文:
定理 faceOppositeCentroid_vsub_centroid_eq_smul_vsub
  结论: [特征零 k]
  证明: by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

Depends on / 依赖: NeZero, NeZero.ne, centroid_vsub_point_eq_smul_vsub, one_smul, smul_smul
-/
theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.centroid = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) := by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

/--
theorem `centroid_vsub_faceOppositeCentroid_eq_smul_vsub` / 定理 `centroid_vsub_faceOppositeCentroid_eq_smul_vsub`

English:
theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub
  statement: [CharZero k]
  proof: by
  rw [point_vsub_centroid_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

中文:
定理 centroid_vsub_faceOppositeCentroid_eq_smul_vsub
  结论: [特征零 k]
  证明: by
  rw [point_vsub_centroid_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

Depends on / 依赖: NeZero, NeZero.ne, one_smul, point_vsub_centroid_eq_smul_vsub, smul_smul
-/
theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • (s.points i -ᵥ s.centroid) := by
  rw [point_vsub_centroid_eq_smul_vsub]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

/--
theorem `centroid_eq_smul_vsub_vadd_point` / 定理 `centroid_eq_smul_vsub_vadd_point`

English:
theorem centroid_eq_smul_vsub_vadd_point
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_vadd]

中文:
定理 centroid_eq_smul_vsub_vadd_point
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_vadd]

Depends on / 依赖: centroid_vsub_point_eq_smul_vsub, vsub_vadd
-/
theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_vadd]

/--
theorem `faceOppositeCentroid_eq_smul_vsub_vadd_point` / 定理 `faceOppositeCentroid_eq_smul_vsub_vadd_point`

English:
theorem faceOppositeCentroid_eq_smul_vsub_vadd_point
  statement: [CharZero k] (s : Simplex k P n)
  proof: by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [eq_vadd_iff_vsub_eq]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

中文:
定理 faceOppositeCentroid_eq_smul_vsub_vadd_point
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [eq_vadd_iff_vsub_eq]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

Depends on / 依赖: NeZero, NeZero.ne, centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, one_smul, smul_smul
-/
theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [centroid_vsub_point_eq_smul_vsub]; rw [eq_vadd_iff_vsub_eq]; rw [smul_smul]; rw [inv_mul_cancel₀ (NeZero.ne (n : k))]; rw [one_smul]

/--
theorem `faceOppositeCentroid_map` / 定理 `faceOppositeCentroid_map`

English:
theorem faceOppositeCentroid_map
  statement: [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂]
  proof: by
  simp only [faceOppositeCentroid, faceOpposite_map, centroid_eq_affineCombination, map_points]
  rw [Finset.map_affineCombination]
  rw [sum_centroidWeights_eq_one_of_card_ne_zero]
  simp

中文:
定理 faceOppositeCentroid_map
  结论: [特征零 k] {V₂ P₂ : 类型} [加法交换群 V₂]
  证明: by
  simp only [faceOppositeCentroid, faceOpposite_map, centroid_eq_affineCombination, map_points]
  rw [Finset.map_affineCombination]
  rw [sum_centroidWeights_eq_one_of_card_ne_zero]
  simp
-/
@[simp] theorem faceOppositeCentroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂]
    [Module k V₂] [AffineSpace V₂ P₂] {n : Nat} [NeZero n] (s : Simplex k P n) (f : P ->ᵃ[k] P₂)
    (hf : Function.Injective f) {i : Fin (n + 1)} :
    (s.map f hf).faceOppositeCentroid i = f (s.faceOppositeCentroid i) := by
  simp only [faceOppositeCentroid, faceOpposite_map, centroid_eq_affineCombination, map_points]
  rw [Finset.map_affineCombination]
  rw [sum_centroidWeights_eq_one_of_card_ne_zero]
  simp

/--
theorem `faceOppositeCentroid_restrict` / 定理 `faceOppositeCentroid_restrict`

English:
theorem faceOppositeCentroid_restrict
  statement: [CharZero k] (s : Simplex k P n)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOppositeCentroid i = s.faceOppositeCentroid i := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtyp

中文:
定理 faceOppositeCentroid_restrict
  结论: [特征零 k] (s : 单纯形 k P n)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOppositeCentroid i = s.faceOppositeCentroid i := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtyp
-/
@[simp] theorem faceOppositeCentroid_restrict [CharZero k] (s : Simplex k P n)
    (S : AffineSubspace k P) (hS : affineSpan k (Set.range s.points) <= S) {i : Fin (n + 1)} :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOppositeCentroid i = s.faceOppositeCentroid i := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.restrict S hS).faceOppositeCentroid_map S.subtype hf (i := i)

/--
theorem `faceOppositeCentroid_reindex` / 定理 `faceOppositeCentroid_reindex`

English:
theorem faceOppositeCentroid_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m)
  proof: by
  ext i
  rw [faceOppositeCentroid]
  obtain rfl : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
exact centroid_eq_of_range_eq Affine.Simplex.range_faceOpposite_reindex s e i

中文:
定理 faceOppositeCentroid_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n] (s : 单纯形 k P m)
  证明: by
  ext i
  rw [faceOppositeCentroid]
  obtain rfl : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
exact centroid_eq_of_range_eq Affine.Simplex.range_faceOpposite_reindex s e i
-/
@[simp] theorem faceOppositeCentroid_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).faceOppositeCentroid = s.faceOppositeCentroid ∘ e.symm := by
  ext i
  rw [faceOppositeCentroid]
  obtain rfl : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
exact centroid_eq_of_range_eq Affine.Simplex.range_faceOpposite_reindex s e i

section median

/--
Definition of `median` / `median` 的定义

English:
definition median
  signature: (s : Simplex k P n) (i : Fin (n + 1))
  body: line[k, s.points i, s.faceOppositeCentroid i]

中文:
定义 median
  签名: (s : 单纯形 k P n) (i : 有限集 (n + 1))
  定义体: line[k, s.points i, s.faceOppositeCentroid i]

Depends on / 依赖: faceOppositeCentroid, points, s.faceOppositeCentroid, s.points
-/
def median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P :=
  line[k, s.points i, s.faceOppositeCentroid i]

/--
theorem `median_reindex` / 定理 `median_reindex`

English:
theorem median_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P n)
  proof: by
  ext i
  simp [median]

@[simp]

中文:
定理 median_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n] (s : 单纯形 k P n)
  证明: by
  ext i
  simp [median]

@[simp]
-/
@[simp] theorem median_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).median = s.median ∘ e.symm := by
  ext i
  simp [median]

@[simp]
/--
theorem `median_map` / 定理 `median_map`

English:
theorem median_map
  statement: [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
  proof: by
  simp [median, map_span, Set.image_pair]

中文:
定理 median_map
  结论: [特征零 k] {V₂ P₂ : 类型} [加法交换群 V₂] [模 k V₂] [仿射空间 V₂ P₂]
  证明: by
  simp [median, map_span, Set.image_pair]

Depends on / 依赖: Set.image_pair, image_pair, map_span, median
-/
theorem median_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1))
    (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).median i = (s.median i).map f := by
  simp [median, map_span, Set.image_pair]

/--
theorem `median_restrict` / 定理 `median_restrict`

English:
theorem median_restrict
  statement: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) (S : AffineSubspace k P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    AffineSubspace.map (AffineSubspace.subtype S) ((s.restrict S hS).median i) = s.median i := by
  simp [median, map_span, Set.image_pair]

中文:
定理 median_restrict
  结论: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1)) (S : 仿射子空间 k P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    AffineSubspace.map (AffineSubspace.subtype S) ((s.restrict S hS).median i) = s.median i := by
  simp [median, map_span, Set.image_pair]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem median_restrict [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    AffineSubspace.map (AffineSubspace.subtype S) ((s.restrict S hS).median i) = s.median i := by
  simp [median, map_span, Set.image_pair]

/--
theorem `faceOppositeCentroid_mem_median` / 定理 `faceOppositeCentroid_mem_median`

English:
theorem faceOppositeCentroid_mem_median
  given: (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  simp [median, right_mem_affineSpan_pair]

中文:
定理 faceOppositeCentroid_mem_median
  条件: (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  simp [median, right_mem_affineSpan_pair]

Depends on / 依赖: median, right_mem_affineSpan_pair
-/
theorem faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i in s.median i := by
  simp [median, right_mem_affineSpan_pair]

/--
theorem `point_mem_median` / 定理 `point_mem_median`

English:
theorem point_mem_median
  given: (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  simp [median, left_mem_affineSpan_pair]

中文:
定理 point_mem_median
  条件: (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  simp [median, left_mem_affineSpan_pair]

Depends on / 依赖: left_mem_affineSpan_pair, median
-/
theorem point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i in s.median i := by
  simp [median, left_mem_affineSpan_pair]

/--
theorem `centroid_mem_median` / 定理 `centroid_mem_median`

English:
theorem centroid_mem_median
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  rw [median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq]; rw [centroid_vsub_point_eq_smul_vsub]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [one_div]; rw [mul_assoc]; 

中文:
定理 centroid_mem_median
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  rw [median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq]; rw [centroid_vsub_point_eq_smul_vsub]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [one_div]; rw [mul_assoc]; 

Depends on / 依赖: centroid, centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, faceOppositeCentroid, faceOppositeCentroid_vsub_point_eq_smul_vsub, median, mul_assoc, mul_one, one_div, points, s.centroid, s.faceOppositeCentroid, s.points, smul_smul, smul_vsub_vadd_mem_affineSpan_pair
-/
theorem centroid_mem_median [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid in s.median i := by
  rw [median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq]; rw [centroid_vsub_point_eq_smul_vsub]; rw [faceOppositeCentroid_vsub_point_eq_smul_vsub]; rw [smul_smul]; rw [one_div]; rw [mul_assoc]; rw [inv_mul_cancel₀ (by norm_cast)]; rw [mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

/--
theorem `median_eq_line_point_centroid` / 定理 `median_eq_line_point_centroid`

English:
theorem median_eq_line_point_centroid
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  have h1 : s.median i <= line[k, s.points i, s.centroid] := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw 

中文:
定理 median_eq_line_point_centroid
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  have h1 : s.median i <= line[k, s.points i, s.centroid] := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw 

Depends on / 依赖: affineSpan_pair_le_of_right_mem, centroid, faceOppositeCentroid_eq_smul_vsub_vadd_point, inv_eq_one_div, median, mul_neg_one, neg_div, neg_vsub_eq_vsub_rev, points, s.centroid, s.median, s.points, smul_smul, smul_vsub_rev_vadd_mem
-/
theorem median_eq_line_point_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.median i = line[k, s.points i, s.centroid] := by
  have h1 : s.median i <= line[k, s.points i, s.centroid] := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw [← neg_vsub_eq_vsub_rev]
      have : -(s.points i -ᵥ s.centroid) = (-1 : k) • (s.points i -ᵥ s.centroid) := by simp
      rw [this]; rw [smul_smul]
      congr 1
      rw [mul_neg_one]; rw [inv_eq_one_div]; rw [neg_div]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : line[k, s.points i, s.centroid] <= s.median i := by
    rw [median]
    apply affineSpan_pair_le_of_right_mem
    exact centroid_mem_median s i
  exact le_antisymm h1 h2

/--
theorem `eq_centroid_of_forall_mem_median` / 定理 `eq_centroid_of_forall_mem_median`

English:
theorem eq_centroid_of_forall_mem_median
  statement: [CharZero k] (s : Simplex k P n) {hn : 1 < n} {p : P}
  proof: by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n + 1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' -> V := fun i => s.points i -ᵥ s.centroid
  have h_span : forall i : s', p -ᵥ s.centroid in (Submodule.span k ({u i} 

中文:
定理 eq_centroid_of_对任意_mem_median
  结论: [特征零 k] (s : 单纯形 k P n) {hn : 1 < n} {p : P}
  证明: by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n + 1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' -> V := fun i => s.points i -ᵥ s.centroid
  have h_span : forall i : s', p -ᵥ s.centroid in (Submodule.span k ({u i} 

Depends on / 依赖: Finset, LinearIndependent, Submodule, Submodule.mem_span_singleton_self, Submodule.smul_mem, Submodule.span, centroid, h_span, median_eq_line_point_centroid, mem_span_singleton_self, points, s.centroid, s.points, smul_mem, vadd_right_mem_affineSpan_pair, vsub_eq_zero_iff_eq, vsub_vadd
-/
theorem eq_centroid_of_forall_mem_median [CharZero k] (s : Simplex k P n) {hn : 1 < n} {p : P}
    (h : forall i, p in s.median i) :
    p = s.centroid := by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n + 1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' -> V := fun i => s.points i -ᵥ s.centroid
  have h_span : forall i : s', p -ᵥ s.centroid in (Submodule.span k ({u i} : Set V)) := by
    intro i
    have hi := h i
    grind only [median_eq_line_point_centroid, vadd_right_mem_affineSpan_pair,
      Submodule.smul_mem, Submodule.mem_span_singleton_self]
  have hi : LinearIndependent k u := by
    set p : Fin (n + 1) -> P := fun x => if x = i₀ then s.centroid else s.points x
    have hindep : AffineIndependent k p := by
      have := affineIndependent_points_update_centroid s i₀
      unfold Function.update at this
      grind
    have h1 := (affineIndependent_iff_linearIndependent_vsub k p i₀).mp hindep
    simp_rw [ne_eq, p] at h1
    set f : {x // x in ({i₀}ᶜ : Finset (Fin (n + 1)))} -> {x // x != i₀} :=
      have h (x : {x // x in ({i₀}ᶜ : Finset (Fin (n + 1)))}) : x.val != i₀ := by
        grind [mem_compl, Finset.notMem_singleton]
      fun x => ⟨x.val, h x⟩
    have f_inj : Function.Injective f := by intro x y hxy; grind
    have h2 := h1.comp f f_inj
    convert! h2 using 1
    grind only [mem_compl, Finset.notMem_singleton]
  have he : exists i j : s', i != j := by
    simp only [ne_eq, Subtype.exists, Subtype.mk.injEq, exists_prop]
    have hcard : s'.card = n := by
      rw [Finset.card_compl]; rw [Fintype.card_fin]; rw [card_singleton]; rw [add_tsub_cancel_right]
    have hcard' : 1 < #s' := by grind
    rw [Finset.one_lt_card_iff] at hcard'
    tauto
  choose i j hij using he
  have h_ij : Disjoint ({i} : Set {x // x in s'}) {j} := by simp [hij]
  have h_disjoint : Disjoint (Submodule.span k {u i}) (Submodule.span k {u j}) := by
    simp_rw [← Set.image_singleton, hi.disjoint_span_image h_ij]
  exact Submodule.disjoint_def.1 h_disjoint _ (h_span i) (h_span j)

end median

/--
Definition of `medial` / `medial` 的定义

English:
definition medial
  signature: [CharZero k] (s : Simplex k P n)
  body: s.faceOppositeCentroid i
  independent := by
    obtain h := s.independent
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0] at h ⊢
    simp_rw [faceOppositeCentroid_vsub_faceOppositeCentroid]
    convert! h.units_smul fun _ => Units.mk0 (-n)⁻¹ (by simpa using NeZero.ne n) with i
    simp 

中文:
定义 medial
  签名: [特征零 k] (s : 单纯形 k P n)
  定义体: s.faceOppositeCentroid i
  independent := by
    obtain h := s.independent
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0] at h ⊢
    simp_rw [faceOppositeCentroid_vsub_faceOppositeCentroid]
    convert! h.units_smul fun _ => Units.mk0 (-n)⁻¹ (by simpa using NeZero.ne n) with i
    simp 

Depends on / 依赖: faceOppositeCentroid, s.faceOppositeCentroid
-/
def medial [CharZero k] (s : Simplex k P n) : Simplex k P n where
  points i := s.faceOppositeCentroid i
  independent := by
    obtain h := s.independent
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0] at h ⊢
    simp_rw [faceOppositeCentroid_vsub_faceOppositeCentroid]
    convert! h.units_smul fun _ => Units.mk0 (-n)⁻¹ (by simpa using NeZero.ne n) with i
    simp [← smul_neg]

/--
theorem `medial_points` / 定理 `medial_points`

English:
theorem medial_points
  given: [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
  proof: rfl

中文:
定理 medial_points
  条件: [特征零 k] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: rfl
-/
theorem medial_points [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.medial.points i = s.faceOppositeCentroid i := rfl

/--
theorem `medial_reindex` / 定理 `medial_reindex`

English:
theorem medial_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n]
  proof: by
  ext i
  simp [medial_points]

中文:
定理 medial_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n]
  证明: by
  ext i
  simp [medial_points]

Depends on / 依赖: medial_points
-/
theorem medial_reindex {m n : Nat} [NeZero m] [NeZero n]
    [CharZero k] (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).medial = s.medial.reindex e := by
  ext i
  simp [medial_points]

/--
theorem `medial_map` / 定理 `medial_map`

English:
theorem medial_map
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] [CharZero k]
  proof: by
  ext i
  simp [medial_points]

中文:
定理 medial_map
  结论: {V₂ P₂ : 类型} [加法交换群 V₂] [模 k V₂] [仿射空间 V₂ P₂] [特征零 k]
  证明: by
  ext i
  simp [medial_points]

Depends on / 依赖: medial_points
-/
theorem medial_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] [CharZero k]
    {n : Nat} [NeZero n] (s : Simplex k P n)
    (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).medial = s.medial.map f hf := by
  ext i
  simp [medial_points]

open scoped Pointwise in
@[simp]
/--
theorem `affineSpan_range_medial` / 定理 `affineSpan_range_medial`

English:
theorem affineSpan_range_medial
  given: [CharZero k] (s : Simplex k P n)
  proof: by
  have hmem1 : s.medial.points 0 in affineSpan k (Set.range s.medial.points) :=
    mem_affineSpan _ (by simp)
  have hmem2 : s.medial.points 0 in affineSpan k (Set.range s.points) := by
    apply Set.mem_of_mem_of_subset (s.faceOppositeCentroid_mem_affineSpan_face 0)
    exact affineSpan_mono k 

中文:
定理 affineSpan_range_medial
  条件: [特征零 k] (s : 单纯形 k P n)
  证明: by
  have hmem1 : s.medial.points 0 in affineSpan k (Set.range s.medial.points) :=
    mem_affineSpan _ (by simp)
  have hmem2 : s.medial.points 0 in affineSpan k (Set.range s.points) := by
    apply Set.mem_of_mem_of_subset (s.faceOppositeCentroid_mem_affineSpan_face 0)
    exact affineSpan_mono k 

Depends on / 依赖: Set.mem_of_mem_of_subset, Set.range, affineSpan, affineSpan_mono, direction_affineSpan, eq_iff_direction_eq_of_mem, faceOppositeCentroid_mem_affineSpan_face, medial, mem_affineSpan, mem_of_mem_of_subset, points, s.faceOppositeCentroid_mem_affineSpan_face, s.medial.points, s.points, simp_rw, vectorSpan_def
-/
theorem affineSpan_range_medial [CharZero k] (s : Simplex k P n) :
    affineSpan k (Set.range (s.medial.points)) = affineSpan k (Set.range (s.points)) := by
  have hmem1 : s.medial.points 0 in affineSpan k (Set.range s.medial.points) :=
    mem_affineSpan _ (by simp)
  have hmem2 : s.medial.points 0 in affineSpan k (Set.range s.points) := by
    apply Set.mem_of_mem_of_subset (s.faceOppositeCentroid_mem_affineSpan_face 0)
    exact affineSpan_mono k (by simp)
  rw [eq_iff_direction_eq_of_mem hmem1 hmem2]
  simp_rw [direction_affineSpan, vectorSpan_def]
  suffices Set.range s.medial.points -ᵥ Set.range s.medial.points
    = (-n : k)⁻¹ • (Set.range s.points -ᵥ Set.range s.points) by
    rw [this]; rw [Submodule.span_smul_eq_of_isUnit]
    simpa using NeZero.ne n
  ext v
  suffices (exists a b, (n : k)⁻¹ • (s.points b -ᵥ s.points a) = v) ↔
    exists a b, -((n : k)⁻¹ • (s.points a -ᵥ s.points b)) = v by
    simpa [Set.mem_vsub, Set.mem_smul_set, medial_points,
      faceOppositeCentroid_vsub_faceOppositeCentroid]
  congrm exists a b, ?_ = v
  simp [← smul_neg]

/--
theorem `medial_restrict` / 定理 `medial_restrict`

English:
theorem medial_restrict
  statement: [CharZero k] (s : Simplex k P n) (S : AffineSubspace k P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (s.affineSpan_range_medial ▸ hS) := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [medial_points]

中文:
定理 medial_restrict
  结论: [特征零 k] (s : 单纯形 k P n) (S : 仿射子空间 k P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (s.affineSpan_range_medial ▸ hS) := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [medial_points]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem medial_restrict [CharZero k] (s : Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (s.affineSpan_range_medial ▸ hS) := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [medial_points]

end Simplex

end Affine
