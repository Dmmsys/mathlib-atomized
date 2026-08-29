/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.Circumcenter

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `mongePoint` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `mongePlane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

* `OrthocentricSystem` is a predicate on sets of points that says
  whether they are four points, one of which is the orthocenter of the
  other three (in which case various other properties hold, including
  that each is the orthocenter of the other three).

## References

* <https://en.wikipedia.org/wiki/Monge_point>
* <https://en.wikipedia.org/wiki/Orthocentric_system>
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry PointsWithCircumcenterIndex

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
Definition of `mongePoint` / `mongePoint` 的定义

English:
definition mongePoint
  signature: {n : Nat} (s : Simplex Real P n)
  body: (((n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)) •
      ((univ : Finset (Fin (n + 1))).centroid Real s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter

中文:
定义 mongePoint
  签名: {n : 自然数} (s : 单纯形 实数 P n)
  定义体: (((n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)) •
      ((univ : Finset (Fin (n + 1))).centroid Real s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter

Depends on / 依赖: Finset, centroid, circumcenter, points, s.circumcenter, s.points
-/
def mongePoint {n : Nat} (s : Simplex Real P n) : P :=
  (((n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)) •
      ((univ : Finset (Fin (n + 1))).centroid Real s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter

/--
theorem `mongePoint_eq_smul_vsub_vadd_circumcenter` / 定理 `mongePoint_eq_smul_vsub_vadd_circumcenter`

English:
theorem mongePoint_eq_smul_vsub_vadd_circumcenter
  given: {n : Nat} (s : Simplex Real P n)
  proof: rfl

中文:
定理 mongePoint_eq_smul_vsub_vadd_circumcenter
  条件: {n : 自然数} (s : 单纯形 实数 P n)
  证明: rfl
-/
theorem mongePoint_eq_smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n) :
    s.mongePoint =
      (((n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)) •
          ((univ : Finset (Fin (n + 1))).centroid Real s.points -ᵥ s.circumcenter) +ᵥ
        s.circumcenter :=
  rfl

/--
lemma `mongePoint_reindex` / 引理 `mongePoint_reindex`

English:
lemma mongePoint_reindex
  given: {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  simp_rw [mongePoint, circumcenter_reindex, centroid_def, reindex]
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  congr 3
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

中文:
引理 mongePoint_reindex
  条件: {m n : 自然数} (s : 单纯形 实数 P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  simp_rw [mongePoint, circumcenter_reindex, centroid_def, reindex]
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  congr 3
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]
-/
@[simp] lemma mongePoint_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).mongePoint = s.mongePoint := by
  simp_rw [mongePoint, circumcenter_reindex, centroid_def, reindex]
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  congr 3
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mongePoint_map` / 定理 `mongePoint_map`

English:
theorem mongePoint_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
  proof: by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_map, circumcenter_map]

中文:
定理 mongePoint_map
  结论: {V₂ P₂ : 类型} [赋范交换加群 V₂] [内积空间 实数 V₂]
  证明: by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_map, circumcenter_map]

Depends on / 依赖: Simplex, Simplex.centroid, centroid, centroid_map, circumcenter_map, mongePoint_eq_smul_vsub_vadd_circumcenter, simp_rw
-/
theorem mongePoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).mongePoint = f s.mongePoint := by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_map, circumcenter_map]

/--
theorem `smul_mongePoint_vsub_circumcenter_eq_sum_vsub` / 定理 `smul_mongePoint_vsub_circumcenter_eq_sum_vsub`

English:
theorem smul_mongePoint_vsub_circumcenter_eq_sum_vsub
  given: {n : Nat} (s : Simplex Real P (n + 2))
  proof: by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [vadd_vsub]; rw [← smul_assoc]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.add_one_sub_one, nsmul_eq_mul]
  field_simp
  have h : Invertible (n + 2 + 1 : Real) := by norm_cast; apply invertibleOfPos
  rw [smul_eq_iff_eq_invOf_smul]; rw [smul_sum]
  rw [univ_centroid_eq]; rw [centroid_eq_affineCombination]
  rw [← Finset.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ (by simp)]
  simp only [centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, invOf_eq_inv]

中文:
定理 smul_mongePoint_vsub_circumcenter_eq_sum_vsub
  条件: {n : 自然数} (s : 单纯形 实数 P (n + 2))
  证明: by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [vadd_vsub]; rw [← smul_assoc]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.add_one_sub_one, nsmul_eq_mul]
  field_simp
  have h : Invertible (n + 2 + 1 : Real) := by norm_cast; apply invertibleOfPos
  rw [smul_eq_iff_eq_invOf_smul]; rw [smul_sum]
  rw [univ_centroid_eq]; rw [centroid_eq_affineCombination]
  rw [← Finset.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ (by simp)]
  simp only [centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, invOf_eq_inv]

Depends on / 依赖: Finset, Finset.sum_smul_vsub_const_eq_affineCombination_vsub, Fintype, Fintype.c, Invertible, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_one_sub_one, card_univ, cast_add, cast_ofNat, cast_one, centroidWeights_apply, centroid_eq_affineCombination, invertibleOfPos, mongePoint_eq_smul_vsub_vadd_circumcenter, nsmul_eq_mul, smul_assoc
-/
theorem smul_mongePoint_vsub_circumcenter_eq_sum_vsub {n : Nat} (s : Simplex Real P (n + 2)) :
    (n + 1) • (s.mongePoint -ᵥ s.circumcenter) = ∑ i, (s.points i -ᵥ s.circumcenter) := by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [vadd_vsub]; rw [← smul_assoc]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.add_one_sub_one, nsmul_eq_mul]
  field_simp
  have h : Invertible (n + 2 + 1 : Real) := by norm_cast; apply invertibleOfPos
  rw [smul_eq_iff_eq_invOf_smul]; rw [smul_sum]
  rw [univ_centroid_eq]; rw [centroid_eq_affineCombination]
  rw [← Finset.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ (by simp)]
  simp only [centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, invOf_eq_inv]

/--
theorem `mongePoint_mem_affineSpan` / 定理 `mongePoint_mem_affineSpan`

English:
theorem mongePoint_mem_affineSpan
  given: {n : Nat} (s : Simplex Real P n)
  proof: smul_vsub_vadd_mem _ _ (centroid_mem_affineSpan_of_card_eq_add_one Real _ (card_fin (n + 1)))
    s.circumcenter_mem_affineSpan s.circumcenter_mem_affineSpan

@[simp]

中文:
定理 mongePoint_mem_affineSpan
  条件: {n : 自然数} (s : 单纯形 实数 P n)
  证明: smul_vsub_vadd_mem _ _ (centroid_mem_affineSpan_of_card_eq_add_one Real _ (card_fin (n + 1)))
    s.circumcenter_mem_affineSpan s.circumcenter_mem_affineSpan

@[simp]

Depends on / 依赖: card_fin, centroid_mem_affineSpan_of_card_eq_add_one, circumcenter_mem_affineSpan, s.circumcenter_mem_affineSpan, smul_vsub_vadd_mem
-/
theorem mongePoint_mem_affineSpan {n : Nat} (s : Simplex Real P n) :
    s.mongePoint in affineSpan Real (Set.range s.points) :=
  smul_vsub_vadd_mem _ _ (centroid_mem_affineSpan_of_card_eq_add_one Real _ (card_fin (n + 1)))
    s.circumcenter_mem_affineSpan s.circumcenter_mem_affineSpan

@[simp]
/--
theorem `mongePoint_restrict` / 定理 `mongePoint_restrict`

English:
theorem mongePoint_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).mongePoint = s.mongePoint := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  simp_rw [mongePoint]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_restrict, circumcenter_restrict]

中文:
定理 mongePoint_restrict
  结论: {n : 自然数} (s : 单纯形 实数 P n) (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).mongePoint = s.mongePoint := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  simp_rw [mongePoint]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_restrict, circumcenter_restrict]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem mongePoint_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).mongePoint = s.mongePoint := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  simp_rw [mongePoint]
  rw [← Simplex.centroid]; rw [← Simplex.centroid]
  simp [centroid_restrict, circumcenter_restrict]

/--
theorem `mongePoint_eq_of_range_eq` / 定理 `mongePoint_eq_of_range_eq`

English:
theorem mongePoint_eq_of_range_eq
  statement: {n : Nat} {s₁ s₂ : Simplex Real P n}
  proof: by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
    circumcenter_eq_of_range_eq h]

中文:
定理 mongePoint_eq_of_range_eq
  结论: {n : 自然数} {s₁ s₂ : 单纯形 实数 P n}
  证明: by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
    circumcenter_eq_of_range_eq h]

Depends on / 依赖: centroid_eq_of_range_eq, circumcenter_eq_of_range_eq, mongePoint_eq_smul_vsub_vadd_circumcenter, simp_rw
-/
theorem mongePoint_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex Real P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.mongePoint = s₂.mongePoint := by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
    circumcenter_eq_of_range_eq h]

/--
Definition of `mongePointWeightsWithCircumcenter` / `mongePointWeightsWithCircumcenter` 的定义

English:
definition mongePointWeightsWithCircumcenter
  signature: (n : Nat)

中文:
定义 mongePointWeightsWithCircumcenter
  签名: (n : 自然数)
-/
def mongePointWeightsWithCircumcenter (n : Nat) : PointsWithCircumcenterIndex (n + 2) -> Real
  | pointIndex _ => ((n + 1 : Nat) : Real)⁻¹
  | circumcenterIndex => -2 / ((n + 1 : Nat) : Real)

/-- `mongePointWeightsWithCircumcenter` sums to 1. -/
@[simp]
/--
theorem `sum_mongePointWeightsWithCircumcenter` / 定理 `sum_mongePointWeightsWithCircumcenter`

English:
theorem sum_mongePointWeightsWithCircumcenter
  given: (n : Nat)
  proof: by
  simp_rw [sum_pointsWithCircumcenter, mongePointWeightsWithCircumcenter, sum_const, card_fin,
    nsmul_eq_mul]
  simp [field]
  ring

中文:
定理 sum_mongePointWeightsWithCircumcenter
  条件: (n : 自然数)
  证明: by
  simp_rw [sum_pointsWithCircumcenter, mongePointWeightsWithCircumcenter, sum_const, card_fin,
    nsmul_eq_mul]
  simp [field]
  ring

Depends on / 依赖: card_fin, mongePointWeightsWithCircumcenter, nsmul_eq_mul, simp_rw, sum_const, sum_pointsWithCircumcenter
-/
theorem sum_mongePointWeightsWithCircumcenter (n : Nat) :
    ∑ i, mongePointWeightsWithCircumcenter n i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, mongePointWeightsWithCircumcenter, sum_const, card_fin,
    nsmul_eq_mul]
  simp [field]
  ring

/--
theorem `mongePoint_eq_affineCombination_of_pointsWithCircumcenter` / 定理 `mongePoint_eq_affineCombination_of_pointsWithCircumcenter`

English:
theorem mongePoint_eq_affineCombination_of_pointsWithCircumcenter
  statement: {n : Nat}
  proof: by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [centroid_eq_affineCombination_of_pointsWithCircumcenter]; rw [circumcenter_eq_affineCombination_of_pointsWithCircumcenter]; rw [affineCombination_vsub]; rw [← map_smul]; rw [weightedVSub_vadd_affineCombination]
  congr with i
  rw [Pi.add_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [Pi.sub_apply]
  cases i <;>
      simp_rw [centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
        mongePointWeightsWithCircumcenter] <;>
    rw [add_tsub_assoc_of_le (by decide : 1 <= 2)]; rw [(by decide : 2 - 1 = 1)]
  · rw [if_pos (mem_univ _), card_fin]
    field
  · simp [field]
    ring

中文:
定理 mongePoint_eq_affineCombination_of_pointsWithCircumcenter
  结论: {n : 自然数}
  证明: by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [centroid_eq_affineCombination_of_pointsWithCircumcenter]; rw [circumcenter_eq_affineCombination_of_pointsWithCircumcenter]; rw [affineCombination_vsub]; rw [← map_smul]; rw [weightedVSub_vadd_affineCombination]
  congr with i
  rw [Pi.add_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [Pi.sub_apply]
  cases i <;>
      simp_rw [centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
        mongePointWeightsWithCircumcenter] <;>
    rw [add_tsub_assoc_of_le (by decide : 1 <= 2)]; rw [(by decide : 2 - 1 = 1)]
  · rw [if_pos (mem_univ _), card_fin]
    field
  · simp [field]
    ring

Depends on / 依赖: Pi.add_apply, Pi.smul_apply, Pi.sub_apply, add_apply, add_tsub_ass, affineCombination_vsub, centroidWeightsWithCircumcenter, centroid_eq_affineCombination_of_pointsWithCircumcenter, circumcenterWeightsWithCircumcenter, circumcenter_eq_affineCombination_of_pointsWithCircumcenter, map_smul, mongePointWeightsWithCircumcenter, mongePoint_eq_smul_vsub_vadd_circumcenter, simp_rw, smul_apply, smul_eq_mul, sub_apply, weightedVSub_vadd_affineCombination
-/
theorem mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : Nat}
    (s : Simplex Real P (n + 2)) :
    s.mongePoint =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).affineCombination Real
        s.pointsWithCircumcenter (mongePointWeightsWithCircumcenter n) := by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [centroid_eq_affineCombination_of_pointsWithCircumcenter]; rw [circumcenter_eq_affineCombination_of_pointsWithCircumcenter]; rw [affineCombination_vsub]; rw [← map_smul]; rw [weightedVSub_vadd_affineCombination]
  congr with i
  rw [Pi.add_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [Pi.sub_apply]
  cases i <;>
      simp_rw [centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
        mongePointWeightsWithCircumcenter] <;>
    rw [add_tsub_assoc_of_le (by decide : 1 <= 2)]; rw [(by decide : 2 - 1 = 1)]
  · rw [if_pos (mem_univ _), card_fin]
    field
  · simp [field]
    ring

/--
Definition of `mongePointVSubFaceCentroidWeightsWithCircumcenter` / `mongePointVSubFaceCentroidWeightsWithCircumcenter` 的定义

English:
definition mongePointVSubFaceCentroidWeightsWithCircumcenter
  signature: {n : Nat} (i₁ i₂ : Fin (n + 3))

中文:
定义 mongePointVSubFaceCentroidWeightsWithCircumcenter
  签名: {n : 自然数} (i₁ i₂ : 有限集 (n + 3))
-/
def mongePointVSubFaceCentroidWeightsWithCircumcenter {n : Nat} (i₁ i₂ : Fin (n + 3)) :
    PointsWithCircumcenterIndex (n + 2) -> Real
  | pointIndex i => if i = i₁ ∨ i = i₂ then ((n + 1 : Nat) : Real)⁻¹ else 0
  | circumcenterIndex => -2 / ((n + 1 : Nat) : Real)

/--
theorem `mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub` / 定理 `mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub`

English:
theorem mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub
  statement: {n : Nat} {i₁ i₂ : Fin (n + 3)}
  proof: by
  ext i
  obtain i | i := i
  · rw [Pi.sub_apply, mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]
    have hu : #{i₁, i₂}ᶜ = n + 1 := by
      simp [card_compl, Fintype.card_fin, h]
    rw [hu]
    by_cases hi : i = i₁ ∨ i = i₂ <;> simp [compl_eq_univ_sdiff, hi]
  · simp [mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]

中文:
定理 mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub
  结论: {n : 自然数} {i₁ i₂ : 有限集 (n + 3)}
  证明: by
  ext i
  obtain i | i := i
  · rw [Pi.sub_apply, mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]
    have hu : #{i₁, i₂}ᶜ = n + 1 := by
      simp [card_compl, Fintype.card_fin, h]
    rw [hu]
    by_cases hi : i = i₁ ∨ i = i₂ <;> simp [compl_eq_univ_sdiff, hi]
  · simp [mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]

Depends on / 依赖: Fintype, Fintype.card_fin, Pi.sub_apply, card_compl, card_fin, centroidWeightsWithCircumcenter, compl_eq_univ_sdiff, mongePointVSubFaceCentroidWeightsWithCircumcenter, mongePointWeightsWithCircumcenter, sub_apply
-/
theorem mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub {n : Nat} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ != i₂) :
    mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂ =
      mongePointWeightsWithCircumcenter n - centroidWeightsWithCircumcenter {i₁, i₂}ᶜ := by
  ext i
  obtain i | i := i
  · rw [Pi.sub_apply, mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]
    have hu : #{i₁, i₂}ᶜ = n + 1 := by
      simp [card_compl, Fintype.card_fin, h]
    rw [hu]
    by_cases hi : i = i₁ ∨ i = i₂ <;> simp [compl_eq_univ_sdiff, hi]
  · simp [mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]

/-- `mongePointVSubFaceCentroidWeightsWithCircumcenter` sums to 0. -/
@[simp]
/--
theorem `sum_mongePointVSubFaceCentroidWeightsWithCircumcenter` / 定理 `sum_mongePointVSubFaceCentroidWeightsWithCircumcenter`

English:
theorem sum_mongePointVSubFaceCentroidWeightsWithCircumcenter
  statement: {n : Nat} {i₁ i₂ : Fin (n + 3)}
  proof: by
  rw [mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]
  simp_rw [Pi.sub_apply, sum_sub_distrib, sum_mongePointWeightsWithCircumcenter]
  rw [sum_centroidWeightsWithCircumcenter]; rw [sub_self]
  simp [← card_pos, card_compl, h]

中文:
定理 sum_mongePointVSubFaceCentroidWeightsWithCircumcenter
  结论: {n : 自然数} {i₁ i₂ : 有限集 (n + 3)}
  证明: by
  rw [mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]
  simp_rw [Pi.sub_apply, sum_sub_distrib, sum_mongePointWeightsWithCircumcenter]
  rw [sum_centroidWeightsWithCircumcenter]; rw [sub_self]
  simp [← card_pos, card_compl, h]

Depends on / 依赖: Pi.sub_apply, card_compl, card_pos, mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub, simp_rw, sub_apply, sub_self, sum_centroidWeightsWithCircumcenter, sum_mongePointWeightsWithCircumcenter, sum_sub_distrib
-/
theorem sum_mongePointVSubFaceCentroidWeightsWithCircumcenter {n : Nat} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ != i₂) : ∑ i, mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂ i = 0 := by
  rw [mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]
  simp_rw [Pi.sub_apply, sum_sub_distrib, sum_mongePointWeightsWithCircumcenter]
  rw [sum_centroidWeightsWithCircumcenter]; rw [sub_self]
  simp [← card_pos, card_compl, h]

/--
theorem `mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter` / 定理 `mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter`

English:
theorem mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter
  statement: {n : Nat}
  proof: by
  simp_rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter,
    centroid_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub,
    mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]

中文:
定理 mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter
  结论: {n : 自然数}
  证明: by
  simp_rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter,
    centroid_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub,
    mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]

Depends on / 依赖: affineCombination_vsub, centroid_eq_affineCombination_of_pointsWithCircumcenter, mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub, mongePoint_eq_affineCombination_of_pointsWithCircumcenter, simp_rw
-/
theorem mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter {n : Nat}
    (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} (h : i₁ != i₂) :
    s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).weightedVSub s.pointsWithCircumcenter
        (mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂) := by
  simp_rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter,
    centroid_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub,
    mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]

/--
theorem `inner_mongePoint_vsub_face_centroid_vsub` / 定理 `inner_mongePoint_vsub_face_centroid_vsub`

English:
theorem inner_mongePoint_vsub_face_centroid_vsub
  statement: {n : Nat} (s : Simplex Real P (n + 2))
  proof: by
  by_cases h : i₁ = i₂
  · simp [h]
  simp_rw [mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter s h,
    point_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub]
  have hs : ∑ i, (pointWeightsWithCircumcenter i₁ - pointWeightsWithCircumcenter i₂) i = 0 := by
    simp
  rw [inner_weightedVSub _ (sum_mongePointVSubFaceCentroidWeightsWithCircumcenter h) _ hs]; rw [sum_pointsWithCircumcenter]; rw [pointsWithCircumcenter_eq_circumcenter]
  simp only [mongePointVSubFaceCentroidWeightsWithCircumcenter, pointsWithCircumcenter_point]
  let fs : Finset (Fin (n + 3)) := {i₁, i₂}
  have hfs : forall i : Fin (n + 3), i ∉ fs -> i != i₁ ∧ i != i₂ := by
    intro i hi
    constructor <;> · intro hj; simp [fs, ← hj] at hi
  rw [← sum_subset fs.subset_univ _]
  · simp_rw [sum_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter,
      pointsWithCircumcenter_point, Pi.sub_apply, pointWeightsWithCircumcenter]
    rw [← sum_subset fs.subset_univ _]
    · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
      repeat rw [← sum_subset fs.subset_univ _]
      · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
        simp [h, Ne.symm h, dist_comm (s.points i₁)]
      all_goals intro i _ hi; simp [hfs i hi]
    · intro i _ hi
      simp [hfs i hi]
  · intro i _ hi
    simp [hfs i hi]

中文:
定理 inner_mongePoint_vsub_face_centroid_vsub
  结论: {n : 自然数} (s : 单纯形 实数 P (n + 2))
  证明: by
  by_cases h : i₁ = i₂
  · simp [h]
  simp_rw [mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter s h,
    point_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub]
  have hs : ∑ i, (pointWeightsWithCircumcenter i₁ - pointWeightsWithCircumcenter i₂) i = 0 := by
    simp
  rw [inner_weightedVSub _ (sum_mongePointVSubFaceCentroidWeightsWithCircumcenter h) _ hs]; rw [sum_pointsWithCircumcenter]; rw [pointsWithCircumcenter_eq_circumcenter]
  simp only [mongePointVSubFaceCentroidWeightsWithCircumcenter, pointsWithCircumcenter_point]
  let fs : Finset (Fin (n + 3)) := {i₁, i₂}
  have hfs : forall i : Fin (n + 3), i ∉ fs -> i != i₁ ∧ i != i₂ := by
    intro i hi
    constructor <;> · intro hj; simp [fs, ← hj] at hi
  rw [← sum_subset fs.subset_univ _]
  · simp_rw [sum_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter,
      pointsWithCircumcenter_point, Pi.sub_apply, pointWeightsWithCircumcenter]
    rw [← sum_subset fs.subset_univ _]
    · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
      repeat rw [← sum_subset fs.subset_univ _]
      · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
        simp [h, Ne.symm h, dist_comm (s.points i₁)]
      all_goals intro i _ hi; simp [hfs i hi]
    · intro i _ hi
      simp [hfs i hi]
  · intro i _ hi
    simp [hfs i hi]

Depends on / 依赖: affineCombination_vsub, inner_weightedVSub, mongePointVSubFaceCentr, mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter, pointWeightsWithCircumcenter, point_eq_affineCombination_of_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter, simp_rw, sum_mongePointVSubFaceCentroidWeightsWithCircumcenter, sum_pointsWithCircumcenter
-/
theorem inner_mongePoint_vsub_face_centroid_vsub {n : Nat} (s : Simplex Real P (n + 2))
    {i₁ i₂ : Fin (n + 3)} :
    ⟪s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points,
        s.points i₁ -ᵥ s.points i₂⟫ =
      0 := by
  by_cases h : i₁ = i₂
  · simp [h]
  simp_rw [mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter s h,
    point_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub]
  have hs : ∑ i, (pointWeightsWithCircumcenter i₁ - pointWeightsWithCircumcenter i₂) i = 0 := by
    simp
  rw [inner_weightedVSub _ (sum_mongePointVSubFaceCentroidWeightsWithCircumcenter h) _ hs]; rw [sum_pointsWithCircumcenter]; rw [pointsWithCircumcenter_eq_circumcenter]
  simp only [mongePointVSubFaceCentroidWeightsWithCircumcenter, pointsWithCircumcenter_point]
  let fs : Finset (Fin (n + 3)) := {i₁, i₂}
  have hfs : forall i : Fin (n + 3), i ∉ fs -> i != i₁ ∧ i != i₂ := by
    intro i hi
    constructor <;> · intro hj; simp [fs, ← hj] at hi
  rw [← sum_subset fs.subset_univ _]
  · simp_rw [sum_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter,
      pointsWithCircumcenter_point, Pi.sub_apply, pointWeightsWithCircumcenter]
    rw [← sum_subset fs.subset_univ _]
    · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
      repeat rw [← sum_subset fs.subset_univ _]
      · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
        simp [h, Ne.symm h, dist_comm (s.points i₁)]
      all_goals intro i _ hi; simp [hfs i hi]
    · intro i _ hi
      simp [hfs i hi]
  · intro i _ hi
    simp [hfs i hi]

/--
Definition of `mongePlane` / `mongePlane` 的定义

English:
definition mongePlane
  signature: {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3))
  body: mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points) (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
    affineSpan Real (Set.range s.points)

中文:
定义 mongePlane
  签名: {n : 自然数} (s : 单纯形 实数 P (n + 2)) (i₁ i₂ : 有限集 (n + 3))
  定义体: mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points) (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
    affineSpan Real (Set.range s.points)

Depends on / 依赖: Finset, Set.range, affineSpan, centroid, points, s.points
-/
def mongePlane {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3)) : AffineSubspace Real P :=
  mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points) (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
    affineSpan Real (Set.range s.points)

/--
theorem `mongePlane_def` / 定理 `mongePlane_def`

English:
theorem mongePlane_def
  given: {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3))
  proof: rfl

中文:
定理 mongePlane_def
  条件: {n : 自然数} (s : 单纯形 实数 P (n + 2)) (i₁ i₂ : 有限集 (n + 3))
  证明: rfl
-/
theorem mongePlane_def {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ =
      mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points)
          (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
        affineSpan Real (Set.range s.points) :=
  rfl

/--
lemma `mongePlane_reindex` / 引理 `mongePlane_reindex`

English:
lemma mongePlane_reindex
  statement: {m n : Nat} (s : Simplex Real P (n + 2)) (e : Fin (n + 3) ≃ Fin (m + 3))
  proof: by
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  simp_rw [mongePlane, reindex_points, reindex_range_points, Function.comp_apply, centroid_def,
    reindex]
  congr 2
  convert! Finset.affineCombination_map {e.symm i₁, e.symm i₂}ᶜ e.toEmbedding _ _ using 3
  · ext i
    simp
  · simp [Function.comp_assoc]
  · simp_rw [centroidWeights, Function.const_comp, Finset.card_compl]
    congr 4
    by_cases h : i₁ = i₂ <;> simp [h]

中文:
引理 mongePlane_reindex
  结论: {m n : 自然数} (s : 单纯形 实数 P (n + 2)) (e : 有限集 (n + 3) ≃ 有限集 (m + 3))
  证明: by
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  simp_rw [mongePlane, reindex_points, reindex_range_points, Function.comp_apply, centroid_def,
    reindex]
  congr 2
  convert! Finset.affineCombination_map {e.symm i₁, e.symm i₂}ᶜ e.toEmbedding _ _ using 3
  · ext i
    simp
  · simp [Function.comp_assoc]
  · simp_rw [centroidWeights, Function.const_comp, Finset.card_compl]
    congr 4
    by_cases h : i₁ = i₂ <;> simp [h]

Depends on / 依赖: Finset, Finset.affineCombination_map, Finset.card_compl, Fintype, Fintype.card_eq, Function, Function.comp_apply, Function.comp_assoc, Function.const_comp, affineCombination_map, card_compl, card_eq, centroidWeights, centroid_def, comp_apply, comp_assoc, const_comp, convert, e.symm, e.toEmbedding
-/
lemma mongePlane_reindex {m n : Nat} (s : Simplex Real P (n + 2)) (e : Fin (n + 3) ≃ Fin (m + 3))
    (i₁ i₂ : Fin (m + 3)) :
    (s.reindex e).mongePlane i₁ i₂ = s.mongePlane (e.symm i₁) (e.symm i₂) := by
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  simp_rw [mongePlane, reindex_points, reindex_range_points, Function.comp_apply, centroid_def,
    reindex]
  congr 2
  convert! Finset.affineCombination_map {e.symm i₁, e.symm i₂}ᶜ e.toEmbedding _ _ using 3
  · ext i
    simp
  · simp [Function.comp_assoc]
  · simp_rw [centroidWeights, Function.const_comp, Finset.card_compl]
    congr 4
    by_cases h : i₁ = i₂ <;> simp [h]

/--
theorem `mongePlane_comm` / 定理 `mongePlane_comm`

English:
theorem mongePlane_comm
  given: {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3))
  proof: by
  simp_rw [mongePlane_def]
  congr 3
  · congr 1
    exact pair_comm _ _
  · ext
    simp_rw [Submodule.mem_span_singleton]
    constructor
    all_goals rintro ⟨r, rfl⟩; use -r; rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]

中文:
定理 mongePlane_comm
  条件: {n : 自然数} (s : 单纯形 实数 P (n + 2)) (i₁ i₂ : 有限集 (n + 3))
  证明: by
  simp_rw [mongePlane_def]
  congr 3
  · congr 1
    exact pair_comm _ _
  · ext
    simp_rw [Submodule.mem_span_singleton]
    constructor
    all_goals rintro ⟨r, rfl⟩; use -r; rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, all_goals, mem_span_singleton, mongePlane_def, neg_smul, neg_vsub_eq_vsub_rev, pair_comm, simp_rw, smul_neg
-/
theorem mongePlane_comm {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ = s.mongePlane i₂ i₁ := by
  simp_rw [mongePlane_def]
  congr 3
  · congr 1
    exact pair_comm _ _
  · ext
    simp_rw [Submodule.mem_span_singleton]
    constructor
    all_goals rintro ⟨r, rfl⟩; use -r; rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]

/--
theorem `mongePoint_mem_mongePlane` / 定理 `mongePoint_mem_mongePlane`

English:
theorem mongePoint_mem_mongePlane
  given: {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)}
  proof: by
  rw [mongePlane_def]; rw [mem_inf_iff]; rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _)]; rw [direction_mk']; rw [Submodule.mem_orthogonal']
  refine ⟨?_, s.mongePoint_mem_affineSpan⟩
  intro v hv
  rcases Submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
  rw [inner_smul_right]; rw [s.inner_mongePoint_vsub_face_centroid_vsub]; rw [mul_zero]

中文:
定理 mongePoint_mem_mongePlane
  条件: {n : 自然数} (s : 单纯形 实数 P (n + 2)) {i₁ i₂ : 有限集 (n + 3)}
  证明: by
  rw [mongePlane_def]; rw [mem_inf_iff]; rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _)]; rw [direction_mk']; rw [Submodule.mem_orthogonal']
  refine ⟨?_, s.mongePoint_mem_affineSpan⟩
  intro v hv
  rcases Submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
  rw [inner_smul_right]; rw [s.inner_mongePoint_vsub_face_centroid_vsub]; rw [mul_zero]

Depends on / 依赖: Submodule, Submodule.mem_orthogonal, Submodule.mem_span_singleton.mp, direction_mk, inner_mongePoint_vsub_face_centroid_vsub, inner_smul_right, mem_inf_iff, mem_orthogonal, mem_span_singleton, mongePlane_def, mongePoint_mem_affineSpan, mul_zero, s.inner_mongePoint_vsub_face_centroid_vsub, s.mongePoint_mem_affineSpan, self_mem_mk, vsub_right_mem_direction_iff_mem
-/
theorem mongePoint_mem_mongePlane {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    s.mongePoint in s.mongePlane i₁ i₂ := by
  rw [mongePlane_def]; rw [mem_inf_iff]; rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _)]; rw [direction_mk']; rw [Submodule.mem_orthogonal']
  refine ⟨?_, s.mongePoint_mem_affineSpan⟩
  intro v hv
  rcases Submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
  rw [inner_smul_right]; rw [s.inner_mongePoint_vsub_face_centroid_vsub]; rw [mul_zero]

/--
theorem `direction_mongePlane` / 定理 `direction_mongePlane`

English:
theorem direction_mongePlane
  given: {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)}
  proof: by
  rw [mongePlane_def]; rw [direction_inf_of_mem_inf s.mongePoint_mem_mongePlane]; rw [direction_mk']; rw [direction_affineSpan]

中文:
定理 direction_mongePlane
  条件: {n : 自然数} (s : 单纯形 实数 P (n + 2)) {i₁ i₂ : 有限集 (n + 3)}
  证明: by
  rw [mongePlane_def]; rw [direction_inf_of_mem_inf s.mongePoint_mem_mongePlane]; rw [direction_mk']; rw [direction_affineSpan]

Depends on / 依赖: direction_affineSpan, direction_inf_of_mem_inf, direction_mk, mongePlane_def, mongePoint_mem_mongePlane, s.mongePoint_mem_mongePlane
-/
theorem direction_mongePlane {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    (s.mongePlane i₁ i₂).direction =
      (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan Real (Set.range s.points) := by
  rw [mongePlane_def]; rw [direction_inf_of_mem_inf s.mongePoint_mem_mongePlane]; rw [direction_mk']; rw [direction_affineSpan]

/--
theorem `eq_mongePoint_of_forall_mem_mongePlane` / 定理 `eq_mongePoint_of_forall_mem_mongePlane`

English:
theorem eq_mongePoint_of_forall_mem_mongePlane
  statement: {n : Nat} {s : Simplex Real P (n + 2)} {i₁ : Fin (n + 3)}
  proof: by
  rw [← @vsub_eq_zero_iff_eq V]
  have h' : forall i₂, i₁ != i₂ -> p -ᵥ s.mongePoint in
      (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan Real (Set.range s.points) := by
    intro i₂ hne
    rw [← s.direction_mongePlane]; rw [vsub_right_mem_direction_iff_mem s.mongePoint_mem_mongePlane]
    exact h i₂ hne
  have hi : p -ᵥ s.mongePoint in ⨅ i₂ : { i // i₁ != i }, (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ := by
    rw [Submodule.mem_iInf]
    exact fun i => (Submodule.mem_inf.1 (h' i i.property)).1
  rw [Submodule.iInf_orthogonal]; rw [← Submodule.span_iUnion] at hi
  have hu :
    ⋃ i : { i // i₁ != i }, ({s.points i₁ -ᵥ s.points i} : Set V) =
      (s.points i₁ -ᵥ ·) '' s.points '' (Set.univ \ {i₁}) := by
    rw [Set.image_image]
    ext x
    simp_rw [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_sdiff_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      use i, ⟨Set.mem_univ _, i.property.symm⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      use ⟨i, hi.symm⟩
  rw [hu]; rw [← vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_univ _)]; rw [Set.image_univ] at hi
  have hv : p -ᵥ s.mongePoint in vectorSpan Real (Set.range s.points) := by
    let s₁ : Finset (Fin (n + 3)) := univ.erase i₁
    obtain ⟨i₂, h₂⟩ := card_pos.1 (show 0 < #s₁ by simp [s₁, card_erase_of_mem])
    have h₁₂ : i₁ != i₂ := (ne_of_mem_erase h₂).symm
    exact (Submodule.mem_inf.1 (h' i₂ h₁₂)).2
  exact Submodule.disjoint_def.1 (vectorSpan Real (Set.range s.points)).orthogonal_disjoint _ hv hi

中文:
定理 eq_mongePoint_of_对任意_mem_mongePlane
  结论: {n : 自然数} {s : 单纯形 实数 P (n + 2)} {i₁ : 有限集 (n + 3)}
  证明: by
  rw [← @vsub_eq_zero_iff_eq V]
  have h' : forall i₂, i₁ != i₂ -> p -ᵥ s.mongePoint in
      (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan Real (Set.range s.points) := by
    intro i₂ hne
    rw [← s.direction_mongePlane]; rw [vsub_right_mem_direction_iff_mem s.mongePoint_mem_mongePlane]
    exact h i₂ hne
  have hi : p -ᵥ s.mongePoint in ⨅ i₂ : { i // i₁ != i }, (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ := by
    rw [Submodule.mem_iInf]
    exact fun i => (Submodule.mem_inf.1 (h' i i.property)).1
  rw [Submodule.iInf_orthogonal]; rw [← Submodule.span_iUnion] at hi
  have hu :
    ⋃ i : { i // i₁ != i }, ({s.points i₁ -ᵥ s.points i} : Set V) =
      (s.points i₁ -ᵥ ·) '' s.points '' (Set.univ \ {i₁}) := by
    rw [Set.image_image]
    ext x
    simp_rw [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_sdiff_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      use i, ⟨Set.mem_univ _, i.property.symm⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      use ⟨i, hi.symm⟩
  rw [hu]; rw [← vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_univ _)]; rw [Set.image_univ] at hi
  have hv : p -ᵥ s.mongePoint in vectorSpan Real (Set.range s.points) := by
    let s₁ : Finset (Fin (n + 3)) := univ.erase i₁
    obtain ⟨i₂, h₂⟩ := card_pos.1 (show 0 < #s₁ by simp [s₁, card_erase_of_mem])
    have h₁₂ : i₁ != i₂ := (ne_of_mem_erase h₂).symm
    exact (Submodule.mem_inf.1 (h' i₂ h₁₂)).2
  exact Submodule.disjoint_def.1 (vectorSpan Real (Set.range s.points)).orthogonal_disjoint _ hv hi

Depends on / 依赖: Set.range, Submodule, Submodule.iInf_ort, Submodule.mem_iInf, Submodule.mem_inf, direction_mongePlane, i.property, iInf_ort, mem_iInf, mem_inf, mongePoint, mongePoint_mem_mongePlane, points, property, s.direction_mongePlane, s.mongePoint, s.mongePoint_mem_mongePlane, s.points, vectorSpan, vsub_eq_zero_iff_eq
-/
theorem eq_mongePoint_of_forall_mem_mongePlane {n : Nat} {s : Simplex Real P (n + 2)} {i₁ : Fin (n + 3)}
    {p : P} (h : forall i₂, i₁ != i₂ -> p in s.mongePlane i₁ i₂) : p = s.mongePoint := by
  rw [← @vsub_eq_zero_iff_eq V]
  have h' : forall i₂, i₁ != i₂ -> p -ᵥ s.mongePoint in
      (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan Real (Set.range s.points) := by
    intro i₂ hne
    rw [← s.direction_mongePlane]; rw [vsub_right_mem_direction_iff_mem s.mongePoint_mem_mongePlane]
    exact h i₂ hne
  have hi : p -ᵥ s.mongePoint in ⨅ i₂ : { i // i₁ != i }, (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ := by
    rw [Submodule.mem_iInf]
    exact fun i => (Submodule.mem_inf.1 (h' i i.property)).1
  rw [Submodule.iInf_orthogonal]; rw [← Submodule.span_iUnion] at hi
  have hu :
    ⋃ i : { i // i₁ != i }, ({s.points i₁ -ᵥ s.points i} : Set V) =
      (s.points i₁ -ᵥ ·) '' s.points '' (Set.univ \ {i₁}) := by
    rw [Set.image_image]
    ext x
    simp_rw [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_sdiff_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      use i, ⟨Set.mem_univ _, i.property.symm⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      use ⟨i, hi.symm⟩
  rw [hu]; rw [← vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_univ _)]; rw [Set.image_univ] at hi
  have hv : p -ᵥ s.mongePoint in vectorSpan Real (Set.range s.points) := by
    let s₁ : Finset (Fin (n + 3)) := univ.erase i₁
    obtain ⟨i₂, h₂⟩ := card_pos.1 (show 0 < #s₁ by simp [s₁, card_erase_of_mem])
    have h₁₂ : i₁ != i₂ := (ne_of_mem_erase h₂).symm
    exact (Submodule.mem_inf.1 (h' i₂ h₁₂)).2
  exact Submodule.disjoint_def.1 (vectorSpan Real (Set.range s.points)).orthogonal_disjoint _ hv hi

end Simplex

namespace Triangle

open EuclideanGeometry Finset Simplex AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
Definition of `orthocenter` / `orthocenter` 的定义

English:
definition orthocenter
  signature: (t : Triangle Real P)
  body: t.mongePoint

中文:
定义 orthocenter
  签名: (t : Triangle 实数 P)
  定义体: t.mongePoint

Depends on / 依赖: mongePoint, t.mongePoint
-/
def orthocenter (t : Triangle Real P) : P :=
  t.mongePoint

/--
theorem `orthocenter_eq_mongePoint` / 定理 `orthocenter_eq_mongePoint`

English:
theorem orthocenter_eq_mongePoint
  given: (t : Triangle Real P)
  statement: t.orthocenter = t.mongePoint
  proof: rfl

中文:
定理 orthocenter_eq_mongePoint
  条件: (t : Triangle 实数 P)
  结论: t.orthocenter = t.mongePoint
  证明: rfl
-/
theorem orthocenter_eq_mongePoint (t : Triangle Real P) : t.orthocenter = t.mongePoint :=
  rfl

/--
lemma `orthocenter_reindex` / 引理 `orthocenter_reindex`

English:
lemma orthocenter_reindex
  given: (t : Triangle Real P) (e : Fin 3 ≃ Fin 3)
  proof: t.mongePoint_reindex e

中文:
引理 orthocenter_reindex
  条件: (t : Triangle 实数 P) (e : 有限集 3 ≃ 有限集 3)
  证明: t.mongePoint_reindex e
-/
@[simp] lemma orthocenter_reindex (t : Triangle Real P) (e : Fin 3 ≃ Fin 3) :
    orthocenter (t.reindex e) = t.orthocenter :=
  t.mongePoint_reindex e

/--
theorem `orthocenter_eq_smul_vsub_vadd_circumcenter` / 定理 `orthocenter_eq_smul_vsub_vadd_circumcenter`

English:
theorem orthocenter_eq_smul_vsub_vadd_circumcenter
  given: (t : Triangle Real P)
  proof: by
  rw [orthocenter_eq_mongePoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  simp

中文:
定理 orthocenter_eq_smul_vsub_vadd_circumcenter
  条件: (t : Triangle 实数 P)
  证明: by
  rw [orthocenter_eq_mongePoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  simp

Depends on / 依赖: mongePoint_eq_smul_vsub_vadd_circumcenter, orthocenter_eq_mongePoint
-/
theorem orthocenter_eq_smul_vsub_vadd_circumcenter (t : Triangle Real P) :
    t.orthocenter =
      (3 : Real) • ((univ : Finset (Fin 3)).centroid Real t.points -ᵥ t.circumcenter : V) +ᵥ
        t.circumcenter := by
  rw [orthocenter_eq_mongePoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  simp

/--
theorem `orthocenter_vsub_circumcenter_eq_sum_vsub` / 定理 `orthocenter_vsub_circumcenter_eq_sum_vsub`

English:
theorem orthocenter_vsub_circumcenter_eq_sum_vsub
  given: (t : Triangle Real P)
  proof: by
  rw [← t.smul_mongePoint_vsub_circumcenter_eq_sum_vsub]; rw [zero_add]; rw [one_smul]; rw [orthocenter_eq_mongePoint]

中文:
定理 orthocenter_vsub_circumcenter_eq_sum_vsub
  条件: (t : Triangle 实数 P)
  证明: by
  rw [← t.smul_mongePoint_vsub_circumcenter_eq_sum_vsub]; rw [zero_add]; rw [one_smul]; rw [orthocenter_eq_mongePoint]

Depends on / 依赖: one_smul, orthocenter_eq_mongePoint, smul_mongePoint_vsub_circumcenter_eq_sum_vsub, t.smul_mongePoint_vsub_circumcenter_eq_sum_vsub, zero_add
-/
theorem orthocenter_vsub_circumcenter_eq_sum_vsub (t : Triangle Real P) :
    t.orthocenter -ᵥ t.circumcenter = ∑ i, (t.points i -ᵥ t.circumcenter) := by
  rw [← t.smul_mongePoint_vsub_circumcenter_eq_sum_vsub]; rw [zero_add]; rw [one_smul]; rw [orthocenter_eq_mongePoint]

/--
theorem `orthocenter_mem_affineSpan` / 定理 `orthocenter_mem_affineSpan`

English:
theorem orthocenter_mem_affineSpan
  given: (t : Triangle Real P)
  proof: t.mongePoint_mem_affineSpan

中文:
定理 orthocenter_mem_affineSpan
  条件: (t : Triangle 实数 P)
  证明: t.mongePoint_mem_affineSpan

Depends on / 依赖: mongePoint_mem_affineSpan, t.mongePoint_mem_affineSpan
-/
theorem orthocenter_mem_affineSpan (t : Triangle Real P) :
    t.orthocenter in affineSpan Real (Set.range t.points) :=
  t.mongePoint_mem_affineSpan

/--
theorem `orthocenter_eq_of_range_eq` / 定理 `orthocenter_eq_of_range_eq`

English:
theorem orthocenter_eq_of_range_eq
  statement: {t₁ t₂ : Triangle Real P}
  proof: mongePoint_eq_of_range_eq h

中文:
定理 orthocenter_eq_of_range_eq
  结论: {t₁ t₂ : Triangle 实数 P}
  证明: mongePoint_eq_of_range_eq h

Depends on / 依赖: mongePoint_eq_of_range_eq
-/
theorem orthocenter_eq_of_range_eq {t₁ t₂ : Triangle Real P}
    (h : Set.range t₁.points = Set.range t₂.points) : t₁.orthocenter = t₂.orthocenter :=
  mongePoint_eq_of_range_eq h

/--
theorem `altitude_eq_mongePlane` / 定理 `altitude_eq_mongePlane`

English:
theorem altitude_eq_mongePlane
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  proof: by
  have hs : ({i₂, i₃}ᶜ : Finset (Fin 3)) = {i₁} := by decide +revert
  have he : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by grind
  rw [mongePlane_def]; rw [altitude_def]; rw [direction_affineSpan]; rw [hs]; rw [he]; rw [centroid_singleton]; rw [vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_insert i₂ _)]
  simp [h₂₃]

中文:
定理 altitude_eq_mongePlane
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  证明: by
  have hs : ({i₂, i₃}ᶜ : Finset (Fin 3)) = {i₁} := by decide +revert
  have he : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by grind
  rw [mongePlane_def]; rw [altitude_def]; rw [direction_affineSpan]; rw [hs]; rw [he]; rw [centroid_singleton]; rw [vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_insert i₂ _)]
  simp [h₂₃]

Depends on / 依赖: Finset, Set.mem_insert, altitude_def, centroid_singleton, direction_affineSpan, mem_insert, mongePlane_def, revert, vectorSpan_image_eq_span_vsub_set_left_ne
-/
theorem altitude_eq_mongePlane (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
    (h₂₃ : i₂ != i₃) : t.altitude i₁ = t.mongePlane i₂ i₃ := by
  have hs : ({i₂, i₃}ᶜ : Finset (Fin 3)) = {i₁} := by decide +revert
  have he : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by grind
  rw [mongePlane_def]; rw [altitude_def]; rw [direction_affineSpan]; rw [hs]; rw [he]; rw [centroid_singleton]; rw [vectorSpan_image_eq_span_vsub_set_left_ne Real _ (Set.mem_insert i₂ _)]
  simp [h₂₃]

/--
theorem `orthocenter_mem_altitude` / 定理 `orthocenter_mem_altitude`

English:
theorem orthocenter_mem_altitude
  given: (t : Triangle Real P) {i₁ : Fin 3}
  proof: by
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : exists i₂ i₃, i₁ != i₂ ∧ i₂ != i₃ ∧ i₁ != i₃ := by
    decide +revert
  rw [orthocenter_eq_mongePoint]; rw [t.altitude_eq_mongePlane h₁₂ h₁₃ h₂₃]
  exact t.mongePoint_mem_mongePlane

中文:
定理 orthocenter_mem_altitude
  条件: (t : Triangle 实数 P) {i₁ : 有限集 3}
  证明: by
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : exists i₂ i₃, i₁ != i₂ ∧ i₂ != i₃ ∧ i₁ != i₃ := by
    decide +revert
  rw [orthocenter_eq_mongePoint]; rw [t.altitude_eq_mongePlane h₁₂ h₁₃ h₂₃]
  exact t.mongePoint_mem_mongePlane

Depends on / 依赖: altitude_eq_mongePlane, mongePoint_mem_mongePlane, orthocenter_eq_mongePoint, revert, t.altitude_eq_mongePlane, t.mongePoint_mem_mongePlane
-/
theorem orthocenter_mem_altitude (t : Triangle Real P) {i₁ : Fin 3} :
    t.orthocenter in t.altitude i₁ := by
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : exists i₂ i₃, i₁ != i₂ ∧ i₂ != i₃ ∧ i₁ != i₃ := by
    decide +revert
  rw [orthocenter_eq_mongePoint]; rw [t.altitude_eq_mongePlane h₁₂ h₁₃ h₂₃]
  exact t.mongePoint_mem_mongePlane

/--
theorem `eq_orthocenter_of_forall_mem_altitude` / 定理 `eq_orthocenter_of_forall_mem_altitude`

English:
theorem eq_orthocenter_of_forall_mem_altitude
  statement: {t : Triangle Real P} {i₁ i₂ : Fin 3} {p : P}
  proof: by
  obtain ⟨i₃, h₂₃, h₁₃⟩ : exists i₃, i₂ != i₃ ∧ i₁ != i₃ := by
    clear h₁ h₂
    decide +revert
  rw [t.altitude_eq_mongePlane h₁₃ h₁₂ h₂₃.symm] at h₁
  rw [t.altitude_eq_mongePlane h₂₃ h₁₂.symm h₁₃.symm] at h₂
  rw [orthocenter_eq_mongePoint]
  have ha : forall i, i₃ != i -> p in t.mongePlane i₃ i := by
    intro i hi
    obtain rfl | rfl : i₁ = i ∨ i₂ = i := by lia
    all_goals assumption
  exact eq_mongePoint_of_forall_mem_mongePlane ha

中文:
定理 eq_orthocenter_of_对任意_mem_altitude
  结论: {t : Triangle 实数 P} {i₁ i₂ : 有限集 3} {p : P}
  证明: by
  obtain ⟨i₃, h₂₃, h₁₃⟩ : exists i₃, i₂ != i₃ ∧ i₁ != i₃ := by
    clear h₁ h₂
    decide +revert
  rw [t.altitude_eq_mongePlane h₁₃ h₁₂ h₂₃.symm] at h₁
  rw [t.altitude_eq_mongePlane h₂₃ h₁₂.symm h₁₃.symm] at h₂
  rw [orthocenter_eq_mongePoint]
  have ha : forall i, i₃ != i -> p in t.mongePlane i₃ i := by
    intro i hi
    obtain rfl | rfl : i₁ = i ∨ i₂ = i := by lia
    all_goals assumption
  exact eq_mongePoint_of_forall_mem_mongePlane ha

Depends on / 依赖: all_goals, altitude_eq_mongePlane, eq_mongePoint_of_forall_mem_mongePlane, mongePlane, orthocenter_eq_mongePoint, revert, t.altitude_eq_mongePlane, t.mongePlane
-/
theorem eq_orthocenter_of_forall_mem_altitude {t : Triangle Real P} {i₁ i₂ : Fin 3} {p : P}
    (h₁₂ : i₁ != i₂) (h₁ : p in t.altitude i₁) (h₂ : p in t.altitude i₂) : p = t.orthocenter := by
  obtain ⟨i₃, h₂₃, h₁₃⟩ : exists i₃, i₂ != i₃ ∧ i₁ != i₃ := by
    clear h₁ h₂
    decide +revert
  rw [t.altitude_eq_mongePlane h₁₃ h₁₂ h₂₃.symm] at h₁
  rw [t.altitude_eq_mongePlane h₂₃ h₁₂.symm h₁₃.symm] at h₂
  rw [orthocenter_eq_mongePoint]
  have ha : forall i, i₃ != i -> p in t.mongePlane i₃ i := by
    intro i hi
    obtain rfl | rfl : i₁ = i ∨ i₂ = i := by lia
    all_goals assumption
  exact eq_mongePoint_of_forall_mem_mongePlane ha

/--
theorem `dist_orthocenter_reflection_circumcenter` / 定理 `dist_orthocenter_reflection_circumcenter`

English:
theorem dist_orthocenter_reflection_circumcenter
  given: (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂)
  proof: by
  rw [← mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg]; rw [t.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter h]; rw [t.orthocenter_eq_mongePoint]; rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter]; rw [dist_affineCombination t.pointsWithCircumcenter (sum_mongePointWeightsWithCircumcenter _)
      (sum_reflectionCircumcenterWeightsWithCircumcenter h)]
  simp_rw [sum_pointsWithCircumcenter, Pi.sub_apply, mongePointWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter]
  have hu : ({i₁, i₂} : Finset (Fin 3)) subseteq univ := subset_univ _
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
      exists i₃, univ \ ({i₁, i₂} : Finset (Fin 3)) = {i₃} ∧ i₃ != i₁ ∧ i₃ != i₂ := by
    decide +revert
  simp_rw [← sum_sdiff hu, hi₃]
  norm_num [hi₃₁, hi₃₂]

中文:
定理 dist_orthocenter_reflection_circumcenter
  条件: (t : Triangle 实数 P) {i₁ i₂ : 有限集 3} (h : i₁ != i₂)
  证明: by
  rw [← mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg]; rw [t.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter h]; rw [t.orthocenter_eq_mongePoint]; rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter]; rw [dist_affineCombination t.pointsWithCircumcenter (sum_mongePointWeightsWithCircumcenter _)
      (sum_reflectionCircumcenterWeightsWithCircumcenter h)]
  simp_rw [sum_pointsWithCircumcenter, Pi.sub_apply, mongePointWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter]
  have hu : ({i₁, i₂} : Finset (Fin 3)) subseteq univ := subset_univ _
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
      exists i₃, univ \ ({i₁, i₂} : Finset (Fin 3)) = {i₃} ∧ i₃ != i₁ ∧ i₃ != i₂ := by
    decide +revert
  simp_rw [← sum_sdiff hu, hi₃]
  norm_num [hi₃₁, hi₃₂]

Depends on / 依赖: Pi.sub_apply, circumradius_nonneg, dist_affineCombination, dist_nonneg, mongePointWeightsWithCircumcenter, mongePoint_eq_affineCombination_of_pointsWithCircumcenter, mul_self_inj_of_nonneg, orthocenter_eq_mongePoint, pointsWithCircumcenter, reflectionCircumce, reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter, simp_rw, sub_apply, sum_mongePointWeightsWithCircumcenter, sum_pointsWithCircumcenter, sum_reflectionCircumcenterWeightsWithCircumcenter, t.circumradius_nonneg, t.orthocenter_eq_mongePoint, t.pointsWithCircumcenter, t.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter
-/
theorem dist_orthocenter_reflection_circumcenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) :
    dist t.orthocenter (reflection (affineSpan Real (t.points '' {i₁, i₂})) t.circumcenter) =
      t.circumradius := by
  rw [← mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg]; rw [t.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter h]; rw [t.orthocenter_eq_mongePoint]; rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter]; rw [dist_affineCombination t.pointsWithCircumcenter (sum_mongePointWeightsWithCircumcenter _)
      (sum_reflectionCircumcenterWeightsWithCircumcenter h)]
  simp_rw [sum_pointsWithCircumcenter, Pi.sub_apply, mongePointWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter]
  have hu : ({i₁, i₂} : Finset (Fin 3)) subseteq univ := subset_univ _
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
      exists i₃, univ \ ({i₁, i₂} : Finset (Fin 3)) = {i₃} ∧ i₃ != i₁ ∧ i₃ != i₂ := by
    decide +revert
  simp_rw [← sum_sdiff hu, hi₃]
  norm_num [hi₃₁, hi₃₂]

/--
theorem `dist_orthocenter_reflection_circumcenter_finset` / 定理 `dist_orthocenter_reflection_circumcenter_finset`

English:
theorem dist_orthocenter_reflection_circumcenter_finset
  statement: (t : Triangle Real P) {i₁ i₂ : Fin 3}
  proof: by
  simp only [coe_insert, coe_singleton]
  exact dist_orthocenter_reflection_circumcenter _ h

中文:
定理 dist_orthocenter_reflection_circumcenter_finset
  结论: (t : Triangle 实数 P) {i₁ i₂ : 有限集 3}
  证明: by
  simp only [coe_insert, coe_singleton]
  exact dist_orthocenter_reflection_circumcenter _ h

Depends on / 依赖: coe_insert, coe_singleton, dist_orthocenter_reflection_circumcenter
-/
theorem dist_orthocenter_reflection_circumcenter_finset (t : Triangle Real P) {i₁ i₂ : Fin 3}
    (h : i₁ != i₂) :
    dist t.orthocenter
        (reflection (affineSpan Real (t.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.circumcenter) =
      t.circumradius := by
  simp only [coe_insert, coe_singleton]
  exact dist_orthocenter_reflection_circumcenter _ h

/--
theorem `dist_circumcenter_reflection_orthocenter` / 定理 `dist_circumcenter_reflection_orthocenter`

English:
theorem dist_circumcenter_reflection_orthocenter
  given: (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂)
  proof: by
  rw [EuclideanGeometry.dist_reflection]; rw [dist_comm]; rw [dist_orthocenter_reflection_circumcenter t h]

中文:
定理 dist_circumcenter_reflection_orthocenter
  条件: (t : Triangle 实数 P) {i₁ i₂ : 有限集 3} (h : i₁ != i₂)
  证明: by
  rw [EuclideanGeometry.dist_reflection]; rw [dist_comm]; rw [dist_orthocenter_reflection_circumcenter t h]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.dist_reflection, dist_comm, dist_orthocenter_reflection_circumcenter, dist_reflection
-/
theorem dist_circumcenter_reflection_orthocenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) :
    dist t.circumcenter (reflection (affineSpan Real (t.points '' {i₁, i₂})) t.orthocenter) =
      t.circumradius := by
  rw [EuclideanGeometry.dist_reflection]; rw [dist_comm]; rw [dist_orthocenter_reflection_circumcenter t h]

/--
theorem `dist_circumcenter_reflection_orthocenter_finset` / 定理 `dist_circumcenter_reflection_orthocenter_finset`

English:
theorem dist_circumcenter_reflection_orthocenter_finset
  statement: (t : Triangle Real P) {i₁ i₂ : Fin 3}
  proof: by
  simp only [coe_insert, coe_singleton]
  exact dist_circumcenter_reflection_orthocenter _ h

中文:
定理 dist_circumcenter_reflection_orthocenter_finset
  结论: (t : Triangle 实数 P) {i₁ i₂ : 有限集 3}
  证明: by
  simp only [coe_insert, coe_singleton]
  exact dist_circumcenter_reflection_orthocenter _ h

Depends on / 依赖: coe_insert, coe_singleton, dist_circumcenter_reflection_orthocenter
-/
theorem dist_circumcenter_reflection_orthocenter_finset (t : Triangle Real P) {i₁ i₂ : Fin 3}
    (h : i₁ != i₂) :
    dist t.circumcenter
      (reflection (affineSpan Real (t.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.orthocenter) =
      t.circumradius := by
  simp only [coe_insert, coe_singleton]
  exact dist_circumcenter_reflection_orthocenter _ h

/--
theorem `affineSpan_orthocenter_point_le_altitude` / 定理 `affineSpan_orthocenter_point_le_altitude`

English:
theorem affineSpan_orthocenter_point_le_altitude
  given: (t : Triangle Real P) (i : Fin 3)
  proof: by
  refine affineSpan_le_of_subset_coe ?_
  rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩

中文:
定理 affineSpan_orthocenter_point_le_altitude
  条件: (t : Triangle 实数 P) (i : 有限集 3)
  证明: by
  refine affineSpan_le_of_subset_coe ?_
  rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, affineSpan_le_of_subset_coe, insert_subset_iff, mem_altitude, orthocenter_mem_altitude, singleton_subset_iff, t.mem_altitude, t.orthocenter_mem_altitude
-/
theorem affineSpan_orthocenter_point_le_altitude (t : Triangle Real P) (i : Fin 3) :
    line[Real, t.orthocenter, t.points i] <= t.altitude i := by
  refine affineSpan_le_of_subset_coe ?_
  rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩

/--
theorem `altitude_replace_orthocenter_eq_affineSpan` / 定理 `altitude_replace_orthocenter_eq_affineSpan`

English:
theorem altitude_replace_orthocenter_eq_affineSpan
  statement: {t₁ t₂ : Triangle Real P}
  proof: by
  symm
  rw [← h₂]; rw [t₂.affineSpan_pair_eq_altitude_iff]
  rw [h₂]
  use t₁.independent.injective.ne hi₁₂
  have he : affineSpan Real (Set.range t₂.points) = affineSpan Real (Set.range t₁.points) := by
    refine ext_of_direction_eq ?_
      ⟨t₁.points i₃, mem_affineSpan Real ⟨j₃, h₃⟩, mem_affineSpan Real (Set.mem_range_self _)⟩
    refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_le_of_subset_coe ?_))
      ?_
    · have hu : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by grind
      rw [← Set.image_univ]; rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₂]; rw [h₃]; rw [Set.insert_subset_iff]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
      exact
        ⟨t₁.orthocenter_mem_affineSpan, mem_affineSpan Real (Set.mem_range_self _),
          mem_affineSpan Real (Set.mem_range_self _)⟩
    · rw [direction_affineSpan, direction_affineSpan,
        t₁.independent.finrank_vectorSpan (Fintype.card_fin _),
        t₂.independent.finrank_vectorSpan (Fintype.card_fin _)]
  rw [he]
  use mem_affineSpan Real (Set.mem_range_self _)
  have hu : ({j₂}ᶜ : Set _) = {j₁, j₃} := by grind
  rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₃]
  have hle : (t₁.altitude i₃).directionᗮ <= line[Real, t₁.orthocenter, t₁.points i₃].directionᗮ :=
    Submodule.orthogonal_le (direction_le (affineSpan_orthocenter_point_le_altitude _ _))
  refine hle ((t₁.vectorSpan_isOrtho_altitude_direction i₃) ?_)
  have hui : ({i₃}ᶜ : Set _) = {i₁, i₂} := by grind
  rw [hui]; rw [Set.image_insert_eq]; rw [Set.image_singleton]
  exact vsub_mem_vectorSpan Real (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

中文:
定理 altitude_replace_orthocenter_eq_affineSpan
  结论: {t₁ t₂ : Triangle 实数 P}
  证明: by
  symm
  rw [← h₂]; rw [t₂.affineSpan_pair_eq_altitude_iff]
  rw [h₂]
  use t₁.independent.injective.ne hi₁₂
  have he : affineSpan Real (Set.range t₂.points) = affineSpan Real (Set.range t₁.points) := by
    refine ext_of_direction_eq ?_
      ⟨t₁.points i₃, mem_affineSpan Real ⟨j₃, h₃⟩, mem_affineSpan Real (Set.mem_range_self _)⟩
    refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_le_of_subset_coe ?_))
      ?_
    · have hu : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by grind
      rw [← Set.image_univ]; rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₂]; rw [h₃]; rw [Set.insert_subset_iff]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
      exact
        ⟨t₁.orthocenter_mem_affineSpan, mem_affineSpan Real (Set.mem_range_self _),
          mem_affineSpan Real (Set.mem_range_self _)⟩
    · rw [direction_affineSpan, direction_affineSpan,
        t₁.independent.finrank_vectorSpan (Fintype.card_fin _),
        t₂.independent.finrank_vectorSpan (Fintype.card_fin _)]
  rw [he]
  use mem_affineSpan Real (Set.mem_range_self _)
  have hu : ({j₂}ᶜ : Set _) = {j₁, j₃} := by grind
  rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₃]
  have hle : (t₁.altitude i₃).directionᗮ <= line[Real, t₁.orthocenter, t₁.points i₃].directionᗮ :=
    Submodule.orthogonal_le (direction_le (affineSpan_orthocenter_point_le_altitude _ _))
  refine hle ((t₁.vectorSpan_isOrtho_altitude_direction i₃) ?_)
  have hui : ({i₃}ᶜ : Set _) = {i₁, i₂} := by grind
  rw [hui]; rw [Set.image_insert_eq]; rw [Set.image_singleton]
  exact vsub_mem_vectorSpan Real (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

Depends on / 依赖: Set.image_univ, Set.mem_range_self, Set.range, Set.univ, Submodule, Submodule.eq_of_le_of_finrank_eq, affineSpan, affineSpan_le_of_subset_coe, affineSpan_pair_eq_altitude_iff, direction_le, eq_of_le_of_finrank_eq, ext_of_direction_eq, image_univ, independent, independent.injective.ne, injective, mem_affineSpan, mem_range_self, points
-/
theorem altitude_replace_orthocenter_eq_affineSpan {t₁ t₂ : Triangle Real P}
    {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3} (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ : i₂ != i₃) (hj₁₂ : j₁ != j₂)
    (hj₁₃ : j₁ != j₃) (hj₂₃ : j₂ != j₃) (h₁ : t₂.points j₁ = t₁.orthocenter)
    (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) :
    t₂.altitude j₂ = line[Real, t₁.points i₁, t₁.points i₂] := by
  symm
  rw [← h₂]; rw [t₂.affineSpan_pair_eq_altitude_iff]
  rw [h₂]
  use t₁.independent.injective.ne hi₁₂
  have he : affineSpan Real (Set.range t₂.points) = affineSpan Real (Set.range t₁.points) := by
    refine ext_of_direction_eq ?_
      ⟨t₁.points i₃, mem_affineSpan Real ⟨j₃, h₃⟩, mem_affineSpan Real (Set.mem_range_self _)⟩
    refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_le_of_subset_coe ?_))
      ?_
    · have hu : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by grind
      rw [← Set.image_univ]; rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₂]; rw [h₃]; rw [Set.insert_subset_iff]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
      exact
        ⟨t₁.orthocenter_mem_affineSpan, mem_affineSpan Real (Set.mem_range_self _),
          mem_affineSpan Real (Set.mem_range_self _)⟩
    · rw [direction_affineSpan, direction_affineSpan,
        t₁.independent.finrank_vectorSpan (Fintype.card_fin _),
        t₂.independent.finrank_vectorSpan (Fintype.card_fin _)]
  rw [he]
  use mem_affineSpan Real (Set.mem_range_self _)
  have hu : ({j₂}ᶜ : Set _) = {j₁, j₃} := by grind
  rw [hu]; rw [Set.image_insert_eq]; rw [Set.image_singleton]; rw [h₁]; rw [h₃]
  have hle : (t₁.altitude i₃).directionᗮ <= line[Real, t₁.orthocenter, t₁.points i₃].directionᗮ :=
    Submodule.orthogonal_le (direction_le (affineSpan_orthocenter_point_le_altitude _ _))
  refine hle ((t₁.vectorSpan_isOrtho_altitude_direction i₃) ?_)
  have hui : ({i₃}ᶜ : Set _) = {i₁, i₂} := by grind
  rw [hui]; rw [Set.image_insert_eq]; rw [Set.image_singleton]
  exact vsub_mem_vectorSpan Real (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/--
theorem `orthocenter_replace_orthocenter_eq_point` / 定理 `orthocenter_replace_orthocenter_eq_point`

English:
theorem orthocenter_replace_orthocenter_eq_point
  statement: {t₁ t₂ : Triangle Real P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3}
  proof: by
  refine (Triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ ?_ ?_).symm
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
    exact mem_affineSpan Real (Set.mem_insert _ _)
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂]
    exact mem_affineSpan Real (Set.mem_insert _ _)

中文:
定理 orthocenter_replace_orthocenter_eq_point
  结论: {t₁ t₂ : Triangle 实数 P} {i₁ i₂ i₃ j₁ j₂ j₃ : 有限集 3}
  证明: by
  refine (Triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ ?_ ?_).symm
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
    exact mem_affineSpan Real (Set.mem_insert _ _)
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂]
    exact mem_affineSpan Real (Set.mem_insert _ _)

Depends on / 依赖: Set.mem_insert, Triangle, Triangle.eq_orthocenter_of_forall_mem_altitude, altitude_replace_orthocenter_eq_affineSpan, eq_orthocenter_of_forall_mem_altitude, mem_affineSpan, mem_insert
-/
theorem orthocenter_replace_orthocenter_eq_point {t₁ t₂ : Triangle Real P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3}
    (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ : i₂ != i₃) (hj₁₂ : j₁ != j₂) (hj₁₃ : j₁ != j₃)
    (hj₂₃ : j₂ != j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) : t₂.orthocenter = t₁.points i₁ := by
  refine (Triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ ?_ ?_).symm
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
    exact mem_affineSpan Real (Set.mem_insert _ _)
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂]
    exact mem_affineSpan Real (Set.mem_insert _ _)

end Triangle

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
Definition of `OrthocentricSystem` / `OrthocentricSystem` 的定义

English:
definition OrthocentricSystem
  signature: (s : Set P)
  body: exists t : Triangle Real P,
    t.orthocenter ∉ Set.range t.points ∧ s = insert t.orthocenter (Set.range t.points)

中文:
定义 OrthocentricSystem
  签名: (s : 集合 P)
  定义体: exists t : Triangle Real P,
    t.orthocenter ∉ Set.range t.points ∧ s = insert t.orthocenter (Set.range t.points)

Depends on / 依赖: Set.range, Triangle, insert, orthocenter, points, t.orthocenter, t.points
-/
def OrthocentricSystem (s : Set P) : Prop :=
  exists t : Triangle Real P,
    t.orthocenter ∉ Set.range t.points ∧ s = insert t.orthocenter (Set.range t.points)

/--
theorem `exists_of_range_subset_orthocentricSystem` / 定理 `exists_of_range_subset_orthocentricSystem`

English:
theorem exists_of_range_subset_orthocentricSystem
  statement: {t : Triangle Real P}
  proof: by
  by_cases h : t.orthocenter in Set.range p
  · left
    rcases h with ⟨i₁, h₁⟩
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
        exists i₂ i₃ : Fin 3, i₁ != i₂ ∧ i₁ != i₃ ∧ i₂ != i₃ ∧ forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by
      clear h₁
      decide +revert
    have h : forall i, i₁ != i -> exists j : Fin 3, t.points j = p i := by
      intro i hi
      replace hps := Set.mem_of_mem_insert_of_ne
        (Set.mem_of_mem_of_subset (Set.mem_range_self i) hps) (h₁ ▸ hpi.ne hi.symm)
      exact hps
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩
    have hj₂₃ : j₂ != j₃ := by
      intro he
      rw [he]; rw [h₃] at h₂
      exact h₂₃.symm (hpi h₂)
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩
  · right
    have hs := Set.subset_sdiff_singleton hps h
    rw [Set.insert_sdiff_self_of_notMem ho] at hs
    classical
    refine Set.eq_of_subset_of_card_le hs ?_
    rw [Set.card_range_of_injective hpi]; rw [Set.card_range_of_injective t.independent.injective]

中文:
定理 存在_of_range_subset_orthocentricSystem
  结论: {t : Triangle 实数 P}
  证明: by
  by_cases h : t.orthocenter in Set.range p
  · left
    rcases h with ⟨i₁, h₁⟩
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
        exists i₂ i₃ : Fin 3, i₁ != i₂ ∧ i₁ != i₃ ∧ i₂ != i₃ ∧ forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by
      clear h₁
      decide +revert
    have h : forall i, i₁ != i -> exists j : Fin 3, t.points j = p i := by
      intro i hi
      replace hps := Set.mem_of_mem_insert_of_ne
        (Set.mem_of_mem_of_subset (Set.mem_range_self i) hps) (h₁ ▸ hpi.ne hi.symm)
      exact hps
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩
    have hj₂₃ : j₂ != j₃ := by
      intro he
      rw [he]; rw [h₃] at h₂
      exact h₂₃.symm (hpi h₂)
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩
  · right
    have hs := Set.subset_sdiff_singleton hps h
    rw [Set.insert_sdiff_self_of_notMem ho] at hs
    classical
    refine Set.eq_of_subset_of_card_le hs ?_
    rw [Set.card_range_of_injective hpi]; rw [Set.card_range_of_injective t.independent.injective]

Depends on / 依赖: Set.mem_of_mem_insert_of_ne, Set.mem_of_mem_of_subset, Set.mem_range_self, Set.range, hi.symm, hpi.ne, mem_of_mem_insert_of_ne, mem_of_mem_of_subset, mem_range_self, orthocenter, points, replace, revert, t.orthocenter, t.points
-/
theorem exists_of_range_subset_orthocentricSystem {t : Triangle Real P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 -> P}
    (hps : Set.range p subseteq insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    (exists i₁ i₂ i₃ j₂ j₃ : Fin 3,
      i₁ != i₂ ∧ i₁ != i₃ ∧ i₂ != i₃ ∧ (forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃) ∧
        p i₁ = t.orthocenter ∧ j₂ != j₃ ∧ t.points j₂ = p i₂ ∧ t.points j₃ = p i₃) ∨
      Set.range p = Set.range t.points := by
  by_cases h : t.orthocenter in Set.range p
  · left
    rcases h with ⟨i₁, h₁⟩
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
        exists i₂ i₃ : Fin 3, i₁ != i₂ ∧ i₁ != i₃ ∧ i₂ != i₃ ∧ forall i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by
      clear h₁
      decide +revert
    have h : forall i, i₁ != i -> exists j : Fin 3, t.points j = p i := by
      intro i hi
      replace hps := Set.mem_of_mem_insert_of_ne
        (Set.mem_of_mem_of_subset (Set.mem_range_self i) hps) (h₁ ▸ hpi.ne hi.symm)
      exact hps
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩
    have hj₂₃ : j₂ != j₃ := by
      intro he
      rw [he]; rw [h₃] at h₂
      exact h₂₃.symm (hpi h₂)
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩
  · right
    have hs := Set.subset_sdiff_singleton hps h
    rw [Set.insert_sdiff_self_of_notMem ho] at hs
    classical
    refine Set.eq_of_subset_of_card_le hs ?_
    rw [Set.card_range_of_injective hpi]; rw [Set.card_range_of_injective t.independent.injective]

/--
theorem `exists_dist_eq_circumradius_of_subset_insert_orthocenter` / 定理 `exists_dist_eq_circumradius_of_subset_insert_orthocenter`

English:
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter
  statement: {t : Triangle Real P}
  proof: by
  rcases exists_of_range_subset_orthocentricSystem ho hps hpi with
    (⟨i₁, i₂, i₃, j₂, j₃, _, _, _, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · use reflection (affineSpan Real (t.points '' {j₂, j₃})) t.circumcenter,
      reflection_mem_of_le_of_mem (affineSpan_mono Real (Set.image_subset_range _ _))
        t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rcases hp₁ with ⟨i, rfl⟩
    have h₁₂₃ := h₁₂₃ i
    repeat' rcases h₁₂₃ with h₁₂₃ | h₁₂₃
    · convert! Triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
    · rw [← h₂, dist_reflection_eq_of_mem _
       (mem_affineSpan Real (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
      exact t.dist_circumcenter_eq_circumradius _
    · rw [← h₃,
        dist_reflection_eq_of_mem _
          (mem_affineSpan Real
            (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
      exact t.dist_circumcenter_eq_circumradius _
  · use t.circumcenter, t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rw [hs] at hp₁
    rcases hp₁ with ⟨i, rfl⟩
    exact t.dist_circumcenter_eq_circumradius _

中文:
定理 存在_dist_eq_circumradius_of_subset_insert_orthocenter
  结论: {t : Triangle 实数 P}
  证明: by
  rcases exists_of_range_subset_orthocentricSystem ho hps hpi with
    (⟨i₁, i₂, i₃, j₂, j₃, _, _, _, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · use reflection (affineSpan Real (t.points '' {j₂, j₃})) t.circumcenter,
      reflection_mem_of_le_of_mem (affineSpan_mono Real (Set.image_subset_range _ _))
        t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rcases hp₁ with ⟨i, rfl⟩
    have h₁₂₃ := h₁₂₃ i
    repeat' rcases h₁₂₃ with h₁₂₃ | h₁₂₃
    · convert! Triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
    · rw [← h₂, dist_reflection_eq_of_mem _
       (mem_affineSpan Real (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
      exact t.dist_circumcenter_eq_circumradius _
    · rw [← h₃,
        dist_reflection_eq_of_mem _
          (mem_affineSpan Real
            (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
      exact t.dist_circumcenter_eq_circumradius _
  · use t.circumcenter, t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rw [hs] at hp₁
    rcases hp₁ with ⟨i, rfl⟩
    exact t.dist_circumcenter_eq_circumradius _

Depends on / 依赖: Set.image_subset_range, Triangle, Triangle.dist_orthocenter_reflection_circumcenter, affineSpan, affineSpan_mono, circumcenter, circumcenter_mem_affineSpan, convert, dist_orthocenter_reflection_circumcenter, dist_reflect, exists_of_range_subset_orthocentricSystem, image_subset_range, points, reflection, reflection_mem_of_le_of_mem, repeat, t.circumcenter, t.circumcenter_mem_affineSpan, t.points
-/
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle Real P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 -> P}
    (hps : Set.range p subseteq insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    exists c in affineSpan Real (Set.range t.points), forall p₁ in Set.range p, dist p₁ c = t.circumradius := by
  rcases exists_of_range_subset_orthocentricSystem ho hps hpi with
    (⟨i₁, i₂, i₃, j₂, j₃, _, _, _, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · use reflection (affineSpan Real (t.points '' {j₂, j₃})) t.circumcenter,
      reflection_mem_of_le_of_mem (affineSpan_mono Real (Set.image_subset_range _ _))
        t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rcases hp₁ with ⟨i, rfl⟩
    have h₁₂₃ := h₁₂₃ i
    repeat' rcases h₁₂₃ with h₁₂₃ | h₁₂₃
    · convert! Triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
    · rw [← h₂, dist_reflection_eq_of_mem _
       (mem_affineSpan Real (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
      exact t.dist_circumcenter_eq_circumradius _
    · rw [← h₃,
        dist_reflection_eq_of_mem _
          (mem_affineSpan Real
            (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
      exact t.dist_circumcenter_eq_circumradius _
  · use t.circumcenter, t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rw [hs] at hp₁
    rcases hp₁ with ⟨i, rfl⟩
    exact t.dist_circumcenter_eq_circumradius _

/--
theorem `OrthocentricSystem.affineIndependent` / 定理 `OrthocentricSystem.affineIndependent`

English:
theorem OrthocentricSystem.affineIndependent
  statement: {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 -> P}
  proof: by
  rcases ho with ⟨t, hto, hst⟩
  rw [hst] at hps
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, _, hc⟩
  exact Cospherical.affineIndependent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi

中文:
定理 OrthocentricSystem.affineIndependent
  结论: {s : 集合 P} (ho : OrthocentricSystem s) {p : 有限集 3 -> P}
  证明: by
  rcases ho with ⟨t, hto, hst⟩
  rw [hst] at hps
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, _, hc⟩
  exact Cospherical.affineIndependent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi

Depends on / 依赖: Cospherical, Cospherical.affineIndependent, Set.Subset.rfl, Subset, affineIndependent, circumradius, exists_dist_eq_circumradius_of_subset_insert_orthocenter, t.circumradius
-/
theorem OrthocentricSystem.affineIndependent {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 -> P}
    (hps : Set.range p subseteq s) (hpi : Function.Injective p) : AffineIndependent Real p := by
  rcases ho with ⟨t, hto, hst⟩
  rw [hst] at hps
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, _, hc⟩
  exact Cospherical.affineIndependent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi

/--
theorem `affineSpan_of_orthocentricSystem` / 定理 `affineSpan_of_orthocentricSystem`

English:
theorem affineSpan_of_orthocentricSystem
  statement: {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 -> P}
  proof: by
  have ha := ho.affineIndependent hps hpi
  rcases ho with ⟨t, _, hts⟩
  have hs : affineSpan Real s = affineSpan Real (Set.range t.points) := by
    rw [hts]; rw [affineSpan_insert_eq_affineSpan Real t.orthocenter_mem_affineSpan]
  refine ext_of_direction_eq ?_
    ⟨p 0, mem_affineSpan Real (Set.mem_range_self _), mem_affineSpan Real (hps (Set.mem_range_self _))⟩
  have hfd : FiniteDimensional Real (affineSpan Real s).direction := by rw [hs]; infer_instance
  refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_mono Real hps)) ?_
  rw [hs]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [ha.finrank_vectorSpan (Fintype.card_fin _)]; rw [t.independent.finrank_vectorSpan (Fintype.card_fin _)]

中文:
定理 affineSpan_of_orthocentricSystem
  结论: {s : 集合 P} (ho : OrthocentricSystem s) {p : 有限集 3 -> P}
  证明: by
  have ha := ho.affineIndependent hps hpi
  rcases ho with ⟨t, _, hts⟩
  have hs : affineSpan Real s = affineSpan Real (Set.range t.points) := by
    rw [hts]; rw [affineSpan_insert_eq_affineSpan Real t.orthocenter_mem_affineSpan]
  refine ext_of_direction_eq ?_
    ⟨p 0, mem_affineSpan Real (Set.mem_range_self _), mem_affineSpan Real (hps (Set.mem_range_self _))⟩
  have hfd : FiniteDimensional Real (affineSpan Real s).direction := by rw [hs]; infer_instance
  refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_mono Real hps)) ?_
  rw [hs]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [ha.finrank_vectorSpan (Fintype.card_fin _)]; rw [t.independent.finrank_vectorSpan (Fintype.card_fin _)]

Depends on / 依赖: FiniteDimensional, Set.mem_range_self, Set.range, Submodule, Submodule.eq_of_le_of_finrank_eq, affineIndependent, affineSpan, affineSpan_insert_eq_affineSpan, direction, direction_l, eq_of_le_of_finrank_eq, ext_of_direction_eq, ho.affineIndependent, infer_instance, mem_affineSpan, mem_range_self, orthocenter_mem_affineSpan, points, t.orthocenter_mem_affineSpan, t.points
-/
theorem affineSpan_of_orthocentricSystem {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 -> P}
    (hps : Set.range p subseteq s) (hpi : Function.Injective p) :
    affineSpan Real (Set.range p) = affineSpan Real s := by
  have ha := ho.affineIndependent hps hpi
  rcases ho with ⟨t, _, hts⟩
  have hs : affineSpan Real s = affineSpan Real (Set.range t.points) := by
    rw [hts]; rw [affineSpan_insert_eq_affineSpan Real t.orthocenter_mem_affineSpan]
  refine ext_of_direction_eq ?_
    ⟨p 0, mem_affineSpan Real (Set.mem_range_self _), mem_affineSpan Real (hps (Set.mem_range_self _))⟩
  have hfd : FiniteDimensional Real (affineSpan Real s).direction := by rw [hs]; infer_instance
  refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_mono Real hps)) ?_
  rw [hs]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [ha.finrank_vectorSpan (Fintype.card_fin _)]; rw [t.independent.finrank_vectorSpan (Fintype.card_fin _)]

/--
theorem `OrthocentricSystem.exists_circumradius_eq` / 定理 `OrthocentricSystem.exists_circumradius_eq`

English:
theorem OrthocentricSystem.exists_circumradius_eq
  given: {s : Set P} (ho : OrthocentricSystem s)
  proof: by
  rcases ho with ⟨t, hto, hts⟩
  use t.circumradius
  intro t₂ ht₂
  have ht₂s := ht₂
  rw [hts] at ht₂
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
      t₂.independent.injective with
    ⟨c, hc, h⟩
  rw [Set.forall_mem_range] at h
  have hs : Set.range t.points subseteq s := by
    rw [hts]
    exact Set.subset_insert _ _
  rw [affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ hs t.independent.injective]; rw [← affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ ht₂s t₂.independent.injective] at hc
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm

中文:
定理 OrthocentricSystem.存在_circumradius_eq
  条件: {s : 集合 P} (ho : OrthocentricSystem s)
  证明: by
  rcases ho with ⟨t, hto, hts⟩
  use t.circumradius
  intro t₂ ht₂
  have ht₂s := ht₂
  rw [hts] at ht₂
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
      t₂.independent.injective with
    ⟨c, hc, h⟩
  rw [Set.forall_mem_range] at h
  have hs : Set.range t.points subseteq s := by
    rw [hts]
    exact Set.subset_insert _ _
  rw [affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ hs t.independent.injective]; rw [← affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ ht₂s t₂.independent.injective] at hc
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm

Depends on / 依赖: Set.forall_mem_range, Set.range, Set.subset_insert, affineSpan_of_orthocentricSystem, circumradius, exists_dist_eq_circumradius_of_subset_insert_orthocenter, forall_mem_range, independent, independent.inj, independent.injective, injective, points, subset_insert, subseteq, t.circumradius, t.independent.injective, t.points
-/
theorem OrthocentricSystem.exists_circumradius_eq {s : Set P} (ho : OrthocentricSystem s) :
    exists r : Real, forall t : Triangle Real P, Set.range t.points subseteq s -> t.circumradius = r := by
  rcases ho with ⟨t, hto, hts⟩
  use t.circumradius
  intro t₂ ht₂
  have ht₂s := ht₂
  rw [hts] at ht₂
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
      t₂.independent.injective with
    ⟨c, hc, h⟩
  rw [Set.forall_mem_range] at h
  have hs : Set.range t.points subseteq s := by
    rw [hts]
    exact Set.subset_insert _ _
  rw [affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ hs t.independent.injective]; rw [← affineSpan_of_orthocentricSystem ⟨t]; rw [hto]; rw [hts⟩ ht₂s t₂.independent.injective] at hc
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm

/--
theorem `OrthocentricSystem.eq_insert_orthocenter` / 定理 `OrthocentricSystem.eq_insert_orthocenter`

English:
theorem OrthocentricSystem.eq_insert_orthocenter
  statement: {s : Set P} (ho : OrthocentricSystem s)
  proof: by
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩
  rw [ht₀s] at ht
  rcases exists_of_range_subset_orthocentricSystem ht₀o ht t.independent.injective with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
        exists j₁ : Fin 3, j₁ != j₂ ∧ j₁ != j₃ ∧ forall j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by
      clear h₂ h₃
      decide +revert
    suffices h : t₀.points j₁ = t.orthocenter by
      have hui : (Set.univ : Set (Fin 3)) = {i₁, i₂, i₃} := by ext x; simpa using h₁₂₃ x
      have huj : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by ext x; simpa using hj₁₂₃ x
      rw [← h]; rw [ht₀s]; rw [← Set.image_univ]; rw [huj]; rw [← Set.image_univ]; rw [hui]
      simp_rw [Set.image_insert_eq, Set.image_singleton, h₁, ← h₂, ← h₃]
      rw [Set.insert_comm]
    exact
      (Triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm
          h₃.symm).symm
  · rw [hs]
    convert! ht₀s using 2
    exact Triangle.orthocenter_eq_of_range_eq hs

中文:
定理 OrthocentricSystem.eq_insert_orthocenter
  结论: {s : 集合 P} (ho : OrthocentricSystem s)
  证明: by
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩
  rw [ht₀s] at ht
  rcases exists_of_range_subset_orthocentricSystem ht₀o ht t.independent.injective with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
        exists j₁ : Fin 3, j₁ != j₂ ∧ j₁ != j₃ ∧ forall j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by
      clear h₂ h₃
      decide +revert
    suffices h : t₀.points j₁ = t.orthocenter by
      have hui : (Set.univ : Set (Fin 3)) = {i₁, i₂, i₃} := by ext x; simpa using h₁₂₃ x
      have huj : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by ext x; simpa using hj₁₂₃ x
      rw [← h]; rw [ht₀s]; rw [← Set.image_univ]; rw [huj]; rw [← Set.image_univ]; rw [hui]
      simp_rw [Set.image_insert_eq, Set.image_singleton, h₁, ← h₂, ← h₃]
      rw [Set.insert_comm]
    exact
      (Triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm
          h₃.symm).symm
  · rw [hs]
    convert! ht₀s using 2
    exact Triangle.orthocenter_eq_of_range_eq hs

Depends on / 依赖: Set.univ, exists_of_range_subset_orthocentricSystem, independent, injective, orthocenter, points, revert, t.independent.injective, t.orthocenter
-/
theorem OrthocentricSystem.eq_insert_orthocenter {s : Set P} (ho : OrthocentricSystem s)
    {t : Triangle Real P} (ht : Set.range t.points subseteq s) :
    s = insert t.orthocenter (Set.range t.points) := by
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩
  rw [ht₀s] at ht
  rcases exists_of_range_subset_orthocentricSystem ht₀o ht t.independent.injective with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
        exists j₁ : Fin 3, j₁ != j₂ ∧ j₁ != j₃ ∧ forall j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by
      clear h₂ h₃
      decide +revert
    suffices h : t₀.points j₁ = t.orthocenter by
      have hui : (Set.univ : Set (Fin 3)) = {i₁, i₂, i₃} := by ext x; simpa using h₁₂₃ x
      have huj : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by ext x; simpa using hj₁₂₃ x
      rw [← h]; rw [ht₀s]; rw [← Set.image_univ]; rw [huj]; rw [← Set.image_univ]; rw [hui]
      simp_rw [Set.image_insert_eq, Set.image_singleton, h₁, ← h₂, ← h₃]
      rw [Set.insert_comm]
    exact
      (Triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm
          h₃.symm).symm
  · rw [hs]
    convert! ht₀s using 2
    exact Triangle.orthocenter_eq_of_range_eq hs

end EuclideanGeometry
