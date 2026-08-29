/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson, Li Jiale
-/
module


public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Similarity

/-!
# Power of a point (intersecting chords and secants)

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main definitions

* `Sphere.power`: The power of a point with respect to a sphere.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `Sphere.mul_dist_eq_abs_power`: The product of distances equals the absolute value of power.
* `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`: Tangent-Secant Theorem.
-/

@[expose] public section


open Real EuclideanGeometry RealInnerProductSpace Real Module FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

namespace InnerProductGeometry



/--
theorem `mul_norm_eq_abs_sub_sq_norm` / 定理 `mul_norm_eq_abs_sub_sq_norm`

English:
theorem mul_norm_eq_abs_sub_sq_norm
  statement: {x y z : V} (h₁ : exists k : Real, x = k • y)
  proof: by
  obtain ⟨r, hr⟩ := h₁
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hr, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ :

中文:
定理 mul_norm_eq_abs_sub_sq_norm
  结论: {x y z : V} (h₁ : 存在 k : 实数, x = k • y)
  证明: by
  obtain ⟨r, hr⟩ := h₁
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hr, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ :

Depends on / 依赖: abs_mul, add_smul, eq_comm, inner_eq_zero_iff_angle_eq_pi_div_two, inner_smul_right, mul_zero, norm_add_eq_norm_sub_iff_angle_eq_pi_div_two, norm_smul, simp_rw, sub_smul
-/
theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : exists k : Real, x = k • y)
    (h₃ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
  obtain ⟨r, hr⟩ := h₁
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hr, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ := by simp [sub_smul, add_smul, hr]
    _ = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) := by simp_rw [norm_smul]
    _ = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 := by ring
    _ = |(r - 1) * (r + 1) * ‖y‖ ^ 2| := by simp [abs_mul]
    _ = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| := by ring_nf
    _ = |‖x‖ ^ 2 - ‖y‖ ^ 2| := by simp [hr, norm_smul, mul_pow, sq_abs]
    _ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
      simp [norm_add_sq_real, norm_sub_sq_real, hzy, hzx, abs_sub_comm]

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry EuclideanGeometry

variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/--
theorem `mul_dist_eq_abs_sub_sq_dist` / 定理 `mul_dist_eq_abs_sub_sq_dist`

English:
theorem mul_dist_eq_abs_sub_sq_dist
  statement: {a b p q : P} (hp : p in line[Real, a, b])
  proof: by
  let m : P := midpoint Real a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h1' := vsub_sub_vsub_cancel_left p a m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : forall r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsu

中文:
定理 mul_dist_eq_abs_sub_sq_dist
  结论: {a b p q : P} (hp : p in line[实数, a, b])
  证明: by
  let m : P := midpoint Real a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h1' := vsub_sub_vsub_cancel_left p a m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : forall r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsu

Depends on / 依赖: add_comm, dist_eq_norm_vsub, iterate, midpoint, midpoint_vsub_left, right_vsub_midpoint, vsub_add_vsub_cancel, vsub_sub_vsub_cancel_left
-/
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : p in line[Real, a, b])
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| := by
  let m : P := midpoint Real a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h1' := vsub_sub_vsub_cancel_left p a m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : forall r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsub_left]; rw [← right_vsub_midpoint]; rw [add_comm]; rw [vsub_add_vsub_cancel]
  iterate 4 rw [dist_eq_norm_vsub V]
  rw [← h1]; rw [← h2]; rw [h]; rw [h]
  rw [dist_eq_norm_vsub V a q]; rw [dist_eq_norm_vsub V b q]; rw [← h3]; rw [h] at hq
  refine mul_norm_eq_abs_sub_sq_norm ?_ hq
  -- TODO: factor this out as a separate lemma?
  · rw [← vsub_vadd p a, vadd_left_mem_affineSpan_pair] at hp
    rcases hp with ⟨r, hr⟩
    rw [h]; rw [← h1']; rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at hr
    rw [hr]
    use 1 - r * 2
    match_scalars
    ring

/--
theorem `mul_dist_eq_mul_dist_of_cospherical` / 定理 `mul_dist_eq_mul_dist_of_cospherical`

English:
theorem mul_dist_eq_mul_dist_of_cospherical
  statement: {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
  proof: by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a (by simp), h' b (by simp), h' c (by simp), h' d (by simp)
  rw [← hd] at hc
  rw [← hb] at ha
  rw [mul_dist_eq_abs_sub_sq_dist hapb ha]; rw [hb]; rw [mul_dist_eq_abs_sub_sq_dist hcpd hc]; rw [hd]

中文:
定理 mul_dist_eq_mul_dist_of_cospherical
  结论: {a b c d p : P} (h : Cospherical ({a, b, c, d} : 集合 P))
  证明: by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a (by simp), h' b (by simp), h' c (by simp), h' d (by simp)
  rw [← hd] at hc
  rw [← hb] at ha
  rw [mul_dist_eq_abs_sub_sq_dist hapb ha]; rw [hb]; rw [mul_dist_eq_abs_sub_sq_dist hcpd hc]; rw [hd]

Depends on / 依赖: cospherical_def, mul_dist_eq_abs_sub_sq_dist
-/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : p in line[Real, a, b]) (hcpd : p in line[Real, c, d]) :
    dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a (by simp), h' b (by simp), h' c (by simp), h' d (by simp)
  rw [← hd] at hc
  rw [← hb] at ha
  rw [mul_dist_eq_abs_sub_sq_dist hapb ha]; rw [hb]; rw [mul_dist_eq_abs_sub_sq_dist hcpd hc]; rw [hd]

/--
theorem `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi` / 定理 `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`

English:
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi
  statement: {a b c d p : P}
  proof: by
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h hapb.wbtw.mem_affineSpan hcpd.wbtw.mem_affineSpan

中文:
定理 mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi
  结论: {a b c d p : P}
  证明: by
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h hapb.wbtw.mem_affineSpan hcpd.wbtw.mem_affineSpan

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.angle_eq_pi_iff_sbtw, angle_eq_pi_iff_sbtw, hapb.wbtw.mem_affineSpan, hcpd.wbtw.mem_affineSpan, mem_affineSpan, mul_dist_eq_mul_dist_of_cospherical
-/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h hapb.wbtw.mem_affineSpan hcpd.wbtw.mem_affineSpan

/--
lemma `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux` / 引理 `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux`

English:
lemma cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux
  proof: by
  suffices h_equiv : Cospherical ({p₁, p₂, p₄, p₃} : Set P) by grind [Set.pair_comm p₄ p₃]
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hp₃p₄]
  rw [angle_eq_pi_iff_sbtw] at hp₁p₂ hp₃p₄
  have hcol_p₁pp₂ := hp₁p₂.wbtw.collinea

中文:
引理 cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux
  证明: by
  suffices h_equiv : Cospherical ({p₁, p₂, p₄, p₃} : Set P) by grind [Set.pair_comm p₄ p₃]
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hp₃p₄]
  rw [angle_eq_pi_iff_sbtw] at hp₁p₂ hp₃p₄
  have hcol_p₁pp₂ := hp₁p₂.wbtw.collinea
-/
private lemma cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux
    [Fact (finrank Real V = 2)] [Oriented Real V (Fin 2)] {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear Real ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  suffices h_equiv : Cospherical ({p₁, p₂, p₄, p₃} : Set P) by grind [Set.pair_comm p₄ p₃]
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hp₃p₄]
  rw [angle_eq_pi_iff_sbtw] at hp₁p₂ hp₃p₄
  have hcol_p₁pp₂ := hp₁p₂.wbtw.collinear
  have hcol_p₃pp₄ := hp₃p₄.wbtw.collinear
  have h_notcol_p₁p₂p₃ : ¬ Collinear Real ({p₁, p₂, p₃} : Set P) := by
    have : AffineIndependent Real ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
    rw [← affineIndependent_iff_not_collinear_set]
    grind [hp₁p₂.left_ne_right, affineIndependent_of_affineIndependent_collinear_ne,
      AffineIndependent.comm_left, AffineIndependent.comm_right]
  apply cospherical_of_two_zsmul_oangle_eq_of_not_collinear ?_ h_notcol_p₁p₂p₃
  suffices ∡ p₁ p₂ p₃ = ∡ p₁ p₄ p₃ by grind
  suffices ∠ p₁ p₂ p₃ = ∠ p₁ p₄ p₃ by
    grind [oangle_eq_of_angle_eq_of_sign_eq, Sbtw.oangle_sign_eq_of_sbtw]
  rw [angle_comm]; rw [← angle_eq_angle_of_angle_eq_pi p₃ hp₁p₂.angle₃₂₁_eq_pi]; rw [← angle_eq_angle_of_angle_eq_pi p₁ hp₃p₄.angle₃₂₁_eq_pi]
  suffices h_sim : Similar ![p₁, p, p₄] ![p₃, p, p₂] by
    grind [angle_comm, h_sim.angle_eq_all.right.left]
  have h_notcol_p₁pp₄ : ¬ Collinear Real ({p₁, p, p₄} : Set P) := by
    intro hcol
    suffices hcol : Collinear Real ({p₁, p, p₃} : Set P) by grind
    suffices hcol : Collinear Real ({p₁, p₃, p, p₄} : Set P) by grind [Collinear.subset _ hcol]
    have hne_pp₄ := hp₃p₄.ne_right
    grind [collinear_insert_insert_of_mem_affineSpan_pair, Collinear.mem_affineSpan_of_mem_of_ne]
  have h_notcol_p₃pp₂ : ¬ Collinear Real ({p₃, p, p₂} : Set P) := by
    intro hcol
    suffices hcol : Collinear Real ({p₁, p, p₃} : Set P) by grind
    suffices hcol : Collinear Real ({p₃, p₁, p, p₂} : Set P) by grind [Collinear.subset _ hcol]
    have hne_pp₂ := hp₁p₂.ne_right
    grind [collinear_insert_insert_of_mem_affineSpan_pair, Collinear.mem_affineSpan_of_mem_of_ne]
  apply similar_of_side_angle_side h_notcol_p₁pp₄ h_notcol_p₃pp₂ h_angle_eq ?_
  grind [dist_comm]

/--
theorem `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi` / 定理 `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi`

English:
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi
  statement: {p₁ p₂ p₃ p₄ p : P}
  proof: by
  have hp₁p₂_sbtw : Sbtw Real p₁ p p₂ := angle_eq_pi_iff_sbtw.mp hp₁p₂
  have hp₃p₄_sbtw : Sbtw Real p₃ p p₄ := angle_eq_pi_iff_sbtw.mp hp₃p₄
  have hindep : AffineIndependent Real ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle Real P := ⟨_, hindep⟩ with 

中文:
定理 cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi
  结论: {p₁ p₂ p₃ p₄ p : P}
  证明: by
  have hp₁p₂_sbtw : Sbtw Real p₁ p p₂ := angle_eq_pi_iff_sbtw.mp hp₁p₂
  have hp₃p₄_sbtw : Sbtw Real p₃ p p₄ := angle_eq_pi_iff_sbtw.mp hp₃p₄
  have hindep : AffineIndependent Real ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle Real P := ⟨_, hindep⟩ with 

Depends on / 依赖: Affine, Affine.Triangle, AffineIndependent, AffineSubspace, Set.range, Triangle, affineIndependent_iff_not_collinear_set, affineIndependent_iff_not_collinear_set.mpr, affineSpan, affineSpan_mono, angle_eq_pi_iff_sbtw, angle_eq_pi_iff_sbtw.mp, hindep, points, t.points
-/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear Real ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hp₁p₂_sbtw : Sbtw Real p₁ p p₂ := angle_eq_pi_iff_sbtw.mp hp₁p₂
  have hp₃p₄_sbtw : Sbtw Real p₃ p p₄ := angle_eq_pi_iff_sbtw.mp hp₃p₄
  have hindep : AffineIndependent Real ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle Real P := ⟨_, hindep⟩ with ht
  set S : AffineSubspace Real P := affineSpan Real (Set.range t.points) with hS
  have hp₂ : p₂ in S := by
    suffices hmem : p₂ in affineSpan Real {p₁, p} by exact affineSpan_mono Real (by simp [ht]; grind) hmem
    simp [hp₁p₂_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₁p₂_sbtw.left_ne]
  have hp₄ : p₄ in S := by
    suffices hmem : p₄ in affineSpan Real {p₃, p} by exact affineSpan_mono Real (by simp [ht]; grind) hmem
    simp [hp₃p₄_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₃p₄_sbtw.left_ne]
  let s_isom : AffineIsometry Real S P := S.subtypeₐᵢ
  let p₁' : S := ⟨p₁, mem_affineSpan Real (s := Set.range t.points) (by aesop)⟩
  let p' : S := ⟨p, mem_affineSpan Real (s := Set.range t.points) (by aesop)⟩
  let p₃' : S := ⟨p₃, mem_affineSpan Real (s := Set.range t.points) (by aesop)⟩
  let p₂' : S := ⟨p₂, hp₂⟩
  let p₄' : S := ⟨p₄, hp₄⟩
  have h_dist' : dist p₁' p' * dist p₂' p' = dist p₃' p' * dist p₄' p' := by
    simpa [dist_eq_norm_vsub, ← s_isom.dist_map] using h
  have hp₁'p₂' : ∠ p₁' p' p₂' = π := by simpa [AffineIsometry.angle_map s_isom]
  have hp₃'p₄' : ∠ p₃' p' p₄' = π := by simpa [AffineIsometry.angle_map s_isom]
  suffices h_cospherical' : Cospherical {p₁', p₂', p₃', p₄'} by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Set.image_insert_eq, Set.image_singleton]` -/
    simpa [Set.image_insert_eq, Set.image_singleton] using Cospherical.subtype_val h_cospherical'
  have hf2 : Fact (finrank Real S.direction = 2) := ⟨by
    rw [hS]; rw [direction_affineSpan]; rw [t.independent.finrank_vectorSpan]
    simp⟩
  let : Module.Oriented Real S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  have hncol : ¬ Collinear Real {p₁', p', p₃'} := by
    rw [← affineIndependent_iff_not_collinear_set]; rw [← s_isom.toAffineMap.affineIndependent_iff s_isom.injective]
    convert! hindep
    ext i; fin_cases i <;> rfl
  exact cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux h_dist' hp₁'p₂' hp₃'p₄' hncol

/--
theorem `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero` / 定理 `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`

English:
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero
  statement: {a b c d p : P}
  proof: by
  apply collinear_of_angle_eq_zero at hapb
  apply collinear_of_angle_eq_zero at hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h
    (hapb.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
    (hcpd.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hcd)

中文:
定理 mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero
  结论: {a b c d p : P}
  证明: by
  apply collinear_of_angle_eq_zero at hapb
  apply collinear_of_angle_eq_zero at hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h
    (hapb.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
    (hcpd.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hcd)

Depends on / 依赖: collinear_of_angle_eq_zero, hapb.mem_affineSpan_of_mem_of_ne, hcpd.mem_affineSpan_of_mem_of_ne, mem_affineSpan_of_mem_of_ne, mul_dist_eq_mul_dist_of_cospherical
-/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a != b) (hcd : c != d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  apply collinear_of_angle_eq_zero at hapb
  apply collinear_of_angle_eq_zero at hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h
    (hapb.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
    (hcpd.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hcd)

namespace Sphere

/--
Definition of `power` / `power` 的定义

English:
definition power
  signature: (s : Sphere P) (p : P)
  body: dist p s.center ^ 2 - s.radius ^ 2

中文:
定义 power
  签名: (s : 球面 P) (p : P)
  定义体: dist p s.center ^ 2 - s.radius ^ 2

Depends on / 依赖: center, radius, s.center, s.radius
-/
def power (s : Sphere P) (p : P) : Real :=
  dist p s.center ^ 2 - s.radius ^ 2

/--
theorem `power_eq_zero_iff_mem_sphere` / 定理 `power_eq_zero_iff_mem_sphere`

English:
theorem power_eq_zero_iff_mem_sphere
  given: {s : Sphere P} {p : P} (hr : 0 <= s.radius)
  proof: by
  rw [power]; rw [mem_sphere]; rw [sub_eq_zero]; rw [pow_left_inj₀ dist_nonneg hr two_ne_zero]

中文:
定理 power_eq_zero_iff_mem_sphere
  条件: {s : 球面 P} {p : P} (hr : 0 <= s.radius)
  证明: by
  rw [power]; rw [mem_sphere]; rw [sub_eq_zero]; rw [pow_left_inj₀ dist_nonneg hr two_ne_zero]

Depends on / 依赖: dist_nonneg, mem_sphere, sub_eq_zero, two_ne_zero
-/
theorem power_eq_zero_iff_mem_sphere {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
    s.power p = 0 ↔ p in s := by
  rw [power]; rw [mem_sphere]; rw [sub_eq_zero]; rw [pow_left_inj₀ dist_nonneg hr two_ne_zero]

/--
theorem `power_pos_iff_radius_lt_dist_center` / 定理 `power_pos_iff_radius_lt_dist_center`

English:
theorem power_pos_iff_radius_lt_dist_center
  given: {s : Sphere P} {p : P} (hr : 0 <= s.radius)
  proof: by
  rw [power]; rw [sub_pos]; rw [pow_lt_pow_iff_left₀ hr dist_nonneg two_ne_zero]

中文:
定理 power_pos_iff_radius_lt_dist_center
  条件: {s : 球面 P} {p : P} (hr : 0 <= s.radius)
  证明: by
  rw [power]; rw [sub_pos]; rw [pow_lt_pow_iff_left₀ hr dist_nonneg two_ne_zero]

Depends on / 依赖: dist_nonneg, sub_pos, two_ne_zero
-/
theorem power_pos_iff_radius_lt_dist_center {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
    0 < s.power p ↔ s.radius < dist p s.center := by
  rw [power]; rw [sub_pos]; rw [pow_lt_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/--
theorem `power_neg_iff_dist_center_lt_radius` / 定理 `power_neg_iff_dist_center_lt_radius`

English:
theorem power_neg_iff_dist_center_lt_radius
  given: {s : Sphere P} {p : P} (hr : 0 <= s.radius)
  proof: by
  rw [power]; rw [sub_neg]; rw [pow_lt_pow_iff_left₀ dist_nonneg hr two_ne_zero]

中文:
定理 power_neg_iff_dist_center_lt_radius
  条件: {s : 球面 P} {p : P} (hr : 0 <= s.radius)
  证明: by
  rw [power]; rw [sub_neg]; rw [pow_lt_pow_iff_left₀ dist_nonneg hr two_ne_zero]

Depends on / 依赖: dist_nonneg, sub_neg, two_ne_zero
-/
theorem power_neg_iff_dist_center_lt_radius {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
  s.power p < 0 ↔ dist p s.center < s.radius := by
  rw [power]; rw [sub_neg]; rw [pow_lt_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/--
theorem `power_nonneg_iff_radius_le_dist_center` / 定理 `power_nonneg_iff_radius_le_dist_center`

English:
theorem power_nonneg_iff_radius_le_dist_center
  given: {s : Sphere P} {p : P} (hr : 0 <= s.radius)
  proof: by
  rw [power]; rw [sub_nonneg]; rw [pow_le_pow_iff_left₀ hr dist_nonneg two_ne_zero]

中文:
定理 power_nonneg_iff_radius_le_dist_center
  条件: {s : 球面 P} {p : P} (hr : 0 <= s.radius)
  证明: by
  rw [power]; rw [sub_nonneg]; rw [pow_le_pow_iff_left₀ hr dist_nonneg two_ne_zero]

Depends on / 依赖: dist_nonneg, sub_nonneg, two_ne_zero
-/
theorem power_nonneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
    0 <= s.power p ↔ s.radius <= dist p s.center := by
  rw [power]; rw [sub_nonneg]; rw [pow_le_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/--
theorem `power_nonpos_iff_dist_center_le_radius` / 定理 `power_nonpos_iff_dist_center_le_radius`

English:
theorem power_nonpos_iff_dist_center_le_radius
  given: {s : Sphere P} {p : P} (hr : 0 <= s.radius)
  proof: by
  rw [power]; rw [sub_nonpos]; rw [pow_le_pow_iff_left₀ dist_nonneg hr two_ne_zero]

中文:
定理 power_nonpos_iff_dist_center_le_radius
  条件: {s : 球面 P} {p : P} (hr : 0 <= s.radius)
  证明: by
  rw [power]; rw [sub_nonpos]; rw [pow_le_pow_iff_left₀ dist_nonneg hr two_ne_zero]

Depends on / 依赖: dist_nonneg, sub_nonpos, two_ne_zero
-/
theorem power_nonpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
    s.power p <= 0 ↔ dist p s.center <= s.radius := by
  rw [power]; rw [sub_nonpos]; rw [pow_le_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/--
theorem `mul_dist_eq_abs_power` / 定理 `mul_dist_eq_abs_power`

English:
theorem mul_dist_eq_abs_power
  statement: {s : Sphere P} {p a b : P}
  proof: by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [power]; rw [abs_sub_comm]

中文:
定理 mul_dist_eq_abs_power
  结论: {s : 球面 P} {p a b : P}
  证明: by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [power]; rw [abs_sub_comm]

Depends on / 依赖: abs_sub_comm, center, dist_comm, mem_sphere, mem_sphere.mp, mul_dist_eq_abs_sub_sq_dist, s.center
-/
theorem mul_dist_eq_abs_power {s : Sphere P} {p a b : P}
    (hp : p in line[Real, a, b])
    (ha : a in s) (hb : b in s) :
    dist p a * dist p b = |s.power p| := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [power]; rw [abs_sub_comm]

/--
theorem `mul_dist_eq_zero_of_mem_sphere` / 定理 `mul_dist_eq_zero_of_mem_sphere`

English:
theorem mul_dist_eq_zero_of_mem_sphere
  statement: {s : Sphere P} {p a b : P}
  proof: by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [mem_sphere.mp hp_on]; rw [sub_self]; rw [abs_zero]

中文:
定理 mul_dist_eq_zero_of_mem_sphere
  结论: {s : 球面 P} {p a b : P}
  证明: by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [mem_sphere.mp hp_on]; rw [sub_self]; rw [abs_zero]

Depends on / 依赖: abs_zero, center, dist_comm, hp_on, mem_sphere, mem_sphere.mp, mul_dist_eq_abs_sub_sq_dist, s.center, sub_self
-/
theorem mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P}
    (hp : p in line[Real, a, b])
    (ha : a in s) (hb : b in s)
    (hp_on : p in s) :
    dist p a * dist p b = 0 := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha]; rw [mem_sphere.mp hb]
  rw [dist_comm p a]; rw [dist_comm p b]; rw [mul_dist_eq_abs_sub_sq_dist hp hq]; rw [mem_sphere.mp hb]; rw [mem_sphere.mp hp_on]; rw [sub_self]; rw [abs_zero]

/--
theorem `mul_dist_eq_power_of_radius_le_dist_center` / 定理 `mul_dist_eq_power_of_radius_le_dist_center`

English:
theorem mul_dist_eq_power_of_radius_le_dist_center
  statement: {s : Sphere P} {p a b : P}
  proof: by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonneg (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

中文:
定理 mul_dist_eq_power_of_radius_le_dist_center
  结论: {s : 球面 P} {p a b : P}
  证明: by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonneg (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

Depends on / 依赖: abs_of_nonneg, mul_dist_eq_abs_power, power_nonneg_iff_radius_le_dist_center
-/
theorem mul_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P}
    (hr : 0 <= s.radius)
    (hp : p in line[Real, a, b])
    (ha : a in s) (hb : b in s)
    (hle : s.radius <= dist p s.center) :
    dist p a * dist p b = s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonneg (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

/--
theorem `mul_dist_eq_neg_power_of_dist_center_le_radius` / 定理 `mul_dist_eq_neg_power_of_dist_center_le_radius`

English:
theorem mul_dist_eq_neg_power_of_dist_center_le_radius
  statement: {s : Sphere P} {p a b : P}
  proof: by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonpos (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

中文:
定理 mul_dist_eq_neg_power_of_dist_center_le_radius
  结论: {s : 球面 P} {p a b : P}
  证明: by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonpos (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

Depends on / 依赖: abs_of_nonpos, mul_dist_eq_abs_power, power_nonpos_iff_dist_center_le_radius
-/
theorem mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P}
    (hr : 0 <= s.radius)
    (hp : p in line[Real, a, b])
    (ha : a in s) (hb : b in s)
    (hle : dist p s.center <= s.radius) :
    dist p a * dist p b = -s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb]; rw [abs_of_nonpos (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

/--
theorem `dist_sq_eq_mul_dist_of_tangent_and_secant` / 定理 `dist_sq_eq_mul_dist_of_tangent_and_secant`

English:
theorem dist_sq_eq_mul_dist_of_tangent_and_secant
  statement: {a b t p : P} {s : Sphere P}
  proof: by
  have hr := radius_nonneg_of_mem ha
  have radius_le_dist := h_tangent.isTangent.radius_le_dist_center (left_mem_affineSpan_pair Real p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb radius_le_dist]; rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Re

中文:
定理 dist_sq_eq_mul_dist_of_tangent_and_secant
  结论: {a b t p : P} {s : 球面 P}
  证明: by
  have hr := radius_nonneg_of_mem ha
  have radius_le_dist := h_tangent.isTangent.radius_le_dist_center (left_mem_affineSpan_pair Real p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb radius_le_dist]; rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Re

Depends on / 依赖: Sphere, Sphere.power, dist_sq_eq_of_mem, h_tangent, h_tangent.dist_sq_eq_of_mem, h_tangent.isTangent.radius_le_dist_center, isTangent, left_mem_affineSpan_pair, mul_dist_eq_power_of_radius_le_dist_center, radius_le_dist, radius_le_dist_center, radius_nonneg_of_mem
-/
theorem dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P}
    (ha : a in s) (hb : b in s)
    (hp : p in line[Real, a, b])
    (h_tangent : s.IsTangentAt t (line[Real, p, t])) :
    dist p t ^ 2 = dist p a * dist p b := by
  have hr := radius_nonneg_of_mem ha
  have radius_le_dist := h_tangent.isTangent.radius_le_dist_center (left_mem_affineSpan_pair Real p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb radius_le_dist]; rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Real p t)]
  ring

/--
theorem `IsTangentAt.power_eq_dist_sq` / 定理 `IsTangentAt.power_eq_dist_sq`

English:
theorem IsTangentAt.power_eq_dist_sq
  statement: {s : Sphere P} {t p : P}
  proof: by
  rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Real p t)]
  ring_nf

中文:
定理 是TangentAt.power_eq_dist_sq
  结论: {s : 球面 P} {t p : P}
  证明: by
  rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Real p t)]
  ring_nf

Depends on / 依赖: Sphere, Sphere.power, dist_sq_eq_of_mem, h_tangent, h_tangent.dist_sq_eq_of_mem, left_mem_affineSpan_pair, ring_nf
-/
theorem IsTangentAt.power_eq_dist_sq {s : Sphere P} {t p : P}
    (h_tangent : s.IsTangentAt t (line[Real, p, t])) :
    s.power p = dist p t ^ 2 := by
  rw [Sphere.power]; rw [h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair Real p t)]
  ring_nf

/--
theorem `isTangentAt_iff_dist_sq_eq_power` / 定理 `isTangentAt_iff_dist_sq_eq_power`

English:
theorem isTangentAt_iff_dist_sq_eq_power
  given: {t p : P} {s : Sphere P} (ht : t in s)
  proof: ⟨fun h => h.power_eq_dist_sq.symm, fun h_dist_eq => by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by
      simp only [Sphere.power, ← mem_sphere.mp ht, dist_eq_norm_vsub V, sq,
                 ← vsub_add_vsub_cancel p t s.center] at h_dist_eq
      exact (norm_add_sq_eq_norm_sq_add_norm_sq_if

中文:
定理 isTangentAt_iff_dist_sq_eq_power
  条件: {t p : P} {s : 球面 P} (ht : t in s)
  证明: ⟨fun h => h.power_eq_dist_sq.symm, fun h_dist_eq => by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by
      simp only [Sphere.power, ← mem_sphere.mp ht, dist_eq_norm_vsub V, sq,
                 ← vsub_add_vsub_cancel p t s.center] at h_dist_eq
      exact (norm_add_sq_eq_norm_sq_add_norm_sq_if

Depends on / 依赖: Sphere, Sphere.power, center, dist_eq_norm_vsub, h.power_eq_dist_sq.symm, h_dist_eq, h_orth, mem_orthRadius_iff_inner_left, mem_sphere, mem_sphere.mp, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, power_eq_dist_sq, right_mem_affineSpan_pair, s.center, vadd_right_mem_affineSpan_pair, vsub_add_vsub_cancel, vsub_vadd
-/
theorem isTangentAt_iff_dist_sq_eq_power {t p : P} {s : Sphere P} (ht : t in s) :
    s.IsTangentAt t (line[Real, p, t]) ↔ dist p t ^ 2 = s.power p :=
  ⟨fun h => h.power_eq_dist_sq.symm, fun h_dist_eq => by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by
      simp only [Sphere.power, ← mem_sphere.mp ht, dist_eq_norm_vsub V, sq,
                 ← vsub_add_vsub_cancel p t s.center] at h_dist_eq
      exact (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero _ _).mp (by linarith)
    refine ⟨ht, right_mem_affineSpan_pair Real p t, fun x hx => ?_⟩
    rw [mem_orthRadius_iff_inner_left]
    obtain ⟨r, hr⟩ := (vadd_right_mem_affineSpan_pair (k := Real)).mp (vsub_vadd x t ▸ hx)
    rw [← hr]; rw [inner_smul_left]; rw [h_orth]; rw [mul_zero]⟩

alias ⟨_, isTangentAt_of_dist_sq_eq_power⟩ := isTangentAt_iff_dist_sq_eq_power

end Sphere

end EuclideanGeometry
