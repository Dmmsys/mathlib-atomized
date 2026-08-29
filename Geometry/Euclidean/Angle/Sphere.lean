/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

/-!
# Angles in circles and spheres

This file proves results about angles in circles and spheres.

-/

public section


noncomputable section

open Module Complex

open scoped EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
variable [Fact (finrank Real V = 2)] (o : Orientation Real V (Fin 2))

/--
theorem `oangle_eq_two_zsmul_oangle_sub_of_norm_eq` / 定理 `oangle_eq_two_zsmul_oangle_sub_of_norm_eq`

English:
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq
  statement: {x y z : V} (hxyne : x != y) (hxzne : x != z)
  proof: by
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x != 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z != 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc
    o.oangle y z = o.oangle x z - o.oa

中文:
定理 oangle_eq_two_zsmul_oangle_sub_of_norm_eq
  结论: {x y z : V} (hxyne : x != y) (hxzne : x != z)
  证明: by
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x != 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z != 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc
    o.oangle y z = o.oangle x z - o.oa

Depends on / 依赖: hxy.symm, hxz.symm, hxzne.symm, norm_eq_zero, norm_ne_zero_iff, norm_zero, o.oangle, o.oangle_eq_p, o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, o.oangle_sub_left, oangle, oangle_eq_p, oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, oangle_sub_left
-/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x != y) (hxzne : x != z)
    (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : Int) • o.oangle (y - x) (z - x) := by
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x != 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z != 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc
    o.oangle y z = o.oangle x z - o.oangle x y := (o.oangle_sub_left hx hy hz).symm
    _ = π - (2 : Int) • o.oangle (x - z) x - (π - (2 : Int) • o.oangle (x - y) x) := by
      rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm]; rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
    _ = (2 : Int) • (o.oangle (x - y) x - o.oangle (x - z) x) := by abel
    _ = (2 : Int) • o.oangle (x - y) (x - z) := by
      rw [o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx]
    _ = (2 : Int) • o.oangle (y - x) (z - x) := by rw [← oangle_neg_neg, neg_sub, neg_sub]

/--
theorem `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real` / 定理 `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real`

English:
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
  statement: {x y z : V} (hxyne : x != y) (hxzne : x != z)
  proof: o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

中文:
定理 oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
  结论: {x y z : V} (hxyne : x != y) (hxzne : x != z)
  证明: o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

Depends on / 依赖: hy.symm, hz.symm, o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq, oangle_eq_two_zsmul_oangle_sub_of_norm_eq
-/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x != y) (hxzne : x != z)
    {r : Real} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    o.oangle y z = (2 : Int) • o.oangle (y - x) (z - x) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/--
theorem `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq` / 定理 `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq`

English:
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
  statement: {x₁ x₂ y z : V} (hx₁yne : x₁ != y)
  proof: o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

中文:
定理 two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
  结论: {x₁ x₂ y z : V} (hx₁yne : x₁ != y)
  证明: o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

Depends on / 依赖: o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real, oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
-/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ != y)
    (hx₁zne : x₁ != z) (hx₂yne : x₂ != y) (hx₂zne : x₂ != z) {r : Real} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r)
    (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    (2 : Int) • o.oangle (y - x₁) (z - x₁) = (2 : Int) • o.oangle (y - x₂) (z - x₂) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

end Orientation

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Sphere

open Real InnerProductSpace InnerProductGeometry

/--
theorem `angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter` / 定理 `angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter`

English:
theorem angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter
  statement: {p₁ p₂ p₃ : P} {s : Sphere P}
  proof: by
  rw [mem_sphere']; rw [EuclideanGeometry.angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  let o := s.center
  have h_center : o = midpoint Real p₁ p₃ := hd.midpoint_eq_center.symm
  rw [← vsub_add_vsub_cancel p₁ o p₂]; rw [← vsub_add_vsub_cancel p₃ o p₂]; rw [inner_add

中文:
定理 angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter
  结论: {p₁ p₂ p₃ : P} {s : 球面 P}
  证明: by
  rw [mem_sphere']; rw [EuclideanGeometry.angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  let o := s.center
  have h_center : o = midpoint Real p₁ p₃ := hd.midpoint_eq_center.symm
  rw [← vsub_add_vsub_cancel p₁ o p₂]; rw [← vsub_add_vsub_cancel p₃ o p₂]; rw [inner_add

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.angle, InnerProductGeometry, InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, center, h_center, h_op, h_opp, hd.midpoint_eq_center.symm, inner_add_left, inner_add_right, inner_eq_zero_iff_angle_eq_pi_div_two, left_vsub_midpoint, mem_sphere, midpoint, midpoint_eq_center, neg_vsub_eq_vsub_rev, right_vsub_midpoint, s.center, smul_neg
-/
theorem angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter {p₁ p₂ p₃ : P} {s : Sphere P}
    (hd : s.IsDiameter p₁ p₃) :
    ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ in s := by
  rw [mem_sphere']; rw [EuclideanGeometry.angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  let o := s.center
  have h_center : o = midpoint Real p₁ p₃ := hd.midpoint_eq_center.symm
  rw [← vsub_add_vsub_cancel p₁ o p₂]; rw [← vsub_add_vsub_cancel p₃ o p₂]; rw [inner_add_left]; rw [inner_add_right]; rw [inner_add_right]
  have h_opp : p₁ -ᵥ o = -(p₃ -ᵥ o) := by
    rw [h_center]; rw [left_vsub_midpoint]; rw [right_vsub_midpoint]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]
  rw [h_opp]; rw [inner_neg_left]; rw [inner_neg_left]; rw [real_inner_comm (p₃ -ᵥ o) (o -ᵥ p₂)]
  ring_nf
  rw [neg_add_eq_zero]; rw [real_inner_self_eq_norm_sq]; rw [← dist_eq_norm_vsub]; rw [real_inner_self_eq_norm_sq]; rw [← dist_eq_norm_vsub]; rw [sq_eq_sq₀ dist_nonneg dist_nonneg]; rw [mem_sphere.mp hd.right_mem]
  exact eq_comm

/--
theorem `angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` / 定理 `angle_eq_pi_div_two_iff_mem_sphere_ofDiameter`

English:
theorem angle_eq_pi_div_two_iff_mem_sphere_ofDiameter
  given: {p₁ p₂ p₃ : P}
  proof: angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter (Sphere.isDiameter_ofDiameter p₁ p₃)

alias thales_theorem := angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter

中文:
定理 angle_eq_pi_div_two_iff_mem_sphere_ofDiameter
  条件: {p₁ p₂ p₃ : P}
  证明: angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter (Sphere.isDiameter_ofDiameter p₁ p₃)

alias thales_theorem := angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter

Depends on / 依赖: Sphere, Sphere.isDiameter_ofDiameter, angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter, isDiameter_ofDiameter
-/
theorem angle_eq_pi_div_two_iff_mem_sphere_ofDiameter {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ in Sphere.ofDiameter p₁ p₃ :=
  angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter (Sphere.isDiameter_ofDiameter p₁ p₃)

alias thales_theorem := angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter

/--
theorem `isDiameter_of_angle_eq_pi_div_two` / 定理 `isDiameter_of_angle_eq_pi_div_two`

English:
theorem isDiameter_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} {s : Sphere P}
  proof: by
  have : FiniteDimensional Real V := .of_finrank_eq_succ (Fact.out : finrank Real V = 2)
  have hne₁₃ : p₁ != p₃ := fun h => by
    rw [h]; rw [angle_self_of_ne hne₂₃.symm] at hangle; linarith [Real.pi_pos]
  have hd := Sphere.isDiameter_ofDiameter p₁ p₃
  have h_eq : s = Sphere.ofDiameter p₁ p₃ 

中文:
定理 isDiameter_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} {s : 球面 P}
  证明: by
  have : FiniteDimensional Real V := .of_finrank_eq_succ (Fact.out : finrank Real V = 2)
  have hne₁₃ : p₁ != p₃ := fun h => by
    rw [h]; rw [angle_self_of_ne hne₂₃.symm] at hangle; linarith [Real.pi_pos]
  have hd := Sphere.isDiameter_ofDiameter p₁ p₃
  have h_eq : s = Sphere.ofDiameter p₁ p₃ 

Depends on / 依赖: Fact.out, FiniteDimensional, Real.pi_pos, Sphere, Sphere.isDiameter_ofDiameter, Sphere.ofDiameter, angle_eq_pi_div_two_iff_mem_sphere_ofDiameter, angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.mp, angle_self_of_ne, eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two, finrank, h_eq, hangle, hd.left_mem, hd.right_mem, isDiameter_ofDiameter, left_mem, ofDiameter, of_finrank_eq_succ, pi_pos
-/
theorem isDiameter_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} {s : Sphere P}
    [Fact (finrank Real V = 2)]
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s)
    (hne₁₂ : p₁ != p₂) (hne₂₃ : p₂ != p₃)
    (hangle : ∠ p₁ p₂ p₃ = π / 2) :
    s.IsDiameter p₁ p₃ := by
  have : FiniteDimensional Real V := .of_finrank_eq_succ (Fact.out : finrank Real V = 2)
  have hne₁₃ : p₁ != p₃ := fun h => by
    rw [h]; rw [angle_self_of_ne hne₂₃.symm] at hangle; linarith [Real.pi_pos]
  have hd := Sphere.isDiameter_ofDiameter p₁ p₃
  have h_eq : s = Sphere.ofDiameter p₁ p₃ := by
    by_contra hne
    have := eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (Fact.out : finrank Real V = 2) hne hne₁₃ hp₁ hp₃ hp₂
      hd.left_mem hd.right_mem (angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.mp hangle)
    exact this.elim hne₁₂.symm hne₂₃
  exact h_eq ▸ hd

/--
theorem `angle_center_eq_pi_iff_isDiameter` / 定理 `angle_center_eq_pi_iff_isDiameter`

English:
theorem angle_center_eq_pi_iff_isDiameter
  statement: {s : Sphere P} {p₁ p₂ : P}
  proof: by
  rw [angle_eq_pi_iff_sbtw]
  exact ⟨fun h => isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨hp₁, hp₂, h.wbtw⟩, fun h => h.sbtw hr⟩

中文:
定理 angle_center_eq_pi_iff_isDiameter
  结论: {s : 球面 P} {p₁ p₂ : P}
  证明: by
  rw [angle_eq_pi_iff_sbtw]
  exact ⟨fun h => isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨hp₁, hp₂, h.wbtw⟩, fun h => h.sbtw hr⟩

Depends on / 依赖: angle_eq_pi_iff_sbtw, h.sbtw, h.wbtw, isDiameter_iff_mem_and_mem_and_wbtw
-/
theorem angle_center_eq_pi_iff_isDiameter {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hr : s.radius != 0) :
    ∠ p₁ s.center p₂ = π ↔ s.IsDiameter p₁ p₂ := by
  rw [angle_eq_pi_iff_sbtw]
  exact ⟨fun h => isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨hp₁, hp₂, h.wbtw⟩, fun h => h.sbtw hr⟩

/--
theorem `angle_center_eq_zero_iff_eq` / 定理 `angle_center_eq_zero_iff_eq`

English:
theorem angle_center_eq_zero_iff_eq
  statement: {s : Sphere P} {p₁ p₂ : P}
  proof: by
  constructor
  · intro h
    refine vsub_left_cancel (eq_of_angle_eq_zero_of_norm_eq (by simpa [angle] using h) ?_)
    rw [norm_vsub_center_eq_radius hp₁]; rw [norm_vsub_center_eq_radius hp₂]
  · rintro rfl
    exact angle_self_of_ne fun h => hr (center_mem_iff.mp (h ▸ hp₁))

中文:
定理 angle_center_eq_zero_iff_eq
  结论: {s : 球面 P} {p₁ p₂ : P}
  证明: by
  constructor
  · intro h
    refine vsub_left_cancel (eq_of_angle_eq_zero_of_norm_eq (by simpa [angle] using h) ?_)
    rw [norm_vsub_center_eq_radius hp₁]; rw [norm_vsub_center_eq_radius hp₂]
  · rintro rfl
    exact angle_self_of_ne fun h => hr (center_mem_iff.mp (h ▸ hp₁))

Depends on / 依赖: angle_self_of_ne, center_mem_iff, center_mem_iff.mp, eq_of_angle_eq_zero_of_norm_eq, norm_vsub_center_eq_radius, vsub_left_cancel
-/
theorem angle_center_eq_zero_iff_eq {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hr : s.radius != 0) :
    ∠ p₁ s.center p₂ = 0 ↔ p₁ = p₂ := by
  constructor
  · intro h
    refine vsub_left_cancel (eq_of_angle_eq_zero_of_norm_eq (by simpa [angle] using h) ?_)
    rw [norm_vsub_center_eq_radius hp₁]; rw [norm_vsub_center_eq_radius hp₂]
  · rintro rfl
    exact angle_self_of_ne fun h => hr (center_mem_iff.mp (h ▸ hp₁))

/--
theorem `IsTangentAt.angle_eq_pi_div_two` / 定理 `IsTangentAt.angle_eq_pi_div_two`

English:
theorem IsTangentAt.angle_eq_pi_div_two
  statement: {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
  proof: by
  have h1 := IsTangentAt.inner_left_eq_zero_of_mem h hq_mem
  rw [inner_eq_zero_iff_angle_eq_pi_div_two] at h1
  rw [angle]; rw [← neg_vsub_eq_vsub_rev _ s.center]; rw [angle_neg_right]; rw [h1]
  linarith

中文:
定理 是TangentAt.angle_eq_pi_div_two
  结论: {s : 球面 P} {p q : P} {as : 仿射子空间 实数 P}
  证明: by
  have h1 := IsTangentAt.inner_left_eq_zero_of_mem h hq_mem
  rw [inner_eq_zero_iff_angle_eq_pi_div_two] at h1
  rw [angle]; rw [← neg_vsub_eq_vsub_rev _ s.center]; rw [angle_neg_right]; rw [h1]
  linarith

Depends on / 依赖: IsTangentAt, IsTangentAt.inner_left_eq_zero_of_mem, angle_neg_right, center, hq_mem, inner_eq_zero_iff_angle_eq_pi_div_two, inner_left_eq_zero_of_mem, neg_vsub_eq_vsub_rev, s.center
-/
theorem IsTangentAt.angle_eq_pi_div_two {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) (hq_mem : q in as) :
    ∠ q p s.center = π / 2 := by
  have h1 := IsTangentAt.inner_left_eq_zero_of_mem h hq_mem
  rw [inner_eq_zero_iff_angle_eq_pi_div_two] at h1
  rw [angle]; rw [← neg_vsub_eq_vsub_rev _ s.center]; rw [angle_neg_right]; rw [h1]
  linarith

/--
theorem `IsTangentAt_of_angle_eq_pi_div_two` / 定理 `IsTangentAt_of_angle_eq_pi_div_two`

English:
theorem IsTangentAt_of_angle_eq_pi_div_two
  statement: {s : Sphere P} {p q : P} (h : ∠ q p s.center = π / 2)
  proof: by
  have hp_mem := left_mem_affineSpan_pair Real p q
  refine ⟨hp, hp_mem, ?_⟩
  have h_ortho : ⟪q -ᵥ p, p -ᵥ s.center⟫ = 0 := by
    rwa [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, ← neg_vsub_eq_vsub_rev p s.center,
      inner_neg_right, neg_eq_zero] at h
  have hq : q in s.orthRadius p := b

中文:
定理 IsTangentAt_of_angle_eq_pi_div_two
  结论: {s : 球面 P} {p q : P} (h : ∠ q p s.center = π / 2)
  证明: by
  have hp_mem := left_mem_affineSpan_pair Real p q
  refine ⟨hp, hp_mem, ?_⟩
  have h_ortho : ⟪q -ᵥ p, p -ᵥ s.center⟫ = 0 := by
    rwa [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, ← neg_vsub_eq_vsub_rev p s.center,
      inner_neg_right, neg_eq_zero] at h
  have hq : q in s.orthRadius p := b

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, Sphere, Sphere.mem_orthRadius_iff_inner_left, Sphere.self_mem_orthRadius, affineSpan_le, center, h_ortho, hp_mem, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_right, insert_subset_iff, left_mem_affineSpan_pair, mem_orthRadius_iff_inner_left, neg_eq_zero, neg_vsub_eq_vsub_rev, orthRadius, s.center, s.orthRadius, self_mem_orthRadius
-/
theorem IsTangentAt_of_angle_eq_pi_div_two {s : Sphere P} {p q : P} (h : ∠ q p s.center = π / 2)
    (hp : p in s) :
    s.IsTangentAt p line[Real, p, q] := by
  have hp_mem := left_mem_affineSpan_pair Real p q
  refine ⟨hp, hp_mem, ?_⟩
  have h_ortho : ⟪q -ᵥ p, p -ᵥ s.center⟫ = 0 := by
    rwa [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, ← neg_vsub_eq_vsub_rev p s.center,
      inner_neg_right, neg_eq_zero] at h
  have hq : q in s.orthRadius p := by
    simp [Sphere.mem_orthRadius_iff_inner_left, h_ortho]
  rw [affineSpan_le]
  have hp : p in s.orthRadius p := by
    simp [Sphere.self_mem_orthRadius]
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp, hq⟩

/--
theorem `IsTangentAt_iff_angle_eq_pi_div_two` / 定理 `IsTangentAt_iff_angle_eq_pi_div_two`

English:
theorem IsTangentAt_iff_angle_eq_pi_div_two
  given: {s : Sphere P} {p q : P} (hp : p in s)
  proof: by
  exact ⟨fun h => IsTangentAt.angle_eq_pi_div_two h (right_mem_affineSpan_pair Real p q),
    fun h => IsTangentAt_of_angle_eq_pi_div_two h hp⟩

中文:
定理 IsTangentAt_iff_angle_eq_pi_div_two
  条件: {s : 球面 P} {p q : P} (hp : p in s)
  证明: by
  exact ⟨fun h => IsTangentAt.angle_eq_pi_div_two h (right_mem_affineSpan_pair Real p q),
    fun h => IsTangentAt_of_angle_eq_pi_div_two h hp⟩

Depends on / 依赖: IsTangentAt, IsTangentAt.angle_eq_pi_div_two, IsTangentAt_of_angle_eq_pi_div_two, angle_eq_pi_div_two, right_mem_affineSpan_pair
-/
theorem IsTangentAt_iff_angle_eq_pi_div_two {s : Sphere P} {p q : P} (hp : p in s) :
    s.IsTangentAt p line[Real, p, q] ↔ ∠ q p s.center = π / 2 := by
  exact ⟨fun h => IsTangentAt.angle_eq_pi_div_two h (right_mem_affineSpan_pair Real p q),
    fun h => IsTangentAt_of_angle_eq_pi_div_two h hp⟩

end Sphere

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

namespace Sphere

/--
theorem `oangle_center_eq_two_zsmul_oangle` / 定理 `oangle_center_eq_two_zsmul_oangle`

English:
theorem oangle_center_eq_two_zsmul_oangle
  statement: {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  proof: by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃
  rw [oangle]; rw [oangle]; rw [o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃] <;>
    simp [hp₂p₁, hp₂p₃]

中文:
定理 oangle_center_eq_two_zsmul_oangle
  结论: {s : 球面 P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  证明: by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃
  rw [oangle]; rw [oangle]; rw [o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃] <;>
    simp [hp₂p₁, hp₂p₃]

Depends on / 依赖: dist_eq_norm_vsub, mem_sphere, o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real, oangle, oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
-/
theorem oangle_center_eq_two_zsmul_oangle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₃ : p₂ != p₃) :
    ∡ p₁ s.center p₃ = (2 : Int) • ∡ p₁ p₂ p₃ := by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃
  rw [oangle]; rw [oangle]; rw [o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃] <;>
    simp [hp₂p₁, hp₂p₃]

/--
theorem `two_zsmul_oangle_eq` / 定理 `two_zsmul_oangle_eq`

English:
theorem two_zsmul_oangle_eq
  statement: {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  proof: by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [←
      vsub_sub_vsub_cancel_right p₄ p₂ s.center]; rw [o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄] <;>
    simp

中文:
定理 two_zsmul_oangle_eq
  结论: {s : 球面 P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  证明: by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [←
      vsub_sub_vsub_cancel_right p₄ p₂ s.center]; rw [o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄] <;>
    simp

Depends on / 依赖: center, dist_eq_norm_vsub, mem_sphere, o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq, oangle, s.center, two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq, vsub_sub_vsub_cancel_right
-/
theorem two_zsmul_oangle_eq {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
    (hp₃ : p₃ in s) (hp₄ : p₄ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₄ : p₂ != p₄) (hp₃p₁ : p₃ != p₁)
    (hp₃p₄ : p₃ != p₄) : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄ := by
  rw [mem_sphere]; rw [@dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [←
      vsub_sub_vsub_cancel_right p₄ p₂ s.center]; rw [o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄] <;>
    simp [hp₂p₁, hp₂p₄, hp₃p₁, hp₃p₄]

end Sphere

/--
theorem `Cospherical.two_zsmul_oangle_eq` / 定理 `Cospherical.two_zsmul_oangle_eq`

English:
theorem Cospherical.two_zsmul_oangle_eq
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  exact Sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄

中文:
定理 Cospherical.two_zsmul_oangle_eq
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  exact Sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, Sphere, Sphere.mem_coe, Sphere.two_zsmul_oangle_eq, cospherical_iff_exists_sphere, insert_subset_iff, mem_coe, simp_rw, singleton_subset_iff, two_zsmul_oangle_eq
-/
theorem Cospherical.two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : Cospherical ({p₁, p₂, p₃, p₄} : Set P)) (hp₂p₁ : p₂ != p₁) (hp₂p₄ : p₂ != p₄)
    (hp₃p₁ : p₃ != p₁) (hp₃p₄ : p₃ != p₄) : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄ := by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  exact Sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄

namespace Sphere

/--
theorem `oangle_eq_pi_sub_two_zsmul_oangle_center_left` / 定理 `oangle_eq_pi_sub_two_zsmul_oangle_center_left`

English:
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_left
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

中文:
定理 oangle_eq_pi_sub_two_zsmul_oangle_center_left
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

Depends on / 依赖: dist_center_eq_dist_center_of_mem_sphere, h.symm, oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ = π - (2 : Int) • ∡ s.center p₂ p₁ := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/--
theorem `oangle_eq_pi_sub_two_zsmul_oangle_center_right` / 定理 `oangle_eq_pi_sub_two_zsmul_oangle_center_right`

English:
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_right
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h]; rw [oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

中文:
定理 oangle_eq_pi_sub_two_zsmul_oangle_center_right
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h]; rw [oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

Depends on / 依赖: dist_center_eq_dist_center_of_mem_sphere, oangle_eq_oangle_of_dist_eq, oangle_eq_pi_sub_two_zsmul_oangle_center_left
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ = π - (2 : Int) • ∡ p₂ p₁ s.center := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h]; rw [oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/--
theorem `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi` / 定理 `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi`

English:
theorem two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  statement: {s : Sphere P} {p₁ p₂ p₃ : P}
  proof: by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃]; rw [oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃]; rw [add_sub_cancel]

中文:
定理 two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  结论: {s : 球面 P} {p₁ p₂ p₃ : P}
  证明: by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃]; rw [oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃]; rw [add_sub_cancel]

Depends on / 依赖: add_sub_cancel, oangle_center_eq_two_zsmul_oangle, oangle_eq_pi_sub_two_zsmul_oangle_center_right
-/
theorem two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₃ : p₂ != p₃)
    (hp₁p₃ : p₁ != p₃) : (2 : Int) • ∡ p₃ p₁ s.center + (2 : Int) • ∡ p₁ p₂ p₃ = π := by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃]; rw [oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃]; rw [add_sub_cancel]

/--
theorem `abs_oangle_center_left_toReal_lt_pi_div_two` / 定理 `abs_oangle_center_left_toReal_lt_pi_div_two`

English:
theorem abs_oangle_center_left_toReal_lt_pi_div_two
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

中文:
定理 abs_oangle_center_left_to实数_lt_pi_div_two
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

Depends on / 依赖: abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq, dist_center_eq_dist_center_of_mem_sphere
-/
theorem abs_oangle_center_left_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) : |(∡ s.center p₂ p₁).toReal| < π / 2 :=
  abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/--
theorem `abs_oangle_center_right_toReal_lt_pi_div_two` / 定理 `abs_oangle_center_right_toReal_lt_pi_div_two`

English:
theorem abs_oangle_center_right_toReal_lt_pi_div_two
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

中文:
定理 abs_oangle_center_right_to实数_lt_pi_div_two
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

Depends on / 依赖: abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq, dist_center_eq_dist_center_of_mem_sphere
-/
theorem abs_oangle_center_right_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) : |(∡ p₂ p₁ s.center).toReal| < π / 2 :=
  abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/--
theorem `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center` / 定理 `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center`

English:
theorem tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
  statement: {s : Sphere P} {p₁ p₂ : P}
  proof: by
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)
  rw [← hr]; rw [← oangle_midpoint_rev_left]; rw [oangle]; rw [vadd_vsub_assoc]
  nth_rw 1 [show p₂ -ᵥ p₁ = (2 : Real) • (midpoint Real p₁ p₂ -ᵥ p₁) by simp]
  rw

中文:
定理 tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
  结论: {s : 球面 P} {p₁ p₂ : P}
  证明: by
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)
  rw [← hr]; rw [← oangle_midpoint_rev_left]; rw [oangle]; rw [vadd_vsub_assoc]
  nth_rw 1 [show p₂ -ᵥ p₁ = (2 : Real) • (midpoint Real p₁ p₂ -ᵥ p₁) by simp]
  rw

Depends on / 依赖: add_comm, dist_center_eq_dist_center_of_mem_sphere, dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint, h.symm, map_smul, midpoint, nth_rw, o.tan_oangle_add_right_smul_rotation_pi_div_two, oangle, oangle_midpoint_rev_left, smul_smul, tan_oangle_add_right_smul_rotation_pi_div_two, two_ne_zero, vadd_vsub_assoc
-/
theorem tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) :
    (Real.Angle.tan (∡ p₂ p₁ s.center) / 2) • o.rotation (π / 2 : Real) (p₂ -ᵥ p₁) +ᵥ
      midpoint Real p₁ p₂ = s.center := by
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)
  rw [← hr]; rw [← oangle_midpoint_rev_left]; rw [oangle]; rw [vadd_vsub_assoc]
  nth_rw 1 [show p₂ -ᵥ p₁ = (2 : Real) • (midpoint Real p₁ p₂ -ᵥ p₁) by simp]
  rw [map_smul]; rw [smul_smul]; rw [add_comm]; rw [o.tan_oangle_add_right_smul_rotation_pi_div_two]; rw [mul_div_cancel_right₀ _ (two_ne_zero' Real)]
  simpa using h.symm

/--
theorem `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center` / 定理 `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center`

English:
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
  statement: {s : Sphere P}
  proof: by
  convert! tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
  convert! (Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm
  rw [add_comm]; rw [two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]

中文:
定理 inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
  结论: {s : 球面 P}
  证明: by
  convert! tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
  convert! (Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm
  rw [add_comm]; rw [two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]

Depends on / 依赖: Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi, add_comm, convert, tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center, tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi, two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
-/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P}
    {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p₃ : p₁ != p₃)
    (hp₂p₃ : p₂ != p₃) :
    ((Real.Angle.tan (∡ p₁ p₂ p₃))⁻¹ / 2) • o.rotation (π / 2 : Real) (p₃ -ᵥ p₁) +ᵥ midpoint Real p₁ p₃ =
      s.center := by
  convert! tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
  convert! (Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm
  rw [add_comm]; rw [two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]

/--
theorem `dist_div_cos_oangle_center_div_two_eq_radius` / 定理 `dist_div_cos_oangle_center_div_two_eq_radius`

English:
theorem dist_div_cos_oangle_center_div_two_eq_radius
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rw [div_right_comm]; rw [div_eq_mul_inv _ (2 : Real)]; rw [mul_comm]; rw [show (2 : Real)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) by simp]; rw [← mem_sphere.1 hp₁]; rw [←
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h]; rw [←
    oangle_midpoint_rev_left]; rw 

中文:
定理 dist_div_cos_oangle_center_div_two_eq_radius
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rw [div_right_comm]; rw [div_eq_mul_inv _ (2 : Real)]; rw [mul_comm]; rw [show (2 : Real)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) by simp]; rw [← mem_sphere.1 hp₁]; rw [←
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h]; rw [←
    oangle_midpoint_rev_left]; rw 

Depends on / 依赖: dist_eq_norm_vsub, div_eq_mul_inv, div_right_comm, map_smul, mem_sphere, midpoint, mul_comm, oangle, oangle_midpoint_rev_left, smul_smul, tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center, two_ne_zero, vadd_vsub_assoc
-/
theorem dist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (h : p₁ != p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) / 2 = s.radius := by
  rw [div_right_comm]; rw [div_eq_mul_inv _ (2 : Real)]; rw [mul_comm]; rw [show (2 : Real)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) by simp]; rw [← mem_sphere.1 hp₁]; rw [←
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h]; rw [←
    oangle_midpoint_rev_left]; rw [oangle]; rw [vadd_vsub_assoc]; rw [show p₂ -ᵥ p₁ = (2 : Real) • (midpoint Real p₁ p₂ -ᵥ p₁) by simp]; rw [map_smul]; rw [smul_smul]; rw [div_mul_cancel₀ _ (two_ne_zero' Real)]; rw [@dist_eq_norm_vsub' V]; rw [@dist_eq_norm_vsub' V]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [o.oangle_add_right_smul_rotation_pi_div_two]; rw [Real.Angle.cos_coe]; rw [Real.cos_arctan]
  · norm_cast
    rw [one_div]; rw [div_inv_eq_mul]; rw [← mul_self_inj (by positivity) (by positivity)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real (o.inner_smul_rotation_pi_div_two_right _ _)]; rw [← mul_assoc]; rw [mul_comm]; rw [mul_comm _ (√_)]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Real.mul_self_sqrt (by positivity)]; rw [norm_smul]; rw [LinearIsometryEquiv.norm_map]
    conv_rhs =>
      rw [← mul_assoc]; rw [mul_comm _ ‖Real.Angle.tan _‖]; rw [← mul_assoc]; rw [Real.norm_eq_abs]; rw [abs_mul_abs_self]
    ring
  · simpa using h.symm

/--
theorem `dist_div_cos_oangle_center_eq_two_mul_radius` / 定理 `dist_div_cos_oangle_center_eq_two_mul_radius`

English:
theorem dist_div_cos_oangle_center_eq_two_mul_radius
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

中文:
定理 dist_div_cos_oangle_center_eq_two_mul_radius
  结论: {s : 球面 P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

Depends on / 依赖: dist_div_cos_oangle_center_div_two_eq_radius, two_ne_zero
-/
theorem dist_div_cos_oangle_center_eq_two_mul_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (h : p₁ != p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) = 2 * s.radius := by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

/--
theorem `dist_div_sin_oangle_div_two_eq_radius` / 定理 `dist_div_sin_oangle_div_two_eq_radius`

English:
theorem dist_div_sin_oangle_div_two_eq_radius
  statement: {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  proof: by
  convert! dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  rw [← Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
    (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃)]; rw [abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_

中文:
定理 dist_div_sin_oangle_div_two_eq_radius
  结论: {s : 球面 P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  证明: by
  convert! dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  rw [← Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
    (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃)]; rw [abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_

Depends on / 依赖: Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi, Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two, abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi, abs_oangle_center_right_toReal_lt_pi_div_two, abs_of_nonneg, convert, cos_nonneg_iff_abs_toReal_le_pi_div_two, dist_div_cos_oangle_center_div_two_eq_radius, two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
-/
theorem dist_div_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p₃ : p₁ != p₃) (hp₂p₃ : p₂ != p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius := by
  convert! dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  rw [← Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
    (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃)]; rw [abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two.2 _)]
  exact (abs_oangle_center_right_toReal_lt_pi_div_two hp₁ hp₃).le

/--
theorem `dist_div_sin_oangle_eq_two_mul_radius` / 定理 `dist_div_sin_oangle_eq_two_mul_radius`

English:
theorem dist_div_sin_oangle_eq_two_mul_radius
  statement: {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  proof: by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

中文:
定理 dist_div_sin_oangle_eq_two_mul_radius
  结论: {s : 球面 P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
  证明: by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

Depends on / 依赖: dist_div_sin_oangle_div_two_eq_radius, two_ne_zero
-/
theorem dist_div_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p₃ : p₁ != p₃) (hp₂p₃ : p₂ != p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius := by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃]; rw [mul_div_cancel₀ _ (two_ne_zero' Real)]

end Sphere

end EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

section Oriented

variable [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/--
theorem `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter` / 定理 `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter`

English:
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter
  statement: (t : Triangle Real P)
  proof: Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.mem_circumsphere _) (t.independent.injective.ne h₁₂)
    (t.independent.injective.ne h₁₃) (t.independent.injective.ne h₂₃)

中文:
定理 inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter
  结论: (t : Triangle 实数 P)
  证明: Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.mem_circumsphere _) (t.independent.injective.ne h₁₂)
    (t.independent.injective.ne h₁₃) (t.independent.injective.ne h₂₃)

Depends on / 依赖: Sphere, Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center, independent, injective, inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center, mem_circumsphere, t.independent.injective.ne, t.mem_circumsphere
-/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter (t : Triangle Real P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    ((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : Real) (t.points i₃ -ᵥ t.points i₁) +ᵥ
        midpoint Real (t.points i₁) (t.points i₃) = t.circumcenter :=
  Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.mem_circumsphere _) (t.independent.injective.ne h₁₂)
    (t.independent.injective.ne h₁₃) (t.independent.injective.ne h₂₃)

/--
theorem `dist_div_sin_oangle_div_two_eq_circumradius` / 定理 `dist_div_sin_oangle_div_two_eq_circumradius`

English:
theorem dist_div_sin_oangle_div_two_eq_circumradius
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
  proof: Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

中文:
定理 dist_div_sin_oangle_div_two_eq_circumradius
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3}
  证明: Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

Depends on / 依赖: Sphere, Sphere.dist_div_sin_oangle_div_two_eq_radius, dist_div_sin_oangle_div_two_eq_radius, independent, injective, mem_circumsphere, t.independent.injective.ne, t.mem_circumsphere
-/
theorem dist_div_sin_oangle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2 = t.circumradius :=
  Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

/--
theorem `dist_div_sin_oangle_eq_two_mul_circumradius` / 定理 `dist_div_sin_oangle_eq_two_mul_circumradius`

English:
theorem dist_div_sin_oangle_eq_two_mul_circumradius
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
  proof: Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

中文:
定理 dist_div_sin_oangle_eq_two_mul_circumradius
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3}
  证明: Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

Depends on / 依赖: Sphere, Sphere.dist_div_sin_oangle_eq_two_mul_radius, dist_div_sin_oangle_eq_two_mul_radius, independent, injective, mem_circumsphere, t.independent.injective.ne, t.mem_circumsphere
-/
theorem dist_div_sin_oangle_eq_two_mul_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| = 2 * t.circumradius :=
  Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

/--
theorem `circumsphere_eq_of_dist_of_oangle` / 定理 `circumsphere_eq_of_dist_of_oangle`

English:
theorem circumsphere_eq_of_dist_of_oangle
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: t.circumsphere.ext
    (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
    (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm

中文:
定理 circumsphere_eq_of_dist_of_oangle
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂)
  证明: t.circumsphere.ext
    (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
    (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm

Depends on / 依赖: circumsphere, dist_div_sin_oangle_div_two_eq_circumradius, inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter, t.circumsphere.ext, t.dist_div_sin_oangle_div_two_eq_circumradius, t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter
-/
theorem circumsphere_eq_of_dist_of_oangle (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : t.circumsphere =
    ⟨((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : Real) (t.points i₃ -ᵥ t.points i₁) +ᵥ midpoint Real (t.points i₁) (t.points i₃),
      dist (t.points i₁) (t.points i₃) /
        |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2⟩ :=
  t.circumsphere.ext
    (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
    (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm

/--
theorem `circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq` / 定理 `circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq`

English:
theorem circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
  statement: {t₁ t₂ : Triangle Real P}
  proof: by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [Real.Angle.tan_eq_of_two_zsmul_eq h₂]; rw [Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂]; rw [h₁]; rw [h₃]

中文:
定理 circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
  结论: {t₁ t₂ : Triangle 实数 P}
  证明: by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [Real.Angle.tan_eq_of_two_zsmul_eq h₂]; rw [Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂]; rw [h₁]; rw [h₃]

Depends on / 依赖: Real.Angle.abs_sin_eq_of_two_zsmul_eq, Real.Angle.tan_eq_of_two_zsmul_eq, abs_sin_eq_of_two_zsmul_eq, circumsphere_eq_of_dist_of_oangle, tan_eq_of_two_zsmul_eq
-/
theorem circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : Triangle Real P}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
    (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃)
    (h₂ : (2 : Int) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) =
      (2 : Int) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)) :
    t₁.circumsphere = t₂.circumsphere := by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]; rw [Real.Angle.tan_eq_of_two_zsmul_eq h₂]; rw [Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂]; rw [h₁]; rw [h₃]

/--
theorem `mem_circumsphere_of_two_zsmul_oangle_eq` / 定理 `mem_circumsphere_of_two_zsmul_oangle_eq`

English:
theorem mem_circumsphere_of_two_zsmul_oangle_eq
  statement: {t : Triangle Real P} {p : P} {i₁ i₂ i₃ : Fin 3}
  proof: by
  let t'p : Fin 3 -> P := Function.update t.points i₂ p
  have h₁ : t'p i₁ = t.points i₁ := by simp [t'p, h₁₂]
  have h₂ : t'p i₂ = p := by simp [t'p]
  have h₃ : t'p i₃ = t.points i₃ := by simp [t'p, h₂₃.symm]
  have ha : AffineIndependent Real t'p := by
    rw [affineIndependent_iff_not_colline

中文:
定理 mem_circumsphere_of_two_zsmul_oangle_eq
  结论: {t : Triangle 实数 P} {p : P} {i₁ i₂ i₃ : 有限集 3}
  证明: by
  let t'p : Fin 3 -> P := Function.update t.points i₂ p
  have h₁ : t'p i₁ = t.points i₁ := by simp [t'p, h₁₂]
  have h₂ : t'p i₂ = p := by simp [t'p]
  have h₃ : t'p i₃ = t.points i₃ := by simp [t'p, h₂₃.symm]
  have ha : AffineIndependent Real t'p := by
    rw [affineIndependent_iff_not_colline

Depends on / 依赖: AffineIndependent, Function, Function.update, Triangle, affineIndependent_iff_not_collinear_of_ne, collinear_iff_of_two_zsmul_oangle_eq, independent, points, t.independent, t.points, update
-/
theorem mem_circumsphere_of_two_zsmul_oangle_eq {t : Triangle Real P} {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
    (h : (2 : Int) • ∡ (t.points i₁) p (t.points i₃) =
      (2 : Int) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)) : p in t.circumsphere := by
  let t'p : Fin 3 -> P := Function.update t.points i₂ p
  have h₁ : t'p i₁ = t.points i₁ := by simp [t'p, h₁₂]
  have h₂ : t'p i₂ = p := by simp [t'p]
  have h₃ : t'p i₃ = t.points i₃ := by simp [t'p, h₂₃.symm]
  have ha : AffineIndependent Real t'p := by
    rw [affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]; rw [h₁]; rw [h₂]; rw [h₃]; rw [collinear_iff_of_two_zsmul_oangle_eq h]; rw [←
      affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]
    exact t.independent
  let t' : Triangle Real P := ⟨t'p, ha⟩
  have h₁' : t'.points i₁ = t.points i₁ := h₁
  have h₂' : t'.points i₂ = p := h₂
  have h₃' : t'.points i₃ = t.points i₃ := h₃
  have h' : (2 : Int) • ∡ (t'.points i₁) (t'.points i₂) (t'.points i₃) =
      (2 : Int) • ∡ (t.points i₁) (t.points i₂) (t.points i₃) := by rwa [h₁', h₂', h₃']
  rw [← circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ h₁' h₃' h']; rw [←
    h₂']
  exact Simplex.mem_circumsphere _ _

end Oriented

/--
theorem `dist_div_sin_angle_div_two_eq_circumradius` / 定理 `dist_div_sin_angle_div_two_eq_circumradius`

English:
theorem dist_div_sin_angle_div_two_eq_circumradius
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
  proof: by
  set S : AffineSubspace Real P := affineSpan Real (Set.range t.points) with hS
  let t' : Triangle Real S := t.restrict S le_rfl
  have hf2 : Fact (finrank Real S.direction = 2) := ⟨by
    rw [hS]; rw [direction_affineSpan]; rw [t.independent.finrank_vectorSpan]
    simp⟩
  have : Module.Oriente

中文:
定理 dist_div_sin_angle_div_two_eq_circumradius
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3}
  证明: by
  set S : AffineSubspace Real P := affineSpan Real (Set.range t.points) with hS
  let t' : Triangle Real S := t.restrict S le_rfl
  have hf2 : Fact (finrank Real S.direction = 2) := ⟨by
    rw [hS]; rw [direction_affineSpan]; rw [t.independent.finrank_vectorSpan]
    simp⟩
  have : Module.Oriente

Depends on / 依赖: AffineSubspace, Basis.orientation, Module, Module.Oriented, Oriented, Real.Angle.sin_toReal, Real.abs_sin_eq_sin_abs_o, S.direction, Set.range, Triangle, abs_sin_eq_sin_abs_o, affineSpan, convert, direction, direction_affineSpan, dist_div_sin_oangle_div_two_eq_circumradius, finBasisOfFinrankEq, finrank, finrank_vectorSpan, hf2.out
-/
theorem dist_div_sin_angle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    dist (t.points i₁) (t.points i₃) / Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) / 2 =
      t.circumradius := by
  set S : AffineSubspace Real P := affineSpan Real (Set.range t.points) with hS
  let t' : Triangle Real S := t.restrict S le_rfl
  have hf2 : Fact (finrank Real S.direction = 2) := ⟨by
    rw [hS]; rw [direction_affineSpan]; rw [t.independent.finrank_vectorSpan]
    simp⟩
  have : Module.Oriented Real S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  convert! t'.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃ using 3
  · rw [← Real.Angle.sin_toReal,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
      ← angle_eq_abs_oangle_toReal (t'.independent.injective.ne h₁₂)
        (t'.independent.injective.ne h₂₃.symm)]
    congr
  · simp [t']

/--
theorem `dist_div_sin_angle_eq_two_mul_circumradius` / 定理 `dist_div_sin_angle_eq_two_mul_circumradius`

English:
theorem dist_div_sin_angle_eq_two_mul_circumradius
  statement: (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
  proof: by
  rw [← t.dist_div_sin_angle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃]
  ring

中文:
定理 dist_div_sin_angle_eq_two_mul_circumradius
  结论: (t : Triangle 实数 P) {i₁ i₂ i₃ : 有限集 3}
  证明: by
  rw [← t.dist_div_sin_angle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃]
  ring

Depends on / 依赖: dist_div_sin_angle_div_two_eq_circumradius, t.dist_div_sin_angle_div_two_eq_circumradius
-/
theorem dist_div_sin_angle_eq_two_mul_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i₁) (t.points i₃) /
      Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) = 2 * t.circumradius := by
  rw [← t.dist_div_sin_angle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃]
  ring

end Triangle

end Affine

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/--
theorem `cospherical_of_two_zsmul_oangle_eq_of_not_collinear` / 定理 `cospherical_of_two_zsmul_oangle_eq_of_not_collinear`

English:
theorem cospherical_of_two_zsmul_oangle_eq_of_not_collinear
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  have hn' : ¬Collinear Real ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle Real P := ⟨![p₁, p₂, p₄], affineIndependent_iff_not_collinear_set.2 hn⟩
  let t₂ : Affine.Triangle Real P := ⟨![p₁, p₃, p₄], affineIndependent_iff_not_collinear_

中文:
定理 cospherical_of_two_zsmul_oangle_eq_of_not_collinear
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  have hn' : ¬Collinear Real ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle Real P := ⟨![p₁, p₂, p₄], affineIndependent_iff_not_collinear_set.2 hn⟩
  let t₂ : Affine.Triangle Real P := ⟨![p₁, p₃, p₄], affineIndependent_iff_not_collinear_

Depends on / 依赖: Affine, Affine.Triangle, Collinear, Set.insert_subset_iff, Set.singleton_subset_iff, Triangle, affineIndependent_iff_not_collinear_set, circumsphere, collinear_iff_of_two_zsmul_oangle_eq, cospherical_iff_exists_sphere, insert_subset_iff, mem_circumsphere, simp_rw, singleton_subset_iff
-/
theorem cospherical_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄) (hn : ¬Collinear Real ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hn' : ¬Collinear Real ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle Real P := ⟨![p₁, p₂, p₄], affineIndependent_iff_not_collinear_set.2 hn⟩
  let t₂ : Affine.Triangle Real P := ⟨![p₁, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hn'⟩
  rw [cospherical_iff_exists_sphere]
  refine ⟨t₂.circumsphere, ?_⟩
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨t₂.mem_circumsphere 0, ?_, t₂.mem_circumsphere 1, t₂.mem_circumsphere 2⟩
  rw [Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
    (by decide : (0 : Fin 3) != 1) (by decide : (0 : Fin 3) != 2) (by decide)
    (show t₂.points 0 = t₁.points 0 from rfl) rfl h.symm]
  exact t₁.mem_circumsphere 1

/--
theorem `concyclic_of_two_zsmul_oangle_eq_of_not_collinear` / 定理 `concyclic_of_two_zsmul_oangle_eq_of_not_collinear`

English:
theorem concyclic_of_two_zsmul_oangle_eq_of_not_collinear
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩

中文:
定理 concyclic_of_two_zsmul_oangle_eq_of_not_collinear
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩

Depends on / 依赖: coplanar_of_fact_finrank_eq_two, cospherical_of_two_zsmul_oangle_eq_of_not_collinear
-/
theorem concyclic_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄) (hn : ¬Collinear Real ({p₁, p₂, p₄} : Set P)) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) :=
  ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩

/--
theorem `cospherical_or_collinear_of_two_zsmul_oangle_eq` / 定理 `cospherical_or_collinear_of_two_zsmul_oangle_eq`

English:
theorem cospherical_or_collinear_of_two_zsmul_oangle_eq
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  by_cases hc : Collinear Real ({p₁, p₂, p₄} : Set P)
  · by_cases he : p₁ = p₄
    · rw [he, Set.insert_eq_self.2
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear Real ({p₂, p₃, p₄} : Set P); · exact Or.inr hl
      rw [or_iff_left 

中文:
定理 cospherical_or_collinear_of_two_zsmul_oangle_eq
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  by_cases hc : Collinear Real ({p₁, p₂, p₄} : Set P)
  · by_cases he : p₁ = p₄
    · rw [he, Set.insert_eq_self.2
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear Real ({p₂, p₃, p₄} : Set P); · exact Or.inr hl
      rw [or_iff_left 

Depends on / 依赖: Affine, Affine.Triangle, Collinear, Or.inr, Set.insert_eq_self, Set.insert_subset_iff, Set.mem_insert_of_mem, Set.mem_singleton, Set.singleton_subset_iff, Triangle, affineIndependent_iff_not_collinear_set, circumsphere, cospherical_iff_exists_sphere, insert_eq_self, insert_subset_iff, mem_insert_of_mem, mem_singleton, or_iff_left, simp_rw, singleton_subset_iff
-/
theorem cospherical_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear Real ({p₁, p₂, p₃, p₄} : Set P) := by
  by_cases hc : Collinear Real ({p₁, p₂, p₄} : Set P)
  · by_cases he : p₁ = p₄
    · rw [he, Set.insert_eq_self.2
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear Real ({p₂, p₃, p₄} : Set P); · exact Or.inr hl
      rw [or_iff_left hl]
      let t : Affine.Triangle Real P := ⟨![p₂, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hl⟩
      rw [cospherical_iff_exists_sphere]
      refine ⟨t.circumsphere, ?_⟩
      simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨t.mem_circumsphere 0, t.mem_circumsphere 1, t.mem_circumsphere 2⟩
    have hc' : Collinear Real ({p₁, p₃, p₄} : Set P) := by
      rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
    refine Or.inr ?_
    rw [Set.insert_comm p₁ p₂] at hc
    rwa [Set.insert_comm p₁ p₂, hc'.collinear_insert_iff_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) he]
  · exact Or.inl (cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hc)

/--
theorem `concyclic_or_collinear_of_two_zsmul_oangle_eq` / 定理 `concyclic_or_collinear_of_two_zsmul_oangle_eq`

English:
theorem concyclic_or_collinear_of_two_zsmul_oangle_eq
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
  · exact Or.inr hc

中文:
定理 concyclic_or_collinear_of_two_zsmul_oangle_eq
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
  · exact Or.inr hc

Depends on / 依赖: Or.inl, Or.inr, coplanar_of_fact_finrank_eq_two, cospherical_or_collinear_of_two_zsmul_oangle_eq
-/
theorem concyclic_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ p₁ p₃ p₄) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear Real ({p₁, p₂, p₃, p₄} : Set P) := by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
  · exact Or.inr hc

end EuclideanGeometry
