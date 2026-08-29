/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : Isometry Φ` and `hΨ : Isometry Ψ`.
We want to complete the square by a space `GlueSpace hΦ hΨ` and two isometries
`toGlueL hΦ hΨ` and `toGlueR hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular,
this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.
(We also register the same metric space structure on a general disjoint union `Σ i, E i`).

We also define the inductive limit of metric spaces. Given
```
     f 0 f 1 f 2 f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

@[expose] public section

noncomputable section

universe u v w

open Function Set Uniformity Topology

namespace Metric

section ApproxGluing

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y] {Φ : Z -> X} {Ψ : Z -> Y} {ε : Real}

/--
Definition of `glueDist` / `glueDist` 的定义

English:
definition glueDist
  signature: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)

中文:
定义 glueDist
  签名: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
-/
def glueDist (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) : X oplus Y -> X oplus Y -> Real
  | .inl x, .inl y => dist x y
  | .inr x, .inr y => dist x y
  | .inl x, .inr y => (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
  | .inr x, .inl y => (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε

set_option backward.privateInPublic true in
/--
theorem `glueDist_self` / 定理 `glueDist_self`

English:
theorem glueDist_self
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)
  statement: forall x, glueDist Φ Ψ ε x x = 0

中文:
定理 glueDist_self
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
  结论: 对任意 x, glueDist Φ Ψ ε x x = 0
-/
private theorem glueDist_self (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) : forall x, glueDist Φ Ψ ε x x = 0
  | .inl _ => dist_self _
  | .inr _ => dist_self _

/--
theorem `glueDist_glued_points` / 定理 `glueDist_glued_points`

English:
theorem glueDist_glued_points
  given: [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (p : Z)
  proof: by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : forall q, 0 <= dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ => by positivity
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]

中文:
定理 glueDist_glued_points
  条件: [非空 Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (p : Z)
  证明: by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : forall q, 0 <= dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ => by positivity
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]

Depends on / 依赖: ciInf_le, forall_mem_range, glueDist, le_antisymm, le_ciInf, zero_add
-/
theorem glueDist_glued_points [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (p : Z) :
    glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p)) = ε := by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : forall q, 0 <= dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ => by positivity
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]

set_option backward.privateInPublic true in
/--
theorem `glueDist_comm` / 定理 `glueDist_comm`

English:
theorem glueDist_comm
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)

中文:
定理 glueDist_comm
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
-/
private theorem glueDist_comm (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) :
    forall x y, glueDist Φ Ψ ε x y = glueDist Φ Ψ ε y x
  | .inl _, .inl _ => dist_comm _ _
  | .inr _, .inr _ => dist_comm _ _
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl

/--
theorem `glueDist_swap` / 定理 `glueDist_swap`

English:
theorem glueDist_swap
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)

中文:
定理 glueDist_swap
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
-/
theorem glueDist_swap (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) :
    forall x y, glueDist Ψ Φ ε x.swap y.swap = glueDist Φ Ψ ε x y
  | .inl _, .inl _ => rfl
  | .inr _, .inr _ => rfl
  | .inl _, .inr _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]
  | .inr _, .inl _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]

/--
theorem `le_glueDist_inl_inr` / 定理 `le_glueDist_inl_inr`

English:
theorem le_glueDist_inl_inr
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y)
  proof: le_add_of_nonneg_left Real.iInf_nonneg fun _ => by positivity

中文:
定理 le_glueDist_inl_inr
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (x y)
  证明: le_add_of_nonneg_left Real.iInf_nonneg fun _ => by positivity

Depends on / 依赖: Real.iInf_nonneg, iInf_nonneg, le_add_of_nonneg_left
-/
theorem le_glueDist_inl_inr (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y) :
    ε <= glueDist Φ Ψ ε (.inl x) (.inr y) :=
le_add_of_nonneg_left Real.iInf_nonneg fun _ => by positivity

/--
theorem `le_glueDist_inr_inl` / 定理 `le_glueDist_inr_inl`

English:
theorem le_glueDist_inr_inl
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y)
  proof: by
  rw [glueDist_comm]; apply le_glueDist_inl_inr

中文:
定理 le_glueDist_inr_inl
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (x y)
  证明: by
  rw [glueDist_comm]; apply le_glueDist_inl_inr

Depends on / 依赖: glueDist_comm, le_glueDist_inl_inr
-/
theorem le_glueDist_inr_inl (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y) :
    ε <= glueDist Φ Ψ ε (.inr x) (.inl y) := by
  rw [glueDist_comm]; apply le_glueDist_inl_inr

section
variable [Nonempty Z]

/--
theorem `glueDist_triangle_inl_inr_inr` / 定理 `glueDist_triangle_inl_inr_inr`

English:
theorem glueDist_triangle_inl_inr_inr
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x : X) (y z : Y)
  proof: by
  simp only [glueDist]
  rw [add_right_comm]; rw [add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => by positivity
  · linarith [dist_triangle_left z (Ψ p) y]

中文:
定理 glueDist_triangle_inl_inr_inr
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (x : X) (y z : Y)
  证明: by
  simp only [glueDist]
  rw [add_right_comm]; rw [add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => by positivity
  · linarith [dist_triangle_left z (Ψ p) y]
-/
private theorem glueDist_triangle_inl_inr_inr (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x : X) (y z : Y) :
    glueDist Φ Ψ ε (.inl x) (.inr z) <=
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inr z) := by
  simp only [glueDist]
  rw [add_right_comm]; rw [add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => by positivity
  · linarith [dist_triangle_left z (Ψ p) y]

/--
theorem `glueDist_triangle_inl_inr_inl` / 定理 `glueDist_triangle_inl_inr_inl`

English:
theorem glueDist_triangle_inl_inr_inl
  statement: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)
  proof: by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm]; rw [add_assoc]; rw [← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]

中文:
定理 glueDist_triangle_inl_inr_inl
  结论: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
  证明: by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm]; rw [add_assoc]; rw [← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]
-/
private theorem glueDist_triangle_inl_inr_inl (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)
    (H : forall p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| <= 2 * ε) (x : X) (y : Y) (z : X) :
    glueDist Φ Ψ ε (.inl x) (.inl z) <=
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inl z) := by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm]; rw [add_assoc]; rw [← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]

set_option backward.privateInPublic true in
/--
theorem `glueDist_triangle` / 定理 `glueDist_triangle`

English:
theorem glueDist_triangle
  statement: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)

中文:
定理 glueDist_triangle
  结论: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数)
-/
private theorem glueDist_triangle (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real)
    (H : forall p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| <= 2 * ε) :
    forall x y z, glueDist Φ Ψ ε x z <= glueDist Φ Ψ ε x y + glueDist Φ Ψ ε y z
  | .inl _, .inl _, .inl _ => dist_triangle _ _ _
  | .inr _, .inr _, .inr _ => dist_triangle _ _ _
  | .inr x, .inl y, .inl z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inr
  | .inr x, .inr y, .inl z => by
    simpa only [glueDist_comm, add_comm] using glueDist_triangle_inl_inr_inr _ _ _ z y x
  | .inl x, .inl y, .inr z => by
    simpa only [← glueDist_swap Φ, glueDist_comm, add_comm, Sum.swap_inl, Sum.swap_inr]
      using glueDist_triangle_inl_inr_inr Ψ Φ ε z y x
  | .inl _, .inr _, .inr _ => glueDist_triangle_inl_inr_inr ..
  | .inl x, .inr y, .inl z => glueDist_triangle_inl_inr_inl Φ Ψ ε H x y z
  | .inr x, .inl y, .inr z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inl
    simpa only [abs_sub_comm]

end

set_option backward.privateInPublic true in
/--
theorem `eq_of_glueDist_eq_zero` / 定理 `eq_of_glueDist_eq_zero`

English:
theorem eq_of_glueDist_eq_zero
  given: (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (ε0 : 0 < ε)

中文:
定理 eq_of_glueDist_eq_zero
  条件: (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (ε0 : 0 < ε)
-/
private theorem eq_of_glueDist_eq_zero (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (ε0 : 0 < ε) :
    forall p q : X oplus Y, glueDist Φ Ψ ε p q = 0 -> p = q
  | .inl x, .inl y, h => by rw [eq_of_dist_eq_zero h]
  | .inl x, .inr y, h => by exfalso; linarith [le_glueDist_inl_inr Φ Ψ ε x y]
  | .inr x, .inl y, h => by exfalso; linarith [le_glueDist_inr_inl Φ Ψ ε x y]
  | .inr x, .inr y, h => by rw [eq_of_dist_eq_zero h]

/--
theorem `Sum.mem_uniformity_iff_glueDist` / 定理 `Sum.mem_uniformity_iff_glueDist`

English:
theorem Sum.mem_uniformity_iff_glueDist
  given: (hε : 0 < ε) (s : Set ((X oplus Y) × (X oplus Y)))
  proof: by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_gt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_gt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

中文:
定理 和.mem_uniformity_iff_glueDist
  条件: (hε : 0 < ε) (s : 集合 ((X oplus Y) × (X oplus Y)))
  证明: by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_gt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_gt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

Depends on / 依赖: Filter, Filter.mem_map, Filter.mem_sup, Sum.uniformity, absurd, le_glueDist_inl_inr, le_glueDist_inr_inl, lt_min, lt_min_iff, mem_map, mem_preimage, mem_sup, mem_uniformity_dist, not_gt, uniformity
-/
theorem Sum.mem_uniformity_iff_glueDist (hε : 0 < ε) (s : Set ((X oplus Y) × (X oplus Y))) :
    s in 𝓤 (X oplus Y) ↔ exists δ > 0, forall a b, glueDist Φ Ψ ε a b < δ -> (a, b) in s := by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_gt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_gt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distances between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` and `Ψ p` are
at distance `ε`. -/
@[instance_reducible]
/--
Definition of `glueMetricApprox` / `glueMetricApprox` 的定义

English:
definition glueMetricApprox
  signature: [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (ε0 : 0 < ε)
  body: glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := eq_of_glueDist_eq_zero Φ Ψ ε ε0 _ _
  toUniformSpace := Sum.instUniformSpace
uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity_iff_glueDist ε0

中文:
定义 glueMetricApprox
  签名: [非空 Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : 实数) (ε0 : 0 < ε)
  定义体: glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := eq_of_glueDist_eq_zero Φ Ψ ε ε0 _ _
  toUniformSpace := Sum.instUniformSpace
uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity_iff_glueDist ε0

Depends on / 依赖: glueDist
-/
def glueMetricApprox [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (ε0 : 0 < ε)
    (H : forall p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| <= 2 * ε) : MetricSpace (X oplus Y) where
  dist := glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := eq_of_glueDist_eq_zero Φ Ψ ε ε0 _ _
  toUniformSpace := Sum.instUniformSpace
uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity_iff_glueDist ε0

end ApproxGluing

section Sum

/-!
### Metric on `X ⊕ Y`

A particular case of the previous construction is when one uses basepoints in `X` and `Y` and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without `iInf`, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved.
-/
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y]

/--
Definition of `Sum.dist` / `Sum.dist` 的定义

English:
definition Sum.dist
  signature: : X oplus Y -> X oplus Y -> Real

中文:
定义 和.dist
  签名: : X oplus Y -> X oplus Y -> 实数
-/
protected def Sum.dist : X oplus Y -> X oplus Y -> Real
  | .inl a, .inl a' => dist a a'
  | .inr b, .inr b' => dist b b'
  | .inl a, .inr b => dist a (Nonempty.some ⟨a⟩) + 1 + dist (Nonempty.some ⟨b⟩) b
  | .inr b, .inl a => dist b (Nonempty.some ⟨b⟩) + 1 + dist (Nonempty.some ⟨a⟩) a

/--
theorem `Sum.dist_eq_glueDist` / 定理 `Sum.dist_eq_glueDist`

English:
theorem Sum.dist_eq_glueDist
  given: {p q : X oplus Y} (x : X) (y : Y)
  proof: by
  cases p <;> cases q <;> first | rfl | simp [Sum.dist, glueDist, dist_comm, add_comm,
    add_left_comm, add_assoc]

中文:
定理 和.dist_eq_glueDist
  条件: {p q : X oplus Y} (x : X) (y : Y)
  证明: by
  cases p <;> cases q <;> first | rfl | simp [Sum.dist, glueDist, dist_comm, add_comm,
    add_left_comm, add_assoc]

Depends on / 依赖: Sum.dist, add_assoc, add_comm, add_left_comm, dist_comm, glueDist
-/
theorem Sum.dist_eq_glueDist {p q : X oplus Y} (x : X) (y : Y) :
    Sum.dist p q =
      glueDist (fun _ : Unit => Nonempty.some ⟨x⟩) (fun _ : Unit => Nonempty.some ⟨y⟩) 1 p q := by
  cases p <;> cases q <;> first | rfl | simp [Sum.dist, glueDist, dist_comm, add_comm,
    add_left_comm, add_assoc]

set_option backward.privateInPublic true in
/--
theorem `Sum.dist_comm` / 定理 `Sum.dist_comm`

English:
theorem Sum.dist_comm
  given: (x y : X oplus Y)
  statement: Sum.dist x y = Sum.dist y x
  proof: by
  cases x <;> cases y <;> simp [Sum.dist, _root_.dist_comm, add_comm, add_left_comm]

中文:
定理 和.dist_comm
  条件: (x y : X oplus Y)
  结论: 和.dist x y = 和.dist y x
  证明: by
  cases x <;> cases y <;> simp [Sum.dist, _root_.dist_comm, add_comm, add_left_comm]
-/
private theorem Sum.dist_comm (x y : X oplus Y) : Sum.dist x y = Sum.dist y x := by
  cases x <;> cases y <;> simp [Sum.dist, _root_.dist_comm, add_comm, add_left_comm]

/--
theorem `Sum.one_le_dist_inl_inr` / 定理 `Sum.one_le_dist_inl_inr`

English:
theorem Sum.one_le_dist_inl_inr
  given: {x : X} {y : Y}
  statement: 1 <= Sum.dist (.inl x) (.inr y)
  proof: by
  grw [Sum.dist, ← le_add_of_nonneg_right dist_nonneg, ← le_add_of_nonneg_left dist_nonneg]

中文:
定理 和.one_le_dist_inl_inr
  条件: {x : X} {y : Y}
  结论: 1 <= 和.dist (.inl x) (.inr y)
  证明: by
  grw [Sum.dist, ← le_add_of_nonneg_right dist_nonneg, ← le_add_of_nonneg_left dist_nonneg]

Depends on / 依赖: Sum.dist, dist_nonneg, le_add_of_nonneg_left, le_add_of_nonneg_right
-/
theorem Sum.one_le_dist_inl_inr {x : X} {y : Y} : 1 <= Sum.dist (.inl x) (.inr y) := by
  grw [Sum.dist, ← le_add_of_nonneg_right dist_nonneg, ← le_add_of_nonneg_left dist_nonneg]

/--
theorem `Sum.one_le_dist_inr_inl` / 定理 `Sum.one_le_dist_inr_inl`

English:
theorem Sum.one_le_dist_inr_inl
  given: {x : X} {y : Y}
  statement: 1 <= Sum.dist (.inr y) (.inl x)
  proof: by
  rw [Sum.dist_comm]; exact Sum.one_le_dist_inl_inr

中文:
定理 和.one_le_dist_inr_inl
  条件: {x : X} {y : Y}
  结论: 1 <= 和.dist (.inr y) (.inl x)
  证明: by
  rw [Sum.dist_comm]; exact Sum.one_le_dist_inl_inr

Depends on / 依赖: Sum.dist_comm, Sum.one_le_dist_inl_inr, dist_comm, one_le_dist_inl_inr
-/
theorem Sum.one_le_dist_inr_inl {x : X} {y : Y} : 1 <= Sum.dist (.inr y) (.inl x) := by
  rw [Sum.dist_comm]; exact Sum.one_le_dist_inl_inr

set_option backward.privateInPublic true in
/--
theorem `Sum.mem_uniformity` / 定理 `Sum.mem_uniformity`

English:
theorem Sum.mem_uniformity
  given: (s : Set ((X oplus Y) × (X oplus Y)))
  proof: by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inl_inr
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inr_inl
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, mem_uniformity_dist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

中文:
定理 和.mem_uniformity
  条件: (s : 集合 ((X oplus Y) × (X oplus Y)))
  证明: by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inl_inr
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inr_inl
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, mem_uniformity_dist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩
-/
private theorem Sum.mem_uniformity (s : Set ((X oplus Y) × (X oplus Y))) :
    s in 𝓤 (X oplus Y) ↔ exists ε > 0, forall a b, Sum.dist a b < ε -> (a, b) in s := by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inl_inr
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inr_inl
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, mem_uniformity_dist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
@[instance_reducible]
/--
Definition of `metricSpaceSum` / `metricSpaceSum` 的定义

English:
definition metricSpaceSum
  signature: : MetricSpace (X oplus Y) where
  body: Sum.dist
  dist_self x := by cases x <;> simp only [Sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle
    | .inl p, .inl q, .inl r => dist_triangle p q r
    | .inl p, .inr q, _ => by
      simp only [Sum.dist_eq_glueDist p q]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | _, .inl q, .inr r => by
      simp only [Sum.dist_eq_glueDist q r]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, _, .inl r => by
      simp only [Sum.dist_eq_glueDist r p]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, .inr q, .inr r => dist_triangle p q r
  eq_of_dist_eq_zero {p q} h := by
    rcases p with p | p <;> rcases q with q | q
    · rw [eq_of_dist_eq_zero h]
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist p q).symm.trans h)
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist q p).symm.trans h)
    · rw [eq_of_dist_eq_zero h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity

中文:
定义 metricSpaceSum
  签名: : 度量空间 (X oplus Y) where
  定义体: Sum.dist
  dist_self x := by cases x <;> simp only [Sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle
    | .inl p, .inl q, .inl r => dist_triangle p q r
    | .inl p, .inr q, _ => by
      simp only [Sum.dist_eq_glueDist p q]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | _, .inl q, .inr r => by
      simp only [Sum.dist_eq_glueDist q r]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, _, .inl r => by
      simp only [Sum.dist_eq_glueDist r p]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, .inr q, .inr r => dist_triangle p q r
  eq_of_dist_eq_zero {p q} h := by
    rcases p with p | p <;> rcases q with q | q
    · rw [eq_of_dist_eq_zero h]
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist p q).symm.trans h)
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist q p).symm.trans h)
    · rw [eq_of_dist_eq_zero h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity

Depends on / 依赖: Sum.dist
-/
def metricSpaceSum : MetricSpace (X oplus Y) where
  dist := Sum.dist
  dist_self x := by cases x <;> simp only [Sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle
    | .inl p, .inl q, .inl r => dist_triangle p q r
    | .inl p, .inr q, _ => by
      simp only [Sum.dist_eq_glueDist p q]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | _, .inl q, .inr r => by
      simp only [Sum.dist_eq_glueDist q r]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, _, .inl r => by
      simp only [Sum.dist_eq_glueDist r p]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, .inr q, .inr r => dist_triangle p q r
  eq_of_dist_eq_zero {p q} h := by
    rcases p with p | p <;> rcases q with q | q
    · rw [eq_of_dist_eq_zero h]
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist p q).symm.trans h)
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist q p).symm.trans h)
    · rw [eq_of_dist_eq_zero h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity

attribute [local instance] metricSpaceSum

/--
theorem `Sum.dist_eq` / 定理 `Sum.dist_eq`

English:
theorem Sum.dist_eq
  given: {x y : X oplus Y}
  statement: dist x y = Sum.dist x y
  proof: rfl

中文:
定理 和.dist_eq
  条件: {x y : X oplus Y}
  结论: dist x y = 和.dist x y
  证明: rfl
-/
theorem Sum.dist_eq {x y : X oplus Y} : dist x y = Sum.dist x y := rfl

/--
theorem `isometry_inl` / 定理 `isometry_inl`

English:
theorem isometry_inl
  statement: Isometry (Sum.inl : X -> X oplus Y)
  proof: Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 isometry_inl
  结论: 等距 (和.inl : X -> X oplus Y)
  证明: Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem isometry_inl : Isometry (Sum.inl : X -> X oplus Y) :=
  Isometry.of_dist_eq fun _ _ => rfl

/--
theorem `isometry_inr` / 定理 `isometry_inr`

English:
theorem isometry_inr
  statement: Isometry (Sum.inr : Y -> X oplus Y)
  proof: Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 isometry_inr
  结论: 等距 (和.inr : Y -> X oplus Y)
  证明: Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem isometry_inr : Isometry (Sum.inr : Y -> X oplus Y) :=
  Isometry.of_dist_eq fun _ _ => rfl

end Sum

namespace Sigma

/- Copy of the previous paragraph, but for arbitrary disjoint unions instead of the disjoint union
of two spaces. I.e., work with sigma types instead of sum types. -/
variable {ι : Type*} {E : ι -> Type*} [forall i, MetricSpace (E i)]

open scoped Classical in
/--
Definition of `dist` / `dist` 的定义

English:
definition dist
  signature: : (Σ i, E i) -> (Σ i, E i) -> Real
  body: by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y

中文:
定义 dist
  签名: : (Σ i, E i) -> (Σ i, E i) -> 实数
  定义体: by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y
-/
protected def dist : (Σ i, E i) -> (Σ i, E i) -> Real
  | ⟨i, x⟩, ⟨j, y⟩ =>
    if h : i = j then
      haveI : E j = E i := by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y

/-- A `Dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
@[instance_reducible]
/--
Definition of `instDist` / `instDist` 的定义

English:
definition instDist
  signature: : Dist (Σ i, E i)
  body: ⟨Sigma.dist⟩

中文:
定义 instDist
  签名: : Dist (Σ i, E i)
  定义体: ⟨Sigma.dist⟩

Depends on / 依赖: Sigma.dist
-/
def instDist : Dist (Σ i, E i) :=
  ⟨Sigma.dist⟩

attribute [local instance] Sigma.instDist

@[simp]
/--
theorem `dist_same` / 定理 `dist_same`

English:
theorem dist_same
  given: (i : ι) (x y : E i)
  statement: dist (Sigma.mk i x) ⟨i, y⟩ = dist x y
  proof: by
  simp [Dist.dist, Sigma.dist]

@[simp]

中文:
定理 dist_same
  条件: (i : ι) (x y : E i)
  结论: dist (依赖和类型.mk i x) ⟨i, y⟩ = dist x y
  证明: by
  simp [Dist.dist, Sigma.dist]

@[simp]

Depends on / 依赖: Dist.dist, Sigma.dist
-/
theorem dist_same (i : ι) (x y : E i) : dist (Sigma.mk i x) ⟨i, y⟩ = dist x y := by
  simp [Dist.dist, Sigma.dist]

@[simp]
/--
theorem `dist_ne` / 定理 `dist_ne`

English:
theorem dist_ne
  given: {i j : ι} (h : i != j) (x : E i) (y : E j)
  proof: dif_neg h

中文:
定理 dist_ne
  条件: {i j : ι} (h : i != j) (x : E i) (y : E j)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem dist_ne {i j : ι} (h : i != j) (x : E i) (y : E j) :
    dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y :=
  dif_neg h

/--
theorem `one_le_dist_of_ne` / 定理 `one_le_dist_of_ne`

English:
theorem one_le_dist_of_ne
  given: {i j : ι} (h : i != j) (x : E i) (y : E j)
  proof: by
  rw [Sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]

中文:
定理 one_le_dist_of_ne
  条件: {i j : ι} (h : i != j) (x : E i) (y : E j)
  证明: by
  rw [Sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]

Depends on / 依赖: Nonempty, Nonempty.some, Sigma.dist_ne, dist_ne, dist_nonneg
-/
theorem one_le_dist_of_ne {i j : ι} (h : i != j) (x : E i) (y : E j) :
    1 <= dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := by
  rw [Sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]

/--
theorem `fst_eq_of_dist_lt_one` / 定理 `fst_eq_of_dist_lt_one`

English:
theorem fst_eq_of_dist_lt_one
  given: (x y : Σ i, E i) (h : dist x y < 1)
  statement: x.1 = y.1
  proof: by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h

中文:
定理 fst_eq_of_dist_lt_one
  条件: (x y : Σ i, E i) (h : dist x y < 1)
  结论: x.1 = y.1
  证明: by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h

Depends on / 依赖: contrapose, one_le_dist_of_ne
-/
theorem fst_eq_of_dist_lt_one (x y : Σ i, E i) (h : dist x y < 1) : x.1 = y.1 := by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h

/--
theorem `dist_triangle` / 定理 `dist_triangle`

English:
theorem dist_triangle
  given: (x y z : Σ i, E i)
  statement: dist x z <= dist x y + dist y z
  proof: by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z <= dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ <= _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ <= _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]

中文:
定理 dist_triangle
  条件: (x y z : Σ i, E i)
  结论: dist x z <= dist x y + dist y z
  证明: by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z <= dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ <= _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ <= _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]
-/
protected theorem dist_triangle (x y z : Σ i, E i) : dist x z <= dist x y + dist y z := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z <= dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ <= _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z <=
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ <= _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (s : Set (Σ i, E i))
  proof: by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, ball x ε subseteq Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist ⟨i, x⟩ ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine fun H => isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, forall y, dist (⟨i, x⟩ : Σ j, E j) y < ε -> y in s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.dist_same]
    exact mem_ball'.1 hy

中文:
定理 isOpen_iff
  条件: (s : 集合 (Σ i, E i))
  证明: by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, ball x ε subseteq Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist ⟨i, x⟩ ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine fun H => isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, forall y, dist (⟨i, x⟩ : Σ j, E j) y < ε -> y in s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.dist_same]
    exact mem_ball'.1 hy
-/
protected theorem isOpen_iff (s : Set (Σ i, E i)) :
    IsOpen s ↔ forall x in s, exists ε > 0, forall y, dist x y < ε -> y in s := by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, ball x ε subseteq Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist ⟨i, x⟩ ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine fun H => isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, forall y, dist (⟨i, x⟩ : Σ j, E j) y < ε -> y in s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.dist_same]
    exact mem_ball'.1 hy

/-- A metric space structure on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
@[instance_reducible]
/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
definition metricSpace
  signature: : MetricSpace (Σ i, E i)
  body: by
  refine MetricSpace.ofDistTopology Sigma.dist ?_ ?_ Sigma.dist_triangle Sigma.isOpen_iff ?_
  · rintro ⟨i, x⟩
    simp [Sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [Sigma.dist, dist_comm]
    · simp only [Sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [Sigma.dist]
    · intro h
      apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by rw [h]; exact zero_lt_one

中文:
定义 metricSpace
  签名: : 度量空间 (Σ i, E i)
  定义体: by
  refine MetricSpace.ofDistTopology Sigma.dist ?_ ?_ Sigma.dist_triangle Sigma.isOpen_iff ?_
  · rintro ⟨i, x⟩
    simp [Sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [Sigma.dist, dist_comm]
    · simp only [Sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [Sigma.dist]
    · intro h
      apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by rw [h]; exact zero_lt_one
-/
protected def metricSpace : MetricSpace (Σ i, E i) := by
  refine MetricSpace.ofDistTopology Sigma.dist ?_ ?_ Sigma.dist_triangle Sigma.isOpen_iff ?_
  · rintro ⟨i, x⟩
    simp [Sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [Sigma.dist, dist_comm]
    · simp only [Sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [Sigma.dist]
    · intro h
      apply (lt_irrefl (1 : Real) _).elim
      calc
        1 <= Sigma.dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by rw [h]; exact zero_lt_one

attribute [local instance] Sigma.metricSpace

open Topology

open Filter

/--
theorem `isometry_mk` / 定理 `isometry_mk`

English:
theorem isometry_mk
  given: (i : ι)
  statement: Isometry (Sigma.mk i : E i -> Σ k, E k)
  proof: Isometry.of_dist_eq fun x y => by simp

中文:
定理 isometry_mk
  条件: (i : ι)
  结论: 等距 (依赖和类型.mk i : E i -> Σ k, E k)
  证明: Isometry.of_dist_eq fun x y => by simp

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem isometry_mk (i : ι) : Isometry (Sigma.mk i : E i -> Σ k, E k) :=
  Isometry.of_dist_eq fun x y => by simp

/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  given: [forall i, CompleteSpace (E i)]
  statement: CompleteSpace (Σ i, E i)
  proof: by
  set s : ι -> Set (Σ i, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σ k, E k) × Σ k, E k | dist p.1 p.2 < 1 }
  have hc : forall i, IsComplete (s i) := fun i => by
    simp only [s, ← range_sigmaMk]
    exact (isometry_mk i).isUniformInducing.isComplete_range
  have hd : forall (i j), forall x in s i, forall y in s j, (x, y) in U -> i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert! isComplete_iUnion_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp only [s, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]

中文:
定理 completeSpace
  条件: [对任意 i, 完备空间 (E i)]
  结论: 完备空间 (Σ i, E i)
  证明: by
  set s : ι -> Set (Σ i, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σ k, E k) × Σ k, E k | dist p.1 p.2 < 1 }
  have hc : forall i, IsComplete (s i) := fun i => by
    simp only [s, ← range_sigmaMk]
    exact (isometry_mk i).isUniformInducing.isComplete_range
  have hd : forall (i j), forall x in s i, forall y in s j, (x, y) in U -> i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert! isComplete_iUnion_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp only [s, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]
-/
protected theorem completeSpace [forall i, CompleteSpace (E i)] : CompleteSpace (Σ i, E i) := by
  set s : ι -> Set (Σ i, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σ k, E k) × Σ k, E k | dist p.1 p.2 < 1 }
  have hc : forall i, IsComplete (s i) := fun i => by
    simp only [s, ← range_sigmaMk]
    exact (isometry_mk i).isUniformInducing.isComplete_range
  have hd : forall (i j), forall x in s i, forall y in s j, (x, y) in U -> i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert! isComplete_iUnion_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp only [s, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]

end Sigma

section Gluing

-- Exact gluing of two metric spaces along isometric subsets.
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Nonempty Z] [MetricSpace Z] [MetricSpace X] [MetricSpace Y] {Φ : Z -> X} {Ψ : Z -> Y}
  {ε : Real}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudometric space
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`. -/
@[instance_reducible]
/--
Definition of `gluePremetric` / `gluePremetric` 的定义

English:
definition gluePremetric
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  body: glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq]; simp

中文:
定义 gluePremetric
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ)
  定义体: glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq]; simp

Depends on / 依赖: glueDist
-/
def gluePremetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (X oplus Y) where
  dist := glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq]; simp

/--
Definition of `GlueSpace` / `GlueSpace` 的定义

English:
definition GlueSpace
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  body: @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace

中文:
定义 GlueSpace
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ)
  定义体: @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace

Depends on / 依赖: SeparationQuotient, gluePremetric, toTopologicalSpace, toUniformSpace, toUniformSpace.toTopologicalSpace
-/
def GlueSpace (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _ :=
  @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace

instance (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : MetricSpace (GlueSpace hΦ hΨ) :=
inferInstanceAs MetricSpace
    @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace

/--
Definition of `toGlueL` / `toGlueL` 的定义

English:
definition toGlueL
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X)
  body: Quotient.mk'' (.inl x)

中文:
定义 toGlueL
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ) (x : X)
  定义体: Quotient.mk'' (.inl x)

Depends on / 依赖: Quotient, Quotient.mk
-/
def toGlueL (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inl x)

/--
Definition of `toGlueR` / `toGlueR` 的定义

English:
definition toGlueR
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y)
  body: Quotient.mk'' (.inr y)

中文:
定义 toGlueR
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ) (y : Y)
  定义体: Quotient.mk'' (.inr y)

Depends on / 依赖: Quotient, Quotient.mk
-/
def toGlueR (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inr y)

/--
Instance `inhabitedLeft` / 实例 `inhabitedLeft`

English:
instance inhabitedLeft
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X]
  body: ⟨toGlueL _ _ default⟩

中文:
实例 inhabitedLeft
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ) [可居 X]
  定义体: ⟨toGlueL _ _ default⟩

Depends on / 依赖: toGlueL
-/
instance inhabitedLeft (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueL _ _ default⟩

/--
Instance `inhabitedRight` / 实例 `inhabitedRight`

English:
instance inhabitedRight
  signature: (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y]
  body: ⟨toGlueR _ _ default⟩

中文:
实例 inhabitedRight
  签名: (hΦ : 等距 Φ) (hΨ : 等距 Ψ) [可居 Y]
  定义体: ⟨toGlueR _ _ default⟩

Depends on / 依赖: toGlueR
-/
instance inhabitedRight (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueR _ _ default⟩

/--
theorem `toGlue_commute` / 定理 `toGlue_commute`

English:
theorem toGlue_commute
  given: (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  proof: by
  let i : PseudoMetricSpace (X oplus Y) := gluePremetric hΦ hΨ
  let _ := i.toUniformSpace.toTopologicalSpace
  funext
  simp only [comp, toGlueL, toGlueR]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact glueDist_glued_points Φ Ψ 0 _

中文:
定理 toGlue_commute
  条件: (hΦ : 等距 Φ) (hΨ : 等距 Ψ)
  证明: by
  let i : PseudoMetricSpace (X oplus Y) := gluePremetric hΦ hΨ
  let _ := i.toUniformSpace.toTopologicalSpace
  funext
  simp only [comp, toGlueL, toGlueR]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact glueDist_glued_points Φ Ψ 0 _

Depends on / 依赖: Metric, Metric.inseparable_iff, PseudoMetricSpace, SeparationQuotient, SeparationQuotient.mk_eq_mk, glueDist_glued_points, gluePremetric, i.toUniformSpace.toTopologicalSpace, inseparable_iff, mk_eq_mk, toGlueL, toGlueR, toTopologicalSpace, toUniformSpace
-/
theorem toGlue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    toGlueL hΦ hΨ ∘ Φ = toGlueR hΦ hΨ ∘ Ψ := by
  let i : PseudoMetricSpace (X oplus Y) := gluePremetric hΦ hΨ
  let _ := i.toUniformSpace.toTopologicalSpace
  funext
  simp only [comp, toGlueL, toGlueR]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact glueDist_glued_points Φ Ψ 0 _

/--
theorem `toGlueL_isometry` / 定理 `toGlueL_isometry`

English:
theorem toGlueL_isometry
  given: (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  statement: Isometry (toGlueL hΦ hΨ)
  proof: Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 toGlueL_isometry
  条件: (hΦ : 等距 Φ) (hΨ : 等距 Ψ)
  结论: 等距 (toGlueL hΦ hΨ)
  证明: Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem toGlueL_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueL hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl

/--
theorem `toGlueR_isometry` / 定理 `toGlueR_isometry`

English:
theorem toGlueR_isometry
  given: (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  statement: Isometry (toGlueR hΦ hΨ)
  proof: Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 toGlueR_isometry
  条件: (hΦ : 等距 Φ) (hΨ : 等距 Ψ)
  结论: 等距 (toGlueR hΦ hΨ)
  证明: Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem toGlueR_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueR hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl

end Gluing --section

section InductiveLimit

/-!
### Inductive limit of metric spaces

In this section, we define the inductive limit of

```
     f 0 f 1 f 2 f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```

where the `X n` are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on `Σ n, X n`, where the predistance `dist x y` is obtained by pushing `x` and `y`
in a common `X k` using composition by the `f n`, and taking the distance there. This does not
depend on the choice of `k` as the `f n` are isometries. The metric space associated to this
premetric space is the desired inductive limit.
-/

open Nat

variable {X : Nat -> Type u} [forall n, MetricSpace (X n)] {f : forall n, X n -> X (n + 1)}

/--
Definition of `inductiveLimitDist` / `inductiveLimitDist` 的定义

English:
definition inductiveLimitDist
  signature: (f : forall n, X n -> X (n + 1)) (x y : Σ n, X n)
  body: dist (leRecOn (le_max_left x.1 y.1) (f _) x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) (f _) y.2 : X (max x.1 y.1))

中文:
定义 inductiveLimitDist
  签名: (f : 对任意 n, X n -> X (n + 1)) (x y : Σ n, X n)
  定义体: dist (leRecOn (le_max_left x.1 y.1) (f _) x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) (f _) y.2 : X (max x.1 y.1))

Depends on / 依赖: leRecOn, le_max_left, le_max_right
-/
def inductiveLimitDist (f : forall n, X n -> X (n + 1)) (x y : Σ n, X n) : Real :=
  dist (leRecOn (le_max_left x.1 y.1) (f _) x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) (f _) y.2 : X (max x.1 y.1))

/--
theorem `inductiveLimitDist_eq_dist` / 定理 `inductiveLimitDist_eq_dist`

English:
theorem inductiveLimitDist_eq_dist
  given: (I : forall n, Isometry (f n)) (x y : Σ n, X n)
  proof: x; obtain ⟨j, y⟩ := y
    obtain rfl : i = 0 := nonpos_iff_eq_zero.1 hx
    obtain rfl : j = 0 := nonpos_iff_eq_zero.1 hy
    rfl
  | (m + 1), hx, hy => by
    by_cases h : max x.1 y.1 = (m + 1)
    · generalize m + 1 = m' at *
      subst m'
      rfl
    · have : max x.1 y.1 <= succ m := by simp [hx, hy]
      have : max x.1 y.1 <= m := by simpa [h] using of_le_succ this
      have xm : x.1 <= m := le_trans (le_max_left _ _) this
      have ym : y.1 <= m := le_trans (le_max_right _ _) this
      rw [leRecOn_succ xm]; rw [leRecOn_succ ym]; rw [(I m).dist_eq]
      exact inductiveLimitDist_eq_dist I x y m xm ym

中文:
定理 inductiveLimitDist_eq_dist
  条件: (I : 对任意 n, 等距 (f n)) (x y : Σ n, X n)
  证明: x; obtain ⟨j, y⟩ := y
    obtain rfl : i = 0 := nonpos_iff_eq_zero.1 hx
    obtain rfl : j = 0 := nonpos_iff_eq_zero.1 hy
    rfl
  | (m + 1), hx, hy => by
    by_cases h : max x.1 y.1 = (m + 1)
    · generalize m + 1 = m' at *
      subst m'
      rfl
    · have : max x.1 y.1 <= succ m := by simp [hx, hy]
      have : max x.1 y.1 <= m := by simpa [h] using of_le_succ this
      have xm : x.1 <= m := le_trans (le_max_left _ _) this
      have ym : y.1 <= m := le_trans (le_max_right _ _) this
      rw [leRecOn_succ xm]; rw [leRecOn_succ ym]; rw [(I m).dist_eq]
      exact inductiveLimitDist_eq_dist I x y m xm ym
-/
theorem inductiveLimitDist_eq_dist (I : forall n, Isometry (f n)) (x y : Σ n, X n) :
    forall m (hx : x.1 <= m) (hy : y.1 <= m), inductiveLimitDist f x y =
      dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m)
  | 0, hx, hy => by
    obtain ⟨i, x⟩ := x; obtain ⟨j, y⟩ := y
    obtain rfl : i = 0 := nonpos_iff_eq_zero.1 hx
    obtain rfl : j = 0 := nonpos_iff_eq_zero.1 hy
    rfl
  | (m + 1), hx, hy => by
    by_cases h : max x.1 y.1 = (m + 1)
    · generalize m + 1 = m' at *
      subst m'
      rfl
    · have : max x.1 y.1 <= succ m := by simp [hx, hy]
      have : max x.1 y.1 <= m := by simpa [h] using of_le_succ this
      have xm : x.1 <= m := le_trans (le_max_left _ _) this
      have ym : y.1 <= m := le_trans (le_max_right _ _) this
      rw [leRecOn_succ xm]; rw [leRecOn_succ ym]; rw [(I m).dist_eq]
      exact inductiveLimitDist_eq_dist I x y m xm ym

/-- Premetric space structure on `Σ n, X n`. -/
@[instance_reducible]
/--
Definition of `inductivePremetric` / `inductivePremetric` 的定义

English:
definition inductivePremetric
  signature: (I : forall n, Isometry (f n))
  body: inductiveLimitDist f
  dist_self x := by simp [inductiveLimitDist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 <= m := le_max_left _ _
    have hy : y.1 <= m := le_max_right _ _
    rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y x m hy hx]; rw [dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 <= m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 <= m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 <= m := le_max_right _ _
    calc
      inductiveLimitDist f x z = dist (leRecOn hx (f _) x.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        inductiveLimitDist_eq_dist I x z m hx hz
      _ <= dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) +
            dist (leRecOn hy (f _) y.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductiveLimitDist f x y + inductiveLimitDist f y z := by
        rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y z m hy hz]

中文:
定义 inductivePremetric
  签名: (I : 对任意 n, 等距 (f n))
  定义体: inductiveLimitDist f
  dist_self x := by simp [inductiveLimitDist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 <= m := le_max_left _ _
    have hy : y.1 <= m := le_max_right _ _
    rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y x m hy hx]; rw [dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 <= m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 <= m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 <= m := le_max_right _ _
    calc
      inductiveLimitDist f x z = dist (leRecOn hx (f _) x.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        inductiveLimitDist_eq_dist I x z m hx hz
      _ <= dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) +
            dist (leRecOn hy (f _) y.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductiveLimitDist f x y + inductiveLimitDist f y z := by
        rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y z m hy hz]

Depends on / 依赖: inductiveLimitDist
-/
def inductivePremetric (I : forall n, Isometry (f n)) : PseudoMetricSpace (Σ n, X n) where
  dist := inductiveLimitDist f
  dist_self x := by simp [inductiveLimitDist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 <= m := le_max_left _ _
    have hy : y.1 <= m := le_max_right _ _
    rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y x m hy hx]; rw [dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 <= m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 <= m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 <= m := le_max_right _ _
    calc
      inductiveLimitDist f x z = dist (leRecOn hx (f _) x.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        inductiveLimitDist_eq_dist I x z m hx hz
      _ <= dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) +
            dist (leRecOn hy (f _) y.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductiveLimitDist f x y + inductiveLimitDist f y z := by
        rw [inductiveLimitDist_eq_dist I x y m hx hy]; rw [inductiveLimitDist_eq_dist I y z m hy hz]

/--
Definition of `InductiveLimit` / `InductiveLimit` 的定义

English:
definition InductiveLimit
  signature: (I : forall n, Isometry (f n))
  body: @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace

中文:
定义 InductiveLimit
  签名: (I : 对任意 n, 等距 (f n))
  定义体: @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace

Depends on / 依赖: SeparationQuotient, inductivePremetric, toTopologicalSpace, toUniformSpace, toUniformSpace.toTopologicalSpace
-/
def InductiveLimit (I : forall n, Isometry (f n)) : Type _ :=
  @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace

instance {I : forall (n : Nat), Isometry (f n)} : MetricSpace (InductiveLimit (f := f) I) :=
inferInstanceAs MetricSpace
    @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace

/--
Definition of `toInductiveLimit` / `toInductiveLimit` 的定义

English:
definition toInductiveLimit
  signature: (I : forall n, Isometry (f n)) (n : Nat) (x : X n)
  body: Quotient.mk'' (Sigma.mk n x)

中文:
定义 toInductiveLimit
  签名: (I : 对任意 n, 等距 (f n)) (n : 自然数) (x : X n)
  定义体: Quotient.mk'' (Sigma.mk n x)

Depends on / 依赖: Quotient, Quotient.mk, Sigma.mk
-/
def toInductiveLimit (I : forall n, Isometry (f n)) (n : Nat) (x : X n) : Metric.InductiveLimit I :=
  Quotient.mk'' (Sigma.mk n x)

instance (I : forall n, Isometry (f n)) [Inhabited (X 0)] : Inhabited (InductiveLimit I) :=
  ⟨toInductiveLimit _ 0 default⟩

/--
theorem `toInductiveLimit_isometry` / 定理 `toInductiveLimit_isometry`

English:
theorem toInductiveLimit_isometry
  given: (I : forall n, Isometry (f n)) (n : Nat)
  proof: Isometry.of_dist_eq fun x y => by
    change inductiveLimitDist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductiveLimitDist_eq_dist I ⟨n]; rw [x⟩ ⟨n]; rw [y⟩ n (le_refl n) (le_refl n)]; rw [leRecOn_self]; rw [leRecOn_self]

中文:
定理 toInductiveLimit_isometry
  条件: (I : 对任意 n, 等距 (f n)) (n : 自然数)
  证明: Isometry.of_dist_eq fun x y => by
    change inductiveLimitDist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductiveLimitDist_eq_dist I ⟨n]; rw [x⟩ ⟨n]; rw [y⟩ n (le_refl n) (le_refl n)]; rw [leRecOn_self]; rw [leRecOn_self]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, inductiveLimitDist, inductiveLimitDist_eq_dist, leRecOn_self, le_refl, of_dist_eq
-/
theorem toInductiveLimit_isometry (I : forall n, Isometry (f n)) (n : Nat) :
    Isometry (toInductiveLimit I n) :=
  Isometry.of_dist_eq fun x y => by
    change inductiveLimitDist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductiveLimitDist_eq_dist I ⟨n]; rw [x⟩ ⟨n]; rw [y⟩ n (le_refl n) (le_refl n)]; rw [leRecOn_self]; rw [leRecOn_self]

/--
theorem `toInductiveLimit_commute` / 定理 `toInductiveLimit_commute`

English:
theorem toInductiveLimit_commute
  given: (I : forall n, Isometry (f n)) (n : Nat)
  proof: by
  let h := inductivePremetric I
  let _ := h.toUniformSpace.toTopologicalSpace
  funext x
  simp only [comp, toInductiveLimit]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  change inductiveLimitDist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  rw [inductiveLimitDist_eq_dist I ⟨n.succ]; rw [f n x⟩ ⟨n]; rw [x⟩ n.succ]; rw [leRecOn_self]; rw [leRecOn_succ]; rw [leRecOn_self]; rw [dist_self]
  · rfl
  · rfl
  · exact le_succ _

中文:
定理 toInductiveLimit_commute
  条件: (I : 对任意 n, 等距 (f n)) (n : 自然数)
  证明: by
  let h := inductivePremetric I
  let _ := h.toUniformSpace.toTopologicalSpace
  funext x
  simp only [comp, toInductiveLimit]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  change inductiveLimitDist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  rw [inductiveLimitDist_eq_dist I ⟨n.succ]; rw [f n x⟩ ⟨n]; rw [x⟩ n.succ]; rw [leRecOn_self]; rw [leRecOn_succ]; rw [leRecOn_self]; rw [dist_self]
  · rfl
  · rfl
  · exact le_succ _

Depends on / 依赖: Metric, Metric.inseparable_iff, SeparationQuotient, SeparationQuotient.mk_eq_mk, dist_self, h.toUniformSpace.toTopologicalSpace, inductiveLimitDist, inductiveLimitDist_eq_dist, inductivePremetric, inseparable_iff, leRecOn_self, leRecOn_succ, le_succ, mk_eq_mk, n.succ, toInductiveLimit, toTopologicalSpace, toUniformSpace
-/
theorem toInductiveLimit_commute (I : forall n, Isometry (f n)) (n : Nat) :
    toInductiveLimit I n.succ ∘ f n = toInductiveLimit I n := by
  let h := inductivePremetric I
  let _ := h.toUniformSpace.toTopologicalSpace
  funext x
  simp only [comp, toInductiveLimit]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  change inductiveLimitDist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  rw [inductiveLimitDist_eq_dist I ⟨n.succ]; rw [f n x⟩ ⟨n]; rw [x⟩ n.succ]; rw [leRecOn_self]; rw [leRecOn_succ]; rw [leRecOn_self]; rw [dist_self]
  · rfl
  · rfl
  · exact le_succ _

/--
theorem `dense_iUnion_range_toInductiveLimit` / 定理 `dense_iUnion_range_toInductiveLimit`

English:
theorem dense_iUnion_range_toInductiveLimit
  proof: by
  refine dense_univ.mono ?_
  rintro ⟨n, x⟩ _
  refine mem_iUnion.2 ⟨n, mem_range.2 ⟨x, rfl⟩⟩

中文:
定理 dense_iUnion_range_toInductiveLimit
  证明: by
  refine dense_univ.mono ?_
  rintro ⟨n, x⟩ _
  refine mem_iUnion.2 ⟨n, mem_range.2 ⟨x, rfl⟩⟩

Depends on / 依赖: dense_univ, dense_univ.mono, mem_iUnion, mem_range
-/
theorem dense_iUnion_range_toInductiveLimit
    {X : Nat -> Type u} [(n : Nat) -> MetricSpace (X n)]
    {f : (n : Nat) -> X n -> X (n + 1)}
    (I : forall (n : Nat), Isometry (f n)) :
    Dense (⋃ i, range (toInductiveLimit I i)) := by
  refine dense_univ.mono ?_
  rintro ⟨n, x⟩ _
  refine mem_iUnion.2 ⟨n, mem_range.2 ⟨x, rfl⟩⟩

/--
theorem `separableSpaceInductiveLimit_of_separableSpace` / 定理 `separableSpaceInductiveLimit_of_separableSpace`

English:
theorem separableSpaceInductiveLimit_of_separableSpace
  proof: by
  choose hsX hcX hdX using (fun n => TopologicalSpace.exists_countable_dense (X n))
  let s := ⋃ (i : Nat), (toInductiveLimit I i '' (hsX i))
  refine ⟨s, countable_iUnion (fun n => (hcX n).image _), ?_⟩
refine .of_closure (dense_iUnion_range_toInductiveLimit I).mono iUnion_subset fun i => ?_
  calc
    range (toInductiveLimit I i) subseteq closure (toInductiveLimit I i '' (hsX i)) :=
      (toInductiveLimit_isometry I i |>.continuous).range_subset_closure_image_dense (hdX i)
_ subseteq closure s := closure_mono subset_iUnion (fun j => toInductiveLimit I j '' hsX j) i

中文:
定理 separableSpaceInductiveLimit_of_separableSpace
  证明: by
  choose hsX hcX hdX using (fun n => TopologicalSpace.exists_countable_dense (X n))
  let s := ⋃ (i : Nat), (toInductiveLimit I i '' (hsX i))
  refine ⟨s, countable_iUnion (fun n => (hcX n).image _), ?_⟩
refine .of_closure (dense_iUnion_range_toInductiveLimit I).mono iUnion_subset fun i => ?_
  calc
    range (toInductiveLimit I i) subseteq closure (toInductiveLimit I i '' (hsX i)) :=
      (toInductiveLimit_isometry I i |>.continuous).range_subset_closure_image_dense (hdX i)
_ subseteq closure s := closure_mono subset_iUnion (fun j => toInductiveLimit I j '' hsX j) i

Depends on / 依赖: TopologicalSpace, TopologicalSpace.exists_countable_dense, closure, closure_mo, continuous, countable_iUnion, dense_iUnion_range_toInductiveLimit, exists_countable_dense, iUnion_subset, of_closure, range_subset_closure_image_dense, subseteq, toInductiveLimit, toInductiveLimit_isometry
-/
theorem separableSpaceInductiveLimit_of_separableSpace
    {X : Nat -> Type u} [(n : Nat) -> MetricSpace (X n)]
    [hs : (n : Nat) -> TopologicalSpace.SeparableSpace (X n)] {f : (n : Nat) -> X n -> X (n + 1)}
    (I : forall (n : Nat), Isometry (f n)) :
    TopologicalSpace.SeparableSpace (Metric.InductiveLimit I) := by
  choose hsX hcX hdX using (fun n => TopologicalSpace.exists_countable_dense (X n))
  let s := ⋃ (i : Nat), (toInductiveLimit I i '' (hsX i))
  refine ⟨s, countable_iUnion (fun n => (hcX n).image _), ?_⟩
refine .of_closure (dense_iUnion_range_toInductiveLimit I).mono iUnion_subset fun i => ?_
  calc
    range (toInductiveLimit I i) subseteq closure (toInductiveLimit I i '' (hsX i)) :=
      (toInductiveLimit_isometry I i |>.continuous).range_subset_closure_image_dense (hdX i)
_ subseteq closure s := closure_mono subset_iUnion (fun j => toInductiveLimit I j '' hsX j) i

end InductiveLimit --section

end Metric --namespace
