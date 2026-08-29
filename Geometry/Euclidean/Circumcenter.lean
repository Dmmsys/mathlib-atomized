/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.DeriveFintype

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/

@[expose] public section

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineSubspace

/--
theorem `existsUnique_dist_eq_of_insert` / 定理 `existsUnique_dist_eq_of_insert`

English:
theorem existsUnique_dist_eq_of_insert
  statement: {s : AffineSubspace Real P}
  proof: by
  have : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y != 0 := dist_orthogonalProjection_ne_zero_of_notMe

中文:
定理 existsUnique_dist_eq_of_insert
  结论: {s : AffineSubspace 实数 P}
  证明: by
  have : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y != 0 := dist_orthogonalProjection_ne_zero_of_notMe

Depends on / 依赖: Nonempty, Set.Nonempty.to_subtype, dist_orthogonalProjection_ne_zero_of_notMem, hcccru, hnps.mono, orthogonalProjection, to_subtype
-/
theorem existsUnique_dist_eq_of_insert {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hnps : ps.Nonempty) {p : P} (hps : ps subseteq s)
    (hp : p ∉ s) (hu : exists! cs : Sphere P, cs.center in s ∧ ps subseteq (cs : Set P)) :
    exists! cs₂ : Sphere P,
      cs₂.center in affineSpan Real (insert p (s : Set P)) ∧ insert p ps subseteq (cs₂ : Set P) := by
  have : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y != 0 := dist_orthogonalProjection_ne_zero_of_notMem hp
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y)
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonalProjection s p : V) +ᵥ cc
  let cr₂ := √(cr * cr + ycc₂ * ycc₂)
  use ⟨cc₂, cr₂⟩
  simp -zeta -proj only
  have hpo : p = (1 : Real) • (p -ᵥ orthogonalProjection s p : V) +ᵥ
    (orthogonalProjection s p : P) := by
    simp
  constructor
  · constructor
    · refine vadd_mem_of_mem_direction ?_ (mem_affineSpan Real (Set.mem_insert_of_mem _ hcc))
      rw [direction_affineSpan]
      exact
        Submodule.smul_mem _ _
          (vsub_mem_vectorSpan Real (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ (orthogonalProjection_mem _)))
    · intro p₁ hp₁
      rw [Sphere.mem_coe]; rw [mem_sphere]; rw [← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _)]; rw [Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
      rcases hp₁ with hp₁ | hp₁
      · rw [hp₁, hpo,
          dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc _ _
            (vsub_orthogonalProjection_mem_direction_orthogonal s p),
          Real.norm_eq_abs, abs_mul_abs_self, ← dist_eq_norm_vsub V p, dist_comm _ cc]
        simp only [ycc₂]
        field
      · rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp₁),
          orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc, Subtype.coe_mk,
          dist_of_mem_subset_mk_sphere hp₁ hcr, dist_eq_norm_vsub V cc₂ cc, vadd_vsub, norm_smul, ←
          dist_eq_norm_vsub V, Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg,
          div_mul_cancel₀ _ hy0, abs_mul_abs_self]
  · rintro ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩
    simp only at hcc₃ hcr₃
    obtain ⟨t₃, cc₃', hcc₃', hcc₃''⟩ :
      exists r : Real, exists p0 in s, cc₃ = r • (p -ᵥ ↑((orthogonalProjection s) p)) +ᵥ p0 := by
      rwa [mem_affineSpan_insert_iff (orthogonalProjection_mem p)] at hcc₃
    have hcr₃' : exists r, forall p₁ in ps, dist p₁ cc₃ = r :=
      ⟨cr₃, fun p₁ hp₁ => dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp₁) hcr₃⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq hps cc₃]; rw [hcc₃'']; rw [orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃'] at hcr₃'
    obtain ⟨cr₃', hcr₃'⟩ := hcr₃'
    have hu := hcccru ⟨cc₃', cr₃'⟩
    simp only at hu
    replace hu := hu ⟨hcc₃', hcr₃'⟩
    cases hu
    have hcr₃val : cr₃ = √(cr * cr + t₃ * y * (t₃ * y)) := by
      obtain ⟨p0, hp0⟩ := hnps
      have h' : ↑(⟨cc, hcc₃'⟩ : s) = cc := rfl
      rw [← dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp0) hcr₃]; rw [hcc₃'']; rw [←
        mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _)]; rw [Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp0)]; rw [orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃']; rw [h']; rw [dist_of_mem_subset_mk_sphere hp0 hcr]; rw [dist_eq_norm_vsub V _ cc]; rw [vadd_vsub]; rw [norm_smul]; rw [←
        dist_eq_norm_vsub V p]; rw [Real.norm_eq_abs]; rw [← mul_assoc]; rw [mul_comm _ |t₃|]; rw [← mul_assoc]; rw [abs_mul_abs_self]
      ring
    replace hcr₃ := dist_of_mem_subset_mk_sphere (Set.mem_insert _ _) hcr₃
    rw [hpo]; rw [hcc₃'']; rw [hcr₃val]; rw [← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _)]; rw [dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc₃' _ _
        (vsub_orthogonalProjection_mem_direction_orthogonal s p)]; rw [Real.norm_eq_abs]; rw [abs_mul_abs_self]; rw [dist_comm]; rw [← dist_eq_norm_vsub V p]; rw [Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at hcr₃
    have : t₃ * y = ycc₂ := by grind
    grind

/--
theorem `_root_.AffineIndependent.existsUnique_dist_eq` / 定理 `_root_.AffineIndependent.existsUnique_dist_eq`

English:
theorem _root_.AffineIndependent.existsUnique_dist_eq
  statement: {ι : Type*} [hne : Nonempty ι] [Finite ι]
  proof: by
  cases nonempty_fintype ι
  induction hn : Fintype.card ι generalizing ι with
  | zero =>
    exfalso
    have h := Fintype.card_pos_iff.2 hne
    lia
  | succ m hm =>
    rcases m with - | m
    · rw [Fintype.card_eq_one_iff] at hn
      obtain ⟨i, hi⟩ := hn
      have : Unique ι := ⟨⟨i⟩, hi⟩
 

中文:
定理 _root_.AffineIndependent.existsUnique_dist_eq
  结论: {ι : 类型} [hne : Nonempty ι] [Finite ι]
  证明: by
  cases nonempty_fintype ι
  induction hn : Fintype.card ι generalizing ι with
  | zero =>
    exfalso
    have h := Fintype.card_pos_iff.2 hne
    lia
  | succ m hm =>
    rcases m with - | m
    · rw [Fintype.card_eq_one_iff] at hn
      obtain ⟨i, hi⟩ := hn
      have : Unique ι := ⟨⟨i⟩, hi⟩
 

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_affineSpan_singleton, Fintype, Fintype.card, Fintype.card_eq_one_iff, Fintype.card_pos_iff, Metric, Metric.sphere_zero, Set.mem_singleton_iff, Set.range_unique, Set.singleton_subset_iff, Unique, card_eq_one_iff, card_pos_iff, generalizing, mem_affineSpan_singleton, mem_singleton_iff, nonempty_fintype, range_unique, simp_rw
-/
theorem _root_.AffineIndependent.existsUnique_dist_eq {ι : Type*} [hne : Nonempty ι] [Finite ι]
    {p : ι -> P} (ha : AffineIndependent Real p) :
    exists! cs : Sphere P, cs.center in affineSpan Real (Set.range p) ∧ Set.range p subseteq (cs : Set P) := by
  cases nonempty_fintype ι
  induction hn : Fintype.card ι generalizing ι with
  | zero =>
    exfalso
    have h := Fintype.card_pos_iff.2 hne
    lia
  | succ m hm =>
    rcases m with - | m
    · rw [Fintype.card_eq_one_iff] at hn
      obtain ⟨i, hi⟩ := hn
      have : Unique ι := ⟨⟨i⟩, hi⟩
      use ⟨p i, 0⟩
      simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton]
      constructor
      · simp_rw [hi default, Set.singleton_subset_iff]
        exact ⟨⟨⟩, by simp only [Metric.sphere_zero, Set.mem_singleton_iff]⟩
      · rintro ⟨cc, cr⟩
        rintro ⟨rfl, hdist⟩
        replace hdist : 0 = cr := by simpa using hdist
        rw [hi default]; rw [hdist]
    · have i := hne.some
      let ι2 := { x // x != i }
      classical
      have hc : Fintype.card ι2 = m + 1 := by
        rw [Fintype.card_of_subtype {x | x != i}]
        · rw [Finset.filter_not, Finset.filter_eq' _ i, if_pos (Finset.mem_univ _),
            Finset.card_sdiff, Finset.card_univ, hn]
          simp
        · simp
      have : Nonempty ι2 := Fintype.card_pos_iff.1 (hc.symm ▸ Nat.zero_lt_succ _)
      have ha2 : AffineIndependent Real fun i2 : ι2 => p i2 := ha.subtype _
      replace hm := hm ha2 _ hc
      have hr : Set.range p = insert (p i) (Set.range fun i2 : ι2 => p i2) := by
        change _ = insert _ (Set.range fun i2 : { x | x != i } => p i2)
        rw [← Set.image_eq_range]; rw [← Set.image_univ]; rw [← Set.image_insert_eq]
        congr with j
        simp [Classical.em]
      rw [hr]; rw [← affineSpan_insert_affineSpan]
      refine existsUnique_dist_eq_of_insert (Set.range_nonempty _) (subset_affineSpan Real _) ?_ hm
      convert! ha.notMem_affineSpan_sdiff i Set.univ
      change (Set.range fun i2 : { x | x != i } => p i2) = _
      rw [← Set.image_eq_range]
      congr 1 with j
      simp

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
Definition of `circumsphere` / `circumsphere` 的定义

English:
definition circumsphere
  signature: {n : Nat} (s : Simplex Real P n)
  body: s.independent.existsUnique_dist_eq.choose

中文:
定义 circumsphere
  签名: {n : 自然数} (s : Simplex 实数 P n)
  定义体: s.independent.existsUnique_dist_eq.choose

Depends on / 依赖: direction, existsUnique_dist_eq, independent, s.independent.existsUnique_dist_eq.choose, self_mem_mk
-/
def circumsphere {n : Nat} (s : Simplex Real P n) : Sphere P :=
  s.independent.existsUnique_dist_eq.choose

/--
theorem `circumsphere_unique_dist_eq` / 定理 `circumsphere_unique_dist_eq`

English:
theorem circumsphere_unique_dist_eq
  given: {n : Nat} (s : Simplex Real P n)
  proof: s.independent.existsUnique_dist_eq.choose_spec

中文:
定理 circumsphere_unique_dist_eq
  条件: {n : 自然数} (s : Simplex 实数 P n)
  证明: s.independent.existsUnique_dist_eq.choose_spec

Depends on / 依赖: choose_spec, direction, existsUnique_dist_eq, independent, s.independent.existsUnique_dist_eq.choose_spec, self_mem_mk
-/
theorem circumsphere_unique_dist_eq {n : Nat} (s : Simplex Real P n) :
    (s.circumsphere.center in affineSpan Real (Set.range s.points) ∧
        Set.range s.points subseteq s.circumsphere) ∧
      forall cs : Sphere P,
        cs.center in affineSpan Real (Set.range s.points) ∧ Set.range s.points subseteq cs ->
          cs = s.circumsphere :=
  s.independent.existsUnique_dist_eq.choose_spec

/--
Definition of `circumcenter` / `circumcenter` 的定义

English:
definition circumcenter
  signature: {n : Nat} (s : Simplex Real P n)
  body: s.circumsphere.center

中文:
定义 circumcenter
  签名: {n : 自然数} (s : Simplex 实数 P n)
  定义体: s.circumsphere.center

Depends on / 依赖: center, circumsphere, s.circumsphere.center
-/
def circumcenter {n : Nat} (s : Simplex Real P n) : P :=
  s.circumsphere.center

/--
Definition of `circumradius` / `circumradius` 的定义

English:
definition circumradius
  signature: {n : Nat} (s : Simplex Real P n)
  body: s.circumsphere.radius

中文:
定义 circumradius
  签名: {n : 自然数} (s : Simplex 实数 P n)
  定义体: s.circumsphere.radius

Depends on / 依赖: Set.mem_inter, circumsphere, direction, direction_mk, ext_of_direction_eq, mem_inter, radius, s.circumsphere.radius, s.direction, self_mem_mk
-/
def circumradius {n : Nat} (s : Simplex Real P n) : Real :=
  s.circumsphere.radius

/-- The center of the circumsphere is the circumcenter. -/
@[simp]
/--
theorem `circumsphere_center` / 定理 `circumsphere_center`

English:
theorem circumsphere_center
  given: {n : Nat} (s : Simplex Real P n)
  statement: s.circumsphere.center = s.circumcenter
  proof: rfl

中文:
定理 circumsphere_center
  条件: {n : 自然数} (s : Simplex 实数 P n)
  结论: s.circumsphere.center = s.circumcenter
  证明: rfl
-/
theorem circumsphere_center {n : Nat} (s : Simplex Real P n) : s.circumsphere.center = s.circumcenter :=
  rfl

/-- The radius of the circumsphere is the circumradius. -/
@[simp]
/--
theorem `circumsphere_radius` / 定理 `circumsphere_radius`

English:
theorem circumsphere_radius
  given: {n : Nat} (s : Simplex Real P n)
  statement: s.circumsphere.radius = s.circumradius
  proof: rfl

中文:
定理 circumsphere_radius
  条件: {n : 自然数} (s : Simplex 实数 P n)
  结论: s.circumsphere.radius = s.circumradius
  证明: rfl
-/
theorem circumsphere_radius {n : Nat} (s : Simplex Real P n) : s.circumsphere.radius = s.circumradius :=
  rfl

/--
theorem `circumcenter_mem_affineSpan` / 定理 `circumcenter_mem_affineSpan`

English:
theorem circumcenter_mem_affineSpan
  given: {n : Nat} (s : Simplex Real P n)
  proof: s.circumsphere_unique_dist_eq.1.1

中文:
定理 circumcenter_mem_affineSpan
  条件: {n : 自然数} (s : Simplex 实数 P n)
  证明: s.circumsphere_unique_dist_eq.1.1

Depends on / 依赖: circumsphere_unique_dist_eq, s.circumsphere_unique_dist_eq
-/
theorem circumcenter_mem_affineSpan {n : Nat} (s : Simplex Real P n) :
    s.circumcenter in affineSpan Real (Set.range s.points) :=
  s.circumsphere_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp]
/--
theorem `dist_circumcenter_eq_circumradius` / 定理 `dist_circumcenter_eq_circumradius`

English:
theorem dist_circumcenter_eq_circumradius
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: dist_of_mem_subset_sphere (Set.mem_range_self _) s.circumsphere_unique_dist_eq.1.2

中文:
定理 dist_circumcenter_eq_circumradius
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: dist_of_mem_subset_sphere (Set.mem_range_self _) s.circumsphere_unique_dist_eq.1.2

Depends on / 依赖: Set.mem_range_self, circumsphere_unique_dist_eq, dist_of_mem_subset_sphere, mem_range_self, s.circumsphere_unique_dist_eq
-/
theorem dist_circumcenter_eq_circumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    dist (s.points i) s.circumcenter = s.circumradius :=
  dist_of_mem_subset_sphere (Set.mem_range_self _) s.circumsphere_unique_dist_eq.1.2

/--
theorem `mem_circumsphere` / 定理 `mem_circumsphere`

English:
theorem mem_circumsphere
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: s.dist_circumcenter_eq_circumradius i

中文:
定理 mem_circumsphere
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: s.dist_circumcenter_eq_circumradius i

Depends on / 依赖: dist_circumcenter_eq_circumradius, s.dist_circumcenter_eq_circumradius
-/
theorem mem_circumsphere {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.points i in s.circumsphere :=
  s.dist_circumcenter_eq_circumradius i

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp]
/--
theorem `dist_circumcenter_eq_circumradius'` / 定理 `dist_circumcenter_eq_circumradius'`

English:
theorem dist_circumcenter_eq_circumradius'
  given: {n : Nat} (s : Simplex Real P n)
  proof: by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _

中文:
定理 dist_circumcenter_eq_circumradius'
  条件: {n : 自然数} (s : Simplex 实数 P n)
  证明: by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _

Depends on / 依赖: dist_circumcenter_eq_circumradius, dist_comm
-/
theorem dist_circumcenter_eq_circumradius' {n : Nat} (s : Simplex Real P n) :
    forall i, dist s.circumcenter (s.points i) = s.circumradius := by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _

/--
theorem `eq_circumcenter_of_dist_eq` / 定理 `eq_circumcenter_of_dist_eq`

English:
theorem eq_circumcenter_of_dist_eq
  statement: {n : Nat} (s : Simplex Real P n) {p : P}
  proof: by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.1

中文:
定理 eq_circumcenter_of_dist_eq
  结论: {n : 自然数} (s : Simplex 实数 P n) {p : P}
  证明: by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.1

Depends on / 依赖: Set.forall_mem_range, Sphere, Sphere.ext_iff, circumsphere_unique_dist_eq, ext_iff, forall_const, forall_mem_range, mem_sphere, s.circumsphere_unique_dist_eq, subset_sphere, true_and
-/
theorem eq_circumcenter_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) {r : Real} (hr : forall i, dist (s.points i) p = r) :
    p = s.circumcenter := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.1

/--
theorem `eq_circumradius_of_dist_eq` / 定理 `eq_circumradius_of_dist_eq`

English:
theorem eq_circumradius_of_dist_eq
  statement: {n : Nat} (s : Simplex Real P n) {p : P}
  proof: by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.2

中文:
定理 eq_circumradius_of_dist_eq
  结论: {n : 自然数} (s : Simplex 实数 P n) {p : P}
  证明: by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.2

Depends on / 依赖: Set.forall_mem_range, Sphere, Sphere.ext_iff, circumsphere_unique_dist_eq, ext_iff, forall_const, forall_mem_range, mem_sphere, s.circumsphere_unique_dist_eq, subset_sphere, true_and
-/
theorem eq_circumradius_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) {r : Real} (hr : forall i, dist (s.points i) p = r) :
    r = s.circumradius := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.2

/--
theorem `circumradius_nonneg` / 定理 `circumradius_nonneg`

English:
theorem circumradius_nonneg
  given: {n : Nat} (s : Simplex Real P n)
  statement: 0 <= s.circumradius
  proof: s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

中文:
定理 circumradius_nonneg
  条件: {n : 自然数} (s : Simplex 实数 P n)
  结论: 0 <= s.circumradius
  证明: s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

Depends on / 依赖: dist_circumcenter_eq_circumradius, dist_nonneg, s.dist_circumcenter_eq_circumradius
-/
theorem circumradius_nonneg {n : Nat} (s : Simplex Real P n) : 0 <= s.circumradius :=
  s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

/--
theorem `circumradius_pos` / 定理 `circumradius_pos`

English:
theorem circumradius_pos
  given: {n : Nat} (s : Simplex Real P (n + 1))
  statement: 0 < s.circumradius
  proof: by
  refine lt_of_le_of_ne s.circumradius_nonneg ?_
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 := s.independent.injective.ne (by simp : (0 : Fin (n + 2)) != 1)
  simp [hr] at h01

中文:
定理 circumradius_pos
  条件: {n : 自然数} (s : Simplex 实数 P (n + 1))
  结论: 0 < s.circumradius
  证明: by
  refine lt_of_le_of_ne s.circumradius_nonneg ?_
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 := s.independent.injective.ne (by simp : (0 : Fin (n + 2)) != 1)
  simp [hr] at h01

Depends on / 依赖: circumradius_nonneg, dist_circumcenter_eq_circumradius, dist_eq_zero, independent, injective, lt_of_le_of_ne, s.circumradius_nonneg, s.dist_circumcenter_eq_circumradius, s.independent.injective.ne, simp_rw
-/
theorem circumradius_pos {n : Nat} (s : Simplex Real P (n + 1)) : 0 < s.circumradius := by
  refine lt_of_le_of_ne s.circumradius_nonneg ?_
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 := s.independent.injective.ne (by simp : (0 : Fin (n + 2)) != 1)
  simp [hr] at h01

/--
theorem `circumcenter_eq_point` / 定理 `circumcenter_eq_point`

English:
theorem circumcenter_eq_point
  given: (s : Simplex Real P 0) (i : Fin 1)
  statement: s.circumcenter = s.points i
  proof: by
  have h := s.circumcenter_mem_affineSpan
  have : Unique (Fin 1) := ⟨⟨0, by decide⟩, fun a => by simp only [Fin.eq_zero]⟩
  simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton] at h
  rw [h]
  congr
  simp only [eq_iff_true_of_subsingleton]

中文:
定理 circumcenter_eq_point
  条件: (s : Simplex 实数 P 0) (i : Fin 1)
  结论: s.circumcenter = s.points i
  证明: by
  have h := s.circumcenter_mem_affineSpan
  have : Unique (Fin 1) := ⟨⟨0, by decide⟩, fun a => by simp only [Fin.eq_zero]⟩
  simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton] at h
  rw [h]
  congr
  simp only [eq_iff_true_of_subsingleton]

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_affineSpan_singleton, Fin.eq_zero, Set.range_unique, Unique, circumcenter_mem_affineSpan, eq_iff_true_of_subsingleton, eq_zero, mem_affineSpan_singleton, range_unique, s.circumcenter_mem_affineSpan
-/
theorem circumcenter_eq_point (s : Simplex Real P 0) (i : Fin 1) : s.circumcenter = s.points i := by
  have h := s.circumcenter_mem_affineSpan
  have : Unique (Fin 1) := ⟨⟨0, by decide⟩, fun a => by simp only [Fin.eq_zero]⟩
  simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton] at h
  rw [h]
  congr
  simp only [eq_iff_true_of_subsingleton]

/--
lemma `circumcenter_ne_point` / 引理 `circumcenter_ne_point`

English:
lemma circumcenter_ne_point
  given: {n : Nat} (s : Simplex Real P (n + 1)) (i : Fin (n + 2))
  proof: by
  rw [← dist_ne_zero]; rw [dist_circumcenter_eq_circumradius']
  exact s.circumradius_pos.ne'

中文:
引理 circumcenter_ne_point
  条件: {n : 自然数} (s : Simplex 实数 P (n + 1)) (i : Fin (n + 2))
  证明: by
  rw [← dist_ne_zero]; rw [dist_circumcenter_eq_circumradius']
  exact s.circumradius_pos.ne'

Depends on / 依赖: circumradius_pos, dist_circumcenter_eq_circumradius, dist_ne_zero, s.circumradius_pos.ne
-/
lemma circumcenter_ne_point {n : Nat} (s : Simplex Real P (n + 1)) (i : Fin (n + 2)) :
    s.circumcenter != s.points i := by
  rw [← dist_ne_zero]; rw [dist_circumcenter_eq_circumradius']
  exact s.circumradius_pos.ne'

/--
theorem `circumcenter_eq_centroid` / 定理 `circumcenter_eq_centroid`

English:
theorem circumcenter_eq_centroid
  given: (s : Simplex Real P 1)
  proof: by
  have hr :
    Set.Pairwise Set.univ fun i j : Fin 2 =>
      dist (s.points i) (Finset.univ.centroid Real s.points) =
        dist (s.points j) (Finset.univ.centroid Real s.points) := by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin]; rw [dist_eq_norm_vsub V (s.points i)]; rw [dist_e

中文:
定理 circumcenter_eq_centroid
  条件: (s : Simplex 实数 P 1)
  证明: by
  have hr :
    Set.Pairwise Set.univ fun i j : Fin 2 =>
      dist (s.points i) (Finset.univ.centroid Real s.points) =
        dist (s.points j) (Finset.univ.centroid Real s.points) := by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin]; rw [dist_eq_norm_vsub V (s.points i)]; rw [dist_e

Depends on / 依赖: Finset, Finset.centroid_pair_fin, Finset.univ.centroid, Pairwise, Set.Pairwise, Set.univ, centroid, centroid_pair_fin, dist_eq_norm_vsub, fin_cases, one_smu, one_smul, points, s.points, vsub_vadd_eq_vsub_sub
-/
theorem circumcenter_eq_centroid (s : Simplex Real P 1) :
    s.circumcenter = Finset.univ.centroid Real s.points := by
  have hr :
    Set.Pairwise Set.univ fun i j : Fin 2 =>
      dist (s.points i) (Finset.univ.centroid Real s.points) =
        dist (s.points j) (Finset.univ.centroid Real s.points) := by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin]; rw [dist_eq_norm_vsub V (s.points i)]; rw [dist_eq_norm_vsub V (s.points j)]; rw [vsub_vadd_eq_vsub_sub]; rw [vsub_vadd_eq_vsub_sub]; rw [←
      one_smul Real (s.points i -ᵥ s.points 0)]; rw [← one_smul Real (s.points j -ᵥ s.points 0)]
    fin_cases i <;> fin_cases j <;> simp [-one_smul, ← sub_smul] <;> norm_num
  rw [Set.pairwise_eq_iff_exists_eq] at hr
  obtain ⟨r, hr⟩ := hr
  exact
    (s.eq_circumcenter_of_dist_eq
        (centroid_mem_affineSpan_of_card_eq_add_one Real _ (Finset.card_fin 2)) fun i =>
        hr i (Set.mem_univ _)).symm

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumsphere. -/
@[simp]
/--
theorem `circumsphere_reindex` / 定理 `circumsphere_reindex`

English:
theorem circumsphere_reindex
  given: {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by
  refine s.circumsphere_unique_dist_eq.2 _ ⟨?_, ?_⟩ <;> rw [← s.reindex_range_points e]
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.1
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.2

中文:
定理 circumsphere_reindex
  条件: {m n : 自然数} (s : Simplex 实数 P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  证明: by
  refine s.circumsphere_unique_dist_eq.2 _ ⟨?_, ?_⟩ <;> rw [← s.reindex_range_points e]
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.1
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.2

Depends on / 依赖: circumsphere_unique_dist_eq, reindex, reindex_range_points, s.circumsphere_unique_dist_eq, s.reindex, s.reindex_range_points
-/
theorem circumsphere_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumsphere = s.circumsphere := by
  refine s.circumsphere_unique_dist_eq.2 _ ⟨?_, ?_⟩ <;> rw [← s.reindex_range_points e]
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.1
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.2

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumcenter. -/
@[simp]
/--
theorem `circumcenter_reindex` / 定理 `circumcenter_reindex`

English:
theorem circumcenter_reindex
  given: {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by simp_rw [circumcenter, circumsphere_reindex]

中文:
定理 circumcenter_reindex
  条件: {m n : 自然数} (s : Simplex 实数 P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  证明: by simp_rw [circumcenter, circumsphere_reindex]

Depends on / 依赖: circumcenter, circumsphere_reindex, simp_rw
-/
theorem circumcenter_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumcenter = s.circumcenter := by simp_rw [circumcenter, circumsphere_reindex]

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumradius. -/
@[simp]
/--
theorem `circumradius_reindex` / 定理 `circumradius_reindex`

English:
theorem circumradius_reindex
  given: {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by simp_rw [circumradius, circumsphere_reindex]

中文:
定理 circumradius_reindex
  条件: {m n : 自然数} (s : Simplex 实数 P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  证明: by simp_rw [circumradius, circumsphere_reindex]

Depends on / 依赖: circumradius, circumsphere_reindex, simp_rw
-/
theorem circumradius_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumradius = s.circumradius := by simp_rw [circumradius, circumsphere_reindex]

/--
lemma `circumcenter_map` / 引理 `circumcenter_map`

English:
lemma circumcenter_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
  proof: by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumcenter_of_dist_eq (r := s.circumradius) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan

中文:
引理 circumcenter_map
  结论: {V₂ P₂ : 类型} [NormedAddCommGroup V₂] [InnerProductSpace 实数 V₂]
  证明: by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumcenter_of_dist_eq (r := s.circumradius) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan
-/
@[simp] lemma circumcenter_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).circumcenter = f s.circumcenter := by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumcenter_of_dist_eq (r := s.circumradius) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan

/--
lemma `circumradius_map` / 引理 `circumradius_map`

English:
lemma circumradius_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
  proof: by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumradius_of_dist_eq (p := f s.circumcenter) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan

中文:
引理 circumradius_map
  结论: {V₂ P₂ : 类型} [NormedAddCommGroup V₂] [InnerProductSpace 实数 V₂]
  证明: by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumradius_of_dist_eq (p := f s.circumcenter) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan
-/
@[simp] lemma circumradius_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).circumradius = s.circumradius := by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumradius_of_dist_eq (p := f s.circumcenter) ?_
    fun i => by simp
  rw [map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan

/--
lemma `circumcenter_restrict` / 引理 `circumcenter_restrict`

English:
lemma circumcenter_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumcenter = s.circumcenter := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumcenter_map S.subtypeₐᵢ

中文:
引理 circumcenter_restrict
  结论: {n : 自然数} (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumcenter = s.circumcenter := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumcenter_map S.subtypeₐᵢ
-/
@[simp] lemma circumcenter_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumcenter = s.circumcenter := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumcenter_map S.subtypeₐᵢ

/--
lemma `circumradius_restrict` / 引理 `circumradius_restrict`

English:
lemma circumradius_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumradius = s.circumradius := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumradius_map S.subtypeₐᵢ

中文:
引理 circumradius_restrict
  结论: {n : 自然数} (s : Simplex 实数 P n) (S : AffineSubspace 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumradius = s.circumradius := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumradius_map S.subtypeₐᵢ
-/
@[simp] lemma circumradius_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumradius = s.circumradius := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumradius_map S.subtypeₐᵢ

/--
theorem `dist_circumcenter_sq_eq_sq_sub_circumradius` / 定理 `dist_circumcenter_sq_eq_sq_sub_circumradius`

English:
theorem dist_circumcenter_sq_eq_sq_sub_circumradius
  statement: {n : Nat} {r : Real} (s : Simplex Real P n) {p₁ : P}
  proof: by
  rw [dist_comm]; rw [← h₁ 0]; rw [s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel_left, Simplex.dist_circumcenter_eq_circumradius]

中文:
定理 dist_circumcenter_sq_eq_sq_sub_circumradius
  结论: {n : 自然数} {r : 实数} (s : Simplex 实数 P n) {p₁ : P}
  证明: by
  rw [dist_comm]; rw [← h₁ 0]; rw [s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel_left, Simplex.dist_circumcenter_eq_circumradius]

Depends on / 依赖: Simplex, Simplex.dist_circumcenter_eq_circumradius, add_sub_cancel_left, dist_circumcenter_eq_circumradius, dist_comm, dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq, s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
-/
theorem dist_circumcenter_sq_eq_sq_sub_circumradius {n : Nat} {r : Real} (s : Simplex Real P n) {p₁ : P}
    (h₁ : forall i : Fin (n + 1), dist (s.points i) p₁ = r)
    (h₁' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter)
    (h : s.points 0 in affineSpan Real (Set.range s.points)) :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius := by
  rw [dist_comm]; rw [← h₁ 0]; rw [s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel_left, Simplex.dist_circumcenter_eq_circumradius]

/--
theorem `orthogonalProjection_eq_circumcenter_of_exists_dist_eq` / 定理 `orthogonalProjection_eq_circumcenter_of_exists_dist_eq`

English:
theorem orthogonalProjection_eq_circumcenter_of_exists_dist_eq
  statement: {n : Nat} (s : Simplex Real P n) {p : P}
  proof: by
  change exists r : Real, forall i, (fun x => dist x p = r) (s.points i) at hr
  have hr : exists (r : Real), forall (a : P),
      a in Set.range (fun (i : Fin (n + 1)) => s.points i) -> dist a p = r := by
    obtain ⟨r, hr⟩ := hr
    use r
    refine Set.forall_mem_range.mpr ?_
    exact hr
  r

中文:
定理 orthogonalProjection_eq_circumcenter_of_exists_dist_eq
  结论: {n : 自然数} (s : Simplex 实数 P n) {p : P}
  证明: by
  change exists r : Real, forall i, (fun x => dist x p = r) (s.points i) at hr
  have hr : exists (r : Real), forall (a : P),
      a in Set.range (fun (i : Fin (n + 1)) => s.points i) -> dist a p = r := by
    obtain ⟨r, hr⟩ := hr
    use r
    refine Set.forall_mem_range.mpr ?_
    exact hr
  r

Depends on / 依赖: Set.forall_mem_range.mpr, Set.mem_range_self, Set.range, eq_circumcenter_of_dist_eq, exists_dist_eq_iff_exists_dist_orthogonalProjection_eq, forall_mem_range, mem_range_self, orthogonalProjection_mem, points, s.eq_circumcenter_of_dist_eq, s.points, subset_affineSpan
-/
theorem orthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : Nat} (s : Simplex Real P n) {p : P}
    (hr : exists r, forall i, dist (s.points i) p = r) :
    ↑(s.orthogonalProjectionSpan p) = s.circumcenter := by
  change exists r : Real, forall i, (fun x => dist x p = r) (s.points i) at hr
  have hr : exists (r : Real), forall (a : P),
      a in Set.range (fun (i : Fin (n + 1)) => s.points i) -> dist a p = r := by
    obtain ⟨r, hr⟩ := hr
    use r
    refine Set.forall_mem_range.mpr ?_
    exact hr
  rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq (subset_affineSpan Real _) p] at hr
  obtain ⟨r, hr⟩ := hr
  exact
    s.eq_circumcenter_of_dist_eq (orthogonalProjection_mem p) fun i => hr _ (Set.mem_range_self i)

/--
theorem `orthogonalProjection_eq_circumcenter_of_dist_eq` / 定理 `orthogonalProjection_eq_circumcenter_of_dist_eq`

English:
theorem orthogonalProjection_eq_circumcenter_of_dist_eq
  statement: {n : Nat} (s : Simplex Real P n) {p : P} {r : Real}
  proof: s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

中文:
定理 orthogonalProjection_eq_circumcenter_of_dist_eq
  结论: {n : 自然数} (s : Simplex 实数 P n) {p : P} {r : 实数}
  证明: s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

Depends on / 依赖: orthogonalProjection_eq_circumcenter_of_exists_dist_eq, s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq
-/
theorem orthogonalProjection_eq_circumcenter_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P} {r : Real}
    (hr : forall i, dist (s.points i) p = r) : ↑(s.orthogonalProjectionSpan p) = s.circumcenter :=
  s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

/--
theorem `orthogonalProjection_circumcenter` / 定理 `orthogonalProjection_circumcenter`

English:
theorem orthogonalProjection_circumcenter
  statement: {n : Nat} (s : Simplex Real P n) {fs : Finset (Fin (n + 1))}
  proof: haveI hr : exists r, forall i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  orthogonalProjection_eq_circumcenter_of_exists_dist_eq _ hr

中文:
定理 orthogonalProjection_circumcenter
  结论: {n : 自然数} (s : Simplex 实数 P n) {fs : Finset (Fin (n + 1))}
  证明: haveI hr : exists r, forall i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  orthogonalProjection_eq_circumcenter_of_exists_dist_eq _ hr

Depends on / 依赖: circumcenter, circumradius, face_points, orthogonalProjection_eq_circumcenter_of_exists_dist_eq, points, s.circumcenter, s.circumradius, s.face
-/
theorem orthogonalProjection_circumcenter {n : Nat} (s : Simplex Real P n) {fs : Finset (Fin (n + 1))}
    {m : Nat} (h : #fs = m + 1) :
    ↑((s.face h).orthogonalProjectionSpan s.circumcenter) = (s.face h).circumcenter :=
  haveI hr : exists r, forall i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  orthogonalProjection_eq_circumcenter_of_exists_dist_eq _ hr

/--
theorem `circumcenter_eq_of_range_eq` / 定理 `circumcenter_eq_of_range_eq`

English:
theorem circumcenter_eq_of_range_eq
  statement: {n : Nat} {s₁ s₂ : Simplex Real P n}
  proof: by
  have hs : s₁.circumcenter in affineSpan Real (Set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affineSpan
  have hr : forall i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i in Set.range s₂.points := Set.mem_range_self _
    rw [← h]; rw [Se

中文:
定理 circumcenter_eq_of_range_eq
  结论: {n : 自然数} {s₁ s₂ : Simplex 实数 P n}
  证明: by
  have hs : s₁.circumcenter in affineSpan Real (Set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affineSpan
  have hr : forall i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i in Set.range s₂.points := Set.mem_range_self _
    rw [← h]; rw [Se

Depends on / 依赖: Set.mem_range, Set.mem_range_self, Set.range, affineSpan, circumcenter, circumcenter_mem_affineSpan, circumradius, dist_circumcenter_eq_circumradius, eq_circumcenter_of_dist_eq, mem_range, mem_range_self, points
-/
theorem circumcenter_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex Real P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.circumcenter = s₂.circumcenter := by
  have hs : s₁.circumcenter in affineSpan Real (Set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affineSpan
  have hr : forall i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i in Set.range s₂.points := Set.mem_range_self _
    rw [← h]; rw [Set.mem_range] at hi
    rcases hi with ⟨j, hj⟩
    rw [← hj]; rw [s₁.dist_circumcenter_eq_circumradius j]
  exact s₂.eq_circumcenter_of_dist_eq hs hr

/--
Inductive type `PointsWithCircumcenterIndex` / 归纳类型 `PointsWithCircumcenterIndex`

English:
inductive PointsWithCircumcenterIndex
  parameters: (n : Nat)
  constructors (2):
    - pointIndex: Fin (n + 1) -> PointsWithCircumcenterIndex n
    - circumcenterIndex: PointsWithCircumcenterIndex n

中文:
归纳类型 PointsWithCircumcenterIndex
  参数: (n : 自然数)
  构造子 (2 个):
    - pointIndex: Fin (n + 1) -> PointsWithCircumcenterIndex n
    - circumcenterIndex: PointsWithCircumcenterIndex n
-/
inductive PointsWithCircumcenterIndex (n : Nat)
  | pointIndex : Fin (n + 1) -> PointsWithCircumcenterIndex n
  | circumcenterIndex : PointsWithCircumcenterIndex n
  deriving Fintype

open PointsWithCircumcenterIndex

/--
Instance `pointsWithCircumcenterIndexInhabited` / 实例 `pointsWithCircumcenterIndexInhabited`

English:
instance pointsWithCircumcenterIndexInhabited
  signature: (n : Nat)
  body: ⟨circumcenterIndex⟩

中文:
实例 pointsWithCircumcenterIndexInhabited
  签名: (n : 自然数)
  定义体: ⟨circumcenterIndex⟩

Depends on / 依赖: circumcenterIndex
-/
instance pointsWithCircumcenterIndexInhabited (n : Nat) : Inhabited (PointsWithCircumcenterIndex n) :=
  ⟨circumcenterIndex⟩

/--
Definition of `pointIndexEmbedding` / `pointIndexEmbedding` 的定义

English:
definition pointIndexEmbedding
  signature: (n : Nat)
  body: ⟨fun i => pointIndex i, fun _ _ h => by injection h⟩

中文:
定义 pointIndexEmbedding
  签名: (n : 自然数)
  定义体: ⟨fun i => pointIndex i, fun _ _ h => by injection h⟩

Depends on / 依赖: injection, pointIndex
-/
def pointIndexEmbedding (n : Nat) : Fin (n + 1) ↪ PointsWithCircumcenterIndex n :=
  ⟨fun i => pointIndex i, fun _ _ h => by injection h⟩

/--
theorem `sum_pointsWithCircumcenter` / 定理 `sum_pointsWithCircumcenter`

English:
theorem sum_pointsWithCircumcenter
  statement: {α : Type*} [AddCommMonoid α] {n : Nat}
  proof: by
  classical
  have h : univ = insert circumcenterIndex (univ.map (pointIndexEmbedding n)) := by
    ext x
    refine ⟨fun h => ?_, fun _ => mem_univ _⟩
    obtain i | - := x
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
    · exact mem_insert_self _ _
  change _ = (∑ i, f (pointIn

中文:
定理 sum_pointsWithCircumcenter
  结论: {α : 类型} [AddCommMonoid α] {n : 自然数}
  证明: by
  classical
  have h : univ = insert circumcenterIndex (univ.map (pointIndexEmbedding n)) := by
    ext x
    refine ⟨fun h => ?_, fun _ => mem_univ _⟩
    obtain i | - := x
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
    · exact mem_insert_self _ _
  change _ = (∑ i, f (pointIn

Depends on / 依赖: Finset, Finset.mem_map, add_comm, circumcenterIndex, classical, injection, insert, mem_insert_of_mem, mem_insert_self, mem_map, mem_map_of_mem, mem_univ, not_exists, pointIndexEmbedding, simp_rw, sum_insert, sum_map, univ.map
-/
theorem sum_pointsWithCircumcenter {α : Type*} [AddCommMonoid α] {n : Nat}
    (f : PointsWithCircumcenterIndex n -> α) :
    ∑ i, f i = (∑ i : Fin (n + 1), f (pointIndex i)) + f circumcenterIndex := by
  classical
  have h : univ = insert circumcenterIndex (univ.map (pointIndexEmbedding n)) := by
    ext x
    refine ⟨fun h => ?_, fun _ => mem_univ _⟩
    obtain i | - := x
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
    · exact mem_insert_self _ _
  change _ = (∑ i, f (pointIndexEmbedding n i)) + _
  rw [add_comm]; rw [h]; rw [← sum_map]; rw [sum_insert]
  simp_rw [Finset.mem_map, not_exists]
  rintro x ⟨_, h⟩
  injection h

/--
Definition of `pointsWithCircumcenter` / `pointsWithCircumcenter` 的定义

English:
definition pointsWithCircumcenter
  signature: {n : Nat} (s : Simplex Real P n)

中文:
定义 pointsWithCircumcenter
  签名: {n : 自然数} (s : Simplex 实数 P n)
-/
def pointsWithCircumcenter {n : Nat} (s : Simplex Real P n) : PointsWithCircumcenterIndex n -> P
  | pointIndex i => s.points i
  | circumcenterIndex => s.circumcenter

/-- `pointsWithCircumcenter`, applied to a `pointIndex` value,
equals `points` applied to that value. -/
@[simp]
/--
theorem `pointsWithCircumcenter_point` / 定理 `pointsWithCircumcenter_point`

English:
theorem pointsWithCircumcenter_point
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: rfl

中文:
定理 pointsWithCircumcenter_point
  条件: {n : 自然数} (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: rfl
-/
theorem pointsWithCircumcenter_point {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.pointsWithCircumcenter (pointIndex i) = s.points i :=
  rfl

/-- `pointsWithCircumcenter`, applied to `circumcenterIndex`, equals the
circumcenter. -/
@[simp]
/--
theorem `pointsWithCircumcenter_eq_circumcenter` / 定理 `pointsWithCircumcenter_eq_circumcenter`

English:
theorem pointsWithCircumcenter_eq_circumcenter
  given: {n : Nat} (s : Simplex Real P n)
  proof: rfl

中文:
定理 pointsWithCircumcenter_eq_circumcenter
  条件: {n : 自然数} (s : Simplex 实数 P n)
  证明: rfl
-/
theorem pointsWithCircumcenter_eq_circumcenter {n : Nat} (s : Simplex Real P n) :
    s.pointsWithCircumcenter circumcenterIndex = s.circumcenter :=
  rfl

/--
Definition of `pointWeightsWithCircumcenter` / `pointWeightsWithCircumcenter` 的定义

English:
definition pointWeightsWithCircumcenter
  signature: {n : Nat} (i : Fin (n + 1))

中文:
定义 pointWeightsWithCircumcenter
  签名: {n : 自然数} (i : Fin (n + 1))
-/
def pointWeightsWithCircumcenter {n : Nat} (i : Fin (n + 1)) : PointsWithCircumcenterIndex n -> Real
  | pointIndex j => if j = i then 1 else 0
  | circumcenterIndex => 0

/-- `pointWeightsWithCircumcenter` sums to 1. -/
@[simp]
/--
theorem `sum_pointWeightsWithCircumcenter` / 定理 `sum_pointWeightsWithCircumcenter`

English:
theorem sum_pointWeightsWithCircumcenter
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  classical
  convert! sum_ite_eq' univ (pointIndex i) (Function.const _ (1 : Real)) with j
  · cases j <;> simp [pointWeightsWithCircumcenter]
  · simp

中文:
定理 sum_pointWeightsWithCircumcenter
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: by
  classical
  convert! sum_ite_eq' univ (pointIndex i) (Function.const _ (1 : Real)) with j
  · cases j <;> simp [pointWeightsWithCircumcenter]
  · simp

Depends on / 依赖: Function, Function.const, classical, convert, pointIndex, pointWeightsWithCircumcenter, sum_ite_eq
-/
theorem sum_pointWeightsWithCircumcenter {n : Nat} (i : Fin (n + 1)) :
    ∑ j, pointWeightsWithCircumcenter i j = 1 := by
  classical
  convert! sum_ite_eq' univ (pointIndex i) (Function.const _ (1 : Real)) with j
  · cases j <;> simp [pointWeightsWithCircumcenter]
  · simp

/--
theorem `point_eq_affineCombination_of_pointsWithCircumcenter` / 定理 `point_eq_affineCombination_of_pointsWithCircumcenter`

English:
theorem point_eq_affineCombination_of_pointsWithCircumcenter
  statement: {n : Nat} (s : Simplex Real P n)
  proof: by
  rw [← pointsWithCircumcenter_point]
  symm
  refine
    affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by simp [pointWeightsWithCircumcenter]) ?_
  intro i hi hn
  cases i
  · have h : _ != i := fun h => hn (h ▸ rfl)
    simp [pointWeightsWithCircumcenter, h]
  · rfl

中文:
定理 point_eq_affineCombination_of_pointsWithCircumcenter
  结论: {n : 自然数} (s : Simplex 实数 P n)
  证明: by
  rw [← pointsWithCircumcenter_point]
  symm
  refine
    affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by simp [pointWeightsWithCircumcenter]) ?_
  intro i hi hn
  cases i
  · have h : _ != i := fun h => hn (h ▸ rfl)
    simp [pointWeightsWithCircumcenter, h]
  · rfl

Depends on / 依赖: affineCombination_of_eq_one_of_eq_zero, mem_univ, pointWeightsWithCircumcenter, pointsWithCircumcenter_point
-/
theorem point_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex Real P n)
    (i : Fin (n + 1)) :
    s.points i =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination Real s.pointsWithCircumcenter
        (pointWeightsWithCircumcenter i) := by
  rw [← pointsWithCircumcenter_point]
  symm
  refine
    affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by simp [pointWeightsWithCircumcenter]) ?_
  intro i hi hn
  cases i
  · have h : _ != i := fun h => hn (h ▸ rfl)
    simp [pointWeightsWithCircumcenter, h]
  · rfl

/--
Definition of `centroidWeightsWithCircumcenter` / `centroidWeightsWithCircumcenter` 的定义

English:
definition centroidWeightsWithCircumcenter
  signature: {n : Nat} (fs : Finset (Fin (n + 1)))

中文:
定义 centroidWeightsWithCircumcenter
  签名: {n : 自然数} (fs : Finset (Fin (n + 1)))
-/
def centroidWeightsWithCircumcenter {n : Nat} (fs : Finset (Fin (n + 1))) :
    PointsWithCircumcenterIndex n -> Real
  | pointIndex i => if i in fs then (#fs : Real)⁻¹ else 0
  | circumcenterIndex => 0

/-- `centroidWeightsWithCircumcenter` sums to 1, if the `Finset` is nonempty. -/
@[simp]
/--
theorem `sum_centroidWeightsWithCircumcenter` / 定理 `sum_centroidWeightsWithCircumcenter`

English:
theorem sum_centroidWeightsWithCircumcenter
  given: {n : Nat} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty)
  proof: by
  simp_rw [sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter, add_zero, ←
    fs.sum_centroidWeights_eq_one_of_nonempty Real h, ← sum_indicator_subset _ fs.subset_univ]
  rcongr

中文:
定理 sum_centroidWeightsWithCircumcenter
  条件: {n : 自然数} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty)
  证明: by
  simp_rw [sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter, add_zero, ←
    fs.sum_centroidWeights_eq_one_of_nonempty Real h, ← sum_indicator_subset _ fs.subset_univ]
  rcongr

Depends on / 依赖: add_zero, centroidWeightsWithCircumcenter, fs.subset_univ, fs.sum_centroidWeights_eq_one_of_nonempty, rcongr, simp_rw, subset_univ, sum_centroidWeights_eq_one_of_nonempty, sum_indicator_subset, sum_pointsWithCircumcenter
-/
theorem sum_centroidWeightsWithCircumcenter {n : Nat} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty) :
    ∑ i, centroidWeightsWithCircumcenter fs i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter, add_zero, ←
    fs.sum_centroidWeights_eq_one_of_nonempty Real h, ← sum_indicator_subset _ fs.subset_univ]
  rcongr

/--
theorem `centroid_eq_affineCombination_of_pointsWithCircumcenter` / 定理 `centroid_eq_affineCombination_of_pointsWithCircumcenter`

English:
theorem centroid_eq_affineCombination_of_pointsWithCircumcenter
  statement: {n : Nat} (s : Simplex Real P n)
  proof: by
  simp_rw [centroid_def, affineCombination_apply, weightedVSubOfPoint_apply,
    sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter,
    pointsWithCircumcenter_point, zero_smul, add_zero, centroidWeights,
    ← sum_indicator_subset_of_eq_zero (Function.const (Fin (n + 1)) (#fs : Real)⁻¹)

中文:
定理 centroid_eq_affineCombination_of_pointsWithCircumcenter
  结论: {n : 自然数} (s : Simplex 实数 P n)
  证明: by
  simp_rw [centroid_def, affineCombination_apply, weightedVSubOfPoint_apply,
    sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter,
    pointsWithCircumcenter_point, zero_smul, add_zero, centroidWeights,
    ← sum_indicator_subset_of_eq_zero (Function.const (Fin (n + 1)) (#fs : Real)⁻¹)

Depends on / 依赖: AddTorsor, AddTorsor.nonempty, Classical, Classical.choice, Function, Function.const, Set.indicator_apply, add_zero, affineCombination_apply, centroidWeights, centroidWeightsWithCircumcenter, centroid_def, choice, fs.subset_univ, indicator_apply, nonempty, points, pointsWithCircumcenter_point, s.points, simp_rw
-/
theorem centroid_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex Real P n)
    (fs : Finset (Fin (n + 1))) :
    fs.centroid Real s.points =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination Real s.pointsWithCircumcenter
        (centroidWeightsWithCircumcenter fs) := by
  simp_rw [centroid_def, affineCombination_apply, weightedVSubOfPoint_apply,
    sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter,
    pointsWithCircumcenter_point, zero_smul, add_zero, centroidWeights,
    ← sum_indicator_subset_of_eq_zero (Function.const (Fin (n + 1)) (#fs : Real)⁻¹)
      (fun i wi => wi • (s.points i -ᵥ Classical.choice AddTorsor.nonempty)) fs.subset_univ fun _ =>
      zero_smul Real _,
    Set.indicator_apply]
  congr

/--
Definition of `circumcenterWeightsWithCircumcenter` / `circumcenterWeightsWithCircumcenter` 的定义

English:
definition circumcenterWeightsWithCircumcenter
  signature: (n : Nat)

中文:
定义 circumcenterWeightsWithCircumcenter
  签名: (n : 自然数)
-/
def circumcenterWeightsWithCircumcenter (n : Nat) : PointsWithCircumcenterIndex n -> Real
  | pointIndex _ => 0
  | circumcenterIndex => 1

/-- `circumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
/--
theorem `sum_circumcenterWeightsWithCircumcenter` / 定理 `sum_circumcenterWeightsWithCircumcenter`

English:
theorem sum_circumcenterWeightsWithCircumcenter
  given: (n : Nat)
  proof: by
  classical
  convert! sum_ite_eq' univ circumcenterIndex (Function.const _ (1 : Real)) with j
  · cases j <;> simp [circumcenterWeightsWithCircumcenter]
  · simp

中文:
定理 sum_circumcenterWeightsWithCircumcenter
  条件: (n : 自然数)
  证明: by
  classical
  convert! sum_ite_eq' univ circumcenterIndex (Function.const _ (1 : Real)) with j
  · cases j <;> simp [circumcenterWeightsWithCircumcenter]
  · simp

Depends on / 依赖: Function, Function.const, circumcenterIndex, circumcenterWeightsWithCircumcenter, classical, convert, sum_ite_eq
-/
theorem sum_circumcenterWeightsWithCircumcenter (n : Nat) :
    ∑ i, circumcenterWeightsWithCircumcenter n i = 1 := by
  classical
  convert! sum_ite_eq' univ circumcenterIndex (Function.const _ (1 : Real)) with j
  · cases j <;> simp [circumcenterWeightsWithCircumcenter]
  · simp

/--
theorem `circumcenter_eq_affineCombination_of_pointsWithCircumcenter` / 定理 `circumcenter_eq_affineCombination_of_pointsWithCircumcenter`

English:
theorem circumcenter_eq_affineCombination_of_pointsWithCircumcenter
  given: {n : Nat} (s : Simplex Real P n)
  proof: by
  rw [← pointsWithCircumcenter_eq_circumcenter]
  symm
  refine affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl ?_
  rintro ⟨i⟩ _ hn <;> tauto

中文:
定理 circumcenter_eq_affineCombination_of_pointsWithCircumcenter
  条件: {n : 自然数} (s : Simplex 实数 P n)
  证明: by
  rw [← pointsWithCircumcenter_eq_circumcenter]
  symm
  refine affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl ?_
  rintro ⟨i⟩ _ hn <;> tauto

Depends on / 依赖: affineCombination_of_eq_one_of_eq_zero, mem_univ, pointsWithCircumcenter_eq_circumcenter
-/
theorem circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex Real P n) :
    s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination Real s.pointsWithCircumcenter
        (circumcenterWeightsWithCircumcenter n) := by
  rw [← pointsWithCircumcenter_eq_circumcenter]
  symm
  refine affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl ?_
  rintro ⟨i⟩ _ hn <;> tauto

/--
Definition of `reflectionCircumcenterWeightsWithCircumcenter` / `reflectionCircumcenterWeightsWithCircumcenter` 的定义

English:
definition reflectionCircumcenterWeightsWithCircumcenter
  signature: {n : Nat} (i₁ i₂ : Fin (n + 1))

中文:
定义 reflectionCircumcenterWeightsWithCircumcenter
  签名: {n : 自然数} (i₁ i₂ : Fin (n + 1))
-/
def reflectionCircumcenterWeightsWithCircumcenter {n : Nat} (i₁ i₂ : Fin (n + 1)) :
    PointsWithCircumcenterIndex n -> Real
  | pointIndex i => if i = i₁ ∨ i = i₂ then 1 else 0
  | circumcenterIndex => -1

/-- `reflectionCircumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
/--
theorem `sum_reflectionCircumcenterWeightsWithCircumcenter` / 定理 `sum_reflectionCircumcenterWeightsWithCircumcenter`

English:
theorem sum_reflectionCircumcenterWeightsWithCircumcenter
  statement: {n : Nat} {i₁ i₂ : Fin (n + 1)}
  proof: by
  simp_rw [sum_pointsWithCircumcenter, reflectionCircumcenterWeightsWithCircumcenter, sum_ite,
    sum_const, filter_or, filter_eq']
  rw [card_union_of_disjoint]
  · norm_num
  · simpa only [if_true, mem_univ, disjoint_singleton] using h

中文:
定理 sum_reflectionCircumcenterWeightsWithCircumcenter
  结论: {n : 自然数} {i₁ i₂ : Fin (n + 1)}
  证明: by
  simp_rw [sum_pointsWithCircumcenter, reflectionCircumcenterWeightsWithCircumcenter, sum_ite,
    sum_const, filter_or, filter_eq']
  rw [card_union_of_disjoint]
  · norm_num
  · simpa only [if_true, mem_univ, disjoint_singleton] using h

Depends on / 依赖: card_union_of_disjoint, disjoint_singleton, filter_eq, filter_or, if_true, mem_univ, reflectionCircumcenterWeightsWithCircumcenter, simp_rw, sum_const, sum_ite, sum_pointsWithCircumcenter
-/
theorem sum_reflectionCircumcenterWeightsWithCircumcenter {n : Nat} {i₁ i₂ : Fin (n + 1)}
    (h : i₁ != i₂) : ∑ i, reflectionCircumcenterWeightsWithCircumcenter i₁ i₂ i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, reflectionCircumcenterWeightsWithCircumcenter, sum_ite,
    sum_const, filter_or, filter_eq']
  rw [card_union_of_disjoint]
  · norm_num
  · simpa only [if_true, mem_univ, disjoint_singleton] using h

/--
theorem `reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter` / 定理 `reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter`

English:
theorem reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter
  statement: {n : Nat}
  proof: by
  have hc : #{i₁, i₂} = 2 := by simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace Real P := affineSpan Real (s.points '' {i₁, i₂})
  have h_faces :
    (orthogonalProjection W s.circumcenter : P) =
      ↑((s.face hc).orthogonalProjectionSpan 

中文:
定理 reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter
  结论: {n : 自然数}
  证明: by
  have hc : #{i₁, i₂} = 2 := by simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace Real P := affineSpan Real (s.points '' {i₁, i₂})
  have h_faces :
    (orthogonalProjection W s.circumcenter : P) =
      ↑((s.face hc).orthogonalProjectionSpan 
-/
theorem reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : Nat}
    (s : Simplex Real P n) {i₁ i₂ : Fin (n + 1)} (h : i₁ != i₂) :
    reflection (affineSpan Real (s.points '' {i₁, i₂})) s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination Real s.pointsWithCircumcenter
        (reflectionCircumcenterWeightsWithCircumcenter i₁ i₂) := by
  have hc : #{i₁, i₂} = 2 := by simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace Real P := affineSpan Real (s.points '' {i₁, i₂})
  have h_faces :
    (orthogonalProjection W s.circumcenter : P) =
      ↑((s.face hc).orthogonalProjectionSpan s.circumcenter) := by
    apply eq_orthogonalProjection_of_eq_subspace
    simp [W]
  rw [reflection_apply']; rw [h_faces]; rw [s.orthogonalProjection_circumcenter hc]; rw [circumcenter_eq_centroid]; rw [s.face_centroid_eq_centroid hc]; rw [centroid_eq_affineCombination_of_pointsWithCircumcenter]; rw [circumcenter_eq_affineCombination_of_pointsWithCircumcenter]; rw [← @vsub_eq_zero_iff_eq V]; rw [affineCombination_vsub]; rw [weightedVSub_vadd_affineCombination]; rw [affineCombination_vsub]; rw [weightedVSub_apply]; rw [sum_pointsWithCircumcenter]
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.sub_apply, sub_smul, add_smul, sub_smul,
    centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter, ite_smul, zero_smul, sub_zero,
    apply_ite₂ (· + ·), add_zero, ← add_smul, hc, zero_sub, neg_smul, sub_self, add_zero]
  convert! sum_const_zero
  norm_num

end Simplex

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
theorem `cospherical_iff_exists_mem_of_complete` / 定理 `cospherical_iff_exists_mem_of_complete`

English:
theorem cospherical_iff_exists_mem_of_complete
  statement: {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
  proof: by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonalProjection_mem _, hcr⟩
  · exact fun ⟨c, _, hd⟩ => ⟨c, hd⟩

中文:
定理 cospherical_iff_exists_mem_of_complete
  结论: {s : AffineSubspace 实数 P} {ps : Set P} (h : ps subseteq s)
  证明: by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonalProjection_mem _, hcr⟩
  · exact fun ⟨c, _, hd⟩ => ⟨c, hd⟩

Depends on / 依赖: exists_dist_eq_iff_exists_dist_orthogonalProjection_eq, orthogonalProjection, orthogonalProjection_mem
-/
theorem cospherical_iff_exists_mem_of_complete {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
    [Nonempty s] [s.direction.HasOrthogonalProjection] :
    Cospherical ps ↔ exists center in s, exists radius : Real, forall p in ps, dist p center = radius := by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonalProjection_mem _, hcr⟩
  · exact fun ⟨c, _, hd⟩ => ⟨c, hd⟩

/--
theorem `cospherical_iff_exists_mem_of_finiteDimensional` / 定理 `cospherical_iff_exists_mem_of_finiteDimensional`

English:
theorem cospherical_iff_exists_mem_of_finiteDimensional
  statement: {s : AffineSubspace Real P} {ps : Set P}
  proof: cospherical_iff_exists_mem_of_complete h

中文:
定理 cospherical_iff_exists_mem_of_finiteDimensional
  结论: {s : AffineSubspace 实数 P} {ps : Set P}
  证明: cospherical_iff_exists_mem_of_complete h

Depends on / 依赖: cospherical_iff_exists_mem_of_complete
-/
theorem cospherical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace Real P} {ps : Set P}
    (h : ps subseteq s) [Nonempty s] [FiniteDimensional Real s.direction] :
    Cospherical ps ↔ exists center in s, exists radius : Real, forall p in ps, dist p center = radius :=
  cospherical_iff_exists_mem_of_complete h

/--
theorem `exists_circumradius_eq_of_cospherical_subset` / 定理 `exists_circumradius_eq_of_cospherical_subset`

English:
theorem exists_circumradius_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P}
  proof: by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe

中文:
定理 exists_circumradius_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P}
  证明: by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe

Depends on / 依赖: Set.mem_range_self, Set.range, affineSpan, affineSpan_eq_of_le_of_card_eq_finrank_add_one, affineSpan_le_of_subset_coe, cospherical_iff_exists_mem_of_finiteDimensional, eq_circumradius_of_dist_eq, hsx.symm, hsxps.trans, independent, mem_range_self, points, sx.eq_circumradius_of_dist_eq, sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one, sx.points
-/
theorem exists_circumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P}
    (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction]
    (hd : finrank Real s.direction = n) (hc : Cospherical ps) :
    exists r : Real, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumradius = r := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c in affineSpan Real (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumradius_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/--
theorem `circumradius_eq_of_cospherical_subset` / 定理 `circumradius_eq_of_cospherical_subset`

English:
theorem circumradius_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
  proof: by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumradius_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P} (h : ps subseteq s)
  证明: by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumradius_eq_of_cospherical_subset
-/
theorem circumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
    [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n} (hsx₁ : Set.range sx₁.points subseteq ps)
    (hsx₂ : Set.range sx₂.points subseteq ps) : sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `exists_circumradius_eq_of_cospherical` / 定理 `exists_circumradius_eq_of_cospherical`

English:
theorem exists_circumradius_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumradius_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

中文:
定理 exists_circumradius_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumradius_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

Depends on / 依赖: Set.subset_univ, direction_top, exists_circumradius_eq_of_cospherical_subset, finrank_top, subset_univ
-/
theorem exists_circumradius_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) :
    exists r : Real, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumradius = r := by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumradius_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/--
theorem `circumradius_eq_of_cospherical` / 定理 `circumradius_eq_of_cospherical`

English:
theorem circumradius_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumradius_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumradius_eq_of_cospherical
-/
theorem circumradius_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n}
    (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subseteq ps) :
    sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `exists_circumcenter_eq_of_cospherical_subset` / 定理 `exists_circumcenter_eq_of_cospherical_subset`

English:
theorem exists_circumcenter_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P}
  proof: by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe

中文:
定理 exists_circumcenter_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P}
  证明: by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe

Depends on / 依赖: Set.mem_range_self, Set.range, affineSpan, affineSpan_eq_of_le_of_card_eq_finrank_add_one, affineSpan_le_of_subset_coe, cospherical_iff_exists_mem_of_finiteDimensional, eq_circumcenter_of_dist_eq, hsx.symm, hsxps.trans, independent, mem_range_self, points, sx.eq_circumcenter_of_dist_eq, sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one, sx.points
-/
theorem exists_circumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P}
    (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction]
    (hd : finrank Real s.direction = n) (hc : Cospherical ps) :
    exists c : P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumcenter = c := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan Real (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c in affineSpan Real (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumcenter_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/--
theorem `circumcenter_eq_of_cospherical_subset` / 定理 `circumcenter_eq_of_cospherical_subset`

English:
theorem circumcenter_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
  proof: by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumcenter_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P} (h : ps subseteq s)
  证明: by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumcenter_eq_of_cospherical_subset
-/
theorem circumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
    [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n} (hsx₁ : Set.range sx₁.points subseteq ps)
    (hsx₂ : Set.range sx₂.points subseteq ps) : sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `exists_circumcenter_eq_of_cospherical` / 定理 `exists_circumcenter_eq_of_cospherical`

English:
theorem exists_circumcenter_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumcenter_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

中文:
定理 exists_circumcenter_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumcenter_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

Depends on / 依赖: Set.subset_univ, direction_top, exists_circumcenter_eq_of_cospherical_subset, finrank_top, subset_univ
-/
theorem exists_circumcenter_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) :
    exists c : P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumcenter = c := by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumcenter_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/--
theorem `circumcenter_eq_of_cospherical` / 定理 `circumcenter_eq_of_cospherical`

English:
theorem circumcenter_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumcenter_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumcenter_eq_of_cospherical
-/
theorem circumcenter_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n}
    (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subseteq ps) :
    sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `exists_circumsphere_eq_of_cospherical_subset` / 定理 `exists_circumsphere_eq_of_cospherical_subset`

English:
theorem exists_circumsphere_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P}
  proof: by
  obtain ⟨r, hr⟩ := exists_circumradius_eq_of_cospherical_subset h hd hc
  obtain ⟨c, hc⟩ := exists_circumcenter_eq_of_cospherical_subset h hd hc
  exact ⟨⟨c, r⟩, fun sx hsx => Sphere.ext (hc sx hsx) (hr sx hsx)⟩

中文:
定理 exists_circumsphere_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P}
  证明: by
  obtain ⟨r, hr⟩ := exists_circumradius_eq_of_cospherical_subset h hd hc
  obtain ⟨c, hc⟩ := exists_circumcenter_eq_of_cospherical_subset h hd hc
  exact ⟨⟨c, r⟩, fun sx hsx => Sphere.ext (hc sx hsx) (hr sx hsx)⟩

Depends on / 依赖: Sphere, Sphere.ext, exists_circumcenter_eq_of_cospherical_subset, exists_circumradius_eq_of_cospherical_subset
-/
theorem exists_circumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P}
    (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction]
    (hd : finrank Real s.direction = n) (hc : Cospherical ps) :
    exists c : Sphere P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumsphere = c := by
  obtain ⟨r, hr⟩ := exists_circumradius_eq_of_cospherical_subset h hd hc
  obtain ⟨c, hc⟩ := exists_circumcenter_eq_of_cospherical_subset h hd hc
  exact ⟨⟨c, r⟩, fun sx hsx => Sphere.ext (hc sx hsx) (hr sx hsx)⟩

/--
theorem `circumsphere_eq_of_cospherical_subset` / 定理 `circumsphere_eq_of_cospherical_subset`

English:
theorem circumsphere_eq_of_cospherical_subset
  statement: {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
  proof: by
  rcases exists_circumsphere_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumsphere_eq_of_cospherical_subset
  结论: {s : AffineSubspace 实数 P} {ps : Set P} (h : ps subseteq s)
  证明: by
  rcases exists_circumsphere_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumsphere_eq_of_cospherical_subset
-/
theorem circumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h : ps subseteq s)
    [Nonempty s] {n : Nat} [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n} (hsx₁ : Set.range sx₁.points subseteq ps)
    (hsx₂ : Set.range sx₂.points subseteq ps) : sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `exists_circumsphere_eq_of_cospherical` / 定理 `exists_circumsphere_eq_of_cospherical`

English:
theorem exists_circumsphere_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumsphere_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

中文:
定理 exists_circumsphere_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumsphere_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

Depends on / 依赖: Set.subset_univ, direction_top, exists_circumsphere_eq_of_cospherical_subset, finrank_top, subset_univ
-/
theorem exists_circumsphere_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) :
    exists c : Sphere P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumsphere = c := by
  rw [← finrank_top]; rw [← direction_top Real V P] at hd
  refine exists_circumsphere_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/--
theorem `circumsphere_eq_of_cospherical` / 定理 `circumsphere_eq_of_cospherical`

English:
theorem circumsphere_eq_of_cospherical
  statement: {ps : Set P} {n : Nat} [FiniteDimensional Real V]
  proof: by
  rcases exists_circumsphere_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

中文:
定理 circumsphere_eq_of_cospherical
  结论: {ps : Set P} {n : 自然数} [FiniteDimensional 实数 V]
  证明: by
  rcases exists_circumsphere_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

Depends on / 依赖: exists_circumsphere_eq_of_cospherical
-/
theorem circumsphere_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V]
    (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P n}
    (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subseteq ps) :
    sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁]; rw [hr sx₂ hsx₂]

/--
theorem `eq_or_eq_reflection_of_dist_eq` / 定理 `eq_or_eq_reflection_of_dist_eq`

English:
theorem eq_or_eq_reflection_of_dist_eq
  statement: {n : Nat} {s : Simplex Real P n} {p p₁ p₂ : P} {r : Real}
  proof: by
  set span_s := affineSpan Real (Set.range s.points)
  have h₁' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₂
  rw [← affineSpan_insert_affineSpan]; rw [mem_affineSpan_insert_iff (orthogonalProjection_mem p)]
    at hp₁ 

中文:
定理 eq_or_eq_reflection_of_dist_eq
  结论: {n : 自然数} {s : Simplex 实数 P n} {p p₁ p₂ : P} {r : 实数}
  证明: by
  set span_s := affineSpan Real (Set.range s.points)
  have h₁' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₂
  rw [← affineSpan_insert_affineSpan]; rw [mem_affineSpan_insert_iff (orthogonalProjection_mem p)]
    at hp₁ 

Depends on / 依赖: Set.range, affineSpan, affineSpan_insert_affineSpan, coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection, mem_affineSpan_insert_iff, orthogonalProjectionSpan, orthogonalProjection_eq_circumcenter_of_dist_eq, orthogonalProjection_mem, points, s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection, s.orthogonalProjectionSpan, s.orthogonalProjection_eq_circumcenter_of_dist_eq, s.points, span_s
-/
theorem eq_or_eq_reflection_of_dist_eq {n : Nat} {s : Simplex Real P n} {p p₁ p₂ : P} {r : Real}
    (hp₁ : p₁ in affineSpan Real (insert p (Set.range s.points)))
    (hp₂ : p₂ in affineSpan Real (insert p (Set.range s.points))) (h₁ : forall i, dist (s.points i) p₁ = r)
    (h₂ : forall i, dist (s.points i) p₂ = r) :
    p₁ = p₂ ∨ p₁ = reflection (affineSpan Real (Set.range s.points)) p₂ := by
  set span_s := affineSpan Real (Set.range s.points)
  have h₁' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₂
  rw [← affineSpan_insert_affineSpan]; rw [mem_affineSpan_insert_iff (orthogonalProjection_mem p)]
    at hp₁ hp₂
  obtain ⟨r₁, p₁o, hp₁o, hp₁⟩ := hp₁
  obtain ⟨r₂, p₂o, hp₂o, hp₂⟩ := hp₂
  obtain rfl : ↑(s.orthogonalProjectionSpan p₁) = p₁o := by
    subst hp₁
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₁o
  rw [h₁'] at hp₁
  obtain rfl : ↑(s.orthogonalProjectionSpan p₂) = p₂o := by
    subst hp₂
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₂o
  rw [h₂'] at hp₂
  have h : s.points 0 in span_s := mem_affineSpan Real (Set.mem_range_self _)
  have hd₁ :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₁ h₁' h
  have hd₂ :
    dist p₂ s.circumcenter * dist p₂ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₂ h₂' h
  rw [← hd₂]; rw [hp₁]; rw [hp₂]; rw [dist_eq_norm_vsub V _ s.circumcenter]; rw [dist_eq_norm_vsub V _ s.circumcenter]; rw [vadd_vsub]; rw [vadd_vsub]; rw [← real_inner_self_eq_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [real_inner_smul_left]; rw [real_inner_smul_left]; rw [real_inner_smul_right]; rw [real_inner_smul_right]; rw [←
    mul_assoc]; rw [← mul_assoc] at hd₁
  by_cases hp : p = s.orthogonalProjectionSpan p
  · rw [Simplex.orthogonalProjectionSpan] at hp
    rw [hp₁]; rw [hp₂]; rw [← hp]
    simp only [true_or, smul_zero, vsub_self]
  · have hz : ⟪p -ᵥ orthogonalProjection span_s p, p -ᵥ orthogonalProjection span_s p⟫ != 0 := by
      simpa only [Ne, vsub_eq_zero_iff_eq, inner_self_eq_zero] using! hp
    rw [mul_left_inj' hz]; rw [mul_self_eq_mul_self_iff] at hd₁
    rw [hp₁]; rw [hp₂]
    rcases hd₁ with hd₁ | hd₁
    · left
      rw [hd₁]
    · right
      rw [hd₁]; rw [reflection_vadd_smul_vsub_orthogonalProjection p r₂ s.circumcenter_mem_affineSpan]; rw [neg_smul]

end EuclideanGeometry
