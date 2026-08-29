/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Geometry.Euclidean.PerpBisector
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`Analysis.NormedSpace.InnerProduct`. Results with longer
proofs or more geometrical content generally go in separate files.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use
`[NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`.
This works better with `outParam` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

public section

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/


variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

/--
theorem `inner_weightedVSub` / 定理 `inner_weightedVSub`

English:
theorem inner_weightedVSub
  statement: {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ -> Real} (p₁ : ι₁ -> P)
  proof: by
  rw [Finset.weightedVSub_apply]; rw [Finset.weightedVSub_apply]; rw [inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr (i₁ i₂) <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]

中文:
定理 inner_weightedVSub
  结论: {ι₁ : 类型} {s₁ : 有限集 ι₁} {w₁ : ι₁ -> 实数} (p₁ : ι₁ -> P)
  证明: by
  rw [Finset.weightedVSub_apply]; rw [Finset.weightedVSub_apply]; rw [inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr (i₁ i₂) <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]

Depends on / 依赖: Finset, Finset.weightedVSub_apply, dist_eq_norm_vsub, inner_sum_smul_sum_smul_of_sum_eq_zero, rcongr, simp_rw, vsub_sub_vsub_cancel_right, weightedVSub_apply
-/
theorem inner_weightedVSub {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ -> Real} (p₁ : ι₁ -> P)
    (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ -> Real} (p₂ : ι₂ -> P)
    (h₂ : ∑ i in s₂, w₂ i = 0) :
    ⟪s₁.weightedVSub p₁ w₁, s₂.weightedVSub p₂ w₂⟫ =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) /
        2 := by
  rw [Finset.weightedVSub_apply]; rw [Finset.weightedVSub_apply]; rw [inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr (i₁ i₂) <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]

/--
theorem `dist_affineCombination` / 定理 `dist_affineCombination`

English:
theorem dist_affineCombination
  statement: {ι : Type*} {s : Finset ι} {w₁ w₂ : ι -> Real} (p : ι -> P)
  proof: s.affineCombination Real p w₁
      have a₂ := s.affineCombination Real p w₂
      exact dist a₁ a₂ * dist a₁ a₂ = (-∑ i₁ in s, ∑ i₂ in s,
        (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 := by
  dsimp only
  rw [dist_eq_norm_vsub V (s.affineCombination Real p w₁)

中文:
定理 dist_affineCombination
  结论: {ι : 类型} {s : 有限集 ι} {w₁ w₂ : ι -> 实数} (p : ι -> P)
  证明: s.affineCombination Real p w₁
      have a₂ := s.affineCombination Real p w₂
      exact dist a₁ a₂ * dist a₁ a₂ = (-∑ i₁ in s, ∑ i₂ in s,
        (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 := by
  dsimp only
  rw [dist_eq_norm_vsub V (s.affineCombination Real p w₁)

Depends on / 依赖: affineCombination, s.affineCombination
-/
theorem dist_affineCombination {ι : Type*} {s : Finset ι} {w₁ w₂ : ι -> Real} (p : ι -> P)
    (h₁ : ∑ i in s, w₁ i = 1) (h₂ : ∑ i in s, w₂ i = 1) : by
      have a₁ := s.affineCombination Real p w₁
      have a₂ := s.affineCombination Real p w₂
      exact dist a₁ a₂ * dist a₁ a₂ = (-∑ i₁ in s, ∑ i₂ in s,
        (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 := by
  dsimp only
  rw [dist_eq_norm_vsub V (s.affineCombination Real p w₁) (s.affineCombination Real p w₂)]; rw [←
    @inner_self_eq_norm_mul_norm Real]; rw [Finset.affineCombination_vsub]
  have h : (∑ i in s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, h₁, h₂, sub_self]
  exact inner_weightedVSub p h p h

/--
theorem `dist_smul_vadd_sq` / 定理 `dist_smul_vadd_sq`

English:
theorem dist_smul_vadd_sq
  given: (r : Real) (v : V) (p₁ p₂ : P)
  proof: by
  rw [dist_eq_norm_vsub V _ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [vadd_vsub_assoc]; rw [real_inner_add_add_self]; rw [real_inner_smul_left]; rw [real_inner_smul_left]; rw [real_inner_smul_right]
  ring

中文:
定理 dist_smul_vadd_sq
  条件: (r : 实数) (v : V) (p₁ p₂ : P)
  证明: by
  rw [dist_eq_norm_vsub V _ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [vadd_vsub_assoc]; rw [real_inner_add_add_self]; rw [real_inner_smul_left]; rw [real_inner_smul_left]; rw [real_inner_smul_right]
  ring

Depends on / 依赖: dist_eq_norm_vsub, real_inner_add_add_self, real_inner_self_eq_norm_mul_norm, real_inner_smul_left, real_inner_smul_right, vadd_vsub_assoc
-/
theorem dist_smul_vadd_sq (r : Real) (v : V) (p₁ p₂ : P) :
    dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
      ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [dist_eq_norm_vsub V _ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [vadd_vsub_assoc]; rw [real_inner_add_add_self]; rw [real_inner_smul_left]; rw [real_inner_smul_left]; rw [real_inner_smul_right]
  ring

/--
theorem `dist_smul_vadd_eq_dist` / 定理 `dist_smul_vadd_eq_dist`

English:
theorem dist_smul_vadd_eq_dist
  given: {v : V} (p₁ p₂ : P) (hv : v != 0) (r : Real)
  proof: by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_smul_vadd_sq]; rw [mul_assoc]; rw [← sub_eq_zero]; rw [add_sub_assoc]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [sub_self]
  have hvi : ⟪v, v⟫ != 0 := by simpa using hv
  have hd :

中文:
定理 dist_smul_vadd_eq_dist
  条件: {v : V} (p₁ p₂ : P) (hv : v != 0) (r : 实数)
  证明: by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_smul_vadd_sq]; rw [mul_assoc]; rw [← sub_eq_zero]; rw [add_sub_assoc]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [sub_self]
  have hvi : ⟪v, v⟫ != 0 := by simpa using hv
  have hd :

Depends on / 依赖: add_sub_assoc, conv_lhs, discrim, dist_eq_norm_vsub, dist_nonneg, dist_smul_vadd_sq, mul_, mul_assoc, mul_self_inj_of_nonneg, neg_add_cancel, neg_mul_eq_neg_mul, quadratic_eq_zero_iff, real_inner_self_eq_norm_mul_norm, sub_eq_zero, sub_self, zero_div
-/
theorem dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v != 0) (r : Real) :
    dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫ := by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_smul_vadd_sq]; rw [mul_assoc]; rw [← sub_eq_zero]; rw [add_sub_assoc]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [← real_inner_self_eq_norm_mul_norm]; rw [sub_self]
  have hvi : ⟪v, v⟫ != 0 := by simpa using hv
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 = 2 * ⟪v, p₁ -ᵥ p₂⟫ * (2 * ⟪v, p₁ -ᵥ p₂⟫) := by
    rw [discrim]
    ring
  rw [quadratic_eq_zero_iff hvi hd]; rw [neg_add_cancel]; rw [zero_div]; rw [neg_mul_eq_neg_mul]; rw [←
    mul_sub_right_distrib]; rw [sub_eq_add_neg]; rw [← mul_two]; rw [mul_assoc]; rw [mul_div_assoc]; rw [mul_div_mul_left]; rw [mul_div_assoc]
  simp

open AffineSubspace Module

/--
theorem `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` / 定理 `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two`

English:
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
  statement: {s : AffineSubspace Real P}
  proof: by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Fin 2 -> V := ![c₂ -ᵥ c₁,

中文:
定理 eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
  结论: {s : 仿射子空间 实数 P}
  证明: by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Fin 2 -> V := ![c₂ -ᵥ c₁,

Depends on / 依赖: LinearIndependent, fin_cases, hc.symm, hp.symm, inner_vsub_vsub_of_dist_eq_of_dist_eq, linearIndependent_of_ne_zero_of_inner_eq_zero
-/
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : AffineSubspace Real P}
    [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
    (hc₁s : c₁ in s) (hc₂s : c₂ in s) (hp₁s : p₁ in s) (hp₂s : p₂ in s) (hps : p in s) {r₁ r₂ : Real}
    (hc : c₁ != c₂) (hp : p₁ != p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
    (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
    (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ := by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Fin 2 -> V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁]
  have hb : LinearIndependent Real b := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i <;> simp [b, hc.symm, hp.symm]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
      · exact ho
      · rw [real_inner_comm]
        exact ho
  have hbs : Submodule.span Real (Set.range b) = s.direction := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact vsub_mem_direction hc₂s hc₁s
      · exact vsub_mem_direction hp₂s hp₁s
    · rw [finrank_span_eq_card hb, Fintype.card_fin, hd]
  have hv : forall v in s.direction, exists t₁ t₂ : Real, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁) := by
    intro v hv
    have hr : Set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁} := by
      have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      classical
      rw [← Fintype.coe_image_univ]; rw [hu]
      simp [b]
    rw [← hbs]; rw [hr]; rw [Submodule.mem_span_insert] at hv
    rcases hv with ⟨t₁, v', hv', hv⟩
    rw [Submodule.mem_span_singleton] at hv'
    rcases hv' with ⟨t₂, rfl⟩
    exact ⟨t₁, t₂, hv⟩
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero,
    mul_eq_zero, inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false] at hop
  rw [hop]; rw [zero_smul]; rw [zero_add]; rw [← eq_vadd_iff_vsub_eq] at hpt
  subst hpt
  have hp' : (p₂ -ᵥ p₁ : V) != 0 := by simp [hp.symm]
  have hp₂ : dist ((1 : Real) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁ := by simp [hp₂c₁]
  rw [← hp₁c₁]; rw [dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂
  simp only [one_ne_zero, false_or] at hp₂
  rw [hp₂.symm] at hpc₁
  rcases hpc₁ with hpc₁ | hpc₁ <;> simp [hpc₁]

/--
theorem `eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` / 定理 `eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`

English:
theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
  statement: [FiniteDimensional Real V] (hd : finrank Real V = 2)
  proof: haveI hd' : finrank Real (⊤ : AffineSubspace Real P).direction = 2 := by
    rw [direction_top]; rw [finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top Real V _) (mem_top Real V _)
    (mem_top Real V _) (mem_top Real V _) (mem_top Real V _) hc hp hp₁c₁ hp₂c₁ 

中文:
定理 eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
  结论: [有限维 实数 V] (hd : finrank 实数 V = 2)
  证明: haveI hd' : finrank Real (⊤ : AffineSubspace Real P).direction = 2 := by
    rw [direction_top]; rw [finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top Real V _) (mem_top Real V _)
    (mem_top Real V _) (mem_top Real V _) (mem_top Real V _) hc hp hp₁c₁ hp₂c₁ 

Depends on / 依赖: AffineSubspace, direction, direction_top, eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two, finrank, finrank_top, mem_top
-/
theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional Real V] (hd : finrank Real V = 2)
    {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : Real} (hc : c₁ != c₂) (hp : p₁ != p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
  haveI hd' : finrank Real (⊤ : AffineSubspace Real P).direction = 2 := by
    rw [direction_top]; rw [finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top Real V _) (mem_top Real V _)
    (mem_top Real V _) (mem_top Real V _) (mem_top Real V _) hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂

end EuclideanGeometry
