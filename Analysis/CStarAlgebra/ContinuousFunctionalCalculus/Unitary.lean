/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.Peel
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.Complex.Basic

/-! # Conditions on unitary elements imposed by the continuous functional calculus

## Main theorems

* `unitary_iff_isStarNormal_and_spectrum_subset_unitary`: An element is unitary if and only if it is
  star-normal and its spectrum lies on the unit circle.

-/

public section

section Generic

variable {R A : Type*} {p : A -> Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R A p]

/--
lemma `cfc_unitary_iff` / 引理 `cfc_unitary_iff`

English:
lemma cfc_unitary_iff
  statement: (f : R -> R) (a : A) (ha : p a := by cfc_tac)
  proof: by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [← IsStarNormal.cfc_map (p := p) f a |>.star_comm_self |>.eq]; rw [and_self]; rw [← cfc_one R a]; rw [← cfc_star]; rw [← cfc_mul ..]; rw [cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

中文:
引理 cfc_unitary_iff
  结论: (f : R -> R) (a : A) (ha : p a := by cfc_tac)
  证明: by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [← IsStarNormal.cfc_map (p := p) f a |>.star_comm_self |>.eq]; rw [and_self]; rw [← cfc_one R a]; rw [← cfc_star]; rw [← cfc_mul ..]; rw [cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

Depends on / 依赖: ContinuousOn, Iff.rfl, IsStarNormal, IsStarNormal.cfc_map, Set.mem_ofPred_eq, Submonoid, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, and_self, cfc_cont_tac, cfc_eq_cfc_iff_eqOn, cfc_map, cfc_mul, cfc_one, cfc_star, cfc_tac, mem_mk, mem_ofPred_eq, spectrum
-/
lemma cfc_unitary_iff (f : R -> R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc f a in unitary A ↔ forall x in spectrum R a, star (f x) * f x = 1 := by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [← IsStarNormal.cfc_map (p := p) f a |>.star_comm_self |>.eq]; rw [and_self]; rw [← cfc_one R a]; rw [← cfc_star]; rw [← cfc_mul ..]; rw [cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

end Generic

section Complex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra Complex A]
  [ContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `unitary_iff_isStarNormal_and_spectrum_subset_unitary` / 引理 `unitary_iff_isStarNormal_and_spectrum_subset_unitary`

English:
lemma unitary_iff_isStarNormal_and_spectrum_subset_unitary
  given: {u : A}
  proof: by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu => ?_
  nth_rw 1 [← cfc_id Complex u]
  rw [cfc_unitary_iff id u]; rw [Set.subset_def]
  simp only [id_eq, RCLike.star_def, SetLike.mem_coe, Unitary.mem_iff_star_mul_self]

中文:
引理 unitary_iff_isStarNormal_and_spectrum_subset_unitary
  条件: {u : A}
  证明: by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu => ?_
  nth_rw 1 [← cfc_id Complex u]
  rw [cfc_unitary_iff id u]; rw [Set.subset_def]
  simp only [id_eq, RCLike.star_def, SetLike.mem_coe, Unitary.mem_iff_star_mul_self]

Depends on / 依赖: RCLike, RCLike.star_def, Set.subset_def, SetLike, SetLike.mem_coe, Unitary, Unitary.mem_iff_star_mul_self, and_congr_right, and_iff_right_of_imp, cfc_id, cfc_unitary_iff, id_eq, isStarNormal_of_mem_unitary, mem_coe, mem_iff_star_mul_self, nth_rw, star_def, subset_def
-/
lemma unitary_iff_isStarNormal_and_spectrum_subset_unitary {u : A} :
    u in unitary A ↔ IsStarNormal u ∧ spectrum Complex u subseteq unitary Complex := by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu => ?_
  nth_rw 1 [← cfc_id Complex u]
  rw [cfc_unitary_iff id u]; rw [Set.subset_def]
  simp only [id_eq, RCLike.star_def, SetLike.mem_coe, Unitary.mem_iff_star_mul_self]

/--
lemma `mem_unitary_of_spectrum_subset_unitary` / 引理 `mem_unitary_of_spectrum_subset_unitary`

English:
lemma mem_unitary_of_spectrum_subset_unitary
  statement: {u : A}
  proof: unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr ⟨‹_›, hu⟩

中文:
引理 mem_unitary_of_spectrum_subset_unitary
  结论: {u : A}
  证明: unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr ⟨‹_›, hu⟩

Depends on / 依赖: unitary_iff_isStarNormal_and_spectrum_subset_unitary, unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr
-/
lemma mem_unitary_of_spectrum_subset_unitary {u : A}
    [IsStarNormal u] (hu : spectrum Complex u subseteq unitary Complex) : u in unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr ⟨‹_›, hu⟩

/--
lemma `spectrum_subset_unitary_of_mem_unitary` / 引理 `spectrum_subset_unitary_of_mem_unitary`

English:
lemma spectrum_subset_unitary_of_mem_unitary
  given: {u : A} (hu : u in unitary A)
  proof: .right unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hu

中文:
引理 spectrum_subset_unitary_of_mem_unitary
  条件: {u : A} (hu : u in unitary A)
  证明: .right unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hu

Depends on / 依赖: unitary_iff_isStarNormal_and_spectrum_subset_unitary, unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp
-/
lemma spectrum_subset_unitary_of_mem_unitary {u : A} (hu : u in unitary A) :
    spectrum Complex u subseteq unitary Complex :=
.right unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hu

end Complex
