/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.SignedDist
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Instances.Sign

/-!
# Incenters and excenters of simplices.

This file defines the insphere and exspheres of a simplex (tangent to the faces of the simplex),
and the center and radius of such spheres.

The terms "exsphere", "excenter" and "exradius" are used in this file in a general sense where
a `Finset` `signs` of indices is given that determine, up to negating all the signs, which
vertices of the simplex lie on the same side of the opposite face as the excenter and which lie
on the opposite side of that face. This includes the cases of the insphere, incenter and
inradius, when `signs` is `∅` (or `univ`); the insphere always exists. It also includes the case
of an exsphere opposite a vertex, when `signs` is a singleton (or its complement), which always
exists in two or more dimensions. In three or more dimensions, there are further possibilities
for `signs`, and the corresponding excenters may or may not exist, depending on the choice of
simplex. For convenience, the most common definitions `exsphere`, `excenter` and `exradius` have
corresponding `insphere`, `incenter` and `inradius` definitions, and various lemmas are duplicated
for the case of the insphere to avoid needing to pass an `ExcenterExists` hypothesis in that case.
However, other definitions such as `excenterWeights`, `touchpoint` and `touchpointWeights` are not
duplicated.

## Main definitions

* `Affine.Simplex.ExcenterExists` says whether an excenter exists with a given set of indices.
* `Affine.Simplex.excenterWeights` are the weights of the excenter with the given set of
  indices, if it exists, as an affine combination of the vertices.
* `Affine.Simplex.exsphere` is the exsphere with the given set of indices, if it exists, with
  shorthands:
  * `Affine.Simplex.excenter` for the center of this sphere
  * `Affine.Simplex.exradius` for the radius of this sphere
* `Affine.Simplex.insphere` is the insphere, with shorthands:
  * `Affine.Simplex.incenter` for the center of this sphere
  * `Affine.Simplex.inradius` for the radius of this sphere
* `Affine.Simplex.touchpoint` for the point where an exsphere of a simplex is tangent to one of
  the faces.
* `Affine.Simplex.touchpointWeights` for the weights of a touchpoint as an affine combination of
  the vertices.

## References

* https://en.wikipedia.org/wiki/Incircle_and_excircles
* https://en.wikipedia.org/wiki/Incenter

-/

@[expose] public section


open EuclideanGeometry
open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

noncomputable section

namespace Affine

namespace Simplex

variable {m n : Nat} [NeZero m] [NeZero n] (s : Simplex Real P n)

/--
Definition of `excenterWeightsUnnorm` / `excenterWeightsUnnorm` 的定义

English:
definition excenterWeightsUnnorm
  signature: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  body: (if i in signs then -1 else 1) * (s.height i)⁻¹

中文:
定义 excenterWeightsUnnorm
  签名: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  定义体: (if i in signs then -1 else 1) * (s.height i)⁻¹

Depends on / 依赖: height, s.height
-/
def excenterWeightsUnnorm (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Real :=
  (if i in signs then -1 else 1) * (s.height i)⁻¹

/--
lemma `excenterWeightsUnnorm_reindex` / 引理 `excenterWeightsUnnorm_reindex`

English:
lemma excenterWeightsUnnorm_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  ext i
  simp [excenterWeightsUnnorm]

中文:
引理 excenterWeightsUnnorm_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  ext i
  simp [excenterWeightsUnnorm]

Depends on / 依赖: excenterWeightsUnnorm
-/
lemma excenterWeightsUnnorm_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeightsUnnorm signs =
      s.excenterWeightsUnnorm (signs.map e.symm) ∘ e.symm := by
  ext i
  simp [excenterWeightsUnnorm]

/--
lemma `excenterWeightsUnnorm_map` / 引理 `excenterWeightsUnnorm_map`

English:
lemma excenterWeightsUnnorm_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  ext
  simp [excenterWeightsUnnorm]

中文:
引理 excenterWeightsUnnorm_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  ext
  simp [excenterWeightsUnnorm]
-/
@[simp] lemma excenterWeightsUnnorm_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]

/--
lemma `excenterWeightsUnnorm_restrict` / 引理 `excenterWeightsUnnorm_restrict`

English:
lemma excenterWeightsUnnorm_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]

中文:
引理 excenterWeightsUnnorm_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]
-/
@[simp] lemma excenterWeightsUnnorm_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]

/--
lemma `excenterWeightsUnnorm_empty_apply` / 引理 `excenterWeightsUnnorm_empty_apply`

English:
lemma excenterWeightsUnnorm_empty_apply
  given: (i : Fin (n + 1))
  proof: one_mul _

中文:
引理 excenterWeightsUnnorm_empty_apply
  条件: (i : 有限集 (n + 1))
  证明: one_mul _
-/
@[simp] lemma excenterWeightsUnnorm_empty_apply (i : Fin (n + 1)) :
    s.excenterWeightsUnnorm ∅ i = (s.height i)⁻¹ :=
  one_mul _

/--
lemma `excenterWeightsUnnorm_ne_zero` / 引理 `excenterWeightsUnnorm_ne_zero`

English:
lemma excenterWeightsUnnorm_ne_zero
  given: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  proof: by
  rw [excenterWeightsUnnorm]
  refine mul_ne_zero ?_ ?_
  · grind
  · simp [(s.height_pos i).ne']

中文:
引理 excenterWeightsUnnorm_ne_zero
  条件: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  证明: by
  rw [excenterWeightsUnnorm]
  refine mul_ne_zero ?_ ?_
  · grind
  · simp [(s.height_pos i).ne']

Depends on / 依赖: excenterWeightsUnnorm, height_pos, mul_ne_zero, s.height_pos
-/
lemma excenterWeightsUnnorm_ne_zero (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.excenterWeightsUnnorm signs i != 0 := by
  rw [excenterWeightsUnnorm]
  refine mul_ne_zero ?_ ?_
  · grind
  · simp [(s.height_pos i).ne']

/--
Definition of `ExcenterExists` / `ExcenterExists` 的定义

English:
definition ExcenterExists
  signature: (signs : Finset (Fin (n + 1)))
  body: ∑ i, s.excenterWeightsUnnorm signs i != 0

中文:
定义 ExcenterExists
  签名: (signs : 有限集 (有限集 (n + 1)))
  定义体: ∑ i, s.excenterWeightsUnnorm signs i != 0

Depends on / 依赖: SetLike, SetLike.le_def, excenterWeightsUnnorm, le_def, mem_mk, s.excenterWeightsUnnorm, simp_rw
-/
def ExcenterExists (signs : Finset (Fin (n + 1))) : Prop :=
  ∑ i, s.excenterWeightsUnnorm signs i != 0

/--
lemma `excenterExists_reindex` / 引理 `excenterExists_reindex`

English:
lemma excenterExists_reindex
  given: {e : Fin (n + 1) ≃ Fin (m + 1)} {signs : Finset (Fin (m + 1))}
  proof: by
  simp_rw [ExcenterExists, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv]

中文:
引理 excenterExists_reindex
  条件: {e : 有限集 (n + 1) ≃ 有限集 (m + 1)} {signs : 有限集 (有限集 (m + 1))}
  证明: by
  simp_rw [ExcenterExists, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv]

Depends on / 依赖: ExcenterExists, Finset, Finset.map_univ_equiv, Finset.sum_comp_equiv, excenterWeightsUnnorm_reindex, map_univ_equiv, simp_rw, sum_comp_equiv
-/
lemma excenterExists_reindex {e : Fin (n + 1) ≃ Fin (m + 1)} {signs : Finset (Fin (m + 1))} :
    (s.reindex e).ExcenterExists signs ↔ s.ExcenterExists (signs.map e.symm) := by
  simp_rw [ExcenterExists, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv]

/--
lemma `excenterExists_map` / 引理 `excenterExists_map`

English:
lemma excenterExists_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  ext
  simp [ExcenterExists]

中文:
引理 excenterExists_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  ext
  simp [ExcenterExists]
-/
@[simp] lemma excenterExists_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]

/--
lemma `excenterExists_restrict` / 引理 `excenterExists_restrict`

English:
lemma excenterExists_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]

中文:
引理 excenterExists_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]
-/
@[simp] lemma excenterExists_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]

/--
Definition of `excenterWeights` / `excenterWeights` 的定义

English:
definition excenterWeights
  signature: (signs : Finset (Fin (n + 1)))
  body: (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs

中文:
定义 excenterWeights
  签名: (signs : 有限集 (有限集 (n + 1)))
  定义体: (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs

Depends on / 依赖: excenterWeightsUnnorm, s.excenterWeightsUnnorm
-/
def excenterWeights (signs : Finset (Fin (n + 1))) : Fin (n + 1) -> Real :=
  (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs

/--
lemma `excenterWeights_reindex` / 引理 `excenterWeights_reindex`

English:
lemma excenterWeights_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  simp_rw [excenterWeights, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv, Pi.smul_comp]

中文:
引理 excenterWeights_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  simp_rw [excenterWeights, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv, Pi.smul_comp]

Depends on / 依赖: Finset, Finset.map_univ_equiv, Finset.sum_comp_equiv, Pi.smul_comp, excenterWeights, excenterWeightsUnnorm_reindex, map_univ_equiv, simp_rw, smul_comp, sum_comp_equiv
-/
lemma excenterWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeights signs =
      s.excenterWeights (signs.map e.symm) ∘ e.symm := by
  simp_rw [excenterWeights, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv, Pi.smul_comp]

/--
lemma `excenterWeights_map` / 引理 `excenterWeights_map`

English:
lemma excenterWeights_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  ext
  simp [excenterWeights]

中文:
引理 excenterWeights_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  ext
  simp [excenterWeights]
-/
@[simp] lemma excenterWeights_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]

/--
lemma `excenterWeights_restrict` / 引理 `excenterWeights_restrict`

English:
lemma excenterWeights_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]

中文:
引理 excenterWeights_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]
-/
@[simp] lemma excenterWeights_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]

variable {s} in
/--
lemma `ExcenterExists.excenterWeights_ne_zero` / 引理 `ExcenterExists.excenterWeights_ne_zero`

English:
lemma ExcenterExists.excenterWeights_ne_zero
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenterWeights]
  refine mul_ne_zero ?_ (s.excenterWeightsUnnorm_ne_zero _ _)
  rw [ExcenterExists] at h
  simp [h]

中文:
引理 ExcenterExists.excenterWeights_ne_zero
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenterWeights]
  refine mul_ne_zero ?_ (s.excenterWeightsUnnorm_ne_zero _ _)
  rw [ExcenterExists] at h
  simp [h]

Depends on / 依赖: ExcenterExists, excenterWeights, excenterWeightsUnnorm_ne_zero, mul_ne_zero, s.excenterWeightsUnnorm_ne_zero
-/
lemma ExcenterExists.excenterWeights_ne_zero {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.excenterWeights signs i != 0 := by
  rw [excenterWeights]
  refine mul_ne_zero ?_ (s.excenterWeightsUnnorm_ne_zero _ _)
  rw [ExcenterExists] at h
  simp [h]

/--
lemma `excenterWeightsUnnorm_compl` / 引理 `excenterWeightsUnnorm_compl`

English:
lemma excenterWeightsUnnorm_compl
  given: (signs : Finset (Fin (n + 1)))
  proof: by
  ext i
  by_cases h : i in signs <;> simp [excenterWeightsUnnorm, h]

中文:
引理 excenterWeightsUnnorm_compl
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: by
  ext i
  by_cases h : i in signs <;> simp [excenterWeightsUnnorm, h]
-/
@[simp] lemma excenterWeightsUnnorm_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeightsUnnorm signsᶜ = -s.excenterWeightsUnnorm signs := by
  ext i
  by_cases h : i in signs <;> simp [excenterWeightsUnnorm, h]

/--
lemma `excenterWeights_compl` / 引理 `excenterWeights_compl`

English:
lemma excenterWeights_compl
  given: (signs : Finset (Fin (n + 1)))
  proof: by
  simp [excenterWeights, inv_neg]

中文:
引理 excenterWeights_compl
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: by
  simp [excenterWeights, inv_neg]
-/
@[simp] lemma excenterWeights_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeights signsᶜ = s.excenterWeights signs := by
  simp [excenterWeights, inv_neg]

/--
lemma `excenterExists_compl` / 引理 `excenterExists_compl`

English:
lemma excenterExists_compl
  given: {signs : Finset (Fin (n + 1))}
  proof: by
  simp [ExcenterExists]

中文:
引理 excenterExists_compl
  条件: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  simp [ExcenterExists]
-/
@[simp] lemma excenterExists_compl {signs : Finset (Fin (n + 1))} :
    s.ExcenterExists signsᶜ ↔ s.ExcenterExists signs := by
  simp [ExcenterExists]

/--
lemma `sum_excenterWeights` / 引理 `sum_excenterWeights`

English:
lemma sum_excenterWeights
  given: (signs : Finset (Fin (n + 1))) [Decidable (s.ExcenterExists signs)]
  proof: by
  simp_rw [ExcenterExists, excenterWeights]
  split_ifs with h
  · simp [← Finset.mul_sum, h]
  · simp only [ne_eq, not_not] at h
    simp [h]

中文:
引理 sum_excenterWeights
  条件: (signs : 有限集 (有限集 (n + 1))) [可判定 (s.ExcenterExists signs)]
  证明: by
  simp_rw [ExcenterExists, excenterWeights]
  split_ifs with h
  · simp [← Finset.mul_sum, h]
  · simp only [ne_eq, not_not] at h
    simp [h]

Depends on / 依赖: ExcenterExists, Finset, Finset.mul_sum, excenterWeights, mul_sum, ne_eq, not_not, simp_rw, split_ifs
-/
lemma sum_excenterWeights (signs : Finset (Fin (n + 1))) [Decidable (s.ExcenterExists signs)] :
    ∑ i, s.excenterWeights signs i = if s.ExcenterExists signs then 1 else 0 := by
  simp_rw [ExcenterExists, excenterWeights]
  split_ifs with h
  · simp [← Finset.mul_sum, h]
  · simp only [ne_eq, not_not] at h
    simp [h]

/--
lemma `sum_excenterWeights_eq_one_iff` / 引理 `sum_excenterWeights_eq_one_iff`

English:
lemma sum_excenterWeights_eq_one_iff
  given: {signs : Finset (Fin (n + 1))}
  proof: by
  classical
  simp [sum_excenterWeights]

alias ⟨_, ExcenterExists.sum_excenterWeights_eq_one⟩ := sum_excenterWeights_eq_one_iff

中文:
引理 sum_excenterWeights_eq_one_iff
  条件: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  classical
  simp [sum_excenterWeights]

alias ⟨_, ExcenterExists.sum_excenterWeights_eq_one⟩ := sum_excenterWeights_eq_one_iff
-/
@[simp] lemma sum_excenterWeights_eq_one_iff {signs : Finset (Fin (n + 1))} :
    ∑ i, s.excenterWeights signs i = 1 ↔ s.ExcenterExists signs := by
  classical
  simp [sum_excenterWeights]

alias ⟨_, ExcenterExists.sum_excenterWeights_eq_one⟩ := sum_excenterWeights_eq_one_iff

/--
lemma `sum_excenterWeightsUnnorm_empty_pos` / 引理 `sum_excenterWeightsUnnorm_empty_pos`

English:
lemma sum_excenterWeightsUnnorm_empty_pos
  statement: 0 < ∑ i, s.excenterWeightsUnnorm ∅ i
  proof: by
  simp_rw [excenterWeightsUnnorm_empty_apply]
  positivity

中文:
引理 sum_excenterWeightsUnnorm_empty_pos
  结论: 0 < ∑ i, s.excenterWeightsUnnorm ∅ i
  证明: by
  simp_rw [excenterWeightsUnnorm_empty_apply]
  positivity

Depends on / 依赖: excenterWeightsUnnorm_empty_apply, simp_rw
-/
lemma sum_excenterWeightsUnnorm_empty_pos : 0 < ∑ i, s.excenterWeightsUnnorm ∅ i := by
  simp_rw [excenterWeightsUnnorm_empty_apply]
  positivity

/--
lemma `excenterWeights_empty_pos` / 引理 `excenterWeights_empty_pos`

English:
lemma excenterWeights_empty_pos
  given: (i : Fin (n + 1))
  statement: 0 < s.excenterWeights ∅ i
  proof: by
  simp only [excenterWeights, excenterWeightsUnnorm_empty_apply, Pi.smul_apply, smul_eq_mul]
  positivity

@[simp]

中文:
引理 excenterWeights_empty_pos
  条件: (i : 有限集 (n + 1))
  结论: 0 < s.excenterWeights ∅ i
  证明: by
  simp only [excenterWeights, excenterWeightsUnnorm_empty_apply, Pi.smul_apply, smul_eq_mul]
  positivity

@[simp]

Depends on / 依赖: Pi.smul_apply, excenterWeights, excenterWeightsUnnorm_empty_apply, smul_apply, smul_eq_mul
-/
lemma excenterWeights_empty_pos (i : Fin (n + 1)) : 0 < s.excenterWeights ∅ i := by
  simp only [excenterWeights, excenterWeightsUnnorm_empty_apply, Pi.smul_apply, smul_eq_mul]
  positivity

@[simp]
/--
lemma `sign_excenterWeights_empty` / 引理 `sign_excenterWeights_empty`

English:
lemma sign_excenterWeights_empty
  given: (i : Fin (n + 1))
  statement: SignType.sign (s.excenterWeights ∅ i) = 1
  proof: by
  rw [sign_eq_one_iff]
  exact s.excenterWeights_empty_pos i

中文:
引理 sign_excenterWeights_empty
  条件: (i : 有限集 (n + 1))
  结论: SignType.sign (s.excenterWeights ∅ i) = 1
  证明: by
  rw [sign_eq_one_iff]
  exact s.excenterWeights_empty_pos i

Depends on / 依赖: excenterWeights_empty_pos, s.excenterWeights_empty_pos, sign_eq_one_iff
-/
lemma sign_excenterWeights_empty (i : Fin (n + 1)) : SignType.sign (s.excenterWeights ∅ i) = 1 := by
  rw [sign_eq_one_iff]
  exact s.excenterWeights_empty_pos i

/--
lemma `excenterExists_empty` / 引理 `excenterExists_empty`

English:
lemma excenterExists_empty
  statement: s.ExcenterExists ∅
  proof: s.sum_excenterWeightsUnnorm_empty_pos.ne'

中文:
引理 excenterExists_empty
  结论: s.ExcenterExists ∅
  证明: s.sum_excenterWeightsUnnorm_empty_pos.ne'
-/
@[simp] lemma excenterExists_empty : s.ExcenterExists ∅ :=
  s.sum_excenterWeightsUnnorm_empty_pos.ne'

/--
lemma `sum_inv_height_sq_smul_vsub_eq_zero` / 引理 `sum_inv_height_sq_smul_vsub_eq_zero`

English:
lemma sum_inv_height_sq_smul_vsub_eq_zero
  proof: by
  suffices forall i, i != 0 ->
      ∑ j, ⟪s.points i -ᵥ s.points 0, (s.height j)⁻¹ ^ 2 • (s.points j -ᵥ s.altitudeFoot j)⟫ = 0 by
    rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
    refine ⟨Submodule.sum_smul_mem _ _ fun i hi =>
              vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
                (mem_affineSpan _ (Set.mem_range_self _))
                (altitudeFoot_mem_affineSpan _ _),
            ?_⟩
    rw [vectorSpan_range_eq_span_range_vsub_right_ne _ _ 0]; rw [Submodule.span_range_eq_iSup]; rw [← Submodule.iInf_orthogonal]; rw [Submodule.coe_iInf]; rw [Set.mem_iInter]
    intro i
    rcases i with ⟨i, hi⟩
    simpa only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sum]
      using this i hi
  intro i hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]; rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hi]; rw [Finset.mem_univ _⟩)]; rw [← add_assoc]
  convert! add_zero _
  · convert! Finset.sum_const_zero with j hj
    rw [real_inner_smul_right]
    convert! mul_zero _
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine SetLike.le_def.1 (Submodule.orthogonal_le ?_)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
    rw [Submodule.span_singleton_le_iff_mem]; rw [direction_affineSpan]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    refine vsub_mem_vectorSpan _ ?_ ?_ <;>
      simp only [range_faceOpposite_points, Set.mem_image]
    · exact ⟨i, hj.1.symm, rfl⟩
    · exact ⟨0, hj.2.symm, rfl⟩
  · rw [inner_smul_right, inner_smul_right, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi,
      ← neg_vsub_eq_vsub_rev, inner_neg_left, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi.symm,
      mul_neg, inv_pow]
    simp [height]

中文:
引理 sum_inv_height_sq_smul_vsub_eq_zero
  证明: by
  suffices forall i, i != 0 ->
      ∑ j, ⟪s.points i -ᵥ s.points 0, (s.height j)⁻¹ ^ 2 • (s.points j -ᵥ s.altitudeFoot j)⟫ = 0 by
    rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
    refine ⟨Submodule.sum_smul_mem _ _ fun i hi =>
              vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
                (mem_affineSpan _ (Set.mem_range_self _))
                (altitudeFoot_mem_affineSpan _ _),
            ?_⟩
    rw [vectorSpan_range_eq_span_range_vsub_right_ne _ _ 0]; rw [Submodule.span_range_eq_iSup]; rw [← Submodule.iInf_orthogonal]; rw [Submodule.coe_iInf]; rw [Set.mem_iInter]
    intro i
    rcases i with ⟨i, hi⟩
    simpa only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sum]
      using this i hi
  intro i hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]; rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hi]; rw [Finset.mem_univ _⟩)]; rw [← add_assoc]
  convert! add_zero _
  · convert! Finset.sum_const_zero with j hj
    rw [real_inner_smul_right]
    convert! mul_zero _
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine SetLike.le_def.1 (Submodule.orthogonal_le ?_)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
    rw [Submodule.span_singleton_le_iff_mem]; rw [direction_affineSpan]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    refine vsub_mem_vectorSpan _ ?_ ?_ <;>
      simp only [range_faceOpposite_points, Set.mem_image]
    · exact ⟨i, hj.1.symm, rfl⟩
    · exact ⟨0, hj.2.symm, rfl⟩
  · rw [inner_smul_right, inner_smul_right, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi,
      ← neg_vsub_eq_vsub_rev, inner_neg_left, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi.symm,
      mul_neg, inv_pow]
    simp [height]

Depends on / 依赖: Set.mem_range_self, Set.range, Submodule, Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, Submodule.span_range, Submodule.sum_smul_mem, altitudeFoot, altitudeFoot_mem_affineSpan, height, inf_orthogonal_eq_bot, mem_affineSpan, mem_bot, mem_range_self, points, s.altitudeFoot, s.height, s.points, span_range, sum_smul_mem
-/
lemma sum_inv_height_sq_smul_vsub_eq_zero :
    ∑ i, (s.height i)⁻¹ ^ 2 • (s.points i -ᵥ s.altitudeFoot i) = 0 := by
  suffices forall i, i != 0 ->
      ∑ j, ⟪s.points i -ᵥ s.points 0, (s.height j)⁻¹ ^ 2 • (s.points j -ᵥ s.altitudeFoot j)⟫ = 0 by
    rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
    refine ⟨Submodule.sum_smul_mem _ _ fun i hi =>
              vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
                (mem_affineSpan _ (Set.mem_range_self _))
                (altitudeFoot_mem_affineSpan _ _),
            ?_⟩
    rw [vectorSpan_range_eq_span_range_vsub_right_ne _ _ 0]; rw [Submodule.span_range_eq_iSup]; rw [← Submodule.iInf_orthogonal]; rw [Submodule.coe_iInf]; rw [Set.mem_iInter]
    intro i
    rcases i with ⟨i, hi⟩
    simpa only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sum]
      using this i hi
  intro i hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]; rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hi]; rw [Finset.mem_univ _⟩)]; rw [← add_assoc]
  convert! add_zero _
  · convert! Finset.sum_const_zero with j hj
    rw [real_inner_smul_right]
    convert! mul_zero _
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine SetLike.le_def.1 (Submodule.orthogonal_le ?_)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
    rw [Submodule.span_singleton_le_iff_mem]; rw [direction_affineSpan]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    refine vsub_mem_vectorSpan _ ?_ ?_ <;>
      simp only [range_faceOpposite_points, Set.mem_image]
    · exact ⟨i, hj.1.symm, rfl⟩
    · exact ⟨0, hj.2.symm, rfl⟩
  · rw [inner_smul_right, inner_smul_right, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi,
      ← neg_vsub_eq_vsub_rev, inner_neg_left, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi.symm,
      mul_neg, inv_pow]
    simp [height]

/--
lemma `inv_height_eq_sum_mul_inv_dist` / 引理 `inv_height_eq_sum_mul_inv_dist`

English:
lemma inv_height_eq_sum_mul_inv_dist
  given: (i : Fin (n + 1))
  proof: by
  rw [← sub_eq_zero]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]; rw [sub_neg_eq_add]; rw [Finset.filter_ne']; rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]; rw [real_inner_self_eq_norm_mul_norm]; rw [← dist_eq_norm_vsub]
  simp only [height, ne_eq, mul_eq_zero, dist_eq_zero, ne_altitudeFoot, or_self,
    not_false_eq_true, div_self, one_mul, add_sub_cancel]
  have h := s.sum_inv_height_sq_smul_vsub_eq_zero
  apply_fun fun v => (s.height i)⁻¹ * ⟪s.points i -ᵥ s.altitudeFoot i, v⟫ at h
  rw [inner_sum]; rw [Finset.mul_sum] at h
  simp only [inner_zero_right, mul_zero, inner_smul_right, height] at h
  convert! h using 2 with j
  ring

中文:
引理 inv_height_eq_sum_mul_inv_dist
  条件: (i : 有限集 (n + 1))
  证明: by
  rw [← sub_eq_zero]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]; rw [sub_neg_eq_add]; rw [Finset.filter_ne']; rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]; rw [real_inner_self_eq_norm_mul_norm]; rw [← dist_eq_norm_vsub]
  simp only [height, ne_eq, mul_eq_zero, dist_eq_zero, ne_altitudeFoot, or_self,
    not_false_eq_true, div_self, one_mul, add_sub_cancel]
  have h := s.sum_inv_height_sq_smul_vsub_eq_zero
  apply_fun fun v => (s.height i)⁻¹ * ⟪s.points i -ᵥ s.altitudeFoot i, v⟫ at h
  rw [inner_sum]; rw [Finset.mul_sum] at h
  simp only [inner_zero_right, mul_zero, inner_smul_right, height] at h
  convert! h using 2 with j
  ring

Depends on / 依赖: Finset, Finset.filter_ne, Finset.mem_univ, Finset.sum_erase_eq_sub, Finset.sum_neg_distrib, add_sub_cancel, altitudeFoot, apply_fun, dist_eq_norm_vsub, dist_eq_zero, div_self, filter_ne, height, inner_sum, mem_univ, mul_eq_zero, ne_altitudeFoot, ne_eq, neg_mul, not_false_eq_true
-/
lemma inv_height_eq_sum_mul_inv_dist (i : Fin (n + 1)) :
    (s.height i)⁻¹ =
      ∑ j in {k | k != i},
        -(⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ /
          (s.height i * s.height j)) *
        (s.height j)⁻¹ := by
  rw [← sub_eq_zero]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]; rw [sub_neg_eq_add]; rw [Finset.filter_ne']; rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]; rw [real_inner_self_eq_norm_mul_norm]; rw [← dist_eq_norm_vsub]
  simp only [height, ne_eq, mul_eq_zero, dist_eq_zero, ne_altitudeFoot, or_self,
    not_false_eq_true, div_self, one_mul, add_sub_cancel]
  have h := s.sum_inv_height_sq_smul_vsub_eq_zero
  apply_fun fun v => (s.height i)⁻¹ * ⟪s.points i -ᵥ s.altitudeFoot i, v⟫ at h
  rw [inner_sum]; rw [Finset.mul_sum] at h
  simp only [inner_zero_right, mul_zero, inner_smul_right, height] at h
  convert! h using 2 with j
  ring

/--
lemma `inv_height_lt_sum_inv_height` / 引理 `inv_height_lt_sum_inv_height`

English:
lemma inv_height_lt_sum_inv_height
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [inv_height_eq_sum_mul_inv_dist]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · rw [Finset.filter_ne', ← Finset.card_ne_zero]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right]
    exact NeZero.ne _
  · rintro j hj
    refine mul_lt_of_lt_one_left ?_ ?_
    · simp [height_pos]
    · rw [neg_lt]
      exact neg_one_lt_inner_vsub_altitudeFoot_div _ _ _

中文:
引理 inv_height_lt_sum_inv_height
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [inv_height_eq_sum_mul_inv_dist]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · rw [Finset.filter_ne', ← Finset.card_ne_zero]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right]
    exact NeZero.ne _
  · rintro j hj
    refine mul_lt_of_lt_one_left ?_ ?_
    · simp [height_pos]
    · rw [neg_lt]
      exact neg_one_lt_inner_vsub_altitudeFoot_div _ _ _

Depends on / 依赖: Finset, Finset.card_erase_of_mem, Finset.card_ne_zero, Finset.card_univ, Finset.filter_ne, Finset.mem_univ, Finset.sum_lt_sum_of_nonempty, Fintype, Fintype.card_fin, NeZero, NeZero.ne, add_tsub_cancel_right, card_erase_of_mem, card_fin, card_ne_zero, card_univ, filter_ne, height_pos, inv_height_eq_sum_mul_inv_dist, mem_univ
-/
lemma inv_height_lt_sum_inv_height [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (s.height i)⁻¹ < ∑ j in {k | k != i}, (s.height j)⁻¹ := by
  rw [inv_height_eq_sum_mul_inv_dist]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · rw [Finset.filter_ne', ← Finset.card_ne_zero]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right]
    exact NeZero.ne _
  · rintro j hj
    refine mul_lt_of_lt_one_left ?_ ?_
    · simp [height_pos]
    · rw [neg_lt]
      exact neg_one_lt_inner_vsub_altitudeFoot_div _ _ _

/--
lemma `sum_excenterWeightsUnnorm_singleton_pos` / 引理 `sum_excenterWeightsUnnorm_singleton_pos`

English:
lemma sum_excenterWeightsUnnorm_singleton_pos
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [← Finset.sum_add_sum_compl {i}]; rw [Finset.sum_singleton]
  nth_rw 1 [excenterWeightsUnnorm]
  simp only [Finset.mem_singleton, ↓reduceIte, neg_mul, one_mul, lt_neg_add_iff_add_lt, add_zero]
  convert! s.inv_height_lt_sum_inv_height i using 2 with j h
  · ext j
    simp
  · rw [Finset.mem_filter_univ] at h
    simp [excenterWeightsUnnorm, h]

中文:
引理 sum_excenterWeightsUnnorm_singleton_pos
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [← Finset.sum_add_sum_compl {i}]; rw [Finset.sum_singleton]
  nth_rw 1 [excenterWeightsUnnorm]
  simp only [Finset.mem_singleton, ↓reduceIte, neg_mul, one_mul, lt_neg_add_iff_add_lt, add_zero]
  convert! s.inv_height_lt_sum_inv_height i using 2 with j h
  · ext j
    simp
  · rw [Finset.mem_filter_univ] at h
    simp [excenterWeightsUnnorm, h]

Depends on / 依赖: Finset, Finset.mem_filter_univ, Finset.mem_singleton, Finset.sum_add_sum_compl, Finset.sum_singleton, add_zero, convert, excenterWeightsUnnorm, inv_height_lt_sum_inv_height, lt_neg_add_iff_add_lt, mem_filter_univ, mem_singleton, neg_mul, nth_rw, one_mul, reduceIte, s.inv_height_lt_sum_inv_height, sum_add_sum_compl, sum_singleton
-/
lemma sum_excenterWeightsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    0 < ∑ j, s.excenterWeightsUnnorm {i} j := by
  rw [← Finset.sum_add_sum_compl {i}]; rw [Finset.sum_singleton]
  nth_rw 1 [excenterWeightsUnnorm]
  simp only [Finset.mem_singleton, ↓reduceIte, neg_mul, one_mul, lt_neg_add_iff_add_lt, add_zero]
  convert! s.inv_height_lt_sum_inv_height i using 2 with j h
  · ext j
    simp
  · rw [Finset.mem_filter_univ] at h
    simp [excenterWeightsUnnorm, h]

/--
lemma `sign_excenterWeights_singleton_neg` / 引理 `sign_excenterWeights_singleton_neg`

English:
lemma sign_excenterWeights_singleton_neg
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm]

中文:
引理 sign_excenterWeights_singleton_neg
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm]

Depends on / 依赖: Pi.smul_apply, convert, excenterWeights, excenterWeightsUnnorm, inv_pos, one_mul, s.sum_excenterWeightsUnnorm_singleton_pos, sign_eq_one_iff, sign_mul, simp_rw, smul_apply, smul_eq_mul, sum_excenterWeightsUnnorm_singleton_pos
-/
lemma sign_excenterWeights_singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    SignType.sign (s.excenterWeights {i} i) = -1 := by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm]

/--
lemma `sign_excenterWeights_singleton_pos` / 引理 `sign_excenterWeights_singleton_pos`

English:
lemma sign_excenterWeights_singleton_pos
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j)
  proof: by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm, h.symm]

中文:
引理 sign_excenterWeights_singleton_pos
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (h : i != j)
  证明: by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm, h.symm]

Depends on / 依赖: Pi.smul_apply, convert, excenterWeights, excenterWeightsUnnorm, h.symm, inv_pos, one_mul, s.sum_excenterWeightsUnnorm_singleton_pos, sign_eq_one_iff, sign_mul, simp_rw, smul_apply, smul_eq_mul, sum_excenterWeightsUnnorm_singleton_pos
-/
lemma sign_excenterWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) :
    SignType.sign (s.excenterWeights {i} j) = 1 := by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm, h.symm]

/--
lemma `excenterExists_singleton` / 引理 `excenterExists_singleton`

English:
lemma excenterExists_singleton
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  statement: s.ExcenterExists {i}
  proof: (s.sum_excenterWeightsUnnorm_singleton_pos i).ne'

中文:
引理 excenterExists_singleton
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  结论: s.ExcenterExists {i}
  证明: (s.sum_excenterWeightsUnnorm_singleton_pos i).ne'

Depends on / 依赖: s.sum_excenterWeightsUnnorm_singleton_pos, sum_excenterWeightsUnnorm_singleton_pos
-/
lemma excenterExists_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i} :=
  (s.sum_excenterWeightsUnnorm_singleton_pos i).ne'

open Finset in
/--
lemma `excenterWeights_empty_lt_inv_two` / 引理 `excenterWeights_empty_lt_inv_two`

English:
lemma excenterWeights_empty_lt_inv_two
  given: [n.AtLeastTwo] (i : Fin (n + 1))
  proof: by
  have h : (s.height i)⁻¹ + (s.height i)⁻¹ < (s.height i)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    have := s.inv_height_lt_sum_inv_height i
    rwa [filter_ne', ← compl_singleton, ← add_lt_add_iff_left (s.height i)⁻¹] at this
  replace h : 2 * (s.height i)⁻¹ < ∑ j in {i}, (s.height j)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    rwa [two_mul, sum_singleton]
  replace h : (s.height i)⁻¹ / ∑ i, (s.height i)⁻¹ < 2⁻¹ := by
    rwa [sum_add_sum_compl, ← lt_inv_mul_iff₀ zero_lt_two, ← div_lt_iff₀ (by positivity)] at h
  convert! h
  simp [excenterWeights, excenterWeightsUnnorm, div_eq_inv_mul]

中文:
引理 excenterWeights_empty_lt_inv_two
  条件: [n.AtLeastTwo] (i : 有限集 (n + 1))
  证明: by
  have h : (s.height i)⁻¹ + (s.height i)⁻¹ < (s.height i)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    have := s.inv_height_lt_sum_inv_height i
    rwa [filter_ne', ← compl_singleton, ← add_lt_add_iff_left (s.height i)⁻¹] at this
  replace h : 2 * (s.height i)⁻¹ < ∑ j in {i}, (s.height j)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    rwa [two_mul, sum_singleton]
  replace h : (s.height i)⁻¹ / ∑ i, (s.height i)⁻¹ < 2⁻¹ := by
    rwa [sum_add_sum_compl, ← lt_inv_mul_iff₀ zero_lt_two, ← div_lt_iff₀ (by positivity)] at h
  convert! h
  simp [excenterWeights, excenterWeightsUnnorm, div_eq_inv_mul]

Depends on / 依赖: add_lt_add_iff_left, compl_singleton, filter_ne, height, inv_height_lt_sum_inv_height, replace, s.height, s.inv_height_lt_sum_inv_height, sum_add_sum_compl, sum_singleton, two_mul, zero_lt_two
-/
lemma excenterWeights_empty_lt_inv_two [n.AtLeastTwo] (i : Fin (n + 1)) :
    s.excenterWeights ∅ i < 2⁻¹ := by
  have h : (s.height i)⁻¹ + (s.height i)⁻¹ < (s.height i)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    have := s.inv_height_lt_sum_inv_height i
    rwa [filter_ne', ← compl_singleton, ← add_lt_add_iff_left (s.height i)⁻¹] at this
  replace h : 2 * (s.height i)⁻¹ < ∑ j in {i}, (s.height j)⁻¹ + ∑ j in {i}ᶜ, (s.height j)⁻¹ := by
    rwa [two_mul, sum_singleton]
  replace h : (s.height i)⁻¹ / ∑ i, (s.height i)⁻¹ < 2⁻¹ := by
    rwa [sum_add_sum_compl, ← lt_inv_mul_iff₀ zero_lt_two, ← div_lt_iff₀ (by positivity)] at h
  convert! h
  simp [excenterWeights, excenterWeightsUnnorm, div_eq_inv_mul]

/--
Definition of `exsphere` / `exsphere` 的定义

English:
definition exsphere
  signature: (signs : Finset (Fin (n + 1)))
  body: Finset.univ.affineCombination Real s.points (s.excenterWeights signs)
  radius := |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|

中文:
定义 exsphere
  签名: (signs : 有限集 (有限集 (n + 1)))
  定义体: Finset.univ.affineCombination Real s.points (s.excenterWeights signs)
  radius := |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|

Depends on / 依赖: Finset, Finset.univ.affineCombination, affineCombination, excenterWeights, points, s.excenterWeights, s.points
-/
def exsphere (signs : Finset (Fin (n + 1))) : Sphere P where
  center := Finset.univ.affineCombination Real s.points (s.excenterWeights signs)
  radius := |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|

/--
lemma `exsphere_reindex` / 引理 `exsphere_reindex`

English:
lemma exsphere_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  simp_rw [exsphere, excenterWeightsUnnorm_reindex, excenterWeights_reindex, Finset.sum_comp_equiv,
    reindex, ← Equiv.coe_toEmbedding, ← Finset.affineCombination_map]
  simp

中文:
引理 exsphere_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  simp_rw [exsphere, excenterWeightsUnnorm_reindex, excenterWeights_reindex, Finset.sum_comp_equiv,
    reindex, ← Equiv.coe_toEmbedding, ← Finset.affineCombination_map]
  simp

Depends on / 依赖: Equiv.coe_toEmbedding, Finset, Finset.affineCombination_map, Finset.sum_comp_equiv, affineCombination_map, coe_toEmbedding, excenterWeightsUnnorm_reindex, excenterWeights_reindex, exsphere, reindex, simp_rw, sum_comp_equiv
-/
lemma exsphere_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).exsphere signs = s.exsphere (signs.map e.symm) := by
  simp_rw [exsphere, excenterWeightsUnnorm_reindex, excenterWeights_reindex, Finset.sum_comp_equiv,
    reindex, ← Equiv.coe_toEmbedding, ← Finset.affineCombination_map]
  simp

/--
Definition of `insphere` / `insphere` 的定义

English:
definition insphere
  signature: : Sphere P
  body: s.exsphere ∅

中文:
定义 insphere
  签名: : 球面 P
  定义体: s.exsphere ∅

Depends on / 依赖: exsphere, s.exsphere
-/
def insphere : Sphere P :=
  s.exsphere ∅

/--
lemma `insphere_reindex` / 引理 `insphere_reindex`

English:
lemma insphere_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  simp_rw [insphere, exsphere_reindex]
  simp

中文:
引理 insphere_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  simp_rw [insphere, exsphere_reindex]
  simp
-/
@[simp] lemma insphere_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).insphere = s.insphere := by
  simp_rw [insphere, exsphere_reindex]
  simp

/--
Definition of `excenter` / `excenter` 的定义

English:
definition excenter
  signature: (signs : Finset (Fin (n + 1)))
  body: (s.exsphere signs).center

中文:
定义 excenter
  签名: (signs : 有限集 (有限集 (n + 1)))
  定义体: (s.exsphere signs).center

Depends on / 依赖: center, exsphere, s.exsphere
-/
def excenter (signs : Finset (Fin (n + 1))) : P :=
  (s.exsphere signs).center

/--
lemma `excenter_reindex` / 引理 `excenter_reindex`

English:
lemma excenter_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  simp_rw [excenter, exsphere_reindex]

中文:
引理 excenter_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  simp_rw [excenter, exsphere_reindex]

Depends on / 依赖: excenter, exsphere_reindex, simp_rw
-/
lemma excenter_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenter signs = s.excenter (signs.map e.symm) := by
  simp_rw [excenter, exsphere_reindex]

variable {s} in
/--
lemma `ExcenterExists.excenter_map` / 引理 `ExcenterExists.excenter_map`

English:
lemma ExcenterExists.excenter_map
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  simp [excenter, exsphere, ← AffineIsometry.coe_toAffineMap, h.sum_excenterWeights_eq_one,
    Finset.map_affineCombination]

中文:
引理 ExcenterExists.excenter_map
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  simp [excenter, exsphere, ← AffineIsometry.coe_toAffineMap, h.sum_excenterWeights_eq_one,
    Finset.map_affineCombination]
-/
@[simp] lemma ExcenterExists.excenter_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).excenter signs = f (s.excenter signs) := by
  simp [excenter, exsphere, ← AffineIsometry.coe_toAffineMap, h.sum_excenterWeights_eq_one,
    Finset.map_affineCombination]

variable {s} in
/--
lemma `ExcenterExists.excenter_restrict` / 引理 `ExcenterExists.excenter_restrict`

English:
lemma ExcenterExists.excenter_restrict
  statement: {signs : Finset (Fin (n + 1))}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenter signs = s.excenter signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.excenter_map S.subtypeₐᵢ).symm

中文:
引理 ExcenterExists.excenter_restrict
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenter signs = s.excenter signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.excenter_map S.subtypeₐᵢ).symm
-/
@[simp] lemma ExcenterExists.excenter_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenter signs = s.excenter signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.excenter_map S.subtypeₐᵢ).symm

/--
Definition of `incenter` / `incenter` 的定义

English:
definition incenter
  signature: : P
  body: (s.exsphere ∅).center

中文:
定义 incenter
  签名: : P
  定义体: (s.exsphere ∅).center

Depends on / 依赖: center, exsphere, s.exsphere
-/
def incenter : P :=
  (s.exsphere ∅).center

/--
lemma `incenter_reindex` / 引理 `incenter_reindex`

English:
lemma incenter_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  simp_rw [incenter, exsphere_reindex]
  simp

中文:
引理 incenter_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  simp_rw [incenter, exsphere_reindex]
  simp
-/
@[simp] lemma incenter_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).incenter = s.incenter := by
  simp_rw [incenter, exsphere_reindex]
  simp

/--
lemma `incenter_map` / 引理 `incenter_map`

English:
lemma incenter_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: s.excenterExists_empty.excenter_map f

中文:
引理 incenter_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: s.excenterExists_empty.excenter_map f
-/
@[simp] lemma incenter_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).incenter = f s.incenter :=
  s.excenterExists_empty.excenter_map f

/--
lemma `incenter_restrict` / 引理 `incenter_restrict`

English:
lemma incenter_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).incenter = s.incenter :=
  s.excenterExists_empty.excenter_restrict S hS

中文:
引理 incenter_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).incenter = s.incenter :=
  s.excenterExists_empty.excenter_restrict S hS
-/
@[simp] lemma incenter_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).incenter = s.incenter :=
  s.excenterExists_empty.excenter_restrict S hS

/--
Definition of `exradius` / `exradius` 的定义

English:
definition exradius
  signature: (signs : Finset (Fin (n + 1)))
  body: (s.exsphere signs).radius

中文:
定义 exradius
  签名: (signs : 有限集 (有限集 (n + 1)))
  定义体: (s.exsphere signs).radius

Depends on / 依赖: exsphere, radius, s.exsphere
-/
def exradius (signs : Finset (Fin (n + 1))) : Real :=
  (s.exsphere signs).radius

/--
lemma `exradius_reindex` / 引理 `exradius_reindex`

English:
lemma exradius_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  simp_rw [exradius, exsphere_reindex]

中文:
引理 exradius_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  simp_rw [exradius, exsphere_reindex]

Depends on / 依赖: exradius, exsphere_reindex, simp_rw
-/
lemma exradius_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).exradius signs = s.exradius (signs.map e.symm) := by
  simp_rw [exradius, exsphere_reindex]

/--
lemma `exradius_map` / 引理 `exradius_map`

English:
lemma exradius_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  ext
  simp [exradius, exsphere]

中文:
引理 exradius_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  ext
  simp [exradius, exsphere]
-/
@[simp] lemma exradius_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]

/--
lemma `exradius_restrict` / 引理 `exradius_restrict`

English:
lemma exradius_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]

中文:
引理 exradius_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]
-/
@[simp] lemma exradius_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]

/--
Definition of `inradius` / `inradius` 的定义

English:
definition inradius
  signature: : Real
  body: (s.exsphere ∅).radius

中文:
定义 inradius
  签名: : 实数
  定义体: (s.exsphere ∅).radius

Depends on / 依赖: exsphere, radius, s.exsphere
-/
def inradius : Real :=
  (s.exsphere ∅).radius

/--
lemma `inradius_reindex` / 引理 `inradius_reindex`

English:
lemma inradius_reindex
  given: (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  simp_rw [inradius, exsphere_reindex]
  simp

中文:
引理 inradius_reindex
  条件: (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  simp_rw [inradius, exsphere_reindex]
  simp
-/
@[simp] lemma inradius_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).inradius = s.inradius := by
  simp_rw [inradius, exsphere_reindex]
  simp

/--
lemma `inradius_map` / 引理 `inradius_map`

English:
lemma inradius_map
  given: (f : P ->ᵃⁱ[Real] P₂)
  proof: congr_fun (s.exradius_map f) _

中文:
引理 inradius_map
  条件: (f : P ->ᵃⁱ[实数] P₂)
  证明: congr_fun (s.exradius_map f) _
-/
@[simp] lemma inradius_map (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).inradius = s.inradius :=
  congr_fun (s.exradius_map f) _

/--
lemma `inradius_restrict` / 引理 `inradius_restrict`

English:
lemma inradius_restrict
  statement: (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).inradius = s.inradius :=
  congr_fun (s.exradius_restrict S hS) _

中文:
引理 inradius_restrict
  结论: (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).inradius = s.inradius :=
  congr_fun (s.exradius_restrict S hS) _
-/
@[simp] lemma inradius_restrict (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).inradius = s.inradius :=
  congr_fun (s.exradius_restrict S hS) _

/--
lemma `exsphere_center` / 引理 `exsphere_center`

English:
lemma exsphere_center
  given: (signs : Finset (Fin (n + 1)))
  proof: rfl

中文:
引理 exsphere_center
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: rfl
-/
@[simp] lemma exsphere_center (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).center = s.excenter signs :=
  rfl

/--
lemma `exsphere_radius` / 引理 `exsphere_radius`

English:
lemma exsphere_radius
  given: (signs : Finset (Fin (n + 1)))
  proof: rfl

中文:
引理 exsphere_radius
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: rfl
-/
@[simp] lemma exsphere_radius (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).radius = s.exradius signs :=
  rfl

/--
lemma `insphere_center` / 引理 `insphere_center`

English:
lemma insphere_center
  statement: s.insphere.center = s.incenter
  proof: rfl

中文:
引理 insphere_center
  结论: s.insphere.center = s.incenter
  证明: rfl
-/
@[simp] lemma insphere_center : s.insphere.center = s.incenter :=
  rfl

/--
lemma `insphere_radius` / 引理 `insphere_radius`

English:
lemma insphere_radius
  statement: s.insphere.radius = s.inradius
  proof: rfl

中文:
引理 insphere_radius
  结论: s.insphere.radius = s.inradius
  证明: rfl
-/
@[simp] lemma insphere_radius : s.insphere.radius = s.inradius :=
  rfl

/--
lemma `exsphere_empty` / 引理 `exsphere_empty`

English:
lemma exsphere_empty
  statement: s.exsphere ∅ = s.insphere
  proof: rfl

中文:
引理 exsphere_empty
  结论: s.exsphere ∅ = s.insphere
  证明: rfl
-/
@[simp] lemma exsphere_empty : s.exsphere ∅ = s.insphere :=
  rfl

/--
lemma `excenter_empty` / 引理 `excenter_empty`

English:
lemma excenter_empty
  statement: s.excenter ∅ = s.incenter
  proof: rfl

中文:
引理 excenter_empty
  结论: s.excenter ∅ = s.incenter
  证明: rfl
-/
@[simp] lemma excenter_empty : s.excenter ∅ = s.incenter :=
  rfl

/--
lemma `exradius_empty` / 引理 `exradius_empty`

English:
lemma exradius_empty
  statement: s.exradius ∅ = s.inradius
  proof: rfl

中文:
引理 exradius_empty
  结论: s.exradius ∅ = s.inradius
  证明: rfl
-/
@[simp] lemma exradius_empty : s.exradius ∅ = s.inradius :=
  rfl

/--
lemma `exsphere_compl` / 引理 `exsphere_compl`

English:
lemma exsphere_compl
  given: (signs : Finset (Fin (n + 1)))
  proof: by
  simp [exsphere, excenterWeights_compl, excenterWeightsUnnorm_compl, Pi.neg_apply]

中文:
引理 exsphere_compl
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: by
  simp [exsphere, excenterWeights_compl, excenterWeightsUnnorm_compl, Pi.neg_apply]
-/
@[simp] lemma exsphere_compl (signs : Finset (Fin (n + 1))) :
    s.exsphere signsᶜ = s.exsphere signs := by
  simp [exsphere, excenterWeights_compl, excenterWeightsUnnorm_compl, Pi.neg_apply]

/--
lemma `excenter_compl` / 引理 `excenter_compl`

English:
lemma excenter_compl
  given: (signs : Finset (Fin (n + 1)))
  proof: by
  simp_rw [excenter, exsphere_compl]

中文:
引理 excenter_compl
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: by
  simp_rw [excenter, exsphere_compl]
-/
@[simp] lemma excenter_compl (signs : Finset (Fin (n + 1))) :
    s.excenter signsᶜ = s.excenter signs := by
  simp_rw [excenter, exsphere_compl]

/--
lemma `exradius_compl` / 引理 `exradius_compl`

English:
lemma exradius_compl
  given: (signs : Finset (Fin (n + 1)))
  proof: by
  simp_rw [exradius, exsphere_compl]

中文:
引理 exradius_compl
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: by
  simp_rw [exradius, exsphere_compl]
-/
@[simp] lemma exradius_compl (signs : Finset (Fin (n + 1))) :
    s.exradius signsᶜ = s.exradius signs := by
  simp_rw [exradius, exsphere_compl]

/--
lemma `exsphere_univ` / 引理 `exsphere_univ`

English:
lemma exsphere_univ
  statement: s.exsphere Finset.univ = s.insphere
  proof: by
  rw [← Finset.compl_empty]; rw [exsphere_compl]; rw [insphere]

中文:
引理 exsphere_univ
  结论: s.exsphere 有限集.univ = s.insphere
  证明: by
  rw [← Finset.compl_empty]; rw [exsphere_compl]; rw [insphere]
-/
@[simp] lemma exsphere_univ : s.exsphere Finset.univ = s.insphere := by
  rw [← Finset.compl_empty]; rw [exsphere_compl]; rw [insphere]

/--
lemma `excenter_univ` / 引理 `excenter_univ`

English:
lemma excenter_univ
  statement: s.excenter Finset.univ = s.incenter
  proof: by
  rw [excenter]; rw [exsphere_univ]; rw [insphere_center]

中文:
引理 excenter_univ
  结论: s.excenter 有限集.univ = s.incenter
  证明: by
  rw [excenter]; rw [exsphere_univ]; rw [insphere_center]

Depends on / 依赖: Set.nonempty_compl_of_nontrivial, nonempty_compl_of_nontrivial, to_subtype
-/
@[simp] lemma excenter_univ : s.excenter Finset.univ = s.incenter := by
  rw [excenter]; rw [exsphere_univ]; rw [insphere_center]

/--
lemma `exradius_univ` / 引理 `exradius_univ`

English:
lemma exradius_univ
  statement: s.exradius Finset.univ = s.inradius
  proof: by
  rw [exradius]; rw [exsphere_univ]; rw [insphere_radius]

中文:
引理 exradius_univ
  结论: s.exradius 有限集.univ = s.inradius
  证明: by
  rw [exradius]; rw [exsphere_univ]; rw [insphere_radius]
-/
@[simp] lemma exradius_univ : s.exradius Finset.univ = s.inradius := by
  rw [exradius]; rw [exsphere_univ]; rw [insphere_radius]

/--
lemma `excenter_eq_affineCombination` / 引理 `excenter_eq_affineCombination`

English:
lemma excenter_eq_affineCombination
  given: (signs : Finset (Fin (n + 1)))
  proof: rfl

中文:
引理 excenter_eq_affineCombination
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: rfl
-/
lemma excenter_eq_affineCombination (signs : Finset (Fin (n + 1))) :
    s.excenter signs = Finset.univ.affineCombination Real s.points (s.excenterWeights signs) :=
  rfl

/--
lemma `exradius_eq_abs_inv_sum` / 引理 `exradius_eq_abs_inv_sum`

English:
lemma exradius_eq_abs_inv_sum
  given: (signs : Finset (Fin (n + 1)))
  proof: rfl

中文:
引理 exradius_eq_abs_inv_sum
  条件: (signs : 有限集 (有限集 (n + 1)))
  证明: rfl
-/
lemma exradius_eq_abs_inv_sum (signs : Finset (Fin (n + 1))) :
    s.exradius signs = |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹| :=
  rfl

/--
lemma `incenter_eq_affineCombination` / 引理 `incenter_eq_affineCombination`

English:
lemma incenter_eq_affineCombination
  proof: rfl

中文:
引理 incenter_eq_affineCombination
  证明: rfl
-/
lemma incenter_eq_affineCombination :
    s.incenter = Finset.univ.affineCombination Real s.points (s.excenterWeights ∅) :=
  rfl

/--
lemma `inradius_eq_abs_inv_sum` / 引理 `inradius_eq_abs_inv_sum`

English:
lemma inradius_eq_abs_inv_sum
  statement: s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹|
  proof: rfl

中文:
引理 inradius_eq_abs_inv_sum
  结论: s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹|
  证明: rfl
-/
lemma inradius_eq_abs_inv_sum : s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹| :=
  rfl

/--
lemma `exradius_nonneg` / 引理 `exradius_nonneg`

English:
lemma exradius_nonneg
  given: (signs : Finset (Fin (n + 1)))
  statement: 0 <= s.exradius signs
  proof: abs_nonneg _

中文:
引理 exradius_nonneg
  条件: (signs : 有限集 (有限集 (n + 1)))
  结论: 0 <= s.exradius signs
  证明: abs_nonneg _

Depends on / 依赖: abs_nonneg
-/
lemma exradius_nonneg (signs : Finset (Fin (n + 1))) : 0 <= s.exradius signs :=
  abs_nonneg _

variable {s} in
/--
lemma `ExcenterExists.exradius_pos` / 引理 `ExcenterExists.exradius_pos`

English:
lemma ExcenterExists.exradius_pos
  given: {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
  proof: abs_pos.2 (inv_ne_zero h)

中文:
引理 ExcenterExists.exradius_pos
  条件: {signs : 有限集 (有限集 (n + 1))} (h : s.ExcenterExists signs)
  证明: abs_pos.2 (inv_ne_zero h)

Depends on / 依赖: abs_pos, inv_ne_zero
-/
lemma ExcenterExists.exradius_pos {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) :
    0 < s.exradius signs :=
  abs_pos.2 (inv_ne_zero h)

/--
lemma `inradius_pos` / 引理 `inradius_pos`

English:
lemma inradius_pos
  statement: 0 < s.inradius
  proof: s.excenterExists_empty.exradius_pos

中文:
引理 inradius_pos
  结论: 0 < s.inradius
  证明: s.excenterExists_empty.exradius_pos

Depends on / 依赖: excenterExists_empty, exradius_pos, s.excenterExists_empty.exradius_pos
-/
lemma inradius_pos : 0 < s.inradius :=
  s.excenterExists_empty.exradius_pos

/--
lemma `exradius_singleton_pos` / 引理 `exradius_singleton_pos`

English:
lemma exradius_singleton_pos
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  statement: 0 < s.exradius {i}
  proof: (s.excenterExists_singleton i).exradius_pos

中文:
引理 exradius_singleton_pos
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  结论: 0 < s.exradius {i}
  证明: (s.excenterExists_singleton i).exradius_pos

Depends on / 依赖: excenterExists_singleton, exradius_pos, s.excenterExists_singleton
-/
lemma exradius_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < s.exradius {i} :=
  (s.excenterExists_singleton i).exradius_pos

variable {s} in
/--
lemma `ExcenterExists.excenter_mem_affineSpan_range` / 引理 `ExcenterExists.excenter_mem_affineSpan_range`

English:
lemma ExcenterExists.excenter_mem_affineSpan_range
  statement: {signs : Finset (Fin (n + 1))}
  proof: affineCombination_mem_affineSpan h.sum_excenterWeights_eq_one _

中文:
引理 ExcenterExists.excenter_mem_affineSpan_range
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: affineCombination_mem_affineSpan h.sum_excenterWeights_eq_one _

Depends on / 依赖: affineCombination_mem_affineSpan, h.sum_excenterWeights_eq_one, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.excenter_mem_affineSpan_range {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) : s.excenter signs in affineSpan Real (Set.range s.points) :=
  affineCombination_mem_affineSpan h.sum_excenterWeights_eq_one _

/--
lemma `incenter_mem_affineSpan_range` / 引理 `incenter_mem_affineSpan_range`

English:
lemma incenter_mem_affineSpan_range
  statement: s.incenter in affineSpan Real (Set.range s.points)
  proof: s.excenterExists_empty.excenter_mem_affineSpan_range

中文:
引理 incenter_mem_affineSpan_range
  结论: s.incenter in affineSpan 实数 (集合.range s.points)
  证明: s.excenterExists_empty.excenter_mem_affineSpan_range

Depends on / 依赖: excenterExists_empty, excenter_mem_affineSpan_range, s.excenterExists_empty.excenter_mem_affineSpan_range
-/
lemma incenter_mem_affineSpan_range : s.incenter in affineSpan Real (Set.range s.points) :=
  s.excenterExists_empty.excenter_mem_affineSpan_range

/--
lemma `incenter_mem_interior` / 引理 `incenter_mem_interior`

English:
lemma incenter_mem_interior
  statement: s.incenter in s.interior
  proof: by
  have h := s.excenterExists_empty.sum_excenterWeights_eq_one
  rw [incenter_eq_affineCombination]; rw [s.affineCombination_mem_interior_iff h]
  intro i
  refine ⟨s.excenterWeights_empty_pos i, ?_⟩
  by_contra! hp
  obtain ⟨j, hj⟩ := exists_ne i
  rw [← Finset.sum_add_sum_compl {j]; rw [i}]; rw [Finset.sum_pair hj] at h
  revert h
  apply ne_of_gt
  nth_rw 2 [add_comm]
  grw [hp]
  rw [add_assoc]; rw [lt_add_iff_pos_right]
  exact add_pos_of_pos_of_nonneg (s.excenterWeights_empty_pos j)
    (Finset.sum_nonneg fun k _ => (s.excenterWeights_empty_pos k).le)

中文:
引理 incenter_mem_interior
  结论: s.incenter in s.interior
  证明: by
  have h := s.excenterExists_empty.sum_excenterWeights_eq_one
  rw [incenter_eq_affineCombination]; rw [s.affineCombination_mem_interior_iff h]
  intro i
  refine ⟨s.excenterWeights_empty_pos i, ?_⟩
  by_contra! hp
  obtain ⟨j, hj⟩ := exists_ne i
  rw [← Finset.sum_add_sum_compl {j]; rw [i}]; rw [Finset.sum_pair hj] at h
  revert h
  apply ne_of_gt
  nth_rw 2 [add_comm]
  grw [hp]
  rw [add_assoc]; rw [lt_add_iff_pos_right]
  exact add_pos_of_pos_of_nonneg (s.excenterWeights_empty_pos j)
    (Finset.sum_nonneg fun k _ => (s.excenterWeights_empty_pos k).le)

Depends on / 依赖: Finset, Finset.sum_add_sum_compl, Finset.sum_nonneg, Finset.sum_pair, add_assoc, add_comm, add_pos_of_pos_of_nonneg, affineCombination_mem_interior_iff, excenterExists_empty, excenterWeights_empty_pos, exists_ne, incenter_eq_affineCombination, lt_add_iff_pos_right, ne_of_gt, nth_rw, revert, s.affineCombination_mem_interior_iff, s.excenterExists_empty.sum_excenterWeights_eq_one, s.excenterWeights_empty_pos, sum_add_sum_compl
-/
lemma incenter_mem_interior : s.incenter in s.interior := by
  have h := s.excenterExists_empty.sum_excenterWeights_eq_one
  rw [incenter_eq_affineCombination]; rw [s.affineCombination_mem_interior_iff h]
  intro i
  refine ⟨s.excenterWeights_empty_pos i, ?_⟩
  by_contra! hp
  obtain ⟨j, hj⟩ := exists_ne i
  rw [← Finset.sum_add_sum_compl {j]; rw [i}]; rw [Finset.sum_pair hj] at h
  revert h
  apply ne_of_gt
  nth_rw 2 [add_comm]
  grw [hp]
  rw [add_assoc]; rw [lt_add_iff_pos_right]
  exact add_pos_of_pos_of_nonneg (s.excenterWeights_empty_pos j)
    (Finset.sum_nonneg fun k _ => (s.excenterWeights_empty_pos k).le)

/--
lemma `excenter_singleton_mem_affineSpan_range` / 引理 `excenter_singleton_mem_affineSpan_range`

English:
lemma excenter_singleton_mem_affineSpan_range
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: (s.excenterExists_singleton i).excenter_mem_affineSpan_range

中文:
引理 excenter_singleton_mem_affineSpan_range
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: (s.excenterExists_singleton i).excenter_mem_affineSpan_range

Depends on / 依赖: excenterExists_singleton, excenter_mem_affineSpan_range, s.excenterExists_singleton
-/
lemma excenter_singleton_mem_affineSpan_range [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.excenter {i} in affineSpan Real (Set.range s.points) :=
  (s.excenterExists_singleton i).excenter_mem_affineSpan_range

variable {s} in
/--
lemma `ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv` / 引理 `ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv`

English:
lemma ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  simp_rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, excenterWeights,
    Pi.smul_apply, ← dist_eq_norm_vsub, excenterWeightsUnnorm]
  rw [← altitudeFoot]; rw [← height]
  simp [(s.height_pos i).ne']

中文:
引理 ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  simp_rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, excenterWeights,
    Pi.smul_apply, ← dist_eq_norm_vsub, excenterWeightsUnnorm]
  rw [← altitudeFoot]; rw [← height]
  simp [(s.height_pos i).ne']

Depends on / 依赖: Pi.smul_apply, altitudeFoot, dist_eq_norm_vsub, excenterWeights, excenterWeightsUnnorm, excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, height, height_pos, s.height_pos, signedInfDist_affineCombination, simp_rw, smul_apply, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) =
      (if i in signs then -1 else 1) * (∑ j, s.excenterWeightsUnnorm signs j)⁻¹ := by
  simp_rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, excenterWeights,
    Pi.smul_apply, ← dist_eq_norm_vsub, excenterWeightsUnnorm]
  rw [← altitudeFoot]; rw [← height]
  simp [(s.height_pos i).ne']

variable {s} in
/--
lemma `ExcenterExists.sign_signedInfDist_excenter` / 引理 `ExcenterExists.sign_signedInfDist_excenter`

English:
lemma ExcenterExists.sign_signedInfDist_excenter
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one]; rw [sign_mul]
  convert! mul_one _
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

中文:
引理 ExcenterExists.sign_signedInfDist_excenter
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one]; rw [sign_mul]
  convert! mul_one _
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

Depends on / 依赖: convert, dist_eq_norm_vsub, excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, height_pos, mul_one, s.height_pos, sign_eq_one_iff, sign_mul, signedInfDist_affineCombination, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.sign_signedInfDist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    SignType.sign (s.signedInfDist i (s.excenter signs)) =
      SignType.sign (s.excenterWeights signs i) := by
  rw [excenter_eq_affineCombination]; rw [signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one]; rw [sign_mul]
  convert! mul_one _
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

/--
lemma `sign_signedInfDist_incenter` / 引理 `sign_signedInfDist_incenter`

English:
lemma sign_signedInfDist_incenter
  given: (i : Fin (n + 1))
  proof: by
  convert! s.excenterExists_empty.sign_signedInfDist_excenter i
  simp

中文:
引理 sign_signedInfDist_incenter
  条件: (i : 有限集 (n + 1))
  证明: by
  convert! s.excenterExists_empty.sign_signedInfDist_excenter i
  simp

Depends on / 依赖: convert, excenterExists_empty, s.excenterExists_empty.sign_signedInfDist_excenter, sign_signedInfDist_excenter
-/
lemma sign_signedInfDist_incenter (i : Fin (n + 1)) :
    SignType.sign (s.signedInfDist i s.incenter) = 1 := by
  convert! s.excenterExists_empty.sign_signedInfDist_excenter i
  simp

variable {s} in
/--
lemma `ExcenterExists.affineCombination_eq_excenter_iff` / 引理 `ExcenterExists.affineCombination_eq_excenter_iff`

English:
lemma ExcenterExists.affineCombination_eq_excenter_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  constructor
  · simp_rw [excenter, exsphere]
    exact fun he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw h.sum_excenterWeights_eq_one he
  · rintro rfl
    rw [excenter]; rw [exsphere]

中文:
引理 ExcenterExists.affineCombination_eq_excenter_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  constructor
  · simp_rw [excenter, exsphere]
    exact fun he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw h.sum_excenterWeights_eq_one he
  · rintro rfl
    rw [excenter]; rw [exsphere]

Depends on / 依赖: affineIndependent_iff_eq_of_fintype_affineCombination_eq, excenter, exsphere, h.sum_excenterWeights_eq_one, independent, points, s.independent, s.points, simp_rw, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.affineCombination_eq_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {w : Fin (n + 1) -> Real} (hw : ∑ j, w j = 1) :
    Finset.univ.affineCombination Real s.points w = s.excenter signs ↔
      w = s.excenterWeights signs := by
  constructor
  · simp_rw [excenter, exsphere]
    exact fun he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw h.sum_excenterWeights_eq_one he
  · rintro rfl
    rw [excenter]; rw [exsphere]

variable {s} in
/--
lemma `ExcenterExists.excenter_notMem_affineSpan_face` / 引理 `ExcenterExists.excenter_notMem_affineSpan_face`

English:
lemma ExcenterExists.excenter_notMem_affineSpan_face
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  intro hm
  rw [range_face_points] at hm
  obtain ⟨i, hi⟩ : exists i, i ∉ (fs : Set (Fin (n + 1))) := by
    simp only [SetLike.mem_coe]
    have hc : #fs < #(Finset.univ : Finset (Fin (n + 1))) := by
      have : m + 1 <= #fs := hfs.ge
      grw [fs.subset_univ] at this
      simp only [Finset.card_univ, Fintype.card_fin] at *
      lia
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨i, hi⟩
  rw [excenter_eq_affineCombination] at hm
  exact h.excenterWeights_ne_zero i (s.independent.eq_zero_of_affineCombination_mem_affineSpan
    h.sum_excenterWeights_eq_one hm (Finset.mem_univ i) hi)

中文:
引理 ExcenterExists.excenter_notMem_affineSpan_face
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  intro hm
  rw [range_face_points] at hm
  obtain ⟨i, hi⟩ : exists i, i ∉ (fs : Set (Fin (n + 1))) := by
    simp only [SetLike.mem_coe]
    have hc : #fs < #(Finset.univ : Finset (Fin (n + 1))) := by
      have : m + 1 <= #fs := hfs.ge
      grw [fs.subset_univ] at this
      simp only [Finset.card_univ, Fintype.card_fin] at *
      lia
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨i, hi⟩
  rw [excenter_eq_affineCombination] at hm
  exact h.excenterWeights_ne_zero i (s.independent.eq_zero_of_affineCombination_mem_affineSpan
    h.sum_excenterWeights_eq_one hm (Finset.mem_univ i) hi)

Depends on / 依赖: Finset, Finset.card_univ, Finset.exists_mem_notMem_of_card_lt_card, Finset.univ, Fintype, Fintype.card_fin, SetLike, SetLike.mem_coe, card_fin, card_univ, eq_zero_of_affineCombinat, excenterWeights_ne_zero, excenter_eq_affineCombination, exists_mem_notMem_of_card_lt_card, fs.subset_univ, h.excenterWeights_ne_zero, hfs.ge, independent, mem_coe, range_face_points
-/
lemma ExcenterExists.excenter_notMem_affineSpan_face {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {fs : Finset (Fin (n + 1))} {m : Nat} (hfs : #fs = m + 1)
    (hne : m != n) : s.excenter signs ∉ affineSpan Real (Set.range (s.face hfs).points) := by
  intro hm
  rw [range_face_points] at hm
  obtain ⟨i, hi⟩ : exists i, i ∉ (fs : Set (Fin (n + 1))) := by
    simp only [SetLike.mem_coe]
    have hc : #fs < #(Finset.univ : Finset (Fin (n + 1))) := by
      have : m + 1 <= #fs := hfs.ge
      grw [fs.subset_univ] at this
      simp only [Finset.card_univ, Fintype.card_fin] at *
      lia
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨i, hi⟩
  rw [excenter_eq_affineCombination] at hm
  exact h.excenterWeights_ne_zero i (s.independent.eq_zero_of_affineCombination_mem_affineSpan
    h.sum_excenterWeights_eq_one hm (Finset.mem_univ i) hi)

/--
lemma `incenter_notMem_affineSpan_face` / 引理 `incenter_notMem_affineSpan_face`

English:
lemma incenter_notMem_affineSpan_face
  statement: {fs : Finset (Fin (n + 1))} {m : Nat} (hfs : #fs = m + 1)
  proof: s.excenterExists_empty.excenter_notMem_affineSpan_face hfs hne

中文:
引理 incenter_notMem_affineSpan_face
  结论: {fs : 有限集 (有限集 (n + 1))} {m : 自然数} (hfs : #fs = m + 1)
  证明: s.excenterExists_empty.excenter_notMem_affineSpan_face hfs hne

Depends on / 依赖: excenterExists_empty, excenter_notMem_affineSpan_face, s.excenterExists_empty.excenter_notMem_affineSpan_face
-/
lemma incenter_notMem_affineSpan_face {fs : Finset (Fin (n + 1))} {m : Nat} (hfs : #fs = m + 1)
    (hne : m != n) : s.incenter ∉ affineSpan Real (Set.range (s.face hfs).points) :=
  s.excenterExists_empty.excenter_notMem_affineSpan_face hfs hne

variable {s} in
/--
lemma `ExcenterExists.excenter_notMem_affineSpan_faceOpposite` / 引理 `ExcenterExists.excenter_notMem_affineSpan_faceOpposite`

English:
lemma ExcenterExists.excenter_notMem_affineSpan_faceOpposite
  statement: {signs : Finset (Fin (n + 1))}
  proof: h.excenter_notMem_affineSpan_face _ (by have := NeZero.ne n; lia)

中文:
引理 ExcenterExists.excenter_notMem_affineSpan_faceOpposite
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: h.excenter_notMem_affineSpan_face _ (by have := NeZero.ne n; lia)

Depends on / 依赖: NeZero, NeZero.ne, excenter_notMem_affineSpan_face, h.excenter_notMem_affineSpan_face
-/
lemma ExcenterExists.excenter_notMem_affineSpan_faceOpposite {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.excenter signs ∉ affineSpan Real (Set.range (s.faceOpposite i).points) :=
  h.excenter_notMem_affineSpan_face _ (by have := NeZero.ne n; lia)

/--
lemma `incenter_notMem_affineSpan_faceOpposite` / 引理 `incenter_notMem_affineSpan_faceOpposite`

English:
lemma incenter_notMem_affineSpan_faceOpposite
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.excenter_notMem_affineSpan_faceOpposite i

中文:
引理 incenter_notMem_affineSpan_faceOpposite
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.excenter_notMem_affineSpan_faceOpposite i

Depends on / 依赖: excenterExists_empty, excenter_notMem_affineSpan_faceOpposite, s.excenterExists_empty.excenter_notMem_affineSpan_faceOpposite
-/
lemma incenter_notMem_affineSpan_faceOpposite (i : Fin (n + 1)) :
    s.incenter ∉ affineSpan Real (Set.range (s.faceOpposite i).points) :=
  s.excenterExists_empty.excenter_notMem_affineSpan_faceOpposite i

variable {s} in
/--
lemma `ExcenterExists.excenter_ne_point` / 引理 `ExcenterExists.excenter_ne_point`

English:
lemma ExcenterExists.excenter_ne_point
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  have hf := h.excenter_notMem_affineSpan_face (fs := {i}) (m := 0) (by simp) (NeZero.ne' _)
  simpa using hf

中文:
引理 ExcenterExists.excenter_ne_point
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  have hf := h.excenter_notMem_affineSpan_face (fs := {i}) (m := 0) (by simp) (NeZero.ne' _)
  simpa using hf

Depends on / 依赖: NeZero, NeZero.ne, excenter_notMem_affineSpan_face, h.excenter_notMem_affineSpan_face
-/
lemma ExcenterExists.excenter_ne_point {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.excenter signs != s.points i := by
  have hf := h.excenter_notMem_affineSpan_face (fs := {i}) (m := 0) (by simp) (NeZero.ne' _)
  simpa using hf

/--
lemma `incenter_ne_point` / 引理 `incenter_ne_point`

English:
lemma incenter_ne_point
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.excenter_ne_point i

中文:
引理 incenter_ne_point
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.excenter_ne_point i

Depends on / 依赖: excenterExists_empty, excenter_ne_point, s.excenterExists_empty.excenter_ne_point
-/
lemma incenter_ne_point (i : Fin (n + 1)) :
    s.incenter != s.points i :=
  s.excenterExists_empty.excenter_ne_point i

variable {s} in
/--
lemma `ExcenterExists.excenter_notMem_affineSpan_pair` / 引理 `ExcenterExists.excenter_notMem_affineSpan_pair`

English:
lemma ExcenterExists.excenter_notMem_affineSpan_pair
  statement: [Nat.AtLeastTwo n]
  proof: by
  by_cases hij : i = j
  · simp only [hij, Set.mem_singleton_iff, Set.insert_eq_of_mem,
      AffineSubspace.mem_affineSpan_singleton]
    exact h.excenter_ne_point j
  · convert!
    h.excenter_notMem_affineSpan_face (fs := { i, j }) (m := 1) (by simp_all)
      Nat.AtLeastTwo.ne_one.symm
    simp [Set.image_insert_eq]

中文:
引理 ExcenterExists.excenter_notMem_affineSpan_pair
  结论: [自然数.AtLeastTwo n]
  证明: by
  by_cases hij : i = j
  · simp only [hij, Set.mem_singleton_iff, Set.insert_eq_of_mem,
      AffineSubspace.mem_affineSpan_singleton]
    exact h.excenter_ne_point j
  · convert!
    h.excenter_notMem_affineSpan_face (fs := { i, j }) (m := 1) (by simp_all)
      Nat.AtLeastTwo.ne_one.symm
    simp [Set.image_insert_eq]

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_affineSpan_singleton, AtLeastTwo, Nat.AtLeastTwo.ne_one.symm, Set.image_insert_eq, Set.insert_eq_of_mem, Set.mem_singleton_iff, convert, excenter_ne_point, excenter_notMem_affineSpan_face, h.excenter_ne_point, h.excenter_notMem_affineSpan_face, image_insert_eq, insert_eq_of_mem, mem_affineSpan_singleton, mem_singleton_iff, ne_one
-/
lemma ExcenterExists.excenter_notMem_affineSpan_pair [Nat.AtLeastTwo n]
    {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) (i j : Fin (n + 1)) :
    s.excenter signs ∉ line[Real, s.points i, s.points j] := by
  by_cases hij : i = j
  · simp only [hij, Set.mem_singleton_iff, Set.insert_eq_of_mem,
      AffineSubspace.mem_affineSpan_singleton]
    exact h.excenter_ne_point j
  · convert!
    h.excenter_notMem_affineSpan_face (fs := { i, j }) (m := 1) (by simp_all)
      Nat.AtLeastTwo.ne_one.symm
    simp [Set.image_insert_eq]

/--
lemma `incenter_notMem_affineSpan_pair` / 引理 `incenter_notMem_affineSpan_pair`

English:
lemma incenter_notMem_affineSpan_pair
  given: [Nat.AtLeastTwo n] (i j : Fin (n + 1))
  proof: s.excenterExists_empty.excenter_notMem_affineSpan_pair i j

中文:
引理 incenter_notMem_affineSpan_pair
  条件: [自然数.AtLeastTwo n] (i j : 有限集 (n + 1))
  证明: s.excenterExists_empty.excenter_notMem_affineSpan_pair i j

Depends on / 依赖: excenterExists_empty, excenter_notMem_affineSpan_pair, s.excenterExists_empty.excenter_notMem_affineSpan_pair
-/
lemma incenter_notMem_affineSpan_pair [Nat.AtLeastTwo n] (i j : Fin (n + 1)) :
    s.incenter ∉ line[Real, s.points i, s.points j] :=
  s.excenterExists_empty.excenter_notMem_affineSpan_pair i j

variable {s} in
/--
lemma `ExcenterExists.excenterWeights_eq_excenterWeights_iff` / 引理 `ExcenterExists.excenterWeights_eq_excenterWeights_iff`

English:
lemma ExcenterExists.excenterWeights_eq_excenterWeights_iff
  statement: {signs₁ signs₂ : Finset (Fin (n + 1))}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hi : forall i, SignType.sign (s.excenterWeights signs₁ i) =
        SignType.sign (s.excenterWeights signs₂ i) := by
      simp [h]
    simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul] at hi
    have hn₁ : ∑ i, s.excenterWeightsUnnorm signs₁ i != 0 := h₁
    have hn₂ : ∑ i, s.excenterWeightsUnnorm signs₂ i != 0 := h₂
    rcases sign_eq_sign_or_eq_neg (inv_ne_zero hn₁) (inv_ne_zero hn₂) with hs | hs
    · simp only [hs, mul_eq_mul_left_iff, sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      left
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
    · simp_rw [hs, neg_mul, ← mul_neg, mul_eq_mul_left_iff] at hi
      simp only [sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      right
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
  · rcases h with rfl | rfl
    · rfl
    · simp

中文:
引理 ExcenterExists.excenterWeights_eq_excenterWeights_iff
  结论: {signs₁ signs₂ : 有限集 (有限集 (n + 1))}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hi : forall i, SignType.sign (s.excenterWeights signs₁ i) =
        SignType.sign (s.excenterWeights signs₂ i) := by
      simp [h]
    simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul] at hi
    have hn₁ : ∑ i, s.excenterWeightsUnnorm signs₁ i != 0 := h₁
    have hn₂ : ∑ i, s.excenterWeightsUnnorm signs₂ i != 0 := h₂
    rcases sign_eq_sign_or_eq_neg (inv_ne_zero hn₁) (inv_ne_zero hn₂) with hs | hs
    · simp only [hs, mul_eq_mul_left_iff, sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      left
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
    · simp_rw [hs, neg_mul, ← mul_neg, mul_eq_mul_left_iff] at hi
      simp only [sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      right
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
  · rcases h with rfl | rfl
    · rfl
    · simp

Depends on / 依赖: Pi.smul_apply, SignType, SignType.sign, excenterWeights, excenterWeightsUnnorm, inv_eq_zero, inv_ne_zero, mul_eq_mul_left_iff, s.excenterWeights, s.excenterWeightsUnnorm, sign_eq_sign_or_eq_neg, sign_eq_zero_iff, sign_mul, simp_rw, smul_apply, smul_eq_mul
-/
lemma ExcenterExists.excenterWeights_eq_excenterWeights_iff {signs₁ signs₂ : Finset (Fin (n + 1))}
    (h₁ : s.ExcenterExists signs₁) (h₂ : s.ExcenterExists signs₂) :
    s.excenterWeights signs₁ = s.excenterWeights signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = signs₂ᶜ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hi : forall i, SignType.sign (s.excenterWeights signs₁ i) =
        SignType.sign (s.excenterWeights signs₂ i) := by
      simp [h]
    simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul] at hi
    have hn₁ : ∑ i, s.excenterWeightsUnnorm signs₁ i != 0 := h₁
    have hn₂ : ∑ i, s.excenterWeightsUnnorm signs₂ i != 0 := h₂
    rcases sign_eq_sign_or_eq_neg (inv_ne_zero hn₁) (inv_ne_zero hn₂) with hs | hs
    · simp only [hs, mul_eq_mul_left_iff, sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      left
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
    · simp_rw [hs, neg_mul, ← mul_neg, mul_eq_mul_left_iff] at hi
      simp only [sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      right
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
  · rcases h with rfl | rfl
    · rfl
    · simp

variable {s} in
/--
lemma `ExcenterExists.excenter_eq_excenter_iff` / 引理 `ExcenterExists.excenter_eq_excenter_iff`

English:
lemma ExcenterExists.excenter_eq_excenter_iff
  statement: {signs₁ signs₂ : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [h₂.affineCombination_eq_excenter_iff (s.sum_excenterWeights_eq_one_iff.2 h₁)]
  exact h₁.excenterWeights_eq_excenterWeights_iff h₂

中文:
引理 ExcenterExists.excenter_eq_excenter_iff
  结论: {signs₁ signs₂ : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [h₂.affineCombination_eq_excenter_iff (s.sum_excenterWeights_eq_one_iff.2 h₁)]
  exact h₁.excenterWeights_eq_excenterWeights_iff h₂

Depends on / 依赖: affineCombination_eq_excenter_iff, excenterWeights_eq_excenterWeights_iff, excenter_eq_affineCombination, s.sum_excenterWeights_eq_one_iff, sum_excenterWeights_eq_one_iff
-/
lemma ExcenterExists.excenter_eq_excenter_iff {signs₁ signs₂ : Finset (Fin (n + 1))}
    (h₁ : s.ExcenterExists signs₁) (h₂ : s.ExcenterExists signs₂) :
    s.excenter signs₁ = s.excenter signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = signs₂ᶜ := by
  rw [excenter_eq_affineCombination]; rw [h₂.affineCombination_eq_excenter_iff (s.sum_excenterWeights_eq_one_iff.2 h₁)]
  exact h₁.excenterWeights_eq_excenterWeights_iff h₂

variable {s} in
/--
lemma `ExcenterExists.excenter_eq_incenter_iff` / 引理 `ExcenterExists.excenter_eq_incenter_iff`

English:
lemma ExcenterExists.excenter_eq_incenter_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [incenter]; rw [← excenter]; rw [h.excenter_eq_excenter_iff s.excenterExists_empty]
  simp

中文:
引理 ExcenterExists.excenter_eq_incenter_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [incenter]; rw [← excenter]; rw [h.excenter_eq_excenter_iff s.excenterExists_empty]
  simp

Depends on / 依赖: excenter, excenterExists_empty, excenter_eq_excenter_iff, h.excenter_eq_excenter_iff, incenter, s.excenterExists_empty
-/
lemma ExcenterExists.excenter_eq_incenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) :
    s.excenter signs = s.incenter ↔ signs = ∅ ∨ signs = Finset.univ := by
  rw [incenter]; rw [← excenter]; rw [h.excenter_eq_excenter_iff s.excenterExists_empty]
  simp

/--
lemma `excenter_singleton_ne_incenter` / 引理 `excenter_singleton_ne_incenter`

English:
lemma excenter_singleton_ne_incenter
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  intro h
  rw [(s.excenterExists_singleton i).excenter_eq_incenter_iff] at h
  simp at h

中文:
引理 excenter_singleton_ne_incenter
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  intro h
  rw [(s.excenterExists_singleton i).excenter_eq_incenter_iff] at h
  simp at h

Depends on / 依赖: excenterExists_singleton, excenter_eq_incenter_iff, s.excenterExists_singleton
-/
lemma excenter_singleton_ne_incenter [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.excenter {i} != s.incenter := by
  intro h
  rw [(s.excenterExists_singleton i).excenter_eq_incenter_iff] at h
  simp at h

/--
lemma `excenter_singleton_injective` / 引理 `excenter_singleton_injective`

English:
lemma excenter_singleton_injective
  given: [Nat.AtLeastTwo n]
  proof: by
  intro i j hij
  dsimp only at hij
  rw [(s.excenterExists_singleton i).excenter_eq_excenter_iff (s.excenterExists_singleton j)] at hij
  rcases hij with hij | hij
  · simpa using hij
  · have : 2 <= n := Nat.AtLeastTwo.prop
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    rw [Finset.ext_iff] at hij
    replace hij := hij k
    simp_all

中文:
引理 excenter_singleton_injective
  条件: [自然数.AtLeastTwo n]
  证明: by
  intro i j hij
  dsimp only at hij
  rw [(s.excenterExists_singleton i).excenter_eq_excenter_iff (s.excenterExists_singleton j)] at hij
  rcases hij with hij | hij
  · simpa using hij
  · have : 2 <= n := Nat.AtLeastTwo.prop
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    rw [Finset.ext_iff] at hij
    replace hij := hij k
    simp_all

Depends on / 依赖: AtLeastTwo, Fin.exists_ne_and_ne_of_two_lt, Finset, Finset.ext_iff, Nat.AtLeastTwo.prop, excenterExists_singleton, excenter_eq_excenter_iff, exists_ne_and_ne_of_two_lt, ext_iff, replace, s.excenterExists_singleton
-/
lemma excenter_singleton_injective [Nat.AtLeastTwo n] :
    Function.Injective fun i => s.excenter {i} := by
  intro i j hij
  dsimp only at hij
  rw [(s.excenterExists_singleton i).excenter_eq_excenter_iff (s.excenterExists_singleton j)] at hij
  rcases hij with hij | hij
  · simpa using hij
  · have : 2 <= n := Nat.AtLeastTwo.prop
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    rw [Finset.ext_iff] at hij
    replace hij := hij k
    simp_all

variable {s} in
/--
lemma `ExcenterExists.sSameSide_excenter_point_iff` / 引理 `ExcenterExists.sSameSide_excenter_point_iff`

English:
lemma ExcenterExists.sSameSide_excenter_point_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

中文:
引理 ExcenterExists.sSameSide_excenter_point_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

Depends on / 依赖: excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, s.sSameSide_affineSpan_faceOpposite_point_right_iff, sSameSide_affineSpan_faceOpposite_point_right_iff, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.sSameSide_excenter_point_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide (s.excenter signs) (s.points i) ↔
      0 < s.excenterWeights signs i := by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

variable {s} in
/--
lemma `ExcenterExists.sSameSide_point_excenter_iff` / 引理 `ExcenterExists.sSameSide_point_excenter_iff`

English:
lemma ExcenterExists.sSameSide_point_excenter_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

中文:
引理 ExcenterExists.sSameSide_point_excenter_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

Depends on / 依赖: excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, s.sSameSide_affineSpan_faceOpposite_point_left_iff, sSameSide_affineSpan_faceOpposite_point_left_iff, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.sSameSide_point_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide (s.points i) (s.excenter signs) ↔
      0 < s.excenterWeights signs i := by
  rw [excenter_eq_affineCombination]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

variable {s} in
/--
lemma `ExcenterExists.sOppSide_excenter_point_iff` / 引理 `ExcenterExists.sOppSide_excenter_point_iff`

English:
lemma ExcenterExists.sOppSide_excenter_point_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

中文:
引理 ExcenterExists.sOppSide_excenter_point_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

Depends on / 依赖: excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, s.sOppSide_affineSpan_faceOpposite_point_right_iff, sOppSide_affineSpan_faceOpposite_point_right_iff, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.sOppSide_excenter_point_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.excenter signs) (s.points i) ↔
      s.excenterWeights signs i < 0 := by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

variable {s} in
/--
lemma `ExcenterExists.sOppSide_point_excenter_iff` / 引理 `ExcenterExists.sOppSide_point_excenter_iff`

English:
lemma ExcenterExists.sOppSide_point_excenter_iff
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

中文:
引理 ExcenterExists.sOppSide_point_excenter_iff
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

Depends on / 依赖: excenter_eq_affineCombination, h.sum_excenterWeights_eq_one, s.sOppSide_affineSpan_faceOpposite_point_left_iff, sOppSide_affineSpan_faceOpposite_point_left_iff, sum_excenterWeights_eq_one
-/
lemma ExcenterExists.sOppSide_point_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.points i) (s.excenter signs) ↔
      s.excenterWeights signs i < 0 := by
  rw [excenter_eq_affineCombination]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

/--
lemma `sSameSide_incenter_point` / 引理 `sSameSide_incenter_point`

English:
lemma sSameSide_incenter_point
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.sSameSide_excenter_point_iff.2 (s.excenterWeights_empty_pos i)

中文:
引理 sSameSide_incenter_point
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.sSameSide_excenter_point_iff.2 (s.excenterWeights_empty_pos i)

Depends on / 依赖: excenterExists_empty, excenterWeights_empty_pos, s.excenterExists_empty.sSameSide_excenter_point_iff, s.excenterWeights_empty_pos, sSameSide_excenter_point_iff
-/
lemma sSameSide_incenter_point (i : Fin (n + 1)) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide s.incenter (s.points i) :=
  s.excenterExists_empty.sSameSide_excenter_point_iff.2 (s.excenterWeights_empty_pos i)

/--
lemma `sSameSide_point_incenter` / 引理 `sSameSide_point_incenter`

English:
lemma sSameSide_point_incenter
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.sSameSide_point_excenter_iff.2 (s.excenterWeights_empty_pos i)

中文:
引理 sSameSide_point_incenter
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.sSameSide_point_excenter_iff.2 (s.excenterWeights_empty_pos i)

Depends on / 依赖: excenterExists_empty, excenterWeights_empty_pos, s.excenterExists_empty.sSameSide_point_excenter_iff, s.excenterWeights_empty_pos, sSameSide_point_excenter_iff
-/
lemma sSameSide_point_incenter (i : Fin (n + 1)) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide (s.points i) s.incenter :=
  s.excenterExists_empty.sSameSide_point_excenter_iff.2 (s.excenterWeights_empty_pos i)

/--
lemma `sOppSide_excenter_singleton_point` / 引理 `sOppSide_excenter_singleton_point`

English:
lemma sOppSide_excenter_singleton_point
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [(s.excenterExists_singleton i).sOppSide_excenter_point_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

中文:
引理 sOppSide_excenter_singleton_point
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [(s.excenterExists_singleton i).sOppSide_excenter_point_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

Depends on / 依赖: excenterExists_singleton, s.excenterExists_singleton, s.sign_excenterWeights_singleton_neg, sOppSide_excenter_point_iff, sign_eq_neg_one_iff, sign_excenterWeights_singleton_neg
-/
lemma sOppSide_excenter_singleton_point [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.excenter {i})
      (s.points i) := by
  rw [(s.excenterExists_singleton i).sOppSide_excenter_point_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

/--
lemma `sOppSide_point_excenter_singleton` / 引理 `sOppSide_point_excenter_singleton`

English:
lemma sOppSide_point_excenter_singleton
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [(s.excenterExists_singleton i).sOppSide_point_excenter_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

中文:
引理 sOppSide_point_excenter_singleton
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [(s.excenterExists_singleton i).sOppSide_point_excenter_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

Depends on / 依赖: excenterExists_singleton, s.excenterExists_singleton, s.sign_excenterWeights_singleton_neg, sOppSide_point_excenter_iff, sign_eq_neg_one_iff, sign_excenterWeights_singleton_neg
-/
lemma sOppSide_point_excenter_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.points i)
      (s.excenter {i}) := by
  rw [(s.excenterExists_singleton i).sOppSide_point_excenter_iff]; rw [← sign_eq_neg_one_iff]; rw [s.sign_excenterWeights_singleton_neg i]

/--
lemma `sSameSide_excenter_singleton_point` / 引理 `sSameSide_excenter_singleton_point`

English:
lemma sSameSide_excenter_singleton_point
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j)
  proof: by
  rw [(s.excenterExists_singleton j).sSameSide_excenter_point_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

中文:
引理 sSameSide_excenter_singleton_point
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (h : i != j)
  证明: by
  rw [(s.excenterExists_singleton j).sSameSide_excenter_point_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

Depends on / 依赖: excenterExists_singleton, h.symm, s.excenterExists_singleton, s.sign_excenterWeights_singleton_pos, sSameSide_excenter_point_iff, sign_eq_one_iff, sign_excenterWeights_singleton_pos
-/
lemma sSameSide_excenter_singleton_point [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide (s.excenter {j})
      (s.points i) := by
  rw [(s.excenterExists_singleton j).sSameSide_excenter_point_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

/--
lemma `sSameSide_point_excenter_singleton` / 引理 `sSameSide_point_excenter_singleton`

English:
lemma sSameSide_point_excenter_singleton
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j)
  proof: by
  rw [(s.excenterExists_singleton j).sSameSide_point_excenter_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

中文:
引理 sSameSide_point_excenter_singleton
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (h : i != j)
  证明: by
  rw [(s.excenterExists_singleton j).sSameSide_point_excenter_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

Depends on / 依赖: excenterExists_singleton, h.symm, s.excenterExists_singleton, s.sign_excenterWeights_singleton_pos, sSameSide_point_excenter_iff, sign_eq_one_iff, sign_excenterWeights_singleton_pos
-/
lemma sSameSide_point_excenter_singleton [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) :
    (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide (s.points i)
      (s.excenter {j}) := by
  rw [(s.excenterExists_singleton j).sSameSide_point_excenter_iff]; rw [← sign_eq_one_iff]; rw [s.sign_excenterWeights_singleton_pos h.symm]

/--
Definition of `touchpoint` / `touchpoint` 的定义

English:
definition touchpoint
  signature: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  body: (s.faceOpposite i).orthogonalProjectionSpan (s.excenter signs)

中文:
定义 touchpoint
  签名: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  定义体: (s.faceOpposite i).orthogonalProjectionSpan (s.excenter signs)

Depends on / 依赖: excenter, faceOpposite, orthogonalProjectionSpan, s.excenter, s.faceOpposite
-/
def touchpoint (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).orthogonalProjectionSpan (s.excenter signs)

/--
lemma `touchpoint_reindex` / 引理 `touchpoint_reindex`

English:
lemma touchpoint_reindex
  statement: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex _ _) (s.excenter_reindex _ _)

中文:
引理 touchpoint_reindex
  结论: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex _ _) (s.excenter_reindex _ _)

Depends on / 依赖: excenter_reindex, orthogonalProjectionSpan_congr, range_faceOpposite_reindex, s.excenter_reindex, s.range_faceOpposite_reindex
-/
lemma touchpoint_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).touchpoint signs i = s.touchpoint (signs.map e.symm) (e.symm i) :=
  orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex _ _) (s.excenter_reindex _ _)

set_option backward.isDefEq.respectTransparency false in
variable {s} in
/--
lemma `ExcenterExists.touchpoint_map` / 引理 `ExcenterExists.touchpoint_map`

English:
lemma ExcenterExists.touchpoint_map
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  simp [touchpoint, h.excenter_map, ← orthogonalProjectionSpan_map]

中文:
引理 ExcenterExists.touchpoint_map
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  simp [touchpoint, h.excenter_map, ← orthogonalProjectionSpan_map]
-/
@[simp] lemma ExcenterExists.touchpoint_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).touchpoint signs i = f (s.touchpoint signs i) := by
  simp [touchpoint, h.excenter_map, ← orthogonalProjectionSpan_map]

variable {s} in
/--
lemma `ExcenterExists.touchpoint_restrict` / 引理 `ExcenterExists.touchpoint_restrict`

English:
lemma ExcenterExists.touchpoint_restrict
  statement: {signs : Finset (Fin (n + 1))}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpoint signs i = s.touchpoint signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpoint_map S.subtypeₐᵢ i).symm

中文:
引理 ExcenterExists.touchpoint_restrict
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpoint signs i = s.touchpoint signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpoint_map S.subtypeₐᵢ i).symm
-/
@[simp] lemma ExcenterExists.touchpoint_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpoint signs i = s.touchpoint signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpoint_map S.subtypeₐᵢ i).symm

/--
lemma `touchpoint_mem_affineSpan` / 引理 `touchpoint_mem_affineSpan`

English:
lemma touchpoint_mem_affineSpan
  given: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  proof: orthogonalProjection_mem _

中文:
引理 touchpoint_mem_affineSpan
  条件: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  证明: orthogonalProjection_mem _

Depends on / 依赖: orthogonalProjection_mem
-/
lemma touchpoint_mem_affineSpan (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.touchpoint signs i in affineSpan Real (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _

/--
lemma `touchpoint_mem_affineSpan_simplex` / 引理 `touchpoint_mem_affineSpan_simplex`

English:
lemma touchpoint_mem_affineSpan_simplex
  given: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  proof: by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.touchpoint_mem_affineSpan signs i)
  simp

中文:
引理 touchpoint_mem_affineSpan_simplex
  条件: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  证明: by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.touchpoint_mem_affineSpan signs i)
  simp

Depends on / 依赖: SetLike, SetLike.le_def, affineSpan_mono, le_def, s.touchpoint_mem_affineSpan, touchpoint_mem_affineSpan
-/
lemma touchpoint_mem_affineSpan_simplex (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.touchpoint signs i in affineSpan Real (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.touchpoint_mem_affineSpan signs i)
  simp

/--
lemma `touchpoint_eq_point_rev` / 引理 `touchpoint_eq_point_rev`

English:
lemma touchpoint_eq_point_rev
  given: (s : Simplex Real P 1) (signs : Finset (Fin 2)) (i : Fin 2)
  proof: s.orthogonalProjectionSpan_faceOpposite_eq_point_rev _ _

中文:
引理 touchpoint_eq_point_rev
  条件: (s : 单纯形 实数 P 1) (signs : 有限集 (有限集 2)) (i : 有限集 2)
  证明: s.orthogonalProjectionSpan_faceOpposite_eq_point_rev _ _

Depends on / 依赖: orthogonalProjectionSpan_faceOpposite_eq_point_rev, s.orthogonalProjectionSpan_faceOpposite_eq_point_rev
-/
lemma touchpoint_eq_point_rev (s : Simplex Real P 1) (signs : Finset (Fin 2)) (i : Fin 2) :
    s.touchpoint signs i = s.points i.rev :=
  s.orthogonalProjectionSpan_faceOpposite_eq_point_rev _ _

variable {s} in
/--
lemma `ExcenterExists.signedInfDist_excenter` / 引理 `ExcenterExists.signedInfDist_excenter`

English:
lemma ExcenterExists.signedInfDist_excenter
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [h.signedInfDist_excenter_eq_mul_sum_inv]; rw [mul_assoc]; rw [exradius_eq_abs_inv_sum]
  congr
  rw [← mul_eq_one_iff_inv_eq₀ h]; rw [← mul_assoc]; rw [self_mul_sign]; rw [← abs_mul]; rw [mul_inv_cancel₀ h]; rw [abs_one]

中文:
引理 ExcenterExists.signedInfDist_excenter
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [h.signedInfDist_excenter_eq_mul_sum_inv]; rw [mul_assoc]; rw [exradius_eq_abs_inv_sum]
  congr
  rw [← mul_eq_one_iff_inv_eq₀ h]; rw [← mul_assoc]; rw [self_mul_sign]; rw [← abs_mul]; rw [mul_inv_cancel₀ h]; rw [abs_one]

Depends on / 依赖: abs_mul, abs_one, exradius_eq_abs_inv_sum, h.signedInfDist_excenter_eq_mul_sum_inv, mul_assoc, self_mul_sign, signedInfDist_excenter_eq_mul_sum_inv
-/
lemma ExcenterExists.signedInfDist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) = (if i in signs then -1 else 1) *
      SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs) := by
  rw [h.signedInfDist_excenter_eq_mul_sum_inv]; rw [mul_assoc]; rw [exradius_eq_abs_inv_sum]
  congr
  rw [← mul_eq_one_iff_inv_eq₀ h]; rw [← mul_assoc]; rw [self_mul_sign]; rw [← abs_mul]; rw [mul_inv_cancel₀ h]; rw [abs_one]

/--
lemma `signedInfDist_incenter` / 引理 `signedInfDist_incenter`

English:
lemma signedInfDist_incenter
  given: (i : Fin (n + 1))
  statement: s.signedInfDist i s.incenter = s.inradius
  proof: by
  rw [incenter]; rw [exsphere_center]; rw [s.excenterExists_empty.signedInfDist_excenter]
  simp (discharger := positivity)

中文:
引理 signedInfDist_incenter
  条件: (i : 有限集 (n + 1))
  结论: s.signedInfDist i s.incenter = s.inradius
  证明: by
  rw [incenter]; rw [exsphere_center]; rw [s.excenterExists_empty.signedInfDist_excenter]
  simp (discharger := positivity)

Depends on / 依赖: discharger, excenterExists_empty, exsphere_center, incenter, s.excenterExists_empty.signedInfDist_excenter, signedInfDist_excenter
-/
lemma signedInfDist_incenter (i : Fin (n + 1)) : s.signedInfDist i s.incenter = s.inradius := by
  rw [incenter]; rw [exsphere_center]; rw [s.excenterExists_empty.signedInfDist_excenter]
  simp (discharger := positivity)

variable {s} in
/--
lemma `ExcenterExists.dist_excenter` / 引理 `ExcenterExists.dist_excenter`

English:
lemma ExcenterExists.dist_excenter
  statement: {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
  proof: by
  rw [touchpoint]; rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range i h.excenter_mem_affineSpan_range]; rw [h.signedInfDist_excenter]; rw [abs_mul]; rw [abs_mul]; rw [abs_of_nonneg (s.exradius_nonneg signs)]
  simp only [abs_ite, abs_neg, abs_one, ite_self, one_mul]
  rcases lt_trichotomy 0 (∑ i, s.excenterWeightsUnnorm signs i) with h' | h' | h'
  · simp [h']
  · simp [h h'.symm]
  · simp [h']

中文:
引理 ExcenterExists.dist_excenter
  结论: {signs : 有限集 (有限集 (n + 1))} (h : s.ExcenterExists signs)
  证明: by
  rw [touchpoint]; rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range i h.excenter_mem_affineSpan_range]; rw [h.signedInfDist_excenter]; rw [abs_mul]; rw [abs_mul]; rw [abs_of_nonneg (s.exradius_nonneg signs)]
  simp only [abs_ite, abs_neg, abs_one, ite_self, one_mul]
  rcases lt_trichotomy 0 (∑ i, s.excenterWeightsUnnorm signs i) with h' | h' | h'
  · simp [h']
  · simp [h h'.symm]
  · simp [h']

Depends on / 依赖: abs_ite, abs_mul, abs_neg, abs_of_nonneg, abs_one, abs_signedInfDist_eq_dist_of_mem_affineSpan_range, excenterWeightsUnnorm, excenter_mem_affineSpan_range, exradius_nonneg, h.excenter_mem_affineSpan_range, h.signedInfDist_excenter, ite_self, lt_trichotomy, one_mul, s.excenterWeightsUnnorm, s.exradius_nonneg, signedInfDist_excenter, touchpoint
-/
lemma ExcenterExists.dist_excenter {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
    (i : Fin (n + 1)) :
    dist (s.excenter signs) (s.touchpoint signs i) = s.exradius signs := by
  rw [touchpoint]; rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range i h.excenter_mem_affineSpan_range]; rw [h.signedInfDist_excenter]; rw [abs_mul]; rw [abs_mul]; rw [abs_of_nonneg (s.exradius_nonneg signs)]
  simp only [abs_ite, abs_neg, abs_one, ite_self, one_mul]
  rcases lt_trichotomy 0 (∑ i, s.excenterWeightsUnnorm signs i) with h' | h' | h'
  · simp [h']
  · simp [h h'.symm]
  · simp [h']

/--
lemma `dist_incenter` / 引理 `dist_incenter`

English:
lemma dist_incenter
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.dist_excenter _

中文:
引理 dist_incenter
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.dist_excenter _

Depends on / 依赖: dist_excenter, excenterExists_empty, s.excenterExists_empty.dist_excenter
-/
lemma dist_incenter (i : Fin (n + 1)) :
    dist s.incenter (s.touchpoint ∅ i) = s.inradius :=
  s.excenterExists_empty.dist_excenter _

variable {s} in
/--
lemma `ExcenterExists.dist_excenter_eq_dist_excenter` / 引理 `ExcenterExists.dist_excenter_eq_dist_excenter`

English:
lemma ExcenterExists.dist_excenter_eq_dist_excenter
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  simp_rw [h.dist_excenter]

中文:
引理 ExcenterExists.dist_excenter_eq_dist_excenter
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  simp_rw [h.dist_excenter]

Depends on / 依赖: dist_excenter, h.dist_excenter, simp_rw
-/
lemma ExcenterExists.dist_excenter_eq_dist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i₁ i₂ : Fin (n + 1)) :
    dist (s.excenter signs) (s.touchpoint signs i₁) =
      dist (s.excenter signs) (s.touchpoint signs i₂) := by
  simp_rw [h.dist_excenter]

/--
lemma `dist_incenter_eq_dist_incenter` / 引理 `dist_incenter_eq_dist_incenter`

English:
lemma dist_incenter_eq_dist_incenter
  given: (i₁ i₂ : Fin (n + 1))
  proof: s.excenterExists_empty.dist_excenter_eq_dist_excenter _ _

中文:
引理 dist_incenter_eq_dist_incenter
  条件: (i₁ i₂ : 有限集 (n + 1))
  证明: s.excenterExists_empty.dist_excenter_eq_dist_excenter _ _

Depends on / 依赖: dist_excenter_eq_dist_excenter, excenterExists_empty, s.excenterExists_empty.dist_excenter_eq_dist_excenter
-/
lemma dist_incenter_eq_dist_incenter (i₁ i₂ : Fin (n + 1)) :
    dist s.incenter (s.touchpoint ∅ i₁) = dist s.incenter (s.touchpoint ∅ i₂) :=
  s.excenterExists_empty.dist_excenter_eq_dist_excenter _ _

variable {s} in
/--
lemma `ExcenterExists.touchpoint_mem_exsphere` / 引理 `ExcenterExists.touchpoint_mem_exsphere`

English:
lemma ExcenterExists.touchpoint_mem_exsphere
  statement: {signs : Finset (Fin (n + 1))}
  proof: mem_sphere'.2 (h.dist_excenter i)

中文:
引理 ExcenterExists.touchpoint_mem_exsphere
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: mem_sphere'.2 (h.dist_excenter i)

Depends on / 依赖: dist_excenter, h.dist_excenter, mem_sphere
-/
lemma ExcenterExists.touchpoint_mem_exsphere {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.touchpoint signs i in s.exsphere signs :=
  mem_sphere'.2 (h.dist_excenter i)

/--
lemma `touchpoint_mem_insphere` / 引理 `touchpoint_mem_insphere`

English:
lemma touchpoint_mem_insphere
  given: (i : Fin (n + 1))
  statement: s.touchpoint ∅ i in s.insphere
  proof: s.excenterExists_empty.touchpoint_mem_exsphere _

中文:
引理 touchpoint_mem_insphere
  条件: (i : 有限集 (n + 1))
  结论: s.touchpoint ∅ i in s.insphere
  证明: s.excenterExists_empty.touchpoint_mem_exsphere _

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.touchpoint_mem_exsphere, touchpoint_mem_exsphere
-/
lemma touchpoint_mem_insphere (i : Fin (n + 1)) : s.touchpoint ∅ i in s.insphere :=
  s.excenterExists_empty.touchpoint_mem_exsphere _

variable {s} in
/--
lemma `ExcenterExists.isTangentAt_touchpoint` / 引理 `ExcenterExists.isTangentAt_touchpoint`

English:
lemma ExcenterExists.isTangentAt_touchpoint
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]; rw [← EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt]; rw [← orthogonalProjectionSpan]; rw [← excenter]; rw [← exradius]; rw [← touchpoint]; rw [h.dist_excenter]

中文:
引理 ExcenterExists.isTangentAt_touchpoint
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]; rw [← EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt]; rw [← orthogonalProjectionSpan]; rw [← excenter]; rw [← exradius]; rw [← touchpoint]; rw [h.dist_excenter]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt, Sphere, dist_excenter, dist_orthogonalProjection_eq_radius_iff_isTangentAt, excenter, exradius, h.dist_excenter, orthogonalProjectionSpan, touchpoint
-/
lemma ExcenterExists.isTangentAt_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    (s.exsphere signs).IsTangentAt (s.touchpoint signs i)
      (affineSpan Real (Set.range (s.faceOpposite i).points)) := by
  rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]; rw [← EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt]; rw [← orthogonalProjectionSpan]; rw [← excenter]; rw [← exradius]; rw [← touchpoint]; rw [h.dist_excenter]

/--
lemma `isTangentAt_insphere_touchpoint` / 引理 `isTangentAt_insphere_touchpoint`

English:
lemma isTangentAt_insphere_touchpoint
  given: (i : Fin (n + 1))
  proof: s.excenterExists_empty.isTangentAt_touchpoint i

中文:
引理 isTangentAt_insphere_touchpoint
  条件: (i : 有限集 (n + 1))
  证明: s.excenterExists_empty.isTangentAt_touchpoint i

Depends on / 依赖: excenterExists_empty, isTangentAt_touchpoint, s.excenterExists_empty.isTangentAt_touchpoint
-/
lemma isTangentAt_insphere_touchpoint (i : Fin (n + 1)) :
    s.insphere.IsTangentAt (s.touchpoint ∅ i)
      (affineSpan Real (Set.range (s.faceOpposite i).points)) :=
  s.excenterExists_empty.isTangentAt_touchpoint i

variable {s} in
/--
lemma `eq_touchpoint_of_isTangentAt_exsphere` / 引理 `eq_touchpoint_of_isTangentAt_exsphere`

English:
lemma eq_touchpoint_of_isTangentAt_exsphere
  statement: {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)} {p : P}
  proof: by
  rw [ht.eq_orthogonalProjection]; rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]

中文:
引理 eq_touchpoint_of_isTangentAt_exsphere
  结论: {signs : 有限集 (有限集 (n + 1))} {i : 有限集 (n + 1)} {p : P}
  证明: by
  rw [ht.eq_orthogonalProjection]; rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]

Depends on / 依赖: eq_orthogonalProjection, excenter, ht.eq_orthogonalProjection, orthogonalProjectionSpan, touchpoint
-/
lemma eq_touchpoint_of_isTangentAt_exsphere {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)} {p : P}
    (ht : (s.exsphere signs).IsTangentAt p (affineSpan Real (Set.range (s.faceOpposite i).points))) :
    p = s.touchpoint signs i := by
  rw [ht.eq_orthogonalProjection]; rw [touchpoint]; rw [orthogonalProjectionSpan]; rw [excenter]

variable {s} in
/--
lemma `ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint` / 引理 `ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint`

English:
lemma ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  refine ⟨eq_touchpoint_of_isTangentAt_exsphere, ?_⟩
  rintro rfl
  exact h.isTangentAt_touchpoint i

中文:
引理 ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  refine ⟨eq_touchpoint_of_isTangentAt_exsphere, ?_⟩
  rintro rfl
  exact h.isTangentAt_touchpoint i

Depends on / 依赖: eq_touchpoint_of_isTangentAt_exsphere, h.isTangentAt_touchpoint, isTangentAt_touchpoint
-/
lemma ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} {p : P} :
    (s.exsphere signs).IsTangentAt p (affineSpan Real (Set.range (s.faceOpposite i).points)) ↔
      p = s.touchpoint signs i := by
  refine ⟨eq_touchpoint_of_isTangentAt_exsphere, ?_⟩
  rintro rfl
  exact h.isTangentAt_touchpoint i

variable {s} in
/--
lemma `isTangentAt_insphere_iff_eq_touchpoint` / 引理 `isTangentAt_insphere_iff_eq_touchpoint`

English:
lemma isTangentAt_insphere_iff_eq_touchpoint
  given: {i : Fin (n + 1)} {p : P}
  proof: s.excenterExists_empty.isTangentAt_exsphere_iff_eq_touchpoint

中文:
引理 isTangentAt_insphere_iff_eq_touchpoint
  条件: {i : 有限集 (n + 1)} {p : P}
  证明: s.excenterExists_empty.isTangentAt_exsphere_iff_eq_touchpoint

Depends on / 依赖: excenterExists_empty, isTangentAt_exsphere_iff_eq_touchpoint, s.excenterExists_empty.isTangentAt_exsphere_iff_eq_touchpoint
-/
lemma isTangentAt_insphere_iff_eq_touchpoint {i : Fin (n + 1)} {p : P} :
    s.insphere.IsTangentAt p (affineSpan Real (Set.range (s.faceOpposite i).points)) ↔
      p = s.touchpoint ∅ i :=
  s.excenterExists_empty.isTangentAt_exsphere_iff_eq_touchpoint

variable {s} in
/--
lemma `ExcenterExists.affineSpan_faceOpposite_eq_orthRadius` / 引理 `ExcenterExists.affineSpan_faceOpposite_eq_orthRadius`

English:
lemma ExcenterExists.affineSpan_faceOpposite_eq_orthRadius
  statement: [hf : Fact (Module.finrank Real V = n)]
  proof: by
  refine (h.isTangentAt_touchpoint i).eq_orthRadius_of_finrank_add_one_eq (h.exradius_pos.ne') ?_
  rw [direction_affineSpan]; rw [(s.faceOpposite i).independent.finrank_vectorSpan_add_one]; rw [Fintype.card_fin]; rw [hf.out]
  have := NeZero.ne n
  lia

中文:
引理 ExcenterExists.affineSpan_faceOpposite_eq_orthRadius
  结论: [hf : Fact (模.finrank 实数 V = n)]
  证明: by
  refine (h.isTangentAt_touchpoint i).eq_orthRadius_of_finrank_add_one_eq (h.exradius_pos.ne') ?_
  rw [direction_affineSpan]; rw [(s.faceOpposite i).independent.finrank_vectorSpan_add_one]; rw [Fintype.card_fin]; rw [hf.out]
  have := NeZero.ne n
  lia

Depends on / 依赖: Fintype, Fintype.card_fin, NeZero, NeZero.ne, card_fin, direction_affineSpan, eq_orthRadius_of_finrank_add_one_eq, exradius_pos, faceOpposite, finrank_vectorSpan_add_one, h.exradius_pos.ne, h.isTangentAt_touchpoint, hf.out, independent, independent.finrank_vectorSpan_add_one, isTangentAt_touchpoint, s.faceOpposite
-/
lemma ExcenterExists.affineSpan_faceOpposite_eq_orthRadius [hf : Fact (Module.finrank Real V = n)]
    {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    affineSpan Real (Set.range (s.faceOpposite i).points) =
      (s.exsphere signs).orthRadius (s.touchpoint signs i) := by
  refine (h.isTangentAt_touchpoint i).eq_orthRadius_of_finrank_add_one_eq (h.exradius_pos.ne') ?_
  rw [direction_affineSpan]; rw [(s.faceOpposite i).independent.finrank_vectorSpan_add_one]; rw [Fintype.card_fin]; rw [hf.out]
  have := NeZero.ne n
  lia

/--
lemma `affineSpan_faceOpposite_eq_orthRadius_insphere` / 引理 `affineSpan_faceOpposite_eq_orthRadius_insphere`

English:
lemma affineSpan_faceOpposite_eq_orthRadius_insphere
  statement: [Fact (Module.finrank Real V = n)]
  proof: s.excenterExists_empty.affineSpan_faceOpposite_eq_orthRadius i

中文:
引理 affineSpan_faceOpposite_eq_orthRadius_insphere
  结论: [Fact (模.finrank 实数 V = n)]
  证明: s.excenterExists_empty.affineSpan_faceOpposite_eq_orthRadius i

Depends on / 依赖: affineSpan_faceOpposite_eq_orthRadius, excenterExists_empty, s.excenterExists_empty.affineSpan_faceOpposite_eq_orthRadius
-/
lemma affineSpan_faceOpposite_eq_orthRadius_insphere [Fact (Module.finrank Real V = n)]
    (i : Fin (n + 1)) :
    affineSpan Real (Set.range (s.faceOpposite i).points) = s.insphere.orthRadius (s.touchpoint ∅ i) :=
  s.excenterExists_empty.affineSpan_faceOpposite_eq_orthRadius i

/--
lemma `exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter` / 引理 `exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter`

English:
lemma exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter
  statement: {p : P}
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    obtain ⟨w, h1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    have h' : forall i, w i * ‖s.points i -ᵥ s.altitudeFoot i‖ = (if i in signs then -1 else 1) * r := by
      intro i
      rw [altitudeFoot]; rw [← s.signedInfDist_affineCombination i h1]
      exact h i
    simp_rw [← dist_eq_norm_vsub] at h'
    have h'' : forall i, w i = r * s.excenterWeightsUnnorm signs i := by
      simp_rw [excenterWeightsUnnorm]
      intro i
      replace h' := h' i
      rw [← height]; rw [← eq_div_iff (s.height_pos i).ne'] at h'
      rw [h']; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [height]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]
    have hw : w = s.excenterWeights signs := by
      simp_rw [h'', ← Finset.mul_sum] at h1
      ext j
      rw [h'']; rw [eq_inv_of_mul_eq_one_left h1]
      simp [excenterWeights]
    subst hw
    exact ⟨s.sum_excenterWeights_eq_one_iff.1 h1, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs), fun i => ?_⟩
    rw [h.signedInfDist_excenter]
    simp

中文:
引理 存在_对任意_signedInfDist_eq_iff_excenterExists_and_eq_excenter
  结论: {p : P}
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    obtain ⟨w, h1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    have h' : forall i, w i * ‖s.points i -ᵥ s.altitudeFoot i‖ = (if i in signs then -1 else 1) * r := by
      intro i
      rw [altitudeFoot]; rw [← s.signedInfDist_affineCombination i h1]
      exact h i
    simp_rw [← dist_eq_norm_vsub] at h'
    have h'' : forall i, w i = r * s.excenterWeightsUnnorm signs i := by
      simp_rw [excenterWeightsUnnorm]
      intro i
      replace h' := h' i
      rw [← height]; rw [← eq_div_iff (s.height_pos i).ne'] at h'
      rw [h']; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [height]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]
    have hw : w = s.excenterWeights signs := by
      simp_rw [h'', ← Finset.mul_sum] at h1
      ext j
      rw [h'']; rw [eq_inv_of_mul_eq_one_left h1]
      simp [excenterWeights]
    subst hw
    exact ⟨s.sum_excenterWeights_eq_one_iff.1 h1, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs), fun i => ?_⟩
    rw [h.signedInfDist_excenter]
    simp

Depends on / 依赖: altitudeFoot, dist_eq_norm_vsub, eq_affineCombination_of_mem_affineSpan_of_fintype, eq_div_iff, excenterWeightsUnnorm, height, points, replace, s.altitudeFoot, s.excenterWeightsUnnorm, s.heigh, s.points, s.signedInfDist_affineCombination, signedInfDist_affineCombination, simp_rw
-/
lemma exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) {signs : Finset (Fin (n + 1))} :
    (exists r : Real, forall i, s.signedInfDist i p = (if i in signs then -1 else 1) * r) ↔
      s.ExcenterExists signs ∧ p = s.excenter signs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    obtain ⟨w, h1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    have h' : forall i, w i * ‖s.points i -ᵥ s.altitudeFoot i‖ = (if i in signs then -1 else 1) * r := by
      intro i
      rw [altitudeFoot]; rw [← s.signedInfDist_affineCombination i h1]
      exact h i
    simp_rw [← dist_eq_norm_vsub] at h'
    have h'' : forall i, w i = r * s.excenterWeightsUnnorm signs i := by
      simp_rw [excenterWeightsUnnorm]
      intro i
      replace h' := h' i
      rw [← height]; rw [← eq_div_iff (s.height_pos i).ne'] at h'
      rw [h']; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [height]; rw [altitudeFoot]; rw [orthogonalProjectionSpan]
    have hw : w = s.excenterWeights signs := by
      simp_rw [h'', ← Finset.mul_sum] at h1
      ext j
      rw [h'']; rw [eq_inv_of_mul_eq_one_left h1]
      simp [excenterWeights]
    subst hw
    exact ⟨s.sum_excenterWeights_eq_one_iff.1 h1, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs), fun i => ?_⟩
    rw [h.signedInfDist_excenter]
    simp

/--
lemma `exists_forall_signedInfDist_eq_iff_eq_incenter` / 引理 `exists_forall_signedInfDist_eq_iff_eq_incenter`

English:
lemma exists_forall_signedInfDist_eq_iff_eq_incenter
  statement: {p : P}
  proof: by
  convert! s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp (signs := ∅)
  · simp
  · simp [excenterExists_empty]

中文:
引理 存在_对任意_signedInfDist_eq_iff_eq_incenter
  结论: {p : P}
  证明: by
  convert! s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp (signs := ∅)
  · simp
  · simp [excenterExists_empty]

Depends on / 依赖: convert, excenterExists_empty, exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter, s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter
-/
lemma exists_forall_signedInfDist_eq_iff_eq_incenter {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) :
    (exists r : Real, forall i, s.signedInfDist i p = r) ↔ p = s.incenter := by
  convert! s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp (signs := ∅)
  · simp
  · simp [excenterExists_empty]

/--
lemma `exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter` / 引理 `exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter`

English:
lemma exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter
  statement: {p : P}
  proof: by
  simp_rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range _ hp]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    have h' : forall i, s.signedInfDist i p = r ∨ s.signedInfDist i p = -r :=
      fun i => eq_or_eq_neg_of_abs_eq (h i)
    refine ⟨{i in (Finset.univ : Finset (Fin (n + 1))) | s.signedInfDist i p = -r}, ?_⟩
    apply (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).1
    refine ⟨r, ?_⟩
    grind
  · rintro ⟨signs, h⟩
    replace h := (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).2 h
    rcases h with ⟨r, h⟩
    refine ⟨|r|, ?_⟩
    simp [h, abs_ite]

中文:
引理 存在_对任意_dist_eq_iff_存在_excenterExists_and_eq_excenter
  结论: {p : P}
  证明: by
  simp_rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range _ hp]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    have h' : forall i, s.signedInfDist i p = r ∨ s.signedInfDist i p = -r :=
      fun i => eq_or_eq_neg_of_abs_eq (h i)
    refine ⟨{i in (Finset.univ : Finset (Fin (n + 1))) | s.signedInfDist i p = -r}, ?_⟩
    apply (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).1
    refine ⟨r, ?_⟩
    grind
  · rintro ⟨signs, h⟩
    replace h := (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).2 h
    rcases h with ⟨r, h⟩
    refine ⟨|r|, ?_⟩
    simp [h, abs_ite]

Depends on / 依赖: Finset, Finset.univ, abs_signedInfDist_eq_dist_of_mem_affineSpan_range, eq_or_eq_neg_of_abs_eq, exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excente, exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter, replace, s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excente, s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter, s.signedInfDist, signedInfDist, simp_rw
-/
lemma exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) :
    (exists r : Real, forall i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = r) ↔
      exists signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  simp_rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range _ hp]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    have h' : forall i, s.signedInfDist i p = r ∨ s.signedInfDist i p = -r :=
      fun i => eq_or_eq_neg_of_abs_eq (h i)
    refine ⟨{i in (Finset.univ : Finset (Fin (n + 1))) | s.signedInfDist i p = -r}, ?_⟩
    apply (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).1
    refine ⟨r, ?_⟩
    grind
  · rintro ⟨signs, h⟩
    replace h := (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).2 h
    rcases h with ⟨r, h⟩
    refine ⟨|r|, ?_⟩
    simp [h, abs_ite]

variable {s} in
/--
lemma `ExcenterExists.touchpoint_injective` / 引理 `ExcenterExists.touchpoint_injective`

English:
lemma ExcenterExists.touchpoint_injective
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  intro i j hij
  by_contra hne
  by_cases hn1 : n = 1
  · subst hn1
    rw [s.touchpoint_eq_point_rev signs i]; rw [s.touchpoint_eq_point_rev signs j] at hij
    apply s.independent.injective.ne hne
    convert! hij.symm <;> clear hij <;> decide +revert
  · suffices s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points))ᗮ by
      have h' : s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points)) := by
        rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
      have h0 : s.excenter signs -ᵥ s.touchpoint signs i = 0 := by
        rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
        exact ⟨h', this⟩
      rw [← norm_eq_zero]; rw [← dist_eq_norm_vsub]; rw [h.dist_excenter] at h0
      exact h.exradius_pos.ne' h0
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    have hu : Set.range s.points =
        Set.range (s.faceOpposite i).points union Set.range (s.faceOpposite j).points := by
      simp only [range_faceOpposite_points, ← Set.image_union, ← Set.compl_inter]
      convert! Set.image_univ.symm
      simp [Ne.symm hne]
    rw [hu]; rw [range_faceOpposite_points]; rw [range_faceOpposite_points]; rw [AffineSubspace.vectorSpan_union_of_mem_of_mem Real (p := s.points k)
        (Set.mem_image_of_mem _ (by simp [hki])) (Set.mem_image_of_mem _ (by simp [hkj])),
      ← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · rw [← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
    · rw [hij, ← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

中文:
引理 ExcenterExists.touchpoint_injective
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  intro i j hij
  by_contra hne
  by_cases hn1 : n = 1
  · subst hn1
    rw [s.touchpoint_eq_point_rev signs i]; rw [s.touchpoint_eq_point_rev signs j] at hij
    apply s.independent.injective.ne hne
    convert! hij.symm <;> clear hij <;> decide +revert
  · suffices s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points))ᗮ by
      have h' : s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points)) := by
        rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
      have h0 : s.excenter signs -ᵥ s.touchpoint signs i = 0 := by
        rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
        exact ⟨h', this⟩
      rw [← norm_eq_zero]; rw [← dist_eq_norm_vsub]; rw [h.dist_excenter] at h0
      exact h.exradius_pos.ne' h0
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    have hu : Set.range s.points =
        Set.range (s.faceOpposite i).points union Set.range (s.faceOpposite j).points := by
      simp only [range_faceOpposite_points, ← Set.image_union, ← Set.compl_inter]
      convert! Set.image_univ.symm
      simp [Ne.symm hne]
    rw [hu]; rw [range_faceOpposite_points]; rw [range_faceOpposite_points]; rw [AffineSubspace.vectorSpan_union_of_mem_of_mem Real (p := s.points k)
        (Set.mem_image_of_mem _ (by simp [hki])) (Set.mem_image_of_mem _ (by simp [hkj])),
      ← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · rw [← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
    · rw [hij, ← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

Depends on / 依赖: AffineSubspace, AffineSubspace.vsub_mem_directi, Set.range, convert, direction_affineSpan, excenter, hij.symm, independent, injective, points, revert, s.excenter, s.independent.injective.ne, s.points, s.touchpoint, s.touchpoint_eq_point_rev, touchpoint, touchpoint_eq_point_rev, vectorSpan, vsub_mem_directi
-/
lemma ExcenterExists.touchpoint_injective {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) : Function.Injective (s.touchpoint signs) := by
  intro i j hij
  by_contra hne
  by_cases hn1 : n = 1
  · subst hn1
    rw [s.touchpoint_eq_point_rev signs i]; rw [s.touchpoint_eq_point_rev signs j] at hij
    apply s.independent.injective.ne hne
    convert! hij.symm <;> clear hij <;> decide +revert
  · suffices s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points))ᗮ by
      have h' : s.excenter signs -ᵥ s.touchpoint signs i in (vectorSpan Real (Set.range s.points)) := by
        rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
      have h0 : s.excenter signs -ᵥ s.touchpoint signs i = 0 := by
        rw [← Submodule.mem_bot Real]; rw [← Submodule.inf_orthogonal_eq_bot (vectorSpan Real (Set.range s.points))]
        exact ⟨h', this⟩
      rw [← norm_eq_zero]; rw [← dist_eq_norm_vsub]; rw [h.dist_excenter] at h0
      exact h.exradius_pos.ne' h0
    obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    have hu : Set.range s.points =
        Set.range (s.faceOpposite i).points union Set.range (s.faceOpposite j).points := by
      simp only [range_faceOpposite_points, ← Set.image_union, ← Set.compl_inter]
      convert! Set.image_univ.symm
      simp [Ne.symm hne]
    rw [hu]; rw [range_faceOpposite_points]; rw [range_faceOpposite_points]; rw [AffineSubspace.vectorSpan_union_of_mem_of_mem Real (p := s.points k)
        (Set.mem_image_of_mem _ (by simp [hki])) (Set.mem_image_of_mem _ (by simp [hkj])),
      ← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · rw [← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
    · rw [hij, ← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
lemma `touchpoint_empty_injective` / 引理 `touchpoint_empty_injective`

English:
lemma touchpoint_empty_injective
  statement: Function.Injective (s.touchpoint ∅)
  proof: s.excenterExists_empty.touchpoint_injective

中文:
引理 touchpoint_empty_injective
  结论: 函数.单射 (s.touchpoint ∅)
  证明: s.excenterExists_empty.touchpoint_injective

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.touchpoint_injective, touchpoint_injective
-/
lemma touchpoint_empty_injective : Function.Injective (s.touchpoint ∅) :=
  s.excenterExists_empty.touchpoint_injective

variable {s} in
/--
lemma `ExcenterExists.touchpoint_notMem_affineSpan_of_ne` / 引理 `ExcenterExists.touchpoint_notMem_affineSpan_of_ne`

English:
lemma ExcenterExists.touchpoint_notMem_affineSpan_of_ne
  statement: {signs : Finset (Fin (n + 1))}
  proof: fun hm => h.touchpoint_injective.ne hne
    ((h.isTangentAt_touchpoint j).eq_of_mem_of_mem (h.touchpoint_mem_exsphere i) hm)

中文:
引理 ExcenterExists.touchpoint_notMem_affineSpan_of_ne
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: fun hm => h.touchpoint_injective.ne hne
    ((h.isTangentAt_touchpoint j).eq_of_mem_of_mem (h.touchpoint_mem_exsphere i) hm)

Depends on / 依赖: eq_of_mem_of_mem, h.isTangentAt_touchpoint, h.touchpoint_injective.ne, h.touchpoint_mem_exsphere, isTangentAt_touchpoint, touchpoint_injective, touchpoint_mem_exsphere
-/
lemma ExcenterExists.touchpoint_notMem_affineSpan_of_ne {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i != j) :
    s.touchpoint signs i ∉ affineSpan Real (Set.range (s.faceOpposite j).points) :=
  fun hm => h.touchpoint_injective.ne hne
    ((h.isTangentAt_touchpoint j).eq_of_mem_of_mem (h.touchpoint_mem_exsphere i) hm)

/--
lemma `touchpoint_empty_notMem_affineSpan_of_ne` / 引理 `touchpoint_empty_notMem_affineSpan_of_ne`

English:
lemma touchpoint_empty_notMem_affineSpan_of_ne
  given: {i j : Fin (n + 1)} (hne : i != j)
  proof: s.excenterExists_empty.touchpoint_notMem_affineSpan_of_ne hne

中文:
引理 touchpoint_empty_notMem_affineSpan_of_ne
  条件: {i j : 有限集 (n + 1)} (hne : i != j)
  证明: s.excenterExists_empty.touchpoint_notMem_affineSpan_of_ne hne

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.touchpoint_notMem_affineSpan_of_ne, touchpoint_notMem_affineSpan_of_ne
-/
lemma touchpoint_empty_notMem_affineSpan_of_ne {i j : Fin (n + 1)} (hne : i != j) :
    s.touchpoint ∅ i ∉ affineSpan Real (Set.range (s.faceOpposite j).points) :=
  s.excenterExists_empty.touchpoint_notMem_affineSpan_of_ne hne

set_option backward.isDefEq.respectTransparency false in
variable {s} in
/--
lemma `ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint` / 引理 `ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint`

English:
lemma ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  have hc : ContinuousOn (fun (t : Real) => SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) t)))
      (Set.Icc 0 1) := by
    refine continuousOn_of_forall_continuousAt
      fun t ht => ((continuousAt_sign_of_ne_zero ?_).comp
        (((s.signedInfDist j).cont.comp ?_).continuousAt))
    · intro h0
      rw [← abs_eq_zero]; rw [abs_signedInfDist_eq_dist_of_mem_affineSpan_range] at h0
      · rw [orthogonalProjectionSpan, dist_orthogonalProjection_eq_zero_iff] at h0
        by_cases ht1 : t = 1
        · subst ht1
          rw [AffineMap.lineMap_apply_one] at h0
          exact h.touchpoint_notMem_affineSpan_of_ne hne h0
        · refine (h.isTangentAt_touchpoint j).isTangent.notMem_of_dist_lt ?_ h0
          simp only [exsphere_center, dist_lineMap_left, Real.norm_eq_abs, h.dist_excenter,
            exsphere_radius, h.exradius_pos, mul_lt_iff_lt_one_left]
          rw [abs_lt]
          rcases ht with ⟨ht0, ht1'⟩
          exact ⟨by linarith, ht1'.lt_of_ne ht1⟩
      · exact AffineMap.lineMap_mem _ h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
    · rw [← ContinuousAffineMap.lineMap_toAffineMap]
      exact ContinuousAffineMap.cont _
  refine ((isConnected_Icc zero_le_one).image _ hc).isPreconnected.subsingleton
    (Set.mem_image_of_mem _ hr) ?_
  convert! Set.mem_image_of_mem _ (Set.left_mem_Icc.2 (zero_le_one' Real))
  simp

中文:
引理 ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  have hc : ContinuousOn (fun (t : Real) => SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) t)))
      (Set.Icc 0 1) := by
    refine continuousOn_of_forall_continuousAt
      fun t ht => ((continuousAt_sign_of_ne_zero ?_).comp
        (((s.signedInfDist j).cont.comp ?_).continuousAt))
    · intro h0
      rw [← abs_eq_zero]; rw [abs_signedInfDist_eq_dist_of_mem_affineSpan_range] at h0
      · rw [orthogonalProjectionSpan, dist_orthogonalProjection_eq_zero_iff] at h0
        by_cases ht1 : t = 1
        · subst ht1
          rw [AffineMap.lineMap_apply_one] at h0
          exact h.touchpoint_notMem_affineSpan_of_ne hne h0
        · refine (h.isTangentAt_touchpoint j).isTangent.notMem_of_dist_lt ?_ h0
          simp only [exsphere_center, dist_lineMap_left, Real.norm_eq_abs, h.dist_excenter,
            exsphere_radius, h.exradius_pos, mul_lt_iff_lt_one_left]
          rw [abs_lt]
          rcases ht with ⟨ht0, ht1'⟩
          exact ⟨by linarith, ht1'.lt_of_ne ht1⟩
      · exact AffineMap.lineMap_mem _ h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
    · rw [← ContinuousAffineMap.lineMap_toAffineMap]
      exact ContinuousAffineMap.cont _
  refine ((isConnected_Icc zero_le_one).image _ hc).isPreconnected.subsingleton
    (Set.mem_image_of_mem _ hr) ?_
  convert! Set.mem_image_of_mem _ (Set.left_mem_Icc.2 (zero_le_one' Real))
  simp

Depends on / 依赖: AffineMap, AffineMap.lineMap, ContinuousOn, Set.Icc, SignType, SignType.sign, abs_eq_zero, abs_signedInfDist_eq_dist_of_mem_affineSpan_range, cont.comp, continuousAt, continuousAt_sign_of_ne_zero, continuousOn_of_forall_continuousAt, dist_orthogonalProjection_eq_zero_iff, excenter, lineMap, orthogonalProjectionSpan, s.excenter, s.signedInfDist, s.touchpoint, signedInfDist
-/
lemma ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i != j) {r : Real} (hr : r in Set.Icc 0 1) :
    SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) r)) =
      SignType.sign (s.signedInfDist j (s.excenter signs)) := by
  have hc : ContinuousOn (fun (t : Real) => SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) t)))
      (Set.Icc 0 1) := by
    refine continuousOn_of_forall_continuousAt
      fun t ht => ((continuousAt_sign_of_ne_zero ?_).comp
        (((s.signedInfDist j).cont.comp ?_).continuousAt))
    · intro h0
      rw [← abs_eq_zero]; rw [abs_signedInfDist_eq_dist_of_mem_affineSpan_range] at h0
      · rw [orthogonalProjectionSpan, dist_orthogonalProjection_eq_zero_iff] at h0
        by_cases ht1 : t = 1
        · subst ht1
          rw [AffineMap.lineMap_apply_one] at h0
          exact h.touchpoint_notMem_affineSpan_of_ne hne h0
        · refine (h.isTangentAt_touchpoint j).isTangent.notMem_of_dist_lt ?_ h0
          simp only [exsphere_center, dist_lineMap_left, Real.norm_eq_abs, h.dist_excenter,
            exsphere_radius, h.exradius_pos, mul_lt_iff_lt_one_left]
          rw [abs_lt]
          rcases ht with ⟨ht0, ht1'⟩
          exact ⟨by linarith, ht1'.lt_of_ne ht1⟩
      · exact AffineMap.lineMap_mem _ h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
    · rw [← ContinuousAffineMap.lineMap_toAffineMap]
      exact ContinuousAffineMap.cont _
  refine ((isConnected_Icc zero_le_one).image _ hc).isPreconnected.subsingleton
    (Set.mem_image_of_mem _ hr) ?_
  convert! Set.mem_image_of_mem _ (Set.left_mem_Icc.2 (zero_le_one' Real))
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sign_signedInfDist_lineMap_incenter_touchpoint` / 引理 `sign_signedInfDist_lineMap_incenter_touchpoint`

English:
lemma sign_signedInfDist_lineMap_incenter_touchpoint
  statement: {i j : Fin (n + 1)} (hne : i != j) {r : Real}
  proof: s.excenterExists_empty.sign_signedInfDist_lineMap_excenter_touchpoint hne hr

中文:
引理 sign_signedInfDist_lineMap_incenter_touchpoint
  结论: {i j : 有限集 (n + 1)} (hne : i != j) {r : 实数}
  证明: s.excenterExists_empty.sign_signedInfDist_lineMap_excenter_touchpoint hne hr

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.sign_signedInfDist_lineMap_excenter_touchpoint, sign_signedInfDist_lineMap_excenter_touchpoint
-/
lemma sign_signedInfDist_lineMap_incenter_touchpoint {i j : Fin (n + 1)} (hne : i != j) {r : Real}
    (hr : r in Set.Icc 0 1) :
    SignType.sign
      (s.signedInfDist j (AffineMap.lineMap s.incenter (s.touchpoint ∅ i) r)) =
      SignType.sign (s.signedInfDist j s.incenter) :=
  s.excenterExists_empty.sign_signedInfDist_lineMap_excenter_touchpoint hne hr

variable {s} in
/--
lemma `ExcenterExists.sign_signedInfDist_touchpoint` / 引理 `ExcenterExists.sign_signedInfDist_touchpoint`

English:
lemma ExcenterExists.sign_signedInfDist_touchpoint
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  rw [← h.sign_signedInfDist_lineMap_excenter_touchpoint hne (r := 1) ⟨zero_le_one]; rw [le_rfl⟩]
  simp

中文:
引理 ExcenterExists.sign_signedInfDist_touchpoint
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  rw [← h.sign_signedInfDist_lineMap_excenter_touchpoint hne (r := 1) ⟨zero_le_one]; rw [le_rfl⟩]
  simp

Depends on / 依赖: h.sign_signedInfDist_lineMap_excenter_touchpoint, le_rfl, sign_signedInfDist_lineMap_excenter_touchpoint, zero_le_one
-/
lemma ExcenterExists.sign_signedInfDist_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.signedInfDist j (s.touchpoint signs i)) =
      SignType.sign (s.signedInfDist j (s.excenter signs)) := by
  rw [← h.sign_signedInfDist_lineMap_excenter_touchpoint hne (r := 1) ⟨zero_le_one]; rw [le_rfl⟩]
  simp

/--
lemma `sign_signedInfDist_touchpoint_empty` / 引理 `sign_signedInfDist_touchpoint_empty`

English:
lemma sign_signedInfDist_touchpoint_empty
  given: {i j : Fin (n + 1)} (hne : i != j)
  proof: s.excenterExists_empty.sign_signedInfDist_touchpoint hne

中文:
引理 sign_signedInfDist_touchpoint_empty
  条件: {i j : 有限集 (n + 1)} (hne : i != j)
  证明: s.excenterExists_empty.sign_signedInfDist_touchpoint hne

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.sign_signedInfDist_touchpoint, sign_signedInfDist_touchpoint
-/
lemma sign_signedInfDist_touchpoint_empty {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.signedInfDist j (s.touchpoint ∅ i)) =
      SignType.sign (s.signedInfDist j s.incenter) :=
  s.excenterExists_empty.sign_signedInfDist_touchpoint hne

/--
Definition of `touchpointWeights` / `touchpointWeights` 的定义

English:
definition touchpointWeights
  signature: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  body: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose

中文:
定义 touchpointWeights
  签名: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  定义体: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose

Depends on / 依赖: eq_affineCombination_of_mem_affineSpan_of_fintype, s.touchpoint_mem_affineSpan_simplex, touchpoint_mem_affineSpan_simplex
-/
def touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Fin (n + 1) -> Real :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose

/--
lemma `sum_touchpointWeights` / 引理 `sum_touchpointWeights`

English:
lemma sum_touchpointWeights
  given: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  proof: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.1

中文:
引理 sum_touchpointWeights
  条件: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  证明: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.1
-/
@[simp] lemma sum_touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    ∑ j, s.touchpointWeights signs i j = 1 :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.1

/--
lemma `affineCombination_touchpointWeights` / 引理 `affineCombination_touchpointWeights`

English:
lemma affineCombination_touchpointWeights
  given: (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
  proof: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.2.symm

中文:
引理 affineCombination_touchpointWeights
  条件: (signs : 有限集 (有限集 (n + 1))) (i : 有限集 (n + 1))
  证明: (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.2.symm
-/
@[simp] lemma affineCombination_touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    Finset.univ.affineCombination Real s.points (s.touchpointWeights signs i) = s.touchpoint signs i :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.2.symm

variable {s} in
/--
lemma `affineCombination_eq_touchpoint_iff` / 引理 `affineCombination_eq_touchpoint_iff`

English:
lemma affineCombination_eq_touchpoint_iff
  statement: {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)}
  proof: by
  constructor
  · rw [← s.affineCombination_touchpointWeights]
    exact fun h => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw (s.sum_touchpointWeights _ _) h
  · rintro rfl
    simp

中文:
引理 affineCombination_eq_touchpoint_iff
  结论: {signs : 有限集 (有限集 (n + 1))} {i : 有限集 (n + 1)}
  证明: by
  constructor
  · rw [← s.affineCombination_touchpointWeights]
    exact fun h => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw (s.sum_touchpointWeights _ _) h
  · rintro rfl
    simp
-/
@[simp] lemma affineCombination_eq_touchpoint_iff {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)}
    {w : Fin (n + 1) -> Real} (hw : ∑ j, w j = 1) :
    Finset.univ.affineCombination Real s.points w = s.touchpoint signs i ↔
      w = s.touchpointWeights signs i := by
  constructor
  · rw [← s.affineCombination_touchpointWeights]
    exact fun h => (affineIndependent_iff_eq_of_fintype_affineCombination_eq Real s.points).1
      s.independent _ _ hw (s.sum_touchpointWeights _ _) h
  · rintro rfl
    simp

/--
lemma `touchpointWeights_reindex` / 引理 `touchpointWeights_reindex`

English:
lemma touchpointWeights_reindex
  statement: (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
  proof: by
  rw [eq_comm]; rw [← affineCombination_eq_touchpoint_iff]
  · rw [touchpoint_reindex, ← affineCombination_touchpointWeights, reindex]
    dsimp only
    rw [← Equiv.coe_toEmbedding]; rw [← Finset.affineCombination_map]
    simp
  · rw [Finset.sum_comp_equiv]
    simp

中文:
引理 touchpointWeights_reindex
  结论: (e : 有限集 (n + 1) ≃ 有限集 (m + 1)) (signs : 有限集 (有限集 (m + 1)))
  证明: by
  rw [eq_comm]; rw [← affineCombination_eq_touchpoint_iff]
  · rw [touchpoint_reindex, ← affineCombination_touchpointWeights, reindex]
    dsimp only
    rw [← Equiv.coe_toEmbedding]; rw [← Finset.affineCombination_map]
    simp
  · rw [Finset.sum_comp_equiv]
    simp

Depends on / 依赖: Equiv.coe_toEmbedding, Finset, Finset.affineCombination_map, Finset.sum_comp_equiv, affineCombination_eq_touchpoint_iff, affineCombination_map, affineCombination_touchpointWeights, coe_toEmbedding, eq_comm, reindex, sum_comp_equiv, touchpoint_reindex
-/
lemma touchpointWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).touchpointWeights signs i =
      s.touchpointWeights (signs.map e.symm) (e.symm i) ∘ e.symm := by
  rw [eq_comm]; rw [← affineCombination_eq_touchpoint_iff]
  · rw [touchpoint_reindex, ← affineCombination_touchpointWeights, reindex]
    dsimp only
    rw [← Equiv.coe_toEmbedding]; rw [← Finset.affineCombination_map]
    simp
  · rw [Finset.sum_comp_equiv]
    simp

variable {s} in
/--
lemma `ExcenterExists.touchpointWeights_map` / 引理 `ExcenterExists.touchpointWeights_map`

English:
lemma ExcenterExists.touchpointWeights_map
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  ext i : 1
  rw [← affineCombination_eq_touchpoint_iff
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _)]
  have hc := (s.map f.toAffineMap f.injective).affineCombination_touchpointWeights signs i
  rwa [h.touchpoint_map, map_points, ← Finset.univ.map_affineCombination _ _
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _), AffineIsometry.coe_toAffineMap,
    AffineIsometry.map_eq_iff] at hc

中文:
引理 ExcenterExists.touchpointWeights_map
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  ext i : 1
  rw [← affineCombination_eq_touchpoint_iff
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _)]
  have hc := (s.map f.toAffineMap f.injective).affineCombination_touchpointWeights signs i
  rwa [h.touchpoint_map, map_points, ← Finset.univ.map_affineCombination _ _
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _), AffineIsometry.coe_toAffineMap,
    AffineIsometry.map_eq_iff] at hc
-/
@[simp] lemma ExcenterExists.touchpointWeights_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).touchpointWeights signs = s.touchpointWeights signs := by
  ext i : 1
  rw [← affineCombination_eq_touchpoint_iff
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _)]
  have hc := (s.map f.toAffineMap f.injective).affineCombination_touchpointWeights signs i
  rwa [h.touchpoint_map, map_points, ← Finset.univ.map_affineCombination _ _
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _), AffineIsometry.coe_toAffineMap,
    AffineIsometry.map_eq_iff] at hc

variable {s} in
/--
lemma `ExcenterExists.touchpointWeights_restrict` / 引理 `ExcenterExists.touchpointWeights_restrict`

English:
lemma ExcenterExists.touchpointWeights_restrict
  statement: {signs : Finset (Fin (n + 1))}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpointWeights signs = s.touchpointWeights signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpointWeights_map S.subtypeₐᵢ).symm

中文:
引理 ExcenterExists.touchpointWeights_restrict
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpointWeights signs = s.touchpointWeights signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpointWeights_map S.subtypeₐᵢ).symm
-/
@[simp] lemma ExcenterExists.touchpointWeights_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpointWeights signs = s.touchpointWeights signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpointWeights_map S.subtypeₐᵢ).symm

variable {s} in
/--
lemma `ExcenterExists.sign_touchpointWeights` / 引理 `ExcenterExists.sign_touchpointWeights`

English:
lemma ExcenterExists.sign_touchpointWeights
  statement: {signs : Finset (Fin (n + 1))}
  proof: by
  have hs := h.sign_signedInfDist_touchpoint hne
  rw [← s.affineCombination_touchpointWeights signs i]; rw [h.sign_signedInfDist_excenter]; rw [s.signedInfDist_affineCombination j (by simp)] at hs
  rw [← hs]; rw [sign_mul]
  convert! (mul_one _).symm
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

中文:
引理 ExcenterExists.sign_touchpointWeights
  结论: {signs : 有限集 (有限集 (n + 1))}
  证明: by
  have hs := h.sign_signedInfDist_touchpoint hne
  rw [← s.affineCombination_touchpointWeights signs i]; rw [h.sign_signedInfDist_excenter]; rw [s.signedInfDist_affineCombination j (by simp)] at hs
  rw [← hs]; rw [sign_mul]
  convert! (mul_one _).symm
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

Depends on / 依赖: affineCombination_touchpointWeights, convert, dist_eq_norm_vsub, h.sign_signedInfDist_excenter, h.sign_signedInfDist_touchpoint, height_pos, mul_one, s.affineCombination_touchpointWeights, s.height_pos, s.signedInfDist_affineCombination, sign_eq_one_iff, sign_mul, sign_signedInfDist_excenter, sign_signedInfDist_touchpoint, signedInfDist_affineCombination
-/
lemma ExcenterExists.sign_touchpointWeights {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.touchpointWeights signs i j) = SignType.sign (s.excenterWeights signs j) := by
  have hs := h.sign_signedInfDist_touchpoint hne
  rw [← s.affineCombination_touchpointWeights signs i]; rw [h.sign_signedInfDist_excenter]; rw [s.signedInfDist_affineCombination j (by simp)] at hs
  rw [← hs]; rw [sign_mul]
  convert! (mul_one _).symm
  rw [sign_eq_one_iff]; rw [← dist_eq_norm_vsub]
  exact s.height_pos _

/--
lemma `sign_touchpointWeights_empty` / 引理 `sign_touchpointWeights_empty`

English:
lemma sign_touchpointWeights_empty
  given: {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  rw [s.excenterExists_empty.sign_touchpointWeights hne]
  simp

中文:
引理 sign_touchpointWeights_empty
  条件: {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  rw [s.excenterExists_empty.sign_touchpointWeights hne]
  simp

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.sign_touchpointWeights, sign_touchpointWeights
-/
lemma sign_touchpointWeights_empty {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.touchpointWeights ∅ i j) = 1 := by
  rw [s.excenterExists_empty.sign_touchpointWeights hne]
  simp

variable {s} in
/--
lemma `touchpointWeights_eq_zero` / 引理 `touchpointWeights_eq_zero`

English:
lemma touchpointWeights_eq_zero
  given: {signs : Finset (Fin (n + 1))} (i : Fin (n + 1))
  proof: by
  refine s.independent.eq_zero_of_affineCombination_mem_affineSpan
    (s.sum_touchpointWeights signs i) ?_ (Finset.mem_univ _)
    (Set.notMem_compl_iff.2 (Set.mem_singleton _))
  rw [s.affineCombination_touchpointWeights]
  convert! s.touchpoint_mem_affineSpan _ _
  simp

中文:
引理 touchpointWeights_eq_zero
  条件: {signs : 有限集 (有限集 (n + 1))} (i : 有限集 (n + 1))
  证明: by
  refine s.independent.eq_zero_of_affineCombination_mem_affineSpan
    (s.sum_touchpointWeights signs i) ?_ (Finset.mem_univ _)
    (Set.notMem_compl_iff.2 (Set.mem_singleton _))
  rw [s.affineCombination_touchpointWeights]
  convert! s.touchpoint_mem_affineSpan _ _
  simp
-/
@[simp] lemma touchpointWeights_eq_zero {signs : Finset (Fin (n + 1))} (i : Fin (n + 1)) :
    s.touchpointWeights signs i i = 0 := by
  refine s.independent.eq_zero_of_affineCombination_mem_affineSpan
    (s.sum_touchpointWeights signs i) ?_ (Finset.mem_univ _)
    (Set.notMem_compl_iff.2 (Set.mem_singleton _))
  rw [s.affineCombination_touchpointWeights]
  convert! s.touchpoint_mem_affineSpan _ _
  simp

/--
lemma `touchpointWeights_empty_pos` / 引理 `touchpointWeights_empty_pos`

English:
lemma touchpointWeights_empty_pos
  given: {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_empty hne

中文:
引理 touchpointWeights_empty_pos
  条件: {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_empty hne

Depends on / 依赖: s.sign_touchpointWeights_empty, sign_eq_one_iff, sign_touchpointWeights_empty
-/
lemma touchpointWeights_empty_pos {i j : Fin (n + 1)} (hne : i != j) :
    0 < s.touchpointWeights ∅ i j := by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_empty hne

attribute [local instance] Nat.AtLeastTwo.neZero_sub_one

/--
lemma `touchpoint_empty_mem_interior_faceOpposite` / 引理 `touchpoint_empty_mem_interior_faceOpposite`

English:
lemma touchpoint_empty_mem_interior_faceOpposite
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_empty_pos (Ne.symm hj)

中文:
引理 touchpoint_empty_mem_interior_faceOpposite
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_empty_pos (Ne.symm hj)

Depends on / 依赖: Decidable, Decidable.not_not, Finset, Finset.mem_compl, Finset.mem_singleton, Ne.symm, affineCombination_mem_interior_face_iff_pos, affineCombination_touchpointWeights, and_true, faceOpposite, forall_eq, mem_compl, mem_singleton, not_not, s.affineCombination_mem_interior_face_iff_pos, s.sum_touchpointWeights, s.touchpointWeights_empty_pos, sum_touchpointWeights, touchpointWeights_empty_pos, touchpointWeights_eq_zero
-/
lemma touchpoint_empty_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.touchpoint ∅ i in (s.faceOpposite i).interior := by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_empty_pos (Ne.symm hj)

/--
lemma `sign_touchpointWeights_singleton_pos` / 引理 `sign_touchpointWeights_singleton_pos`

English:
lemma sign_touchpointWeights_singleton_pos
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne]; rw [s.sign_excenterWeights_singleton_pos hne]

中文:
引理 sign_touchpointWeights_singleton_pos
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne]; rw [s.sign_excenterWeights_singleton_pos hne]

Depends on / 依赖: excenterExists_singleton, s.excenterExists_singleton, s.sign_excenterWeights_singleton_pos, sign_excenterWeights_singleton_pos, sign_touchpointWeights
-/
lemma sign_touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.touchpointWeights {i} i j) = 1 := by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne]; rw [s.sign_excenterWeights_singleton_pos hne]

/--
lemma `touchpointWeights_singleton_pos` / 引理 `touchpointWeights_singleton_pos`

English:
lemma touchpointWeights_singleton_pos
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_singleton_pos hne

中文:
引理 touchpointWeights_singleton_pos
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_singleton_pos hne

Depends on / 依赖: s.sign_touchpointWeights_singleton_pos, sign_eq_one_iff, sign_touchpointWeights_singleton_pos
-/
lemma touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) :
    0 < s.touchpointWeights {i} i j := by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_singleton_pos hne

/--
lemma `touchpoint_singleton_mem_interior_faceOpposite` / 引理 `touchpoint_singleton_mem_interior_faceOpposite`

English:
lemma touchpoint_singleton_mem_interior_faceOpposite
  given: [Nat.AtLeastTwo n] (i : Fin (n + 1))
  proof: by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_singleton_pos (Ne.symm hj)

中文:
引理 touchpoint_singleton_mem_interior_faceOpposite
  条件: [自然数.AtLeastTwo n] (i : 有限集 (n + 1))
  证明: by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_singleton_pos (Ne.symm hj)

Depends on / 依赖: Decidable, Decidable.not_not, Finset, Finset.mem_compl, Finset.mem_singleton, Ne.symm, affineCombination_mem_interior_face_iff_pos, affineCombination_touchpointWeights, and_true, faceOpposite, forall_eq, mem_compl, mem_singleton, not_not, s.affineCombination_mem_interior_face_iff_pos, s.sum_touchpointWeights, s.touchpointWeights_singleton_pos, sum_touchpointWeights, touchpointWeights_eq_zero, touchpointWeights_singleton_pos
-/
lemma touchpoint_singleton_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.touchpoint {i} i in (s.faceOpposite i).interior := by
  rw [faceOpposite]; rw [← affineCombination_touchpointWeights]; rw [s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_singleton_pos (Ne.symm hj)

/--
lemma `sign_touchpointWeights_singleton_neg` / 引理 `sign_touchpointWeights_singleton_neg`

English:
lemma sign_touchpointWeights_singleton_neg
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne.symm]; rw [s.sign_excenterWeights_singleton_neg]

中文:
引理 sign_touchpointWeights_singleton_neg
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne.symm]; rw [s.sign_excenterWeights_singleton_neg]

Depends on / 依赖: excenterExists_singleton, hne.symm, s.excenterExists_singleton, s.sign_excenterWeights_singleton_neg, sign_excenterWeights_singleton_neg, sign_touchpointWeights
-/
lemma sign_touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) :
    SignType.sign (s.touchpointWeights {i} j i) = -1 := by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne.symm]; rw [s.sign_excenterWeights_singleton_neg]

/--
lemma `touchpointWeights_singleton_neg` / 引理 `touchpointWeights_singleton_neg`

English:
lemma touchpointWeights_singleton_neg
  given: [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j)
  proof: by
  simpa [sign_eq_neg_one_iff] using s.sign_touchpointWeights_singleton_neg hne

中文:
引理 touchpointWeights_singleton_neg
  条件: [自然数.AtLeastTwo n] {i j : 有限集 (n + 1)} (hne : i != j)
  证明: by
  simpa [sign_eq_neg_one_iff] using s.sign_touchpointWeights_singleton_neg hne

Depends on / 依赖: s.sign_touchpointWeights_singleton_neg, sign_eq_neg_one_iff, sign_touchpointWeights_singleton_neg
-/
lemma touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) :
    s.touchpointWeights {i} j i < 0 := by
  simpa [sign_eq_neg_one_iff] using s.sign_touchpointWeights_singleton_neg hne

variable {s} in
/--
lemma `ExcenterExists.touchpoint_ne_point` / 引理 `ExcenterExists.touchpoint_ne_point`

English:
lemma ExcenterExists.touchpoint_ne_point
  statement: [Nat.AtLeastTwo n] {signs : Finset (Fin (n + 1))}
  proof: by
  intro he
  rw [eq_comm]; rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ _)]; rw [affineCombination_eq_touchpoint_iff (Fintype.sum_pi_single' _ _)] at he
  have : 1 < n := Nat.AtLeastTwo.one_lt
  obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
  have he' := congr(SignType.sign ($he k))
  rw [Pi.single_eq_of_ne hkj]; rw [sign_zero]; rw [eq_comm]; rw [h.sign_touchpointWeights hki.symm]; rw [sign_eq_zero_iff]; rw [excenterWeights] at he'
  rw [ExcenterExists] at h
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, h, false_or] at he'
  rw [excenterWeightsUnnorm] at he'
  by_cases hk : k in signs <;> simp [hk, (s.height_pos k).ne'] at he'

中文:
引理 ExcenterExists.touchpoint_ne_point
  结论: [自然数.AtLeastTwo n] {signs : 有限集 (有限集 (n + 1))}
  证明: by
  intro he
  rw [eq_comm]; rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ _)]; rw [affineCombination_eq_touchpoint_iff (Fintype.sum_pi_single' _ _)] at he
  have : 1 < n := Nat.AtLeastTwo.one_lt
  obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
  have he' := congr(SignType.sign ($he k))
  rw [Pi.single_eq_of_ne hkj]; rw [sign_zero]; rw [eq_comm]; rw [h.sign_touchpointWeights hki.symm]; rw [sign_eq_zero_iff]; rw [excenterWeights] at he'
  rw [ExcenterExists] at h
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, h, false_or] at he'
  rw [excenterWeightsUnnorm] at he'
  by_cases hk : k in signs <;> simp [hk, (s.height_pos k).ne'] at he'

Depends on / 依赖: AtLeastTwo, Fin.exists_ne_and_ne_of_two_lt, Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, Nat.AtLeastTwo.one_lt, Pi.single_eq_of_ne, SignType, SignType.sign, affineCombination_eq_touchpoint_iff, affineCombination_piSingle, eq_comm, excenterWeights, exists_ne_and_ne_of_two_lt, h.sign_touchpointWeights, hki.symm, mem_univ, one_lt
-/
lemma ExcenterExists.touchpoint_ne_point [Nat.AtLeastTwo n] {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i j : Fin (n + 1)) : s.touchpoint signs i != s.points j := by
  intro he
  rw [eq_comm]; rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ _)]; rw [affineCombination_eq_touchpoint_iff (Fintype.sum_pi_single' _ _)] at he
  have : 1 < n := Nat.AtLeastTwo.one_lt
  obtain ⟨k, hki, hkj⟩ : exists k, k != i ∧ k != j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
  have he' := congr(SignType.sign ($he k))
  rw [Pi.single_eq_of_ne hkj]; rw [sign_zero]; rw [eq_comm]; rw [h.sign_touchpointWeights hki.symm]; rw [sign_eq_zero_iff]; rw [excenterWeights] at he'
  rw [ExcenterExists] at h
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, h, false_or] at he'
  rw [excenterWeightsUnnorm] at he'
  by_cases hk : k in signs <;> simp [hk, (s.height_pos k).ne'] at he'

/--
lemma `touchpoint_empty_ne_point` / 引理 `touchpoint_empty_ne_point`

English:
lemma touchpoint_empty_ne_point
  given: [Nat.AtLeastTwo n] (i j : Fin (n + 1))
  proof: s.excenterExists_empty.touchpoint_ne_point i j

中文:
引理 touchpoint_empty_ne_point
  条件: [自然数.AtLeastTwo n] (i j : 有限集 (n + 1))
  证明: s.excenterExists_empty.touchpoint_ne_point i j

Depends on / 依赖: excenterExists_empty, s.excenterExists_empty.touchpoint_ne_point, touchpoint_ne_point
-/
lemma touchpoint_empty_ne_point [Nat.AtLeastTwo n] (i j : Fin (n + 1)) :
    s.touchpoint ∅ i != s.points j :=
  s.excenterExists_empty.touchpoint_ne_point i j

end Simplex

namespace Triangle

variable (t : Triangle Real P)

/--
lemma `excenterExists` / 引理 `excenterExists`

English:
lemma excenterExists
  given: (signs : Finset (Fin 3))
  statement: t.ExcenterExists signs
  proof: by
  have h : signs = ∅ ∨ signs = ∅ᶜ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact t.excenterExists_empty
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_empty
  · exact t.excenterExists_singleton _
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_singleton _

中文:
引理 excenterExists
  条件: (signs : 有限集 (有限集 3))
  结论: t.ExcenterExists signs
  证明: by
  have h : signs = ∅ ∨ signs = ∅ᶜ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact t.excenterExists_empty
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_empty
  · exact t.excenterExists_singleton _
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_singleton _

Depends on / 依赖: Simplex, Simplex.excenterExists_compl, excenterExists_compl, excenterExists_empty, excenterExists_singleton, revert, t.excenterExists_empty, t.excenterExists_singleton
-/
lemma excenterExists (signs : Finset (Fin 3)) : t.ExcenterExists signs := by
  have h : signs = ∅ ∨ signs = ∅ᶜ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact t.excenterExists_empty
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_empty
  · exact t.excenterExists_singleton _
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_singleton _

/--
lemma `excenter_eq_incenter_or_excenter_singleton` / 引理 `excenter_eq_incenter_or_excenter_singleton`

English:
lemma excenter_eq_incenter_or_excenter_singleton
  given: (signs : Finset (Fin 3))
  proof: by
  have h : signs = ∅ ∨ signs = Finset.univ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact .inl rfl
  · exact .inl t.excenter_univ
  · exact .inr ⟨i, rfl⟩
  · refine .inr ⟨i, ?_⟩
    rw [t.excenter_compl]

中文:
引理 excenter_eq_incenter_or_excenter_singleton
  条件: (signs : 有限集 (有限集 3))
  证明: by
  have h : signs = ∅ ∨ signs = Finset.univ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact .inl rfl
  · exact .inl t.excenter_univ
  · exact .inr ⟨i, rfl⟩
  · refine .inr ⟨i, ?_⟩
    rw [t.excenter_compl]

Depends on / 依赖: Finset, Finset.univ, excenter_compl, excenter_univ, revert, t.excenter_compl, t.excenter_univ
-/
lemma excenter_eq_incenter_or_excenter_singleton (signs : Finset (Fin 3)) :
    t.excenter signs = t.incenter ∨ exists i, t.excenter signs = t.excenter {i} := by
  have h : signs = ∅ ∨ signs = Finset.univ ∨ exists i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact .inl rfl
  · exact .inl t.excenter_univ
  · exact .inr ⟨i, rfl⟩
  · refine .inr ⟨i, ?_⟩
    rw [t.excenter_compl]

/--
lemma `excenter_eq_incenter_or_excenter_singleton_of_ne` / 引理 `excenter_eq_incenter_or_excenter_singleton_of_ne`

English:
lemma excenter_eq_incenter_or_excenter_singleton_of_ne
  statement: (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3}
  proof: by
  rcases t.excenter_eq_incenter_or_excenter_singleton signs with h | ⟨i, h⟩
  · exact .inl h
  · refine .inr ?_
    rw [h]
    have : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear h; decide +revert
    grind

中文:
引理 excenter_eq_incenter_or_excenter_singleton_of_ne
  结论: (signs : 有限集 (有限集 3)) {i₁ i₂ i₃ : 有限集 3}
  证明: by
  rcases t.excenter_eq_incenter_or_excenter_singleton signs with h | ⟨i, h⟩
  · exact .inl h
  · refine .inr ?_
    rw [h]
    have : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear h; decide +revert
    grind

Depends on / 依赖: excenter_eq_incenter_or_excenter_singleton, revert, t.excenter_eq_incenter_or_excenter_singleton
-/
lemma excenter_eq_incenter_or_excenter_singleton_of_ne (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    t.excenter signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} ∨
      t.excenter signs = t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃} := by
  rcases t.excenter_eq_incenter_or_excenter_singleton signs with h | ⟨i, h⟩
  · exact .inl h
  · refine .inr ?_
    rw [h]
    have : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear h; decide +revert
    grind

/--
lemma `sSameSide_affineSpan_pair_incenter_point` / 引理 `sSameSide_affineSpan_pair_incenter_point`

English:
lemma sSameSide_affineSpan_pair_incenter_point
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  proof: by
  convert! t.sSameSide_incenter_point i₁
  simp
  grind

中文:
引理 sSameSide_affineSpan_pair_incenter_point
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  证明: by
  convert! t.sSameSide_incenter_point i₁
  simp
  grind

Depends on / 依赖: convert, sSameSide_incenter_point, t.sSameSide_incenter_point
-/
lemma sSameSide_affineSpan_pair_incenter_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
    (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SSameSide t.incenter (t.points i₁) := by
  convert! t.sSameSide_incenter_point i₁
  simp
  grind

/--
lemma `sSameSide_affineSpan_pair_point_incenter` / 引理 `sSameSide_affineSpan_pair_point_incenter`

English:
lemma sSameSide_affineSpan_pair_point_incenter
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  proof: by
  convert! t.sSameSide_point_incenter i₁
  simp
  grind

中文:
引理 sSameSide_affineSpan_pair_point_incenter
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
  证明: by
  convert! t.sSameSide_point_incenter i₁
  simp
  grind

Depends on / 依赖: convert, sSameSide_point_incenter, t.sSameSide_point_incenter
-/
lemma sSameSide_affineSpan_pair_point_incenter {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
    (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SSameSide (t.points i₁) t.incenter := by
  convert! t.sSameSide_point_incenter i₁
  simp
  grind

/--
lemma `sOppSide_affineSpan_pair_excenter_singleton_point` / 引理 `sOppSide_affineSpan_pair_excenter_singleton_point`

English:
lemma sOppSide_affineSpan_pair_excenter_singleton_point
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: by
  convert! t.sOppSide_excenter_singleton_point i₁
  simp
  grind

中文:
引理 sOppSide_affineSpan_pair_excenter_singleton_point
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂)
  证明: by
  convert! t.sOppSide_excenter_singleton_point i₁
  simp
  grind

Depends on / 依赖: convert, sOppSide_excenter_singleton_point, t.sOppSide_excenter_singleton_point
-/
lemma sOppSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SOppSide (t.excenter {i₁}) (t.points i₁) := by
  convert! t.sOppSide_excenter_singleton_point i₁
  simp
  grind

/--
lemma `sOppSide_affineSpan_pair_point_excenter_singleton` / 引理 `sOppSide_affineSpan_pair_point_excenter_singleton`

English:
lemma sOppSide_affineSpan_pair_point_excenter_singleton
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: by
  convert! t.sOppSide_point_excenter_singleton i₁
  simp
  grind

中文:
引理 sOppSide_affineSpan_pair_point_excenter_singleton
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂)
  证明: by
  convert! t.sOppSide_point_excenter_singleton i₁
  simp
  grind

Depends on / 依赖: convert, sOppSide_point_excenter_singleton, t.sOppSide_point_excenter_singleton
-/
lemma sOppSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SOppSide (t.points i₁) (t.excenter {i₁}) := by
  convert! t.sOppSide_point_excenter_singleton i₁
  simp
  grind

/--
lemma `sSameSide_affineSpan_pair_excenter_singleton_point` / 引理 `sSameSide_affineSpan_pair_excenter_singleton_point`

English:
lemma sSameSide_affineSpan_pair_excenter_singleton_point
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: by
  convert! t.sSameSide_excenter_singleton_point h₁₂
  simp
  grind

中文:
引理 sSameSide_affineSpan_pair_excenter_singleton_point
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂)
  证明: by
  convert! t.sSameSide_excenter_singleton_point h₁₂
  simp
  grind

Depends on / 依赖: convert, sSameSide_excenter_singleton_point, t.sSameSide_excenter_singleton_point
-/
lemma sSameSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SSameSide (t.excenter {i₂}) (t.points i₁) := by
  convert! t.sSameSide_excenter_singleton_point h₁₂
  simp
  grind

/--
lemma `sSameSide_affineSpan_pair_point_excenter_singleton` / 引理 `sSameSide_affineSpan_pair_point_excenter_singleton`

English:
lemma sSameSide_affineSpan_pair_point_excenter_singleton
  statement: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: by
  convert! t.sSameSide_point_excenter_singleton h₁₂
  simp
  grind

中文:
引理 sSameSide_affineSpan_pair_point_excenter_singleton
  结论: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂)
  证明: by
  convert! t.sSameSide_point_excenter_singleton h₁₂
  simp
  grind

Depends on / 依赖: convert, sSameSide_point_excenter_singleton, t.sSameSide_point_excenter_singleton
-/
lemma sSameSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃].SSameSide (t.points i₁) (t.excenter {i₂}) := by
  convert! t.sSameSide_point_excenter_singleton h₁₂
  simp
  grind

/--
lemma `affineSpan_pair_eq_orthRadius` / 引理 `affineSpan_pair_eq_orthRadius`

English:
lemma affineSpan_pair_eq_orthRadius
  statement: [Fact (Module.finrank Real V = 2)] (signs : Finset (Fin 3))
  proof: by
  convert! (t.excenterExists signs).affineSpan_faceOpposite_eq_orthRadius i₁
  have hc : {i₁}ᶜ = ({i₂, i₃} : Set (Fin 3)) := by grind
  simp [Simplex.range_faceOpposite_points, hc, Set.image_insert_eq]

中文:
引理 affineSpan_pair_eq_orthRadius
  结论: [Fact (模.finrank 实数 V = 2)] (signs : 有限集 (有限集 3))
  证明: by
  convert! (t.excenterExists signs).affineSpan_faceOpposite_eq_orthRadius i₁
  have hc : {i₁}ᶜ = ({i₂, i₃} : Set (Fin 3)) := by grind
  simp [Simplex.range_faceOpposite_points, hc, Set.image_insert_eq]

Depends on / 依赖: Set.image_insert_eq, Simplex, Simplex.range_faceOpposite_points, affineSpan_faceOpposite_eq_orthRadius, convert, excenterExists, image_insert_eq, range_faceOpposite_points, t.excenterExists
-/
lemma affineSpan_pair_eq_orthRadius [Fact (Module.finrank Real V = 2)] (signs : Finset (Fin 3))
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃] =
      (t.exsphere signs).orthRadius (t.touchpoint signs i₁) := by
  convert! (t.excenterExists signs).affineSpan_faceOpposite_eq_orthRadius i₁
  have hc : {i₁}ᶜ = ({i₂, i₃} : Set (Fin 3)) := by grind
  simp [Simplex.range_faceOpposite_points, hc, Set.image_insert_eq]

/--
lemma `affineSpan_pair_eq_orthRadius_insphere` / 引理 `affineSpan_pair_eq_orthRadius_insphere`

English:
lemma affineSpan_pair_eq_orthRadius_insphere
  statement: [Fact (Module.finrank Real V = 2)]
  proof: t.affineSpan_pair_eq_orthRadius ∅ h₁₂ h₁₃ h₂₃

中文:
引理 affineSpan_pair_eq_orthRadius_insphere
  结论: [Fact (模.finrank 实数 V = 2)]
  证明: t.affineSpan_pair_eq_orthRadius ∅ h₁₂ h₁₃ h₂₃

Depends on / 依赖: affineSpan_pair_eq_orthRadius, t.affineSpan_pair_eq_orthRadius
-/
lemma affineSpan_pair_eq_orthRadius_insphere [Fact (Module.finrank Real V = 2)]
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    line[Real, t.points i₂, t.points i₃] = t.insphere.orthRadius (t.touchpoint ∅ i₁) :=
  t.affineSpan_pair_eq_orthRadius ∅ h₁₂ h₁₃ h₂₃

/--
lemma `sbtw_touchpoint_empty` / 引理 `sbtw_touchpoint_empty`

English:
lemma sbtw_touchpoint_empty
  given: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  proof: by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_empty_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

中文:
引理 sbtw_touchpoint_empty
  条件: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  证明: by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_empty_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

Depends on / 依赖: Affine, Affine.Simplex.faceOpposite, Simplex, convert, faceOpposite, mem_interior_face_iff_sbtw, revert, t.mem_interior_face_iff_sbtw, t.touchpoint_empty_mem_interior_faceOpposite, touchpoint_empty_mem_interior_faceOpposite
-/
lemma sbtw_touchpoint_empty {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    Sbtw Real (t.points i₁) (t.touchpoint ∅ i₂) (t.points i₃) := by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_empty_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

/--
lemma `sbtw_touchpoint_singleton` / 引理 `sbtw_touchpoint_singleton`

English:
lemma sbtw_touchpoint_singleton
  given: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  proof: by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_singleton_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

中文:
引理 sbtw_touchpoint_singleton
  条件: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  证明: by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_singleton_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

Depends on / 依赖: Affine, Affine.Simplex.faceOpposite, Simplex, convert, faceOpposite, mem_interior_face_iff_sbtw, revert, t.mem_interior_face_iff_sbtw, t.touchpoint_singleton_mem_interior_faceOpposite, touchpoint_singleton_mem_interior_faceOpposite
-/
lemma sbtw_touchpoint_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    Sbtw Real (t.points i₁) (t.touchpoint {i₂} i₂) (t.points i₃) := by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_singleton_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert

/--
lemma `touchpoint_singleton_sbtw` / 引理 `touchpoint_singleton_sbtw`

English:
lemma touchpoint_singleton_sbtw
  given: {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  proof: by
  rw [← Affine.Simplex.affineCombination_touchpointWeights]
  have hw := t.sum_touchpointWeights {i₁} i₂
  rw [(by clear hw; decide +revert : (Finset.univ : Finset (Fin 3)) = {i₁]; rw [i₂]; rw [i₃})] at hw
  simp only [Nat.reduceAdd, Finset.mem_insert, h₁₂, Finset.mem_singleton, h₁₃, or_self,
    not_false_eq_true, Finset.sum_insert, h₂₃, Simplex.touchpointWeights_eq_zero,
    Finset.sum_singleton, zero_add] at hw
  have h : t.touchpointWeights {i₁} i₂ =
      Finset.affineCombinationLineMapWeights i₁ i₃ (t.touchpointWeights {i₁} i₂ i₃) := by
    ext i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear hw; decide +revert
    rcases h with rfl | rfl | rfl
    · rw [Finset.affineCombinationLineMapWeights_apply_left h₁₃]
      simp [← hw]
    · simp [h₁₂.symm, h₂₃]
    · simp [h₁₃]
  rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
    (Finset.mem_univ _)]; rw [sbtw_iff_right_ne_and_left_mem_image_Ioi]
  simp [t.independent.injective.ne h₁₃, ← hw, t.touchpointWeights_singleton_neg h₁₂]

中文:
引理 touchpoint_singleton_sbtw
  条件: {i₁ i₂ i₃ : 有限集 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
  证明: by
  rw [← Affine.Simplex.affineCombination_touchpointWeights]
  have hw := t.sum_touchpointWeights {i₁} i₂
  rw [(by clear hw; decide +revert : (Finset.univ : Finset (Fin 3)) = {i₁]; rw [i₂]; rw [i₃})] at hw
  simp only [Nat.reduceAdd, Finset.mem_insert, h₁₂, Finset.mem_singleton, h₁₃, or_self,
    not_false_eq_true, Finset.sum_insert, h₂₃, Simplex.touchpointWeights_eq_zero,
    Finset.sum_singleton, zero_add] at hw
  have h : t.touchpointWeights {i₁} i₂ =
      Finset.affineCombinationLineMapWeights i₁ i₃ (t.touchpointWeights {i₁} i₂ i₃) := by
    ext i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear hw; decide +revert
    rcases h with rfl | rfl | rfl
    · rw [Finset.affineCombinationLineMapWeights_apply_left h₁₃]
      simp [← hw]
    · simp [h₁₂.symm, h₂₃]
    · simp [h₁₃]
  rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
    (Finset.mem_univ _)]; rw [sbtw_iff_right_ne_and_left_mem_image_Ioi]
  simp [t.independent.injective.ne h₁₃, ← hw, t.touchpointWeights_singleton_neg h₁₂]

Depends on / 依赖: Affine, Affine.Simplex.affineCombination_touchpointWeights, Finset, Finset.affineCombinationLineMapWeights, Finset.mem_insert, Finset.mem_singleton, Finset.sum_insert, Finset.sum_singleton, Finset.univ, Nat.reduceAdd, Simplex, Simplex.touchpointWeights_eq_zero, affineCombinationLineMapWeights, affineCombination_touchpointWeights, mem_insert, mem_singleton, not_false_eq_true, or_self, reduceAdd, revert
-/
lemma touchpoint_singleton_sbtw {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    Sbtw Real (t.touchpoint {i₁} i₂) (t.points i₃) (t.points i₁) := by
  rw [← Affine.Simplex.affineCombination_touchpointWeights]
  have hw := t.sum_touchpointWeights {i₁} i₂
  rw [(by clear hw; decide +revert : (Finset.univ : Finset (Fin 3)) = {i₁]; rw [i₂]; rw [i₃})] at hw
  simp only [Nat.reduceAdd, Finset.mem_insert, h₁₂, Finset.mem_singleton, h₁₃, or_self,
    not_false_eq_true, Finset.sum_insert, h₂₃, Simplex.touchpointWeights_eq_zero,
    Finset.sum_singleton, zero_add] at hw
  have h : t.touchpointWeights {i₁} i₂ =
      Finset.affineCombinationLineMapWeights i₁ i₃ (t.touchpointWeights {i₁} i₂ i₃) := by
    ext i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear hw; decide +revert
    rcases h with rfl | rfl | rfl
    · rw [Finset.affineCombinationLineMapWeights_apply_left h₁₃]
      simp [← hw]
    · simp [h₁₂.symm, h₂₃]
    · simp [h₁₃]
  rw [h]; rw [Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
    (Finset.mem_univ _)]; rw [sbtw_iff_right_ne_and_left_mem_image_Ioi]
  simp [t.independent.injective.ne h₁₃, ← hw, t.touchpointWeights_singleton_neg h₁₂]

end Triangle

end Affine
