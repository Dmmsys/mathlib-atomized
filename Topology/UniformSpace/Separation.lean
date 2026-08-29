/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

Two points of a topological space are called `Inseparable`,
if their neighborhoods filter are equal.
Equivalently, `Inseparable x y` means that any open set that contains `x` must contain `y`
and vice versa.

In a uniform space, points `x` and `y` are inseparable
if and only if `(x, y)` belongs to all entourages,
see `inseparable_iff_ker_uniformity`.

A uniform space is a regular topological space,
hence separation axioms `T0Space`, `T1Space`, `T2Space`, and `T3Space`
are equivalent for uniform spaces,
and Lean typeclass search can automatically convert from one assumption to another.
We say that a uniform space is *separated*, if it satisfies these axioms.
If you need an `Iff` statement (e.g., to rewrite),
then see `R1Space.t0Space_iff_t2Space` and `RegularSpace.t0Space_iff_t3Space`.

In this file we prove several facts
that relate `Inseparable` and `Specializes` to the uniformity filter.
Most of them are simple corollaries of `Filter.HasBasis.inseparable_iff_uniformity`
for different filter bases of `𝓤 α`.

Then we study the Kolmogorov quotient `SeparationQuotient X` of a uniform space.
For a general topological space,
this quotient is defined as the quotient by `Inseparable` equivalence relation.
It is the maximal T₀ quotient of a topological space.

In case of a uniform space, we equip this quotient with a `UniformSpace` structure
that agrees with the quotient topology.
We also prove that the quotient map induces uniformity on the original space.

Finally, we turn `SeparationQuotient` into a functor
(not in terms of `CategoryTheory.Functor` to avoid extra imports)
by defining `SeparationQuotient.lift'` and `SeparationQuotient.map` operations.

## Main definitions

* `SeparationQuotient.instUniformSpace`: uniform space structure on `SeparationQuotient α`,
  where `α` is a uniform space;

* `SeparationQuotient.lift'`: given a map `f : α → β`
  from a uniform space to a separated uniform space,
  lift it to a map `SeparationQuotient α → β`;
  if the original map is not uniformly continuous, then returns a constant map.

* `SeparationQuotient.map`: given a map `f : α → β` between uniform spaces,
  returns a map `SeparationQuotient α → SeparationQuotient β`.
  If the original map is not uniformly continuous, then returns a constant map.
  Otherwise, `SeparationQuotient.map f (SeparationQuotient.mk x) = SeparationQuotient.mk (f x)`.

## Main results

* `SeparationQuotient.uniformity_eq`: the uniformity filter on `SeparationQuotient α`
  is the push forward of the uniformity filter on `α`.
* `SeparationQuotient.comap_mk_uniformity`: the quotient map `α → SeparationQuotient α`
  induces uniform space structure on the original space.
* `SeparationQuotient.uniformContinuous_lift'`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Implementation notes

This file used to contain definitions of `separationRel α` and `UniformSpace.SeparationQuotient α`.
These definitions were equal (but not definitionally equal)
to `{x : α × α | Inseparable x.1 x.2}` and `SeparationQuotient α`, respectively,
and were added to the library before their generalizations to topological spaces.

In https://github.com/leanprover-community/mathlib4/pull/10644, we migrated from these definitions
to more general `Inseparable` and `SeparationQuotient`.

## TODO

Definitions `SeparationQuotient.lift'` and `SeparationQuotient.map`
rely on `UniformSpace` structures in the domain and in the codomain.
We should generalize them to topological spaces.
This generalization will drop `UniformContinuous` assumptions in some lemmas,
and add these assumptions in other lemmas,
so it was not done in https://github.com/leanprover-community/mathlib4/pull/10644 to keep it reasonably sized.

## Keywords

uniform space, separated space, Hausdorff space, separation quotient
-/

@[expose] public section

open Filter Set Function Topology Uniformity UniformSpace

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/

instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .of_hasBasis
    (fun _ => nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun a _V hV => isClosed_ball a hV.2

/--
theorem `UniformSpace.completelyNormalSpace_of_hasAntitoneBasis` / 定理 `UniformSpace.completelyNormalSpace_of_hasAntitoneBasis`

English:
theorem UniformSpace.completelyNormalSpace_of_hasAntitoneBasis
  statement: {ι : Type*} [LinearOrder ι]
  proof: by
    let S (b : Bool) : Set α := b.casesOn (false := s) (true := t)
    have hx (b : Bool) (x : S b) : exists i, Disjoint (ball x.1 ((B i).comp (B i).inv)) (S (!b)) := by
      have hST : Disjoint (S b) (closure (S !b)) := b.casesOn (false := hsT) (true := hSt.symm)
      rw [← disjoint_nhdsSet_principal]; rw [disjoint_principal_right] at hST
      obtain ⟨U, hUu, hU⟩ := UniformSpace.mem_nhds_iff.1 (nhds_le_nhdsSet x.2 hST)
      obtain ⟨(V : SetRel α α), hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hUu
      obtain ⟨i, hi⟩ := hB.mem_iff.1 hV
      refine ⟨i, subset_compl_iff_disjoint_right.1 (subset_trans (ball_mono ?_ x.1) hU)⟩
      exact subset_trans (SetRel.comp_subset_comp hi (V.inv_eq_self ▸ (SetRel.inv_mono hi))) hVU
    choose U hU using hx
    have hUS (b : Bool) : ⋃ x, ball x.1 (B (U b x)) in nhdsSet (S b) := by
      rw [mem_nhdsSet_iff_forall]
      intro x hx
      apply mem_of_superset (ball_mem_nhds x (hB.mem (U b ⟨x, hx⟩)))
      exact subset_iUnion (fun x => ball x.1 (B (U b x))) ⟨x, hx⟩
    rw [Filter.disjoint_iff]
    refine ⟨_, hUS false, _, hUS true, ?_⟩
    have hdj (b : Bool) (x : S b) (y : S (!b)) (hxy : U b x <= U (!b) y) :
        Disjoint (ball x.1 (B (U b x))) (ball y.1 (B (U (!b) y))) := by
      rw [Set.disjoint_iff]
      intro z hz
      exact (hU b x).notMem_of_mem_left (mem_ball_comp hz.1 (hB.antitone hxy hz.2)) y.2
    simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro x y
    exact (le_total (U false x) (U true y)).elim
      (fun h => hdj false x y h) (fun h => (hdj true y x h).symm)

中文:
定理 一致空间.completelyNormalSpace_of_hasAntitoneBasis
  结论: {ι : 类型} [线性序 ι]
  证明: by
    let S (b : Bool) : Set α := b.casesOn (false := s) (true := t)
    have hx (b : Bool) (x : S b) : exists i, Disjoint (ball x.1 ((B i).comp (B i).inv)) (S (!b)) := by
      have hST : Disjoint (S b) (closure (S !b)) := b.casesOn (false := hsT) (true := hSt.symm)
      rw [← disjoint_nhdsSet_principal]; rw [disjoint_principal_right] at hST
      obtain ⟨U, hUu, hU⟩ := UniformSpace.mem_nhds_iff.1 (nhds_le_nhdsSet x.2 hST)
      obtain ⟨(V : SetRel α α), hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hUu
      obtain ⟨i, hi⟩ := hB.mem_iff.1 hV
      refine ⟨i, subset_compl_iff_disjoint_right.1 (subset_trans (ball_mono ?_ x.1) hU)⟩
      exact subset_trans (SetRel.comp_subset_comp hi (V.inv_eq_self ▸ (SetRel.inv_mono hi))) hVU
    choose U hU using hx
    have hUS (b : Bool) : ⋃ x, ball x.1 (B (U b x)) in nhdsSet (S b) := by
      rw [mem_nhdsSet_iff_forall]
      intro x hx
      apply mem_of_superset (ball_mem_nhds x (hB.mem (U b ⟨x, hx⟩)))
      exact subset_iUnion (fun x => ball x.1 (B (U b x))) ⟨x, hx⟩
    rw [Filter.disjoint_iff]
    refine ⟨_, hUS false, _, hUS true, ?_⟩
    have hdj (b : Bool) (x : S b) (y : S (!b)) (hxy : U b x <= U (!b) y) :
        Disjoint (ball x.1 (B (U b x))) (ball y.1 (B (U (!b) y))) := by
      rw [Set.disjoint_iff]
      intro z hz
      exact (hU b x).notMem_of_mem_left (mem_ball_comp hz.1 (hB.antitone hxy hz.2)) y.2
    simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro x y
    exact (le_total (U false x) (U true y)).elim
      (fun h => hdj false x y h) (fun h => (hdj true y x h).symm)

Depends on / 依赖: Disjoint, SetRel, UniformSpace, UniformSpace.mem_nhds_iff, b.casesOn, casesOn, closure, comp_symm_mem_uniformity_sets, disjoint_nhdsSet_principal, disjoint_principal_right, hSt.symm, mem_nhds_iff, nhds_le_nhdsSet
-/
theorem UniformSpace.completelyNormalSpace_of_hasAntitoneBasis {ι : Type*} [LinearOrder ι]
    {B : ι -> SetRel α α} (hB : (uniformity α).HasAntitoneBasis B) : CompletelyNormalSpace α where
  completely_normal s t hSt hsT := by
    let S (b : Bool) : Set α := b.casesOn (false := s) (true := t)
    have hx (b : Bool) (x : S b) : exists i, Disjoint (ball x.1 ((B i).comp (B i).inv)) (S (!b)) := by
      have hST : Disjoint (S b) (closure (S !b)) := b.casesOn (false := hsT) (true := hSt.symm)
      rw [← disjoint_nhdsSet_principal]; rw [disjoint_principal_right] at hST
      obtain ⟨U, hUu, hU⟩ := UniformSpace.mem_nhds_iff.1 (nhds_le_nhdsSet x.2 hST)
      obtain ⟨(V : SetRel α α), hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hUu
      obtain ⟨i, hi⟩ := hB.mem_iff.1 hV
      refine ⟨i, subset_compl_iff_disjoint_right.1 (subset_trans (ball_mono ?_ x.1) hU)⟩
      exact subset_trans (SetRel.comp_subset_comp hi (V.inv_eq_self ▸ (SetRel.inv_mono hi))) hVU
    choose U hU using hx
    have hUS (b : Bool) : ⋃ x, ball x.1 (B (U b x)) in nhdsSet (S b) := by
      rw [mem_nhdsSet_iff_forall]
      intro x hx
      apply mem_of_superset (ball_mem_nhds x (hB.mem (U b ⟨x, hx⟩)))
      exact subset_iUnion (fun x => ball x.1 (B (U b x))) ⟨x, hx⟩
    rw [Filter.disjoint_iff]
    refine ⟨_, hUS false, _, hUS true, ?_⟩
    have hdj (b : Bool) (x : S b) (y : S (!b)) (hxy : U b x <= U (!b) y) :
        Disjoint (ball x.1 (B (U b x))) (ball y.1 (B (U (!b) y))) := by
      rw [Set.disjoint_iff]
      intro z hz
      exact (hU b x).notMem_of_mem_left (mem_ball_comp hz.1 (hB.antitone hxy hz.2)) y.2
    simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro x y
    exact (le_total (U false x) (U true y)).elim
      (fun h => hdj false x y h) (fun h => (hdj true y x h).symm)

instance (priority := 100) UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity
    [(uniformity α).IsCountablyGenerated] : CompletelyNormalSpace α :=
  (has_seq_basis α).elim fun _ hB =>
    UniformSpace.completelyNormalSpace_of_hasAntitoneBasis hB.1

/--
theorem `Filter.HasBasis.specializes_iff_uniformity` / 定理 `Filter.HasBasis.specializes_iff_uniformity`

English:
theorem Filter.HasBasis.specializes_iff_uniformity
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)}
  proof: (nhds_basis_uniformity h).specializes_iff

中文:
定理 滤子.有基.specializes_iff_uniformity
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 (α × α)}
  证明: (nhds_basis_uniformity h).specializes_iff

Depends on / 依赖: nhds_basis_uniformity, specializes_iff
-/
theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ forall i, p i -> (x, y) in s i :=
  (nhds_basis_uniformity h).specializes_iff

/--
theorem `Filter.HasBasis.inseparable_iff_uniformity` / 定理 `Filter.HasBasis.inseparable_iff_uniformity`

English:
theorem Filter.HasBasis.inseparable_iff_uniformity
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)}
  proof: specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

中文:
定理 滤子.有基.inseparable_iff_uniformity
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 (α × α)}
  证明: specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

Depends on / 依赖: h.specializes_iff_uniformity, specializes_iff_inseparable, specializes_iff_inseparable.symm.trans, specializes_iff_uniformity
-/
theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ forall i, p i -> (x, y) in s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

/--
theorem `inseparable_iff_ker_uniformity` / 定理 `inseparable_iff_ker_uniformity`

English:
theorem inseparable_iff_ker_uniformity
  given: {x y : α}
  statement: Inseparable x y ↔ (x, y) in (𝓤 α).ker
  proof: (𝓤 α).basis_sets.inseparable_iff_uniformity

中文:
定理 inseparable_iff_ker_uniformity
  条件: {x y : α}
  结论: 不可分 x y ↔ (x, y) in (𝓤 α).ker
  证明: (𝓤 α).basis_sets.inseparable_iff_uniformity

Depends on / 依赖: basis_sets, basis_sets.inseparable_iff_uniformity, inseparable_iff_uniformity
-/
theorem inseparable_iff_ker_uniformity {x y : α} : Inseparable x y ↔ (x, y) in (𝓤 α).ker :=
  (𝓤 α).basis_sets.inseparable_iff_uniformity

/--
theorem `Inseparable.nhds_le_uniformity` / 定理 `Inseparable.nhds_le_uniformity`

English:
theorem Inseparable.nhds_le_uniformity
  given: {x y : α} (h : Inseparable x y)
  proof: by
  rw [h.prod rfl]
  apply nhds_le_uniformity

中文:
定理 不可分.nhds_le_uniformity
  条件: {x y : α} (h : 不可分 x y)
  证明: by
  rw [h.prod rfl]
  apply nhds_le_uniformity
-/
protected theorem Inseparable.nhds_le_uniformity {x y : α} (h : Inseparable x y) :
    𝓝 (x, y) <= 𝓤 α := by
  rw [h.prod rfl]
  apply nhds_le_uniformity

/--
theorem `inseparable_iff_clusterPt_uniformity` / 定理 `inseparable_iff_clusterPt_uniformity`

English:
theorem inseparable_iff_clusterPt_uniformity
  given: {x y : α}
  proof: by
  refine ⟨fun h => .of_nhds_le h.nhds_le_uniformity, fun h => ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
exact fun U ⟨hU, hUc⟩ => hUc _ h.mono le_principal_iff.2 hU

中文:
定理 inseparable_iff_clusterPt_uniformity
  条件: {x y : α}
  证明: by
  refine ⟨fun h => .of_nhds_le h.nhds_le_uniformity, fun h => ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
exact fun U ⟨hU, hUc⟩ => hUc _ h.mono le_principal_iff.2 hU

Depends on / 依赖: h.mono, h.nhds_le_uniformity, inseparable_iff_uniformity, isClosed_iff_clusterPt, le_principal_iff, nhds_le_uniformity, of_nhds_le, simp_rw, uniformity_hasBasis_closed, uniformity_hasBasis_closed.inseparable_iff_uniformity
-/
theorem inseparable_iff_clusterPt_uniformity {x y : α} :
    Inseparable x y ↔ ClusterPt (x, y) (𝓤 α) := by
  refine ⟨fun h => .of_nhds_le h.nhds_le_uniformity, fun h => ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
exact fun U ⟨hU, hUc⟩ => hUc _ h.mono le_principal_iff.2 hU

/--
theorem `t0Space_iff_uniformity` / 定理 `t0Space_iff_uniformity`

English:
theorem t0Space_iff_uniformity
  proof: by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker]

中文:
定理 t0Space_iff_uniformity
  证明: by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker]

Depends on / 依赖: inseparable_iff_ker_uniformity, mem_ker, t0Space_iff_inseparable
-/
theorem t0Space_iff_uniformity :
    T0Space α ↔ forall x y, (forall r in 𝓤 α, (x, y) in r) -> x = y := by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker]

/--
theorem `t0Space_iff_uniformity'` / 定理 `t0Space_iff_uniformity'`

English:
theorem t0Space_iff_uniformity'
  proof: by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]

中文:
定理 t0Space_iff_uniformity'
  证明: by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]

Depends on / 依赖: inseparable_iff_ker_uniformity, t0Space_iff_not_inseparable
-/
theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y => exists r in 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]

/--
theorem `t0Space_iff_ker_uniformity` / 定理 `t0Space_iff_ker_uniformity`

English:
theorem t0Space_iff_ker_uniformity
  statement: T0Space α ↔ (𝓤 α).ker = diagonal α
  proof: by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs => refl_mem_uniformity hs

中文:
定理 t0Space_iff_ker_uniformity
  结论: T0空间 α ↔ (𝓤 α).ker = diagonal α
  证明: by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs => refl_mem_uniformity hs

Depends on / 依赖: Filter, Filter.mem_ker, Prod.forall, diagonal_subset_iff, iff_self_and, mem_diagonal_iff, mem_ker, refl_mem_uniformity, simp_rw, subset_antisymm_iff, subset_def, t0Space_iff_uniformity
-/
theorem t0Space_iff_ker_uniformity : T0Space α ↔ (𝓤 α).ker = diagonal α := by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs => refl_mem_uniformity hs

/--
theorem `eq_of_uniformity` / 定理 `eq_of_uniformity`

English:
theorem eq_of_uniformity
  statement: {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
  proof: t0Space_iff_uniformity.mp ‹T0Space α› x y @h

中文:
定理 eq_of_uniformity
  结论: {α : 类型} [一致空间 α] [T0空间 α] {x y : α}
  证明: t0Space_iff_uniformity.mp ‹T0Space α› x y @h

Depends on / 依赖: T0Space, t0Space_iff_uniformity, t0Space_iff_uniformity.mp
-/
theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : forall {V}, V in 𝓤 α -> (x, y) in V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h

/--
theorem `eq_of_uniformity_basis` / 定理 `eq_of_uniformity_basis`

English:
theorem eq_of_uniformity_basis
  statement: {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
  proof: (hs.inseparable_iff_uniformity.2 @h).eq

中文:
定理 eq_of_uniformity_basis
  结论: {α : 类型} [一致空间 α] [T0空间 α] {ι : 类型层*}
  证明: (hs.inseparable_iff_uniformity.2 @h).eq

Depends on / 依赖: hs.inseparable_iff_uniformity, inseparable_iff_uniformity
-/
theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι -> Prop} {s : ι -> Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : forall {i}, p i -> (x, y) in s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq

/--
theorem `eq_of_forall_symmetric` / 定理 `eq_of_forall_symmetric`

English:
theorem eq_of_forall_symmetric
  statement: {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
  proof: eq_of_uniformity_basis hasBasis_symmetric (by simpa)

中文:
定理 eq_of_对任意_symmetric
  结论: {α : 类型} [一致空间 α] [T0空间 α] {x y : α}
  证明: eq_of_uniformity_basis hasBasis_symmetric (by simpa)

Depends on / 依赖: eq_of_uniformity_basis, hasBasis_symmetric
-/
theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (x, y) in V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)

/--
theorem `eq_of_clusterPt_uniformity` / 定理 `eq_of_clusterPt_uniformity`

English:
theorem eq_of_clusterPt_uniformity
  given: [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α))
  statement: x = y
  proof: (inseparable_iff_clusterPt_uniformity.2 h).eq

中文:
定理 eq_of_clusterPt_uniformity
  条件: [T0空间 α] {x y : α} (h : ClusterPt (x, y) (𝓤 α))
  结论: x = y
  证明: (inseparable_iff_clusterPt_uniformity.2 h).eq

Depends on / 依赖: inseparable_iff_clusterPt_uniformity
-/
theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  (inseparable_iff_clusterPt_uniformity.2 h).eq

/--
theorem `Filter.Tendsto.inseparable_iff_uniformity` / 定理 `Filter.Tendsto.inseparable_iff_uniformity`

English:
theorem Filter.Tendsto.inseparable_iff_uniformity
  statement: {β} {l : Filter β} [NeBot l] {f g : β -> α}
  proof: by
  refine ⟨fun h => (ha.prodMk_nhds hb).mono_right h.nhds_le_uniformity, fun h => ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prodMk_nhds hb)).mono h

中文:
定理 滤子.收敛.inseparable_iff_uniformity
  结论: {β} {l : 滤子 β} [NeBot l] {f g : β -> α}
  证明: by
  refine ⟨fun h => (ha.prodMk_nhds hb).mono_right h.nhds_le_uniformity, fun h => ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prodMk_nhds hb)).mono h

Depends on / 依赖: ClusterPt, ClusterPt.of_le_nhds, h.nhds_le_uniformity, ha.prodMk_nhds, inseparable_iff_clusterPt_uniformity, mono_right, nhds_le_uniformity, of_le_nhds, prodMk_nhds
-/
theorem Filter.Tendsto.inseparable_iff_uniformity {β} {l : Filter β} [NeBot l] {f g : β -> α}
    {a b : α} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) :
    Inseparable a b ↔ Tendsto (fun x => (f x, g x)) l (𝓤 α) := by
  refine ⟨fun h => (ha.prodMk_nhds hb).mono_right h.nhds_le_uniformity, fun h => ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prodMk_nhds hb)).mono h

/--
theorem `isClosed_of_spaced_out` / 定理 `isClosed_of_spaced_out`

English:
theorem isClosed_of_spaced_out
  statement: [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α) {s : Set α}
  proof: by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz

中文:
定理 isClosed_of_spaced_out
  结论: [T0空间 α] {V₀ : 集合 (α × α)} (V₀_in : V₀ in 𝓤 α) {s : 集合 α}
  证明: by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz

Depends on / 依赖: V_in, ball_inter_left, ball_inter_right, comp_symm_mem_uniformity_sets, eq_of_forall_symmetric, h_comp, inter_mem, isClosed_of_closure_subset, mem_closure_iff_ball, mem_comp_of_mem_ball
-/
theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz

/--
theorem `isClosed_range_of_spaced_out` / 定理 `isClosed_range_of_spaced_out`

English:
theorem isClosed_range_of_spaced_out
  statement: {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α)
  proof: isClosed_of_spaced_out V₀_in by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)

中文:
定理 isClosed_range_of_spaced_out
  结论: {ι} [T0空间 α] {V₀ : 集合 (α × α)} (V₀_in : V₀ in 𝓤 α)
  证明: isClosed_of_spaced_out V₀_in by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)

Depends on / 依赖: isClosed_of_spaced_out, ne_of_apply_ne
-/
theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α)
    {f : ι -> α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
isClosed_of_spaced_out V₀_in by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)

/-!
### Separation quotient
-/

namespace SeparationQuotient

/--
theorem `comap_map_mk_uniformity` / 定理 `comap_map_mk_uniformity`

English:
theorem comap_map_mk_uniformity
  statement: comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α
  proof: by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU => ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ => ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

中文:
定理 comap_map_mk_uniformity
  结论: comap (积类型.map mk mk) (map (积类型.map mk mk) (𝓤 α)) = 𝓤 α
  证明: by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU => ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ => ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

Depends on / 依赖: Prod.ext_iff, Prod.map, basis_sets, basis_sets.map, ext_iff, le_antisymm, le_basis_iff, le_comap_map, mem_open_iff, mk_eq_mk, uniformity_hasBasis_open
-/
theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU => ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ => ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (SeparationQuotient α) where
  body: map (Prod.map mk mk) (𝓤 α)
symm := tendsto_map' tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht => by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, SetRel.mem_comp, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x => comap_injective surjective_mk by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]

中文:
实例 instUniformSpace
  签名: : 一致空间 (SeparationQuotient α) where
  定义体: map (Prod.map mk mk) (𝓤 α)
symm := tendsto_map' tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht => by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, SetRel.mem_comp, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x => comap_injective surjective_mk by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]

Depends on / 依赖: Prod.map
-/
instance instUniformSpace : UniformSpace (SeparationQuotient α) where
  uniformity := map (Prod.map mk mk) (𝓤 α)
symm := tendsto_map' tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht => by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, SetRel.mem_comp, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x => comap_injective surjective_mk by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]

/--
theorem `uniformity_eq` / 定理 `uniformity_eq`

English:
theorem uniformity_eq
  statement: 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk)
  proof: rfl

@[fun_prop]

中文:
定理 uniformity_eq
  结论: 𝓤 (SeparationQuotient α) = (𝓤 α).map (积类型.map mk mk)
  证明: rfl

@[fun_prop]
-/
theorem uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk) := rfl

@[fun_prop]
/--
theorem `uniformContinuous_mk` / 定理 `uniformContinuous_mk`

English:
theorem uniformContinuous_mk
  statement: UniformContinuous (mk : α -> SeparationQuotient α)
  proof: le_rfl

中文:
定理 uniformContinuous_mk
  结论: 一致连续 (mk : α -> SeparationQuotient α)
  证明: le_rfl

Depends on / 依赖: le_rfl
-/
theorem uniformContinuous_mk : UniformContinuous (mk : α -> SeparationQuotient α) :=
  le_rfl

/--
theorem `uniformContinuous_dom` / 定理 `uniformContinuous_dom`

English:
theorem uniformContinuous_dom
  given: {f : SeparationQuotient α -> β}
  proof: .rfl

中文:
定理 uniformContinuous_dom
  条件: {f : SeparationQuotient α -> β}
  证明: .rfl
-/
theorem uniformContinuous_dom {f : SeparationQuotient α -> β} :
    UniformContinuous f ↔ UniformContinuous (f ∘ mk) :=
  .rfl

/--
theorem `uniformContinuous_dom₂` / 定理 `uniformContinuous_dom₂`

English:
theorem uniformContinuous_dom₂
  given: {f : SeparationQuotient α × SeparationQuotient β -> γ}
  proof: by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl

中文:
定理 uniformContinuous_dom₂
  条件: {f : SeparationQuotient α × SeparationQuotient β -> γ}
  证明: by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl

Depends on / 依赖: UniformContinuous, _iff, prod_map_map_eq, tendsto_map, uniformity_eq, uniformity_prod_eq_prod
-/
theorem uniformContinuous_dom₂ {f : SeparationQuotient α × SeparationQuotient β -> γ} :
    UniformContinuous f ↔ UniformContinuous fun p : α × β => f (mk p.1, mk p.2) := by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl

/--
theorem `uniformContinuous_lift` / 定理 `uniformContinuous_lift`

English:
theorem uniformContinuous_lift
  given: {f : α -> β} (h : forall a b, Inseparable a b -> f a = f b)
  proof: .rfl

中文:
定理 uniformContinuous_lift
  条件: {f : α -> β} (h : 对任意 a b, 不可分 a b -> f a = f b)
  证明: .rfl
-/
theorem uniformContinuous_lift {f : α -> β} (h : forall a b, Inseparable a b -> f a = f b) :
    UniformContinuous (lift f h) ↔ UniformContinuous f :=
  .rfl

/--
theorem `uniformContinuous_uncurry_lift₂` / 定理 `uniformContinuous_uncurry_lift₂`

English:
theorem uniformContinuous_uncurry_lift₂
  statement: {f : α -> β -> γ}
  proof: uniformContinuous_dom₂

中文:
定理 uniformContinuous_uncurry_lift₂
  结论: {f : α -> β -> γ}
  证明: uniformContinuous_dom₂
-/
theorem uniformContinuous_uncurry_lift₂ {f : α -> β -> γ}
    (h : forall a c b d, Inseparable a b -> Inseparable c d -> f a c = f b d) :
    UniformContinuous (uncurry <| lift₂ f h) ↔ UniformContinuous (uncurry f) :=
  uniformContinuous_dom₂

/--
theorem `comap_mk_uniformity` / 定理 `comap_mk_uniformity`

English:
theorem comap_mk_uniformity
  statement: (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α
  proof: comap_map_mk_uniformity

中文:
定理 comap_mk_uniformity
  结论: (𝓤 (SeparationQuotient α)).comap (积类型.map mk mk) = 𝓤 α
  证明: comap_map_mk_uniformity

Depends on / 依赖: comap_map_mk_uniformity
-/
theorem comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α :=
  comap_map_mk_uniformity

open scoped Classical in
/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: [T0Space β] (f : α -> β)
  body: if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)

中文:
定义 lift'
  签名: [T0空间 β] (f : α -> β)
  定义体: if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)

Depends on / 依赖: Nonempty, Nonempty.some, UniformContinuous, continuous, h.map, hc.continuous, x.out
-/
def lift' [T0Space β] (f : α -> β) : SeparationQuotient α -> β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)

/--
theorem `lift'_mk` / 定理 `lift'_mk`

English:
theorem lift'_mk
  given: [T0Space β] {f : α -> β} (h : UniformContinuous f) (a : α)
  proof: by rw [lift', dif_pos h, lift_mk]

@[fun_prop]

中文:
定理 lift'_mk
  条件: [T0空间 β] {f : α -> β} (h : 一致连续 f) (a : α)
  证明: by rw [lift', dif_pos h, lift_mk]

@[fun_prop]
-/
theorem lift'_mk [T0Space β] {f : α -> β} (h : UniformContinuous f) (a : α) :
    lift' f (mk a) = f a := by rw [lift', dif_pos h, lift_mk]

@[fun_prop]
/--
theorem `uniformContinuous_lift'` / 定理 `uniformContinuous_lift'`

English:
theorem uniformContinuous_lift'
  given: [T0Space β] (f : α -> β)
  statement: UniformContinuous (lift' f)
  proof: by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl

中文:
定理 uniformContinuous_lift'
  条件: [T0空间 β] (f : α -> β)
  结论: 一致连续 (lift' f)
  证明: by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl

Depends on / 依赖: UniformContinuous, dif_neg, dif_pos, uniformContinuous_lift, uniformContinuous_of_const
-/
theorem uniformContinuous_lift' [T0Space β] (f : α -> β) : UniformContinuous (lift' f) := by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: lift' (mk ∘ f)

中文:
定义 map
  签名: (f : α -> β)
  定义体: lift' (mk ∘ f)
-/
def map (f : α -> β) : SeparationQuotient α -> SeparationQuotient β := lift' (mk ∘ f)

/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {f : α -> β} (h : UniformContinuous f) (a : α)
  statement: map f (mk a) = mk (f a)
  proof: by
  rw [map]; rw [lift'_mk (uniformContinuous_mk.comp h)]; rfl

@[fun_prop]

中文:
定理 map_mk
  条件: {f : α -> β} (h : 一致连续 f) (a : α)
  结论: map f (mk a) = mk (f a)
  证明: by
  rw [map]; rw [lift'_mk (uniformContinuous_mk.comp h)]; rfl

@[fun_prop]

Depends on / 依赖: uniformContinuous_mk, uniformContinuous_mk.comp
-/
theorem map_mk {f : α -> β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk (f a) := by
  rw [map]; rw [lift'_mk (uniformContinuous_mk.comp h)]; rfl

@[fun_prop]
/--
theorem `uniformContinuous_map` / 定理 `uniformContinuous_map`

English:
theorem uniformContinuous_map
  given: (f : α -> β)
  statement: UniformContinuous (map f)
  proof: uniformContinuous_lift' _

中文:
定理 uniformContinuous_map
  条件: (f : α -> β)
  结论: 一致连续 (map f)
  证明: uniformContinuous_lift' _

Depends on / 依赖: uniformContinuous_lift
-/
theorem uniformContinuous_map (f : α -> β) : UniformContinuous (map f) :=
  uniformContinuous_lift' _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_unique` / 定理 `map_unique`

English:
theorem map_unique
  statement: {f : α -> β} (hf : UniformContinuous f)
  proof: by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a

@[simp]

中文:
定理 map_unique
  结论: {f : α -> β} (hf : 一致连续 f)
  证明: by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a

@[simp]

Depends on / 依赖: congr_fun, map_mk
-/
theorem map_unique {f : α -> β} (hf : UniformContinuous f)
    {g : SeparationQuotient α -> SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (@id α) = id
  proof: map_unique uniformContinuous_id rfl

中文:
定理 map_id
  结论: map (@id α) = id
  证明: map_unique uniformContinuous_id rfl

Depends on / 依赖: map_unique, uniformContinuous_id
-/
theorem map_id : map (@id α) = id := map_unique uniformContinuous_id rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {f : α -> β} {g : β -> γ} (hf : UniformContinuous f) (hg : UniformContinuous g)
  proof: (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm

中文:
定理 map_comp
  条件: {f : α -> β} {g : β -> γ} (hf : 一致连续 f) (hg : 一致连续 g)
  证明: (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm

Depends on / 依赖: Function, Function.comp_def, comp_def, hg.comp, map_mk, map_unique
-/
theorem map_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm

end SeparationQuotient

namespace IndiscreteTopology

variable {α : Type*} [u : UniformSpace α]

/--
theorem `of_uniformity_eq_top` / 定理 `of_uniformity_eq_top`

English:
theorem of_uniformity_eq_top
  given: (h : uniformity α = ⊤)
  statement: IndiscreteTopology α
  proof: ⟨(UniformSpace.ext h.symm : ⊤ = u) ▸ rfl⟩

中文:
定理 of_uniformity_eq_top
  条件: (h : uniformity α = ⊤)
  结论: Indiscrete拓扑 α
  证明: ⟨(UniformSpace.ext h.symm : ⊤ = u) ▸ rfl⟩

Depends on / 依赖: UniformSpace, UniformSpace.ext, h.symm
-/
theorem of_uniformity_eq_top (h : uniformity α = ⊤) : IndiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊤ = u) ▸ rfl⟩

/--
lemma `eq_top_uniformSpace` / 引理 `eq_top_uniformSpace`

English:
lemma eq_top_uniformSpace
  given: [IndiscreteTopology α]
  statement: u = ⊤
  proof: by
  refine UniformSpace.ext ?_
  rw [top_uniformity]; rw [← Filter.ker_eq_univ]
  ext x
  rw [← inseparable_iff_ker_uniformity]
  simp

中文:
引理 eq_top_uniformSpace
  条件: [Indiscrete拓扑 α]
  结论: u = ⊤
  证明: by
  refine UniformSpace.ext ?_
  rw [top_uniformity]; rw [← Filter.ker_eq_univ]
  ext x
  rw [← inseparable_iff_ker_uniformity]
  simp

Depends on / 依赖: Filter, Filter.ker_eq_univ, UniformSpace, UniformSpace.ext, inseparable_iff_ker_uniformity, ker_eq_univ, top_uniformity
-/
lemma eq_top_uniformSpace [IndiscreteTopology α] : u = ⊤ := by
  refine UniformSpace.ext ?_
  rw [top_uniformity]; rw [← Filter.ker_eq_univ]
  ext x
  rw [← inseparable_iff_ker_uniformity]
  simp

/--
lemma `eq_top_iff_indiscrete` / 引理 `eq_top_iff_indiscrete`

English:
lemma eq_top_iff_indiscrete
  statement: u = ⊤ ↔ IndiscreteTopology α
  proof: ⟨fun h => IndiscreteTopology.mk h ▸ UniformSpace.toTopologicalSpace_top (α := α),
  fun _ => eq_top_uniformSpace⟩

@[fun_prop]

中文:
引理 eq_top_iff_indiscrete
  结论: u = ⊤ ↔ Indiscrete拓扑 α
  证明: ⟨fun h => IndiscreteTopology.mk h ▸ UniformSpace.toTopologicalSpace_top (α := α),
  fun _ => eq_top_uniformSpace⟩

@[fun_prop]

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.mk, UniformSpace, UniformSpace.toTopologicalSpace_top, eq_top_uniformSpace, toTopologicalSpace_top
-/
lemma eq_top_iff_indiscrete : u = ⊤ ↔ IndiscreteTopology α :=
⟨fun h => IndiscreteTopology.mk h ▸ UniformSpace.toTopologicalSpace_top (α := α),
  fun _ => eq_top_uniformSpace⟩

@[fun_prop]
/--
lemma `uniformContinuous` / 引理 `uniformContinuous`

English:
lemma uniformContinuous
  given: [IndiscreteTopology β] {f : α -> β}
  statement: UniformContinuous f
  proof: by
  rw [UniformContinuous]; rw [eq_top_uniformSpace (α := β)]; rw [top_uniformity]
  exact Filter.tendsto_top

中文:
引理 uniformContinuous
  条件: [Indiscrete拓扑 β] {f : α -> β}
  结论: 一致连续 f
  证明: by
  rw [UniformContinuous]; rw [eq_top_uniformSpace (α := β)]; rw [top_uniformity]
  exact Filter.tendsto_top

Depends on / 依赖: Filter, Filter.tendsto_top, UniformContinuous, eq_top_uniformSpace, tendsto_top, top_uniformity
-/
lemma uniformContinuous [IndiscreteTopology β] {f : α -> β} : UniformContinuous f := by
  rw [UniformContinuous]; rw [eq_top_uniformSpace (α := β)]; rw [top_uniformity]
  exact Filter.tendsto_top

end IndiscreteTopology
