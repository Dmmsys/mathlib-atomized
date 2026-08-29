/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `UniformOnFun.continuousSMul_induced_of_image_bounded` : let `E` be a TVS, `𝔖 : Set (Set α)` and
  `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is bounded (in the
  sense of `Bornology.IsVonNBounded`), then `H`, equipped with the topology induced from
  `α →ᵤ[𝔖] E`, is a TVS.

## Implementation notes

Like in `Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean`, we use the type aliases
`UniformFun` (denoted `α →ᵤ β`) and `UniformOnFun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/

public section

open Filter Topology
open scoped Pointwise UniformConvergence Uniformity

section Module

variable (𝕜 α E H : Type*) {hom : Type*} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace H] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] {𝔖 : Set <| Set α}
  [FunLike hom H (α -> E)] [LinearMapClass hom 𝕜 H (α -> E)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `UniformFun.continuousSMul_induced_of_range_bounded` / 引理 `UniformFun.continuousSMul_induced_of_range_bounded`

English:
lemma UniformFun.continuousSMul_induced_of_range_bounded
  statement: (φ : hom)
  proof: by
  have : IsTopologicalAddGroup H :=
    let ofFun' : (α -> E) ->+ (α ->ᵤ E) := AddMonoidHom.id _
    IsInducing.topologicalAddGroup (ofFun'.comp (φ : H ->+ (α -> E))) hφ
  have hb : (𝓝 (0 : H)).HasBasis (· in 𝓝 (0 : E)) fun V => {u | forall x, φ u x in V} := by
    simp only [hφ.nhds_eq_comap, Fu

中文:
引理 UniformFun.continuousSMul_induced_of_range_bounded
  结论: (φ : hom)
  证明: by
  have : IsTopologicalAddGroup H :=
    let ofFun' : (α -> E) ->+ (α ->ᵤ E) := AddMonoidHom.id _
    IsInducing.topologicalAddGroup (ofFun'.comp (φ : H ->+ (α -> E))) hφ
  have hb : (𝓝 (0 : H)).HasBasis (· in 𝓝 (0 : E)) fun V => {u | forall x, φ u x in V} := by
    simp only [hφ.nhds_eq_comap, Fu

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, ContinuousSMul, ContinuousSMul.of_basis_zero, Function, Function.comp_apply, HasBasis, IsInducing, IsInducing.topologicalAddGroup, IsTopologicalAddGroup, Tendsto, UniformFun, UniformFun.hasBasis_nhds_zero.comap, comp_apply, continuous_smul, continuous_smul.tendsto, hasBasis_nhds_zero, map_zero, nhds_eq_comap, of_basis_zero
-/
lemma UniformFun.continuousSMul_induced_of_range_bounded (φ : hom)
    (hφ : IsInducing (ofFun ∘ φ)) (h : forall u : H, Bornology.IsVonNBounded 𝕜 (Set.range (φ u))) :
    ContinuousSMul 𝕜 H := by
  have : IsTopologicalAddGroup H :=
    let ofFun' : (α -> E) ->+ (α ->ᵤ E) := AddMonoidHom.id _
    IsInducing.topologicalAddGroup (ofFun'.comp (φ : H ->+ (α -> E))) hφ
  have hb : (𝓝 (0 : H)).HasBasis (· in 𝓝 (0 : E)) fun V => {u | forall x, φ u x in V} := by
    simp only [hφ.nhds_eq_comap, Function.comp_apply, map_zero]
    exact UniformFun.hasBasis_nhds_zero.comap _
  apply ContinuousSMul.of_basis_zero hb
  · intro U hU
    have : Tendsto (fun x : 𝕜 × E => x.1 • x.2) (𝓝 0) (𝓝 0) :=
      continuous_smul.tendsto' _ _ (zero_smul _ _)
    rcases ((Filter.basis_sets _).prod_nhds (Filter.basis_sets _)).tendsto_left_iff.1 this U hU
      with ⟨⟨V, W⟩, ⟨hV, hW⟩, hVW⟩
    refine ⟨V, hV, W, hW, Set.smul_subset_iff.2 fun a ha u hu x => ?_⟩
    rw [map_smul]
    exact hVW (Set.mk_mem_prod ha (hu x))
  · intro c U hU
    have : Tendsto (c • · : E -> E) (𝓝 0) (𝓝 0) :=
      (continuous_const_smul c).tendsto' _ _ (smul_zero _)
    refine ⟨_, this hU, fun u hu x => ?_⟩
    simpa only [map_smul] using! hu x
  · intro u U hU
    simp only [Set.mem_ofPred_eq, map_smul, Pi.smul_apply]
    simpa only [Set.mapsTo_range_iff] using (h u hU).eventually_nhds_zero (mem_of_mem_nhds hU)

/--
lemma `UniformOnFun.continuousSMul_induced_of_image_bounded` / 引理 `UniformOnFun.continuousSMul_induced_of_image_bounded`

English:
lemma UniformOnFun.continuousSMul_induced_of_image_bounded
  statement: (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ))
  proof: by
  obtain rfl := hφ.eq_induced; clear hφ
  simp +instances only [induced_iInf, UniformOnFun.topologicalSpace_eq, induced_compose]
  refine continuousSMul_iInf fun s => continuousSMul_iInf fun hs => ?_
  let : TopologicalSpace H :=
    .induced (UniformFun.ofFun ∘ s.domRestrict ∘ φ) (UniformFun.top

中文:
引理 UniformOnFun.continuousSMul_induced_of_image_bounded
  结论: (φ : hom) (hφ : 是Inducing (ofFun 𝔖 ∘ φ))
  证明: by
  obtain rfl := hφ.eq_induced; clear hφ
  simp +instances only [induced_iInf, UniformOnFun.topologicalSpace_eq, induced_compose]
  refine continuousSMul_iInf fun s => continuousSMul_iInf fun hs => ?_
  let : TopologicalSpace H :=
    .induced (UniformFun.ofFun ∘ s.domRestrict ∘ φ) (UniformFun.top

Depends on / 依赖: TopologicalSpace, UniformFun, UniformFun.ofFun, UniformFun.topologicalSpace, UniformOnFun, UniformOnFun.topologicalSpace_eq, congr_arg, continuousSMul_iInf, domRestrict, eq_induced, induced, induced_compose, induced_iInf, instances, map_add, map_smul, s.domRestrict, topologicalSpace, topologicalSpace_eq
-/
lemma UniformOnFun.continuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ))
    (h : forall u : H, forall s in 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α -> E) '' s)) :
    ContinuousSMul 𝕜 H := by
  obtain rfl := hφ.eq_induced; clear hφ
  simp +instances only [induced_iInf, UniformOnFun.topologicalSpace_eq, induced_compose]
  refine continuousSMul_iInf fun s => continuousSMul_iInf fun hs => ?_
  let : TopologicalSpace H :=
    .induced (UniformFun.ofFun ∘ s.domRestrict ∘ φ) (UniformFun.topologicalSpace s E)
  set φ' : H ->ₗ[𝕜] (s -> E) :=
    { toFun := s.domRestrict ∘ φ,
      map_smul' := fun c x => by exact congr_arg s.domRestrict (map_smul φ c x),
      map_add' := fun x y => by exact congr_arg s.domRestrict (map_add φ x y) }
  refine UniformFun.continuousSMul_induced_of_range_bounded 𝕜 s E H φ' ⟨rfl⟩ fun u => ?_
  simpa only [Set.image_eq_range] using! h u s hs

/--
theorem `UniformOnFun.continuousSMul_submodule_of_image_bounded` / 定理 `UniformOnFun.continuousSMul_submodule_of_image_bounded`

English:
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded
  statement: (H : Submodule 𝕜 (α ->ᵤ[𝔖] E))
  proof: UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H
    (LinearMap.id.domRestrict H : H ->ₗ[𝕜] α -> E) IsInducing.subtypeVal fun ⟨u, hu⟩ => h u hu

中文:
定理 UniformOnFun.continuousSMul_submodule_of_image_bounded
  结论: (H : 子模 𝕜 (α ->ᵤ[𝔖] E))
  证明: UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H
    (LinearMap.id.domRestrict H : H ->ₗ[𝕜] α -> E) IsInducing.subtypeVal fun ⟨u, hu⟩ => h u hu

Depends on / 依赖: IsInducing, IsInducing.subtypeVal, LinearMap, LinearMap.id.domRestrict, UniformOnFun, UniformOnFun.continuousSMul_induced_of_image_bounded, continuousSMul_induced_of_image_bounded, domRestrict, subtypeVal
-/
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded (H : Submodule 𝕜 (α ->ᵤ[𝔖] E))
    (h : forall u in H, forall s in 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced ((↑) : H -> α ->ᵤ[𝔖] E)) :=
  UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H
    (LinearMap.id.domRestrict H : H ->ₗ[𝕜] α -> E) IsInducing.subtypeVal fun ⟨u, hu⟩ => h u hu

end Module
