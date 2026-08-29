/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Interaction of separation properties with connectedness properties
-/

public section

variable {X : Type*} [TopologicalSpace X]

open Filter Set
open scoped Topology

-- see Note [lower instance priority]
instance (priority := 100) TotallyDisconnectedSpace.t1Space [h : TotallyDisconnectedSpace X] :
    T1Space X := by
  rw [((t1Space_TFAE X).out 0 1 :)]
  intro x
  rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.mp h x]
  exact isClosed_connectedComponent

/--
theorem `PreconnectedSpace.trivial_of_discrete` / 定理 `PreconnectedSpace.trivial_of_discrete`

English:
theorem PreconnectedSpace.trivial_of_discrete
  given: [PreconnectedSpace X] [DiscreteTopology X]
  proof: by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne]; rw [← mem_singleton_iff]; rw [(isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)

中文:
定理 PreconnectedSpace.trivial_of_discrete
  条件: [PreconnectedSpace X] [DiscreteTopology X]
  证明: by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne]; rw [← mem_singleton_iff]; rw [(isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)

Depends on / 依赖: eq_univ, isClopen_discrete, mem_singleton_iff, mem_univ, singleton_nonempty
-/
theorem PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopology X] :
    Subsingleton X := by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne]; rw [← mem_singleton_iff]; rw [(isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)

/--
theorem `IsPreconnected.infinite_of_nontrivial` / 定理 `IsPreconnected.infinite_of_nontrivial`

English:
theorem IsPreconnected.infinite_of_nontrivial
  statement: [T1Space X] {s : Set X} (h : IsPreconnected s)
  proof: by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  have := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _

中文:
定理 IsPreconnected.infinite_of_nontrivial
  结论: [T1Space X] {s : Set X} (h : IsPreconnected s)
  证明: by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  have := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _

Depends on / 依赖: Finite, Finite.instDiscreteTopology, PreconnectedSpace, PreconnectedSpace.trivial_of_discrete, Subtype, Subtype.preconnectedSpace, hf.to_subtype, instDiscreteTopology, not_subsingleton_iff, not_subsingleton_iff.mpr, preconnectedSpace, subsingleton_coe, to_subtype, trivial_of_discrete
-/
theorem IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreconnected s)
    (hs : s.Nontrivial) : s.Infinite := by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  have := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _

/--
theorem `PreconnectedSpace.infinite` / 定理 `PreconnectedSpace.infinite`

English:
theorem PreconnectedSpace.infinite
  given: [PreconnectedSpace X] [Nontrivial X] [T1Space X]
  statement: Infinite X
  proof: infinite_univ_iff.mp isPreconnected_univ.infinite_of_nontrivial nontrivial_univ

中文:
定理 PreconnectedSpace.infinite
  条件: [PreconnectedSpace X] [Nontrivial X] [T1Space X]
  结论: Infinite X
  证明: infinite_univ_iff.mp isPreconnected_univ.infinite_of_nontrivial nontrivial_univ

Depends on / 依赖: infinite_of_nontrivial, infinite_univ_iff, infinite_univ_iff.mp, isPreconnected_univ, isPreconnected_univ.infinite_of_nontrivial, nontrivial_univ
-/
theorem PreconnectedSpace.infinite [PreconnectedSpace X] [Nontrivial X] [T1Space X] : Infinite X :=
infinite_univ_iff.mp isPreconnected_univ.infinite_of_nontrivial nontrivial_univ

/--
theorem `subsingleton_iff_discrete_and_indiscrete` / 定理 `subsingleton_iff_discrete_and_indiscrete`

English:
theorem subsingleton_iff_discrete_and_indiscrete
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => PreconnectedSpace.trivial_of_discrete⟩

中文:
定理 subsingleton_iff_discrete_and_indiscrete
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => PreconnectedSpace.trivial_of_discrete⟩

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.trivial_of_discrete, trivial_of_discrete
-/
theorem subsingleton_iff_discrete_and_indiscrete :
    Subsingleton X ↔ DiscreteTopology X ∧ IndiscreteTopology X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => PreconnectedSpace.trivial_of_discrete⟩

/-- A non-trivial connected T1 space has no isolated points. -/
instance (priority := 100) ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space
    [ConnectedSpace X] [Nontrivial X] [T1Space X] (x : X) :
    NeBot (𝓝[!=] x) := by
  by_contra contra
  rw [not_neBot]; rw [← isOpen_singleton_iff_punctured_nhds] at contra
  replace contra := nonempty_inter isOpen_compl_singleton
    contra (compl_union_self _) (Set.nonempty_compl_of_nontrivial _) (singleton_nonempty _)
  simp [compl_inter_self {x}] at contra
