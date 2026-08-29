/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `productOfMemOpens` from `X` to `Opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `productOfMemOpens` is always inducing. Whenever `X` is T0, `productOfMemOpens` is
also injective and therefore an embedding.
-/

@[expose] public section

open Topology

noncomputable section

namespace TopologicalSpace

/--
theorem `eq_induced_by_maps_to_sierpinski` / 定理 `eq_induced_by_maps_to_sierpinski`

English:
theorem eq_induced_by_maps_to_sierpinski
  given: (X : Type*) [t : TopologicalSpace X]
  proof: by
  apply le_antisymm
  · rw [le_iInf_iff]
    exact fun u => Continuous.le_induced (isOpen_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_iUnion_isOpen]
    apply isOpen_generateFrom_of_mem
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {T

中文:
定理 eq_induced_by_maps_to_sierpinski
  条件: (X : 类型) [t : TopologicalSpace X]
  证明: by
  apply le_antisymm
  · rw [le_iInf_iff]
    exact fun u => Continuous.le_induced (isOpen_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_iUnion_isOpen]
    apply isOpen_generateFrom_of_mem
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {T

Depends on / 依赖: Continuous, Continuous.le_induced, Set.mem_iUnion, Set.mem_ofPred_eq, Set.preimage, generateFrom_iUnion_isOpen, isOpen_generateFrom_of_mem, isOpen_iff_continuous_mem, isOpen_iff_continuous_mem.mp, isOpen_induced_iff, isOpen_singleton_true, le_antisymm, le_iInf_iff, le_induced, mem_iUnion, mem_ofPred_eq, preimage
-/
theorem eq_induced_by_maps_to_sierpinski (X : Type*) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· in u) := by
  apply le_antisymm
  · rw [le_iInf_iff]
    exact fun u => Continuous.le_induced (isOpen_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_iUnion_isOpen]
    apply isOpen_generateFrom_of_mem
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {True}, isOpen_singleton_true, by simp [Set.preimage]⟩

variable (X : Type*) [TopologicalSpace X]

/--
Definition of `productOfMemOpens` / `productOfMemOpens` 的定义

English:
definition productOfMemOpens
  signature: : C(X, Opens X -> Prop) where
  body: x in u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.isOpen

中文:
定义 productOfMemOpens
  签名: : C(X, Opens X -> 命题) where
  定义体: x in u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.isOpen
-/
def productOfMemOpens : C(X, Opens X -> Prop) where
  toFun x u := x in u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.isOpen

/--
theorem `productOfMemOpens_isInducing` / 定理 `productOfMemOpens_isInducing`

English:
theorem productOfMemOpens_isInducing
  statement: IsInducing (productOfMemOpens X)
  proof: by
  convert! inducing_iInf_to_pi fun (u : Opens X) (x : X) => x in u
  apply eq_induced_by_maps_to_sierpinski

中文:
定理 productOfMemOpens_isInducing
  结论: IsInducing (productOfMemOpens X)
  证明: by
  convert! inducing_iInf_to_pi fun (u : Opens X) (x : X) => x in u
  apply eq_induced_by_maps_to_sierpinski

Depends on / 依赖: convert, eq_induced_by_maps_to_sierpinski, inducing_iInf_to_pi
-/
theorem productOfMemOpens_isInducing : IsInducing (productOfMemOpens X) := by
  convert! inducing_iInf_to_pi fun (u : Opens X) (x : X) => x in u
  apply eq_induced_by_maps_to_sierpinski

/--
theorem `productOfMemOpens_injective` / 定理 `productOfMemOpens_injective`

English:
theorem productOfMemOpens_injective
  given: [T0Space X]
  statement: Function.Injective (productOfMemOpens X)
  proof: by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (productOfMemOpens_isInducing X)]; rw [h]

中文:
定理 productOfMemOpens_injective
  条件: [T0Space X]
  结论: Function.Injective (productOfMemOpens X)
  证明: by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (productOfMemOpens_isInducing X)]; rw [h]

Depends on / 依赖: Inseparable, Inseparable.eq, IsInducing, IsInducing.inseparable_iff, inseparable_iff, productOfMemOpens_isInducing
-/
theorem productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMemOpens X) := by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (productOfMemOpens_isInducing X)]; rw [h]

/--
theorem `productOfMemOpens_isEmbedding` / 定理 `productOfMemOpens_isEmbedding`

English:
theorem productOfMemOpens_isEmbedding
  given: [T0Space X]
  statement: IsEmbedding (productOfMemOpens X)
  proof: .mk (productOfMemOpens_isInducing X) (productOfMemOpens_injective X)

中文:
定理 productOfMemOpens_isEmbedding
  条件: [T0Space X]
  结论: IsEmbedding (productOfMemOpens X)
  证明: .mk (productOfMemOpens_isInducing X) (productOfMemOpens_injective X)

Depends on / 依赖: productOfMemOpens_injective, productOfMemOpens_isInducing
-/
theorem productOfMemOpens_isEmbedding [T0Space X] : IsEmbedding (productOfMemOpens X) :=
  .mk (productOfMemOpens_isInducing X) (productOfMemOpens_injective X)

end TopologicalSpace
