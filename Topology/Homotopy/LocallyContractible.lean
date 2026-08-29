/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Strongly locally contractible spaces

This file defines `LocallyContractibleSpace` and `StronglyLocallyContractibleSpace`.

## Main definitions

* `LocallyContractibleSpace X`: classical local contractibility (null-homotopic inclusions).
* `StronglyLocallyContractibleSpace X`: a space where each point has a neighborhood basis
  consisting of contractible sets (not necessarily open).

## Main results

* `StronglyLocallyContractibleSpace.locallyContractible`: SLC implies classical LC
* `instLocallyPathConnectedSpace`: strongly locally contractible spaces are locally path-connected
* `StronglyLocallyContractibleSpace.of_bases`: a helper to construct strongly locally contractible
  spaces from a neighborhood basis
* `contractible_subset_basis`: basis of contractible neighborhoods contained in an open set
* `IsOpenEmbedding.stronglyLocallyContractibleSpace`: open embeddings preserve strong local
  contractibility
* `IsOpen.stronglyLocallyContractibleSpace`: open subsets of strongly locally contractible spaces
  are strongly locally contractible
* Products of strongly locally contractible spaces are strongly locally contractible

## TODO

* Define contractible components and prove they are open in strongly locally contractible spaces
* Add examples: convex sets, real vector spaces, star-shaped sets

## Notes

**Terminology:** The classical definition of *locally contractible* (LC) requires that for every
point `x` and neighborhood `U ∋ x`, there exists a neighborhood `V ∋ x` with `V ⊆ U` such that the
inclusion `V ↪ U` is null-homotopic. The definition here is **strictly stronger**: we require
contractible neighborhoods to form a neighborhood basis. This is often called **strongly locally
contractible** (SLC).

**Hierarchy of notions:**
* "Basis of open contractible neighborhoods" (strongest)
* "Basis of contractible neighborhoods" (this file, SLC)
* "Null-homotopic inclusions" (classical LC, weakest)

This naming is not used uniformly: according to
https://ncatlab.org/nlab/show/locally+contractible+space
the second and third notion here could also be called
"locally contractible" and "semilocally contractible" respectively.
We've enquired at
https://math.stackexchange.com/questions/5109428/terminology-for-local-contractibility-locally-contractible-vs-strongly-local
in the hope of getting definitive naming advice.

The Borsuk-Mazurkiewicz counterexample [borsuk_mazurkiewicz1934] shows that classical LC does not
imply SLC. Moreover, from a contractible neighborhood `S` one generally cannot shrink to an open
`V ⊆ S` that remains contractible, so requiring neighborhoods to be open is potentially strictly
stronger than SLC.
-/

@[expose] public section

noncomputable section

open Topology Filter Set Function ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {ι : Type*}

section LocallyContractible

/--
Definition of `LocallyContractibleSpace` / `LocallyContractibleSpace` 的定义

English:
definition LocallyContractibleSpace
  signature: (X : Type*) [TopologicalSpace X]
  body: forall (x : X) (U : Set X), U in 𝓝 x ->
    exists (V : Set X) (hVU : V subseteq U), V in 𝓝 x ∧ Nullhomotopic (inclusion hVU)

中文:
定义 LocallyContractibleSpace
  签名: (X : 类型) [拓扑空间 X]
  定义体: forall (x : X) (U : Set X), U in 𝓝 x ->
    exists (V : Set X) (hVU : V subseteq U), V in 𝓝 x ∧ Nullhomotopic (inclusion hVU)

Depends on / 依赖: Nullhomotopic, inclusion, subseteq
-/
def LocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop :=
  forall (x : X) (U : Set X), U in 𝓝 x ->
    exists (V : Set X) (hVU : V subseteq U), V in 𝓝 x ∧ Nullhomotopic (inclusion hVU)

end LocallyContractible

section StronglyLocallyContractibleSpace

/--
Definition of `StronglyLocallyContractibleSpace` / `StronglyLocallyContractibleSpace` 的定义

English:
class StronglyLocallyContractibleSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - contractible_basis : forall x : X, (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ ContractibleSpace s) id

中文:
类 StronglyLocallyContractible空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - contractible_basis : 对任意 x : X, (𝓝 x).有基 (fun s : 集合 X => s in 𝓝 x ∧ 余ntractible空间 s) id
-/
class StronglyLocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of contractible subspace neighborhoods. -/
  contractible_basis : forall x : X,
    (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ ContractibleSpace s) id

export StronglyLocallyContractibleSpace (contractible_basis)

/--
theorem `StronglyLocallyContractibleSpace.of_bases` / 定理 `StronglyLocallyContractibleSpace.of_bases`

English:
theorem StronglyLocallyContractibleSpace.of_bases
  statement: {p : X -> ι -> Prop} {s : X -> ι -> Set X}
  proof: by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

中文:
定理 StronglyLocallyContractible空间.of_bases
  结论: {p : X -> ι -> 命题} {s : X -> ι -> 集合 X}
  证明: by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

Depends on / 依赖: hasBasis_self, mem_iff, mem_iff.mp, mem_of_mem
-/
theorem StronglyLocallyContractibleSpace.of_bases {p : X -> ι -> Prop} {s : X -> ι -> Set X}
    (h : forall x, (𝓝 x).HasBasis (p x) (s x)) (h' : forall x i, p x i -> ContractibleSpace (s x i)) :
    StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [StronglyLocallyContractibleSpace X]

/--
theorem `contractible_subset_basis` / 定理 `contractible_subset_basis`

English:
theorem contractible_subset_basis
  given: {U : Set X} (h : IsOpen U) (hx : x in U)
  proof: (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

中文:
定理 contractible_subset_basis
  条件: {U : 集合 X} (h : 是开集 U) (hx : x in U)
  证明: (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, contractible_basis, hasBasis_self_subset, mem_nhds
-/
theorem contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x in U) :
    (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ ContractibleSpace s ∧ s subseteq U) id :=
  (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/-- Strongly locally contractible spaces are locally path-connected. -/
instance (priority := 100) instLocallyPathConnectedSpace : LocallyPathConnectedSpace X where
  path_connected_basis x := by
.to_hasBasis' refine contractible_basis x
      (fun s ⟨hs, hs'⟩ => ⟨s, ⟨hs, ?_⟩, le_rfl⟩) (fun s hs => hs.1)
    rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance

/--
theorem `Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace` / 定理 `Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace`

English:
theorem Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace
  statement: {e : Y -> X}
  proof: .of_bases
    (fun _ => he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _))
    fun _ _ ⟨_, hs, hse⟩ =>
      (he.toIsEmbedding.homeomorphOfSubsetRange hse).contractibleSpace_iff.mpr hs

中文:
定理 拓扑.是开嵌入.stronglyLocallyContractibleSpace
  结论: {e : Y -> X}
  证明: .of_bases
    (fun _ => he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _))
    fun _ _ ⟨_, hs, hse⟩ =>
      (he.toIsEmbedding.homeomorphOfSubsetRange hse).contractibleSpace_iff.mpr hs

Depends on / 依赖: basis_nhds, contractibleSpace_iff, contractibleSpace_iff.mpr, contractible_subset_basis, he.basis_nhds, he.isOpen_range, he.toIsEmbedding.homeomorphOfSubsetRange, homeomorphOfSubsetRange, isOpen_range, mem_range_self, of_bases, toIsEmbedding
-/
theorem Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace {e : Y -> X}
    (he : IsOpenEmbedding e) : StronglyLocallyContractibleSpace Y :=
  .of_bases
    (fun _ => he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _))
    fun _ _ ⟨_, hs, hse⟩ =>
      (he.toIsEmbedding.homeomorphOfSubsetRange hse).contractibleSpace_iff.mpr hs

/--
theorem `IsOpen.stronglyLocallyContractibleSpace` / 定理 `IsOpen.stronglyLocallyContractibleSpace`

English:
theorem IsOpen.stronglyLocallyContractibleSpace
  given: {U : Set X} (h : IsOpen U)
  proof: h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace

中文:
定理 是开集.stronglyLocallyContractibleSpace
  条件: {U : 集合 X} (h : 是开集 U)
  证明: h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace

Depends on / 依赖: h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace, isOpenEmbedding_subtypeVal, stronglyLocallyContractibleSpace
-/
theorem IsOpen.stronglyLocallyContractibleSpace {U : Set X} (h : IsOpen U) :
    StronglyLocallyContractibleSpace U :=
  h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace

end StronglyLocallyContractibleSpace

section Products

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StronglyLocallyContractibleSpace
  signature: X] [StronglyLocallyContractibleSpace Y] :
  body: by
  refine .of_bases (ι := Set X × Set Y)
    (p := fun (x, y) (Ux, Uy) =>
      (Ux in 𝓝 x ∧ ContractibleSpace Ux) ∧ (Uy in 𝓝 y ∧ ContractibleSpace Uy))
    (s := fun _ (Ux, Uy) => Ux ×ˢ Uy) ?_ ?_
  · intro (x, y)
    rw [nhds_prod_eq]
    exact (contractible_basis x).prod (contractible_basis y)
 

中文:
实例 [StronglyLocallyContractible空间
  签名: X] [StronglyLocallyContractible空间 Y] :
  定义体: by
  refine .of_bases (ι := Set X × Set Y)
    (p := fun (x, y) (Ux, Uy) =>
      (Ux in 𝓝 x ∧ ContractibleSpace Ux) ∧ (Uy in 𝓝 y ∧ ContractibleSpace Uy))
    (s := fun _ (Ux, Uy) => Ux ×ˢ Uy) ?_ ?_
  · intro (x, y)
    rw [nhds_prod_eq]
    exact (contractible_basis x).prod (contractible_basis y)
 

Depends on / 依赖: ContractibleSpace, Homeomorph, Homeomorph.Set.prod, contractibleSpace, contractible_basis, nhds_prod_eq, of_bases
-/
instance [StronglyLocallyContractibleSpace X] [StronglyLocallyContractibleSpace Y] :
    StronglyLocallyContractibleSpace (X × Y) := by
  refine .of_bases (ι := Set X × Set Y)
    (p := fun (x, y) (Ux, Uy) =>
      (Ux in 𝓝 x ∧ ContractibleSpace Ux) ∧ (Uy in 𝓝 y ∧ ContractibleSpace Uy))
    (s := fun _ (Ux, Uy) => Ux ×ˢ Uy) ?_ ?_
  · intro (x, y)
    rw [nhds_prod_eq]
    exact (contractible_basis x).prod (contractible_basis y)
  · intro (x, y) (Ux, Uy) ⟨hUx, hUy⟩
    have : ContractibleSpace Ux := hUx.2
    have : ContractibleSpace Uy := hUy.2
    exact (Homeomorph.Set.prod Ux Uy).contractibleSpace

end Products

section Implications

/--
theorem `StronglyLocallyContractibleSpace.locallyContractible` / 定理 `StronglyLocallyContractibleSpace.locallyContractible`

English:
theorem StronglyLocallyContractibleSpace.locallyContractible
  given: [StronglyLocallyContractibleSpace X]
  proof: by
  intro x U hU
  obtain ⟨V, ⟨hVmem, hVcontractible⟩, hVU⟩ := (contractible_basis x).mem_iff.mp hU
  refine ⟨V, hVU, hVmem, ?_⟩
  -- V is contractible, so the identity on V is nullhomotopic to a constant map
  obtain ⟨v₀, hid⟩ := id_nullhomotopic V
  -- The inclusion V ↪ U is homotopic to the cons

中文:
定理 StronglyLocallyContractible空间.locallyContractible
  条件: [StronglyLocallyContractible空间 X]
  证明: by
  intro x U hU
  obtain ⟨V, ⟨hVmem, hVcontractible⟩, hVU⟩ := (contractible_basis x).mem_iff.mp hU
  refine ⟨V, hVU, hVmem, ?_⟩
  -- V is contractible, so the identity on V is nullhomotopic to a constant map
  obtain ⟨v₀, hid⟩ := id_nullhomotopic V
  -- The inclusion V ↪ U is homotopic to the cons

Depends on / 依赖: contractible_basis, hVcontractible, mem_iff, mem_iff.mp
-/
theorem StronglyLocallyContractibleSpace.locallyContractible [StronglyLocallyContractibleSpace X] :
    LocallyContractibleSpace X := by
  intro x U hU
  obtain ⟨V, ⟨hVmem, hVcontractible⟩, hVU⟩ := (contractible_basis x).mem_iff.mp hU
  refine ⟨V, hVU, hVmem, ?_⟩
  -- V is contractible, so the identity on V is nullhomotopic to a constant map
  obtain ⟨v₀, hid⟩ := id_nullhomotopic V
  -- The inclusion V ↪ U is homotopic to the constant map at (inclusion v₀)
  refine ⟨ContinuousMap.inclusion hVU v₀, ?_⟩
  convert! Homotopic.comp (.refl _) hid
  ext
  simp

end Implications
