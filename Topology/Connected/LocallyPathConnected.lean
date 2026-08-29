/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Ben Eltschig
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.AlexandrovDiscrete

/-!
# Locally path-connected spaces

This file defines `LocallyPathConnectedSpace X`, a predicate class asserting that `X` is locally
path-connected, in that each point has a basis of path-connected neighborhoods.

## Main results

* `IsOpen.pathComponent` / `IsClosed.pathComponent`: in locally path-connected spaces,
  path-components are both open and closed.
* `pathComponent_eq_connectedComponent`: in locally path-connected spaces, path-components and
  connected components agree.
* `pathConnectedSpace_iff_connectedSpace`: locally path-connected spaces are path-connected iff they
  are connected.
* `instLocallyConnectedSpace`: locally path-connected spaces are also locally connected.
* `IsOpen.locallyPathConnectedSpace`: open subsets of locally path-connected spaces are
  locally path-connected.
* `LocallyPathConnectedSpace.coinduced` / `Quotient.locallyPathConnectedSpace`: quotients of locally
  path-connected spaces are locally path-connected.
* `Sum.locallyPathConnectedSpace` / `Sigma.locallyPathConnectedSpace`: disjoint unions of locally
  path-connected spaces are locally path-connected.
* `Prod.locallyPathConnectedSpace` / `Pi.locallyPathConnectedSpace`: binary products of locally
  path-connected spaces are locally path-connected; likewise for pi types when the index type is
  finite or all factors are path-connected.
* `Pi.locallyPathConnectedSpace_iff`: a product of spaces is locally path-connected iff it is
  empty, or every factor is locally path-connected and all but finitely many factors are
  path-connected.

Abstractly, this also shows that locally path-connected spaces form a coreflective subcategory of
the category of topological spaces, although we do not prove that in this form here.

## Implementation notes

In the definition of `LocallyPathConnectedSpace X` we require neighbourhoods in the basis to be
path-connected, but not necessarily open; that they can also be required to be open is shown as
a theorem in `isOpen_isPathConnected_basis`.
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*} {F : Set X}

section LocallyPathConnectedSpace

/--
Definition of `LocallyPathConnectedSpace` / `LocallyPathConnectedSpace` 的定义

English:
class LocallyPathConnectedSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - path_connected_basis : forall x : X, (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConnected s) id

中文:
类 LocallyPathConnectedSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - path_connected_basis : 对任意 x : X, (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConnected s) id
-/
class LocallyPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : forall x : X, (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConnected s) id

@[deprecated (since := "2026-06-21")] alias LocPathConnectedSpace := LocallyPathConnectedSpace
@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.path_connected_basis :=
  LocallyPathConnectedSpace.path_connected_basis

export LocallyPathConnectedSpace (path_connected_basis)

/--
theorem `LocallyPathConnectedSpace.of_bases` / 定理 `LocallyPathConnectedSpace.of_bases`

English:
theorem LocallyPathConnectedSpace.of_bases
  statement: {p : X -> ι -> Prop} {s : X -> ι -> Set X}
  proof: by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.of_bases := LocallyPathConnectedSpace.of_bases

中文:
定理 LocallyPathConnectedSpace.of_bases
  结论: {p : X -> ι -> 命题} {s : X -> ι -> Set X}
  证明: by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.of_bases := LocallyPathConnectedSpace.of_bases

Depends on / 依赖: hasBasis_self, mem_iff, mem_iff.mp, mem_of_mem
-/
theorem LocallyPathConnectedSpace.of_bases {p : X -> ι -> Prop} {s : X -> ι -> Set X}
    (h : forall x, (𝓝 x).HasBasis (p x) (s x)) (h' : forall x i, p x i -> IsPathConnected (s x i)) :
    LocallyPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.of_bases := LocallyPathConnectedSpace.of_bases

variable [LocallyPathConnectedSpace X]

/--
theorem `IsOpen.pathComponentIn` / 定理 `IsOpen.pathComponentIn`

English:
theorem IsOpen.pathComponentIn
  given: (hF : IsOpen F) (x : X)
  proof: by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
exact mem_of_superset hs.1.1 pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

中文:
定理 IsOpen.pathComponentIn
  条件: (hF : IsOpen F) (x : X)
  证明: by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
exact mem_of_superset hs.1.1 pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2
-/
protected theorem IsOpen.pathComponentIn (hF : IsOpen F) (x : X) :
    IsOpen (pathComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
exact mem_of_superset hs.1.1 pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

/--
theorem `IsOpen.pathComponent` / 定理 `IsOpen.pathComponent`

English:
theorem IsOpen.pathComponent
  given: (x : X)
  statement: IsOpen (pathComponent x)
  proof: by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

中文:
定理 IsOpen.pathComponent
  条件: (x : X)
  结论: IsOpen (pathComponent x)
  证明: by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _
-/
protected theorem IsOpen.pathComponent (x : X) : IsOpen (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

/--
theorem `IsClosed.pathComponent` / 定理 `IsClosed.pathComponent`

English:
theorem IsClosed.pathComponent
  given: (x : X)
  statement: IsClosed (pathComponent x)
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
exact hxy hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

中文:
定理 IsClosed.pathComponent
  条件: (x : X)
  结论: IsClosed (pathComponent x)
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
exact hxy hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined
-/
protected theorem IsClosed.pathComponent (x : X) : IsClosed (pathComponent x) := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
exact hxy hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

/--
theorem `IsClopen.pathComponent` / 定理 `IsClopen.pathComponent`

English:
theorem IsClopen.pathComponent
  given: (x : X)
  statement: IsClopen (pathComponent x)
  proof: ⟨.pathComponent x, .pathComponent x⟩

中文:
定理 IsClopen.pathComponent
  条件: (x : X)
  结论: IsClopen (pathComponent x)
  证明: ⟨.pathComponent x, .pathComponent x⟩
-/
protected theorem IsClopen.pathComponent (x : X) : IsClopen (pathComponent x) :=
  ⟨.pathComponent x, .pathComponent x⟩

/--
lemma `pathComponentIn_mem_nhds` / 引理 `pathComponentIn_mem_nhds`

English:
lemma pathComponentIn_mem_nhds
  given: (hF : F in 𝓝 x)
  statement: pathComponentIn F x in 𝓝 x
  proof: by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩

中文:
引理 pathComponentIn_mem_nhds
  条件: (hF : F in 𝓝 x)
  结论: pathComponentIn F x in 𝓝 x
  证明: by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩

Depends on / 依赖: hu.pathComponentIn, mem_nhds_iff, mem_nhds_iff.mp, mem_nhds_iff.mpr, mem_pathComponentIn_self, pathComponentIn, pathComponentIn_mono
-/
lemma pathComponentIn_mem_nhds (hF : F in 𝓝 x) : pathComponentIn F x in 𝓝 x := by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩

/--
theorem `PathConnectedSpace.of_locallyPathConnectedSpace` / 定理 `PathConnectedSpace.of_locallyPathConnectedSpace`

English:
theorem PathConnectedSpace.of_locallyPathConnectedSpace
  given: [ConnectedSpace X]
  statement: PathConnectedSpace X
  proof: ⟨inferInstance, by simp [← mem_pathComponent_iff, IsClopen.pathComponent _ |>.eq_univ]⟩

@[deprecated (since := "2026-06-21")]
alias PathConnectedSpace.of_locPathConnectedSpace := PathConnectedSpace.of_locallyPathConnectedSpace

中文:
定理 PathConnectedSpace.of_locallyPathConnectedSpace
  条件: [ConnectedSpace X]
  结论: PathConnectedSpace X
  证明: ⟨inferInstance, by simp [← mem_pathComponent_iff, IsClopen.pathComponent _ |>.eq_univ]⟩

@[deprecated (since := "2026-06-21")]
alias PathConnectedSpace.of_locPathConnectedSpace := PathConnectedSpace.of_locallyPathConnectedSpace

Depends on / 依赖: IsClopen, IsClopen.pathComponent, eq_univ, mem_pathComponent_iff, pathComponent
-/
theorem PathConnectedSpace.of_locallyPathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X :=
  ⟨inferInstance, by simp [← mem_pathComponent_iff, IsClopen.pathComponent _ |>.eq_univ]⟩

@[deprecated (since := "2026-06-21")]
alias PathConnectedSpace.of_locPathConnectedSpace := PathConnectedSpace.of_locallyPathConnectedSpace

/--
theorem `pathConnectedSpace_iff_connectedSpace` / 定理 `pathConnectedSpace_iff_connectedSpace`

English:
theorem pathConnectedSpace_iff_connectedSpace
  statement: PathConnectedSpace X ↔ ConnectedSpace X
  proof: ⟨fun _ => inferInstance, fun _ => .of_locallyPathConnectedSpace⟩

中文:
定理 pathConnectedSpace_iff_connectedSpace
  结论: PathConnectedSpace X ↔ ConnectedSpace X
  证明: ⟨fun _ => inferInstance, fun _ => .of_locallyPathConnectedSpace⟩

Depends on / 依赖: of_locallyPathConnectedSpace
-/
theorem pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X :=
  ⟨fun _ => inferInstance, fun _ => .of_locallyPathConnectedSpace⟩

/--
theorem `pathComponent_eq_connectedComponent` / 定理 `pathComponent_eq_connectedComponent`

English:
theorem pathComponent_eq_connectedComponent
  given: (x : X)
  statement: pathComponent x = connectedComponent x
  proof: (pathComponent_subset_component x).antisymm
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

中文:
定理 pathComponent_eq_connectedComponent
  条件: (x : X)
  结论: pathComponent x = connectedComponent x
  证明: (pathComponent_subset_component x).antisymm
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

Depends on / 依赖: IsClopen, IsClopen.pathComponent, antisymm, connectedComponent_subset, mem_pathComponent_self, pathComponent, pathComponent_subset_component
-/
theorem pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedComponent x :=
(pathComponent_subset_component x).antisymm
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

/--
theorem `connectedComponent_eq_iff_joined` / 定理 `connectedComponent_eq_iff_joined`

English:
theorem connectedComponent_eq_iff_joined
  given: (x y : X)
  proof: by
  rw [← mem_pathComponent_iff]; rw [pathComponent_eq_connectedComponent]; rw [eq_comm]
  exact connectedComponent_eq_iff_mem

中文:
定理 connectedComponent_eq_iff_joined
  条件: (x y : X)
  证明: by
  rw [← mem_pathComponent_iff]; rw [pathComponent_eq_connectedComponent]; rw [eq_comm]
  exact connectedComponent_eq_iff_mem

Depends on / 依赖: connectedComponent_eq_iff_mem, eq_comm, mem_pathComponent_iff, pathComponent_eq_connectedComponent
-/
theorem connectedComponent_eq_iff_joined (x y : X) :
    connectedComponent x = connectedComponent y ↔ Joined x y := by
  rw [← mem_pathComponent_iff]; rw [pathComponent_eq_connectedComponent]; rw [eq_comm]
  exact connectedComponent_eq_iff_mem

/--
theorem `connectedComponentSetoid_eq_pathSetoid` / 定理 `connectedComponentSetoid_eq_pathSetoid`

English:
theorem connectedComponentSetoid_eq_pathSetoid
  statement: connectedComponentSetoid X = pathSetoid X
  proof: Setoid.ext connectedComponent_eq_iff_joined

中文:
定理 connectedComponentSetoid_eq_pathSetoid
  结论: connectedComponentSetoid X = pathSetoid X
  证明: Setoid.ext connectedComponent_eq_iff_joined

Depends on / 依赖: Setoid, Setoid.ext, connectedComponent_eq_iff_joined
-/
theorem connectedComponentSetoid_eq_pathSetoid : connectedComponentSetoid X = pathSetoid X :=
  Setoid.ext connectedComponent_eq_iff_joined

/--
Definition of `connectedComponentsEquivZerothHomotopy` / `connectedComponentsEquivZerothHomotopy` 的定义

English:
definition connectedComponentsEquivZerothHomotopy
  signature: : ConnectedComponents X ≃ ZerothHomotopy X where
  body: Quotient.map id (connectedComponent_eq_iff_joined · · |>.mp ·)
  invFun := ZerothHomotopy.toConnectedComponents
left_inv := Quot.ind congrFun rfl
right_inv := Quot.ind congrFun rfl

@[simp]

中文:
定义 connectedComponentsEquivZerothHomotopy
  签名: : ConnectedComponents X ≃ ZerothHomotopy X where
  定义体: Quotient.map id (connectedComponent_eq_iff_joined · · |>.mp ·)
  invFun := ZerothHomotopy.toConnectedComponents
left_inv := Quot.ind congrFun rfl
right_inv := Quot.ind congrFun rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.map, connectedComponent_eq_iff_joined
-/
def connectedComponentsEquivZerothHomotopy : ConnectedComponents X ≃ ZerothHomotopy X where
  toFun := Quotient.map id (connectedComponent_eq_iff_joined · · |>.mp ·)
  invFun := ZerothHomotopy.toConnectedComponents
left_inv := Quot.ind congrFun rfl
right_inv := Quot.ind congrFun rfl

@[simp]
/--
lemma `connectedComponentsEquivZerothHomotopy_apply` / 引理 `connectedComponentsEquivZerothHomotopy_apply`

English:
lemma connectedComponentsEquivZerothHomotopy_apply
  given: (x : X)
  proof: rfl

@[simp]

中文:
引理 connectedComponentsEquivZerothHomotopy_apply
  条件: (x : X)
  证明: rfl

@[simp]
-/
lemma connectedComponentsEquivZerothHomotopy_apply (x : X) :
    connectedComponentsEquivZerothHomotopy ⟦x⟧ = (.mk x) :=
  rfl

@[simp]
/--
lemma `coe_connectedComponentsEquivZerothHomotopy_symm` / 引理 `coe_connectedComponentsEquivZerothHomotopy_symm`

English:
lemma coe_connectedComponentsEquivZerothHomotopy_symm
  proof: rfl

中文:
引理 coe_connectedComponentsEquivZerothHomotopy_symm
  证明: rfl
-/
lemma coe_connectedComponentsEquivZerothHomotopy_symm :
    ⇑connectedComponentsEquivZerothHomotopy.symm = ZerothHomotopy.toConnectedComponents (X := X) :=
  rfl

/--
lemma `connectedComponentsEquivZerothHomotopy_symm_apply` / 引理 `connectedComponentsEquivZerothHomotopy_symm_apply`

English:
lemma connectedComponentsEquivZerothHomotopy_symm_apply
  given: (x : X)
  proof: rfl

中文:
引理 connectedComponentsEquivZerothHomotopy_symm_apply
  条件: (x : X)
  证明: rfl
-/
lemma connectedComponentsEquivZerothHomotopy_symm_apply (x : X) :
    connectedComponentsEquivZerothHomotopy.symm (.mk x) = ⟦x⟧ :=
  rfl

/--
theorem `pathConnected_subset_basis` / 定理 `pathConnected_subset_basis`

English:
theorem pathConnected_subset_basis
  given: {U : Set X} (h : IsOpen U) (hx : x in U)
  proof: (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

中文:
定理 pathConnected_subset_basis
  条件: {U : Set X} (h : IsOpen U) (hx : x in U)
  证明: (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, hasBasis_self_subset, mem_nhds, path_connected_basis
-/
theorem pathConnected_subset_basis {U : Set X} (h : IsOpen U) (hx : x in U) :
    (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConnected s ∧ s subseteq U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/--
theorem `isOpen_isPathConnected_basis` / 定理 `isOpen_isPathConnected_basis`

English:
theorem isOpen_isPathConnected_basis
  given: (x : X)
  proof: by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn u x, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.tran

中文:
定理 isOpen_isPathConnected_basis
  条件: (x : X)
  证明: by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn u x, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.tran

Depends on / 依赖: hu.pathComponentIn, isPathConnected_pathComponentIn, mem_nhds_iff, mem_nhds_iff.mp, mem_nhds_iff.mpr, mem_pathComponentIn_self, pathComponentIn, pathComponentIn_subset, pathComponentIn_subset.trans
-/
theorem isOpen_isPathConnected_basis (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => IsOpen s ∧ x in s ∧ IsPathConnected s) id := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn u x, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.trans hus⟩

/--
theorem `Topology.IsOpenEmbedding.locallyPathConnectedSpace` / 定理 `Topology.IsOpenEmbedding.locallyPathConnectedSpace`

English:
theorem Topology.IsOpenEmbedding.locallyPathConnectedSpace
  given: {e : Y -> X} (he : IsOpenEmbedding e)
  proof: have (y : Y) :
      (𝓝 y).HasBasis (fun s => s in 𝓝 (e y) ∧ IsPathConnected s ∧ s subseteq range e) (e ⁻¹' ·) :=
he.basis_nhds pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ => by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]


中文:
定理 Topology.IsOpenEmbedding.locallyPathConnectedSpace
  条件: {e : Y -> X} (he : IsOpenEmbedding e)
  证明: have (y : Y) :
      (𝓝 y).HasBasis (fun s => s in 𝓝 (e y) ∧ IsPathConnected s ∧ s subseteq range e) (e ⁻¹' ·) :=
he.basis_nhds pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ => by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]


Depends on / 依赖: HasBasis, IsPathConnected, basis_nhds, he.basis_nhds, he.isOpen_range, he.isPathConnected_iff, image_preimage_eq_of_subset, isOpen_range, isPathConnected_iff, mem_range_self, of_bases, pathConnected_subset_basis, subseteq
-/
theorem Topology.IsOpenEmbedding.locallyPathConnectedSpace {e : Y -> X} (he : IsOpenEmbedding e) :
    LocallyPathConnectedSpace Y :=
  have (y : Y) :
      (𝓝 y).HasBasis (fun s => s in 𝓝 (e y) ∧ IsPathConnected s ∧ s subseteq range e) (e ⁻¹' ·) :=
he.basis_nhds pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ => by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]

@[deprecated (since := "2026-06-21")]
alias Topology.IsOpenEmbedding.locPathConnectedSpace :=
  Topology.IsOpenEmbedding.locallyPathConnectedSpace

/--
theorem `IsOpen.locallyPathConnectedSpace` / 定理 `IsOpen.locallyPathConnectedSpace`

English:
theorem IsOpen.locallyPathConnectedSpace
  given: {U : Set X} (h : IsOpen U)
  statement: LocallyPathConnectedSpace U
  proof: h.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias IsOpen.locPathConnectedSpace := IsOpen.locallyPathConnectedSpace

中文:
定理 IsOpen.locallyPathConnectedSpace
  条件: {U : Set X} (h : IsOpen U)
  结论: LocallyPathConnectedSpace U
  证明: h.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias IsOpen.locPathConnectedSpace := IsOpen.locallyPathConnectedSpace

Depends on / 依赖: h.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace, isOpenEmbedding_subtypeVal, locallyPathConnectedSpace
-/
theorem IsOpen.locallyPathConnectedSpace {U : Set X} (h : IsOpen U) : LocallyPathConnectedSpace U :=
  h.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias IsOpen.locPathConnectedSpace := IsOpen.locallyPathConnectedSpace

/--
theorem `IsOpen.isConnected_iff_isPathConnected` / 定理 `IsOpen.isConnected_iff_isPathConnected`

English:
theorem IsOpen.isConnected_iff_isPathConnected
  given: {U : Set X} (U_op : IsOpen U)
  proof: by
  rw [isConnected_iff_connectedSpace]; rw [isPathConnected_iff_pathConnectedSpace]
  have := U_op.locallyPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

中文:
定理 IsOpen.isConnected_iff_isPathConnected
  条件: {U : Set X} (U_op : IsOpen U)
  证明: by
  rw [isConnected_iff_connectedSpace]; rw [isPathConnected_iff_pathConnectedSpace]
  have := U_op.locallyPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

Depends on / 依赖: U_op, U_op.locallyPathConnectedSpace, isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace, locallyPathConnectedSpace, pathConnectedSpace_iff_connectedSpace, pathConnectedSpace_iff_connectedSpace.symm
-/
theorem IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) :
    IsConnected U ↔ IsPathConnected U := by
  rw [isConnected_iff_connectedSpace]; rw [isPathConnected_iff_pathConnectedSpace]
  have := U_op.locallyPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyConnectedSpace X
  body: by
  refine ⟨forall_imp (fun x h => ⟨fun s => ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs => ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ => mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

中文:
实例 :
  签名: LocallyConnectedSpace X
  定义体: by
  refine ⟨forall_imp (fun x h => ⟨fun s => ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs => ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ => mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

Depends on / 依赖: forall_imp, h.mem_iff, isConnected, isOpen_isPathConnected_basis, mem_iff, mem_nhds_iff, mem_nhds_iff.mpr
-/
instance : LocallyConnectedSpace X := by
  refine ⟨forall_imp (fun x h => ⟨fun s => ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs => ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ => mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

/--
lemma `locallyPathConnectedSpace_iff_isOpen_pathComponentIn` / 引理 `locallyPathConnectedSpace_iff_isOpen_pathComponentIn`

English:
lemma locallyPathConnectedSpace_iff_isOpen_pathComponentIn
  given: {X : Type*} [TopologicalSpace X]
  proof: ⟨fun _ _ _ hu => hu.pathComponentIn _, fun h => ⟨fun x => ⟨fun s => by
    refine ⟨fun hs => ?_, fun ⟨_, ht⟩ => Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn u x, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_

中文:
引理 locallyPathConnectedSpace_iff_isOpen_pathComponentIn
  条件: {X : 类型} [TopologicalSpace X]
  证明: ⟨fun _ _ _ hu => hu.pathComponentIn _, fun h => ⟨fun x => ⟨fun s => by
    refine ⟨fun hs => ?_, fun ⟨_, ht⟩ => Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn u x, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_

Depends on / 依赖: Filter, Filter.mem_of_superset, hu.pathComponentIn, isPathConnected_pathComponentIn, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, mem_of_superset, mem_pathComponentIn_self, pathComponentIn, pathComponentIn_subset, pathComponentIn_subset.trans
-/
lemma locallyPathConnectedSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] :
    LocallyPathConnectedSpace X ↔ forall (x : X) (u : Set X), IsOpen u -> IsOpen (pathComponentIn u x) :=
  ⟨fun _ _ _ hu => hu.pathComponentIn _, fun h => ⟨fun x => ⟨fun s => by
    refine ⟨fun hs => ?_, fun ⟨_, ht⟩ => Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn u x, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_pathComponentIn hu.2.2⟩, pathComponentIn_subset.trans hu.1⟩⟩⟩⟩

@[deprecated (since := "2026-06-21")]
alias locPathConnectedSpace_iff_isOpen_pathComponentIn :=
  locallyPathConnectedSpace_iff_isOpen_pathComponentIn

/--
lemma `locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds` / 引理 `locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds`

English:
lemma locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds
  given: {X : Type*} [TopologicalSpace X]
  proof: by
  rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  exact ⟨fun h x hxu => (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x => isOpen_iff_mem_nhds.mpr fun y hy =>


中文:
引理 locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds
  条件: {X : 类型} [TopologicalSpace X]
  证明: by
  rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  exact ⟨fun h x hxu => (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x => isOpen_iff_mem_nhds.mpr fun y hy =>


Depends on / 依赖: forall_comm, forall_congr, imp_congr_right, imp_forall_iff, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, locallyPathConnectedSpace_iff_isOpen_pathComponentIn, mem_nhds, mem_pathComponentIn_self, pathComponentIn_congr, pathComponentIn_subset, simp_rw
-/
lemma locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] :
    LocallyPathConnectedSpace X ↔
    forall x : X, forall u : Set X, IsOpen u -> x in u -> pathComponentIn u x in nhds x := by
  rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  exact ⟨fun h x hxu => (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x => isOpen_iff_mem_nhds.mpr fun y hy =>
pathComponentIn_congr hy ▸ h y pathComponentIn_subset hy⟩

@[deprecated (since := "2026-06-21")]
alias locPathConnectedSpace_iff_pathComponentIn_mem_nhds :=
  locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds

/--
lemma `LocallyPathConnectedSpace.coinduced` / 引理 `LocallyPathConnectedSpace.coinduced`

English:
lemma LocallyPathConnectedSpace.coinduced
  given: {Y : Type*} (f : X -> Y)
  proof: by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu =>
isOpen_coinduced.mpr isOpen_iff_mem_nhds.mpr fun x hx => ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refin

中文:
引理 LocallyPathConnectedSpace.coinduced
  条件: {Y : 类型} (f : X -> Y)
  证明: by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu =>
isOpen_coinduced.mpr isOpen_iff_mem_nhds.mpr fun x hx => ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refin

Depends on / 依赖: Continuous, TopologicalSpace, TopologicalSpace.coinduced, coinduced, continuous_coinduced_rng, hu.preimage, image_subset_iff, isOpen_coinduced, isOpen_coinduced.mpr, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, isPathConnected_pathComp, locallyPathConnectedSpace_iff_isOpen_pathComponentIn, locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr, mem_nhds_iff, mem_nhds_iff.mpr, mem_pathComponentIn_self, pathComponentIn, pathComponentIn_congr, pathComponentIn_subset
-/
lemma LocallyPathConnectedSpace.coinduced {Y : Type*} (f : X -> Y) :
    @LocallyPathConnectedSpace Y (.coinduced f ‹_›) := by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu =>
isOpen_coinduced.mpr isOpen_iff_mem_nhds.mpr fun x hx => ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refine mem_nhds_iff.mpr ⟨pathComponentIn (f ⁻¹' u) x, ?_,
    (hu.preimage hf).pathComponentIn _, mem_pathComponentIn_self hx'⟩
  rw [← image_subset_iff]; rw [← pathComponentIn_congr hx]
  exact ((isPathConnected_pathComponentIn hx').image hf).subset_pathComponentIn
⟨x, mem_pathComponentIn_self hx', rfl⟩
(image_mono pathComponentIn_subset).trans u.image_preimage_subset f

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.coinduced := LocallyPathConnectedSpace.coinduced

/--
lemma `Topology.IsQuotientMap.locallyPathConnectedSpace` / 引理 `Topology.IsQuotientMap.locallyPathConnectedSpace`

English:
lemma Topology.IsQuotientMap.locallyPathConnectedSpace
  given: {f : X -> Y} (h : IsQuotientMap f)
  proof: h.isCoinducing.eq_coinduced ▸ LocallyPathConnectedSpace.coinduced f

@[deprecated (since := "2026-06-21")]
alias Topology.IsQuotientMap.locPathConnectedSpace :=
  Topology.IsQuotientMap.locallyPathConnectedSpace

中文:
引理 Topology.IsQuotientMap.locallyPathConnectedSpace
  条件: {f : X -> Y} (h : IsQuotientMap f)
  证明: h.isCoinducing.eq_coinduced ▸ LocallyPathConnectedSpace.coinduced f

@[deprecated (since := "2026-06-21")]
alias Topology.IsQuotientMap.locPathConnectedSpace :=
  Topology.IsQuotientMap.locallyPathConnectedSpace

Depends on / 依赖: LocallyPathConnectedSpace, LocallyPathConnectedSpace.coinduced, coinduced, eq_coinduced, h.isCoinducing.eq_coinduced, isCoinducing
-/
lemma Topology.IsQuotientMap.locallyPathConnectedSpace {f : X -> Y} (h : IsQuotientMap f) :
    LocallyPathConnectedSpace Y :=
  h.isCoinducing.eq_coinduced ▸ LocallyPathConnectedSpace.coinduced f

@[deprecated (since := "2026-06-21")]
alias Topology.IsQuotientMap.locPathConnectedSpace :=
  Topology.IsQuotientMap.locallyPathConnectedSpace

/--
Instance `Quot.locallyPathConnectedSpace` / 实例 `Quot.locallyPathConnectedSpace`

English:
instance Quot.locallyPathConnectedSpace
  signature: {r : X -> X -> Prop}
  body: isQuotientMap_quot_mk.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quot.locPathConnectedSpace := Quot.locallyPathConnectedSpace

中文:
实例 Quot.locallyPathConnectedSpace
  签名: {r : X -> X -> 命题}
  定义体: isQuotientMap_quot_mk.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quot.locPathConnectedSpace := Quot.locallyPathConnectedSpace

Depends on / 依赖: isQuotientMap_quot_mk, isQuotientMap_quot_mk.locallyPathConnectedSpace, locallyPathConnectedSpace
-/
instance Quot.locallyPathConnectedSpace {r : X -> X -> Prop} : LocallyPathConnectedSpace (Quot r) :=
  isQuotientMap_quot_mk.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quot.locPathConnectedSpace := Quot.locallyPathConnectedSpace

/--
Instance `Quotient.locallyPathConnectedSpace` / 实例 `Quotient.locallyPathConnectedSpace`

English:
instance Quotient.locallyPathConnectedSpace
  signature: {s : Setoid X}
  body: isQuotientMap_quotient_mk'.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quotient.locPathConnectedSpace := Quotient.locallyPathConnectedSpace

中文:
实例 Quotient.locallyPathConnectedSpace
  签名: {s : Setoid X}
  定义体: isQuotientMap_quotient_mk'.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quotient.locPathConnectedSpace := Quotient.locallyPathConnectedSpace

Depends on / 依赖: isQuotientMap_quotient_mk, locallyPathConnectedSpace
-/
instance Quotient.locallyPathConnectedSpace {s : Setoid X} :
    LocallyPathConnectedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quotient.locPathConnectedSpace := Quotient.locallyPathConnectedSpace

/--
Instance `Sum.locallyPathConnectedSpace` / 实例 `Sum.locallyPathConnectedSpace`

English:
instance Sum.locallyPathConnectedSpace
  signature: [LocallyPathConnectedSpace Y]
  body: by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' pathComponentIn (Sum.inl ⁻¹' u) x, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact 

中文:
实例 Sum.locallyPathConnectedSpace
  签名: [LocallyPathConnectedSpace Y]
  定义体: by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' pathComponentIn (Sum.inl ⁻¹' u) x, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact 

Depends on / 依赖: IsPathConnected, IsPathConnected.subset_pathComponentIn, Sum.inl, continuous_inl, hu.preimage, image_mono, image_preimage_subset, isOpenMap_inl, isPathConnected_pathComponentIn, locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds, mem_nhds_iff, mem_pathComponentIn_self, pathCompone, pathComponentIn, pathComponentIn_subset, preimage, subset_pathComponentIn, u.image_preimage_subset
-/
instance Sum.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] :
    LocallyPathConnectedSpace (X oplus Y) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' pathComponentIn (Sum.inl ⁻¹' u) x, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inl
      · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
· exact isOpenMap_inl _ (hu.preimage continuous_inl).pathComponentIn _
    · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
  · refine ⟨Sum.inr '' pathComponentIn (Sum.inr ⁻¹' u) y, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inr
      · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
· exact isOpenMap_inr _ (hu.preimage continuous_inr).pathComponentIn _
    · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩

@[deprecated (since := "2026-06-21")]
alias Sum.locPathConnectedSpace := Sum.locallyPathConnectedSpace

/--
Instance `Sigma.locallyPathConnectedSpace` / 实例 `Sigma.locallyPathConnectedSpace`

English:
instance Sigma.locallyPathConnectedSpace
  signature: {X : ι -> Type*}
  body: by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' pathComponentIn ((Sigma.mk x.1) ⁻¹' u) x.2, ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).imag

中文:
实例 Sigma.locallyPathConnectedSpace
  签名: {X : ι -> 类型}
  定义体: by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' pathComponentIn ((Sigma.mk x.1) ⁻¹' u) x.2, ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).imag

Depends on / 依赖: IsPathConnected, IsPathConnected.subset_pathComponentIn, Sigma.mk, continuous_sigmaMk, hu.preimage, image_mono, image_preimage_subset, isOpenMap_sigmaMk, isPathConnected_pathComponentIn, locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds, mem_nhds_iff, mem_pathComponentIn_self, pathComponentIn, pathComponentIn_subset, preimage, subset_pathComponentIn, u.image_preimage_subset
-/
instance Sigma.locallyPathConnectedSpace {X : ι -> Type*}
    [(i : ι) -> TopologicalSpace (X i)] [(i : ι) -> LocallyPathConnectedSpace (X i)] :
    LocallyPathConnectedSpace ((i : ι) × X i) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' pathComponentIn ((Sigma.mk x.1) ⁻¹' u) x.2, ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_sigmaMk
    · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩
    · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
· exact isOpenMap_sigmaMk _ (hu.preimage continuous_sigmaMk).pathComponentIn _
  · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩

@[deprecated (since := "2026-06-21")]
alias Sigma.locPathConnectedSpace := Sigma.locallyPathConnectedSpace

/--
Instance `Prod.locallyPathConnectedSpace` / 实例 `Prod.locallyPathConnectedSpace`

English:
instance Prod.locallyPathConnectedSpace
  signature: [LocallyPathConnectedSpace Y]
  body: fun (x, y) => hasBasis_self.mpr fun U hU => by
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
    exact ⟨pathComponentIn u x ×ˢ pathComponentIn v y,
      prod_mem_nhds (pathComponentIn_mem_nhds hu) (pathComponentIn_mem_nhds hv),
      (isPathConnected_pathComponentIn (mem_of_mem_nhds hu)

中文:
实例 Prod.locallyPathConnectedSpace
  签名: [LocallyPathConnectedSpace Y]
  定义体: fun (x, y) => hasBasis_self.mpr fun U hU => by
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
    exact ⟨pathComponentIn u x ×ˢ pathComponentIn v y,
      prod_mem_nhds (pathComponentIn_mem_nhds hu) (pathComponentIn_mem_nhds hv),
      (isPathConnected_pathComponentIn (mem_of_mem_nhds hu)

Depends on / 依赖: Set.prod_mono, hasBasis_self, hasBasis_self.mpr, isPathConnected_pathComponentIn, mem_nhds_prod_iff, mem_nhds_prod_iff.mp, mem_of_mem_nhds, pathComponentIn, pathComponentIn_mem_nhds, pathComponentIn_subset, prod_mem_nhds, prod_mono
-/
instance Prod.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] :
    LocallyPathConnectedSpace (X × Y) where
  path_connected_basis := fun (x, y) => hasBasis_self.mpr fun U hU => by
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
    exact ⟨pathComponentIn u x ×ˢ pathComponentIn v y,
      prod_mem_nhds (pathComponentIn_mem_nhds hu) (pathComponentIn_mem_nhds hv),
      (isPathConnected_pathComponentIn (mem_of_mem_nhds hu)).prod
        (isPathConnected_pathComponentIn (mem_of_mem_nhds hv)),
      (Set.prod_mono pathComponentIn_subset pathComponentIn_subset).trans huv⟩

/--
theorem `Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace` / 定理 `Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace`

English:
theorem Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
  statement: {Z : ι -> Type*}
  proof: hasBasis_self.mpr fun U hU => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hU
    obtain ⟨J, hJ, t, ht, htU⟩ := hU
    let K := J union {i | ¬PathConnectedSpace (Z i)}
    refine ⟨K.pi fun i => pathComponentIn (t i) (x i),
      set_pi_mem_nhds (hJ.union hfinite) fun i _ => pathComponentIn_mem_nhds (h

中文:
定理 Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
  结论: {Z : ι -> 类型}
  证明: hasBasis_self.mpr fun U hU => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hU
    obtain ⟨J, hJ, t, ht, htU⟩ := hU
    let K := J union {i | ¬PathConnectedSpace (Z i)}
    refine ⟨K.pi fun i => pathComponentIn (t i) (x i),
      set_pi_mem_nhds (hJ.union hfinite) fun i _ => pathComponentIn_mem_nhds (h

Depends on / 依赖: Filter, Filter.mem_pi, K.pi, PathConnectedSpace, classical, hJ.union, hasBasis_self, hasBasis_self.mpr, hfinite, mem_pi, mem_union_left, nhds_pi, pathComponentIn, pathComponentIn_mem_nhds, pathComponentIn_subset, piecewise_eq_of_mem, set_pi_mem_nhds, univ_pi_piecewise_univ
-/
theorem Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace {Z : ι -> Type*}
    [forall i, TopologicalSpace (Z i)] [forall i, LocallyPathConnectedSpace (Z i)]
    (hfinite : {i | ¬PathConnectedSpace (Z i)}.Finite) :
    LocallyPathConnectedSpace (forall i, Z i) where
  path_connected_basis x := hasBasis_self.mpr fun U hU => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hU
    obtain ⟨J, hJ, t, ht, htU⟩ := hU
    let K := J union {i | ¬PathConnectedSpace (Z i)}
    refine ⟨K.pi fun i => pathComponentIn (t i) (x i),
      set_pi_mem_nhds (hJ.union hfinite) fun i _ => pathComponentIn_mem_nhds (ht i), ?_,
      fun f hf => htU fun i hiJ => pathComponentIn_subset (hf i (mem_union_left _ hiJ))⟩
    classical
    rw [← univ_pi_piecewise_univ]
    refine .pi fun i => ?_
    by_cases hi : i in K
    · rw [piecewise_eq_of_mem _ _ _ hi]
      exact isPathConnected_pathComponentIn (mem_of_mem_nhds (ht i))
    · rw [piecewise_eq_of_notMem _ _ _ hi]
      have : PathConnectedSpace (Z i) := not_not.mp (not_or.1 hi).2
      exact isPathConnected_univ

/--
Instance `Pi.locallyPathConnectedSpace_of_finite` / 实例 `Pi.locallyPathConnectedSpace_of_finite`

English:
instance Pi.locallyPathConnectedSpace_of_finite
  signature: [Finite ι] {Z : ι -> Type*}
  body: locallyPathConnectedSpace_of_finite_not_pathConnectedSpace (toFinite _)

中文:
实例 Pi.locallyPathConnectedSpace_of_finite
  签名: [Finite ι] {Z : ι -> 类型}
  定义体: locallyPathConnectedSpace_of_finite_not_pathConnectedSpace (toFinite _)

Depends on / 依赖: locallyPathConnectedSpace_of_finite_not_pathConnectedSpace, toFinite
-/
instance Pi.locallyPathConnectedSpace_of_finite [Finite ι] {Z : ι -> Type*}
    [forall i, TopologicalSpace (Z i)] [forall i, LocallyPathConnectedSpace (Z i)] :
    LocallyPathConnectedSpace (forall i, Z i) :=
  locallyPathConnectedSpace_of_finite_not_pathConnectedSpace (toFinite _)

/--
Instance `Pi.locallyPathConnectedSpace` / 实例 `Pi.locallyPathConnectedSpace`

English:
instance Pi.locallyPathConnectedSpace
  signature: {Z : ι -> Type*} [forall i, TopologicalSpace (Z i)]
  body: locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

中文:
实例 Pi.locallyPathConnectedSpace
  签名: {Z : ι -> 类型} [对任意 i, TopologicalSpace (Z i)]
  定义体: locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

Depends on / 依赖: finite_empty, finite_empty.subset, locallyPathConnectedSpace_of_finite_not_pathConnectedSpace, subset
-/
instance Pi.locallyPathConnectedSpace {Z : ι -> Type*} [forall i, TopologicalSpace (Z i)]
    [forall i, LocallyPathConnectedSpace (Z i)] [forall i, PathConnectedSpace (Z i)] :
    LocallyPathConnectedSpace (forall i, Z i) :=
  locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

/--
theorem `Pi.locallyPathConnectedSpace_iff` / 定理 `Pi.locallyPathConnectedSpace_iff`

English:
theorem Pi.locallyPathConnectedSpace_iff
  given: {Z : ι -> Type*} [forall i, TopologicalSpace (Z i)]
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, Z i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (Z i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
    

中文:
定理 Pi.locallyPathConnectedSpace_iff
  条件: {Z : ι -> 类型} [对任意 i, TopologicalSpace (Z i)]
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, Z i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (Z i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
    

Depends on / 依赖: Classical, Classical.nonempty_pi.mp, Filter, Filter.mem_pi, IsOpen, IsOpen.pathComponent, Nonempty, classical, continuous_apply, isEmpty_or_nonempty, isOpenMap_eval, isQuotientMap, locallyPathConnectedSpace, mem_nhds, mem_pathComponent_self, mem_pi, nhds_pi, nonempty_pi, pathComponent, surjective_eval
-/
theorem Pi.locallyPathConnectedSpace_iff {Z : ι -> Type*} [forall i, TopologicalSpace (Z i)] :
    LocallyPathConnectedSpace (forall i, Z i) ↔
      IsEmpty (forall i, Z i) ∨
        (forall i, LocallyPathConnectedSpace (Z i)) ∧ {i | ¬PathConnectedSpace (Z i)}.Finite := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, Z i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (Z i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
      (surjective_eval i)).locallyPathConnectedSpace, ?_⟩
    have hVn : pathComponent x in 𝓝 x :=
      (IsOpen.pathComponent x).mem_nhds (mem_pathComponent_self x)
    rw [nhds_pi]; rw [Filter.mem_pi] at hVn
    obtain ⟨J, hJ, t, ht, htV⟩ := hVn
    refine hJ.subset fun i hi => by_contra fun hiJ => hi ?_
    suffices himg : eval i '' pathComponent x = univ from pathConnectedSpace_iff_univ.mpr
      (himg ▸ isPathConnected_pathComponent.image (continuous_apply i))
    refine (subset_univ _).antisymm fun z _ => ⟨update x i z, htV fun j hj => ?_, by simp⟩
    rw [update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
    exact mem_of_mem_nhds (ht j)
  · rintro (he | ⟨hloc, hfin⟩)
    · exact ⟨he.elim⟩
    · exact locallyPathConnectedSpace_of_finite_not_pathConnectedSpace hfin

/--
Instance `AlexandrovDiscrete.locallyPathConnectedSpace` / 实例 `AlexandrovDiscrete.locallyPathConnectedSpace`

English:
instance AlexandrovDiscrete.locallyPathConnectedSpace
  signature: [AlexandrovDiscrete X]
  body: by
  apply LocallyPathConnectedSpace.of_bases nhds_basis_nhdsKer_singleton
  simp only [forall_const, IsPathConnected, mem_nhdsKer_singleton]
  intro x
  exists x, specializes_rfl
  intro y hy
  symm
  apply hy.joinedIn <;> rewrite [mem_nhdsKer_singleton] <;> [assumption; rfl]

@[deprecated (since :

中文:
实例 AlexandrovDiscrete.locallyPathConnectedSpace
  签名: [AlexandrovDiscrete X]
  定义体: by
  apply LocallyPathConnectedSpace.of_bases nhds_basis_nhdsKer_singleton
  simp only [forall_const, IsPathConnected, mem_nhdsKer_singleton]
  intro x
  exists x, specializes_rfl
  intro y hy
  symm
  apply hy.joinedIn <;> rewrite [mem_nhdsKer_singleton] <;> [assumption; rfl]

@[deprecated (since :

Depends on / 依赖: IsPathConnected, LocallyPathConnectedSpace, LocallyPathConnectedSpace.of_bases, forall_const, hy.joinedIn, joinedIn, mem_nhdsKer_singleton, nhds_basis_nhdsKer_singleton, of_bases, rewrite, specializes_rfl
-/
instance AlexandrovDiscrete.locallyPathConnectedSpace [AlexandrovDiscrete X] :
    LocallyPathConnectedSpace X := by
  apply LocallyPathConnectedSpace.of_bases nhds_basis_nhdsKer_singleton
  simp only [forall_const, IsPathConnected, mem_nhdsKer_singleton]
  intro x
  exists x, specializes_rfl
  intro y hy
  symm
  apply hy.joinedIn <;> rewrite [mem_nhdsKer_singleton] <;> [assumption; rfl]

@[deprecated (since := "2026-06-21")]
alias AlexandrovDiscrete.locPathConnectedSpace := AlexandrovDiscrete.locallyPathConnectedSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology ZerothHomotopy X
  body: by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  rw [← ZerothHomotopy.isQuotientMap_mk.isOpen_preimage]
  grind [ZerothHomotopy.preimage_singleton_eq_pathComponent, IsOpen.pathComponent]

中文:
实例 :
  签名: DiscreteTopology ZerothHomotopy X
  定义体: by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  rw [← ZerothHomotopy.isQuotientMap_mk.isOpen_preimage]
  grind [ZerothHomotopy.preimage_singleton_eq_pathComponent, IsOpen.pathComponent]

Depends on / 依赖: IsOpen, IsOpen.pathComponent, ZerothHomotopy, ZerothHomotopy.isQuotientMap_mk.isOpen_preimage, ZerothHomotopy.mk_surjective, ZerothHomotopy.preimage_singleton_eq_pathComponent, discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, isOpen_preimage, isQuotientMap_mk, mk_surjective, pathComponent, preimage_singleton_eq_pathComponent
-/
instance : DiscreteTopology ZerothHomotopy X := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  rw [← ZerothHomotopy.isQuotientMap_mk.isOpen_preimage]
  grind [ZerothHomotopy.preimage_singleton_eq_pathComponent, IsOpen.pathComponent]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] : Finite ZerothHomotopy X
  body: finite_of_compact_of_discrete

中文:
实例 [CompactSpace
  签名: X] : Finite ZerothHomotopy X
  定义体: finite_of_compact_of_discrete

Depends on / 依赖: finite_of_compact_of_discrete
-/
instance [CompactSpace X] : Finite ZerothHomotopy X :=
  finite_of_compact_of_discrete

end LocallyPathConnectedSpace
