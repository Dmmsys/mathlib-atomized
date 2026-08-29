/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!

# Jacobson spaces

## Main results
- `JacobsonSpace`: The class of Jacobson spaces, i.e.
  spaces such that the set of closed points are dense in every closed subspace.
- `jacobsonSpace_iff_locallyClosed`:
  `X` is a Jacobson space iff every locally closed subset contains a closed point of `X`.
- `JacobsonSpace.discreteTopology`:
  If `X` only has finitely many closed points, then the topology on `X` is discrete.

## References
- https://stacks.math.columbia.edu/tag/005T

-/

@[expose] public section

open Topology TopologicalSpace

variable (X) {Y} [TopologicalSpace X] [TopologicalSpace Y] {f : X -> Y}

section closedPoints

/--
Definition of `closedPoints` / `closedPoints` 的定义

English:
definition closedPoints
  signature: : Set X
  body: Set.ofPred (IsClosed {·})

中文:
定义 closedPoints
  签名: : Set X
  定义体: Set.ofPred (IsClosed {·})

Depends on / 依赖: IsClosed, Set.ofPred, ofPred
-/
def closedPoints : Set X := Set.ofPred (IsClosed {·})

variable {X}

@[simp]
/--
lemma `mem_closedPoints_iff` / 引理 `mem_closedPoints_iff`

English:
lemma mem_closedPoints_iff
  given: {x}
  statement: x in closedPoints X ↔ IsClosed {x}
  proof: Iff.rfl

中文:
引理 mem_closedPoints_iff
  条件: {x}
  结论: x in closedPoints X ↔ IsClosed {x}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_closedPoints_iff {x} : x in closedPoints X ↔ IsClosed {x} := Iff.rfl

/--
lemma `preimage_closedPoints_subset` / 引理 `preimage_closedPoints_subset`

English:
lemma preimage_closedPoints_subset
  given: (hf : Function.Injective f) (hf' : Continuous f)
  proof: by
  intro x hx
  rw [mem_closedPoints_iff]
  convert! continuous_iff_isClosed.mp hf' _ hx
  rw [← Set.image_singleton]; rw [Set.preimage_image_eq _ hf]

中文:
引理 preimage_closedPoints_subset
  条件: (hf : Function.Injective f) (hf' : Continuous f)
  证明: by
  intro x hx
  rw [mem_closedPoints_iff]
  convert! continuous_iff_isClosed.mp hf' _ hx
  rw [← Set.image_singleton]; rw [Set.preimage_image_eq _ hf]

Depends on / 依赖: Set.image_singleton, Set.preimage_image_eq, continuous_iff_isClosed, continuous_iff_isClosed.mp, convert, image_singleton, mem_closedPoints_iff, preimage_image_eq
-/
lemma preimage_closedPoints_subset (hf : Function.Injective f) (hf' : Continuous f) :
    f ⁻¹' closedPoints Y subseteq closedPoints X := by
  intro x hx
  rw [mem_closedPoints_iff]
  convert! continuous_iff_isClosed.mp hf' _ hx
  rw [← Set.image_singleton]; rw [Set.preimage_image_eq _ hf]

/--
lemma `Topology.IsClosedEmbedding.preimage_closedPoints` / 引理 `Topology.IsClosedEmbedding.preimage_closedPoints`

English:
lemma Topology.IsClosedEmbedding.preimage_closedPoints
  given: (hf : IsClosedEmbedding f)
  proof: by
  ext x
  simp [mem_closedPoints_iff, ← Set.image_singleton, hf.isClosed_iff_image_isClosed]

中文:
引理 Topology.IsClosedEmbedding.preimage_closedPoints
  条件: (hf : IsClosedEmbedding f)
  证明: by
  ext x
  simp [mem_closedPoints_iff, ← Set.image_singleton, hf.isClosed_iff_image_isClosed]

Depends on / 依赖: Set.image_singleton, hf.isClosed_iff_image_isClosed, image_singleton, isClosed_iff_image_isClosed, mem_closedPoints_iff
-/
lemma Topology.IsClosedEmbedding.preimage_closedPoints (hf : IsClosedEmbedding f) :
    f ⁻¹' closedPoints Y = closedPoints X := by
  ext x
  simp [mem_closedPoints_iff, ← Set.image_singleton, hf.isClosed_iff_image_isClosed]

/--
lemma `closedPoints_eq_univ` / 引理 `closedPoints_eq_univ`

English:
lemma closedPoints_eq_univ
  given: [T1Space X]
  proof: Set.eq_univ_iff_forall.mpr fun _ => isClosed_singleton

中文:
引理 closedPoints_eq_univ
  条件: [T1Space X]
  证明: Set.eq_univ_iff_forall.mpr fun _ => isClosed_singleton

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, eq_univ_iff_forall, isClosed_singleton
-/
lemma closedPoints_eq_univ [T1Space X] :
    closedPoints X = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun _ => isClosed_singleton

/--
lemma `Set.Finite.isDiscrete_of_subset_closedPoints` / 引理 `Set.Finite.isDiscrete_of_subset_closedPoints`

English:
lemma Set.Finite.isDiscrete_of_subset_closedPoints
  proof: by
  have : T1Space s := ⟨fun x => by convert! (hs' x.2).preimage continuous_subtype_val; aesop⟩
  have : Finite s := hs
  exact ⟨inferInstance⟩

中文:
引理 Set.Finite.isDiscrete_of_subset_closedPoints
  证明: by
  have : T1Space s := ⟨fun x => by convert! (hs' x.2).preimage continuous_subtype_val; aesop⟩
  have : Finite s := hs
  exact ⟨inferInstance⟩

Depends on / 依赖: Finite, T1Space, continuous_subtype_val, convert, preimage
-/
lemma Set.Finite.isDiscrete_of_subset_closedPoints
    {s : Set X} (hs : s.Finite) (hs' : s subseteq closedPoints X) : IsDiscrete s := by
  have : T1Space s := ⟨fun x => by convert! (hs' x.2).preimage continuous_subtype_val; aesop⟩
  have : Finite s := hs
  exact ⟨inferInstance⟩

end closedPoints

/-- The class of Jacobson spaces, i.e.
spaces such that the set of closed points are dense in every closed subspace. -/
@[mk_iff, stacks 005U]
/--
Definition of `JacobsonSpace` / `JacobsonSpace` 的定义

English:
class JacobsonSpace
  parameters: : Prop where
  axioms and operations (1):
    - closure_inter_closedPoints : forall {Z}, IsClosed Z -> closure (Z inter closedPoints X) = Z

中文:
类 JacobsonSpace
  参数: : 命题 where
  公理与运算 (1 个):
    - closure_inter_closedPoints : 对任意 {Z}, IsClosed Z -> closure (Z inter closedPoints X) = Z
-/
class JacobsonSpace : Prop where
  closure_inter_closedPoints : forall {Z}, IsClosed Z -> closure (Z inter closedPoints X) = Z

export JacobsonSpace (closure_inter_closedPoints)

variable {X}

/--
lemma `closure_closedPoints` / 引理 `closure_closedPoints`

English:
lemma closure_closedPoints
  given: [JacobsonSpace X]
  statement: closure (closedPoints X) = Set.univ
  proof: by
  simpa using closure_inter_closedPoints isClosed_univ

中文:
引理 closure_closedPoints
  条件: [JacobsonSpace X]
  结论: closure (closedPoints X) = Set.univ
  证明: by
  simpa using closure_inter_closedPoints isClosed_univ

Depends on / 依赖: closure_inter_closedPoints, isClosed_univ
-/
lemma closure_closedPoints [JacobsonSpace X] : closure (closedPoints X) = Set.univ := by
  simpa using closure_inter_closedPoints isClosed_univ

/--
lemma `jacobsonSpace_iff_locallyClosed` / 引理 `jacobsonSpace_iff_locallyClosed`

English:
lemma jacobsonSpace_iff_locallyClosed
  proof: by
  rw [jacobsonSpace_iff]
  constructor
  · simp_rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff,
      Set.nonempty_iff_ne_empty]
    intro H Z hZ hZ' e
    have : Z subseteq closure Z \ Z := by
      refine subset_closure.trans ?_
      nth_rw 1 [← H isClosed_closure]
      r

中文:
引理 jacobsonSpace_iff_locallyClosed
  证明: by
  rw [jacobsonSpace_iff]
  constructor
  · simp_rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff,
      Set.nonempty_iff_ne_empty]
    intro H Z hZ hZ' e
    have : Z subseteq closure Z \ Z := by
      refine subset_closure.trans ?_
      nth_rw 1 [← H isClosed_closure]
      r

Depends on / 依赖: Set.bot_e, Set.disjoint_iff, Set.inter_assoc, Set.inter_comm, Set.inter_subset_left, Set.inter_subset_right, Set.nonempty_iff_ne_empty, Set.subset_sdiff, bot_e, closure, closure_subset_iff, coborder, disjoint_iff, disjoint_self, inter_assoc, inter_comm, inter_subset_left, inter_subset_right, isClosed_closure, isLocallyClosed_iff_isOpen_coborder
-/
lemma jacobsonSpace_iff_locallyClosed :
    JacobsonSpace X ↔ forall Z, Z.Nonempty -> IsLocallyClosed Z -> (Z inter closedPoints X).Nonempty := by
  rw [jacobsonSpace_iff]
  constructor
  · simp_rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff,
      Set.nonempty_iff_ne_empty]
    intro H Z hZ hZ' e
    have : Z subseteq closure Z \ Z := by
      refine subset_closure.trans ?_
      nth_rw 1 [← H isClosed_closure]
      rw [hZ'.closure_subset_iff]; rw [Set.subset_sdiff]; rw [Set.disjoint_iff]; rw [Set.inter_assoc]; rw [Set.inter_comm _ Z]; rw [e]
      exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩
    rw [Set.subset_sdiff]; rw [disjoint_self]; rw [Set.bot_eq_empty] at this
    exact hZ this.2
  · intro H Z hZ
    refine subset_antisymm (hZ.closure_subset_iff.mpr Set.inter_subset_left) ?_
    rw [← Set.disjoint_compl_left_iff_subset]; rw [Set.disjoint_iff_inter_eq_empty]; rw [← Set.not_nonempty_iff_eq_empty]
    intro H'
    have := H _ H' (isClosed_closure.isOpen_compl.isLocallyClosed.inter hZ.isLocallyClosed)
    rw [Set.nonempty_iff_ne_empty]; rw [Set.inter_assoc]; rw [ne_eq]; rw [← Set.disjoint_iff_inter_eq_empty]; rw [Set.disjoint_compl_left_iff_subset] at this
    exact this subset_closure

/--
lemma `nonempty_inter_closedPoints` / 引理 `nonempty_inter_closedPoints`

English:
lemma nonempty_inter_closedPoints
  statement: [JacobsonSpace X] {Z : Set X}
  proof: jacobsonSpace_iff_locallyClosed.mp inferInstance Z hZ hZ'

中文:
引理 nonempty_inter_closedPoints
  结论: [JacobsonSpace X] {Z : Set X}
  证明: jacobsonSpace_iff_locallyClosed.mp inferInstance Z hZ hZ'

Depends on / 依赖: jacobsonSpace_iff_locallyClosed, jacobsonSpace_iff_locallyClosed.mp
-/
lemma nonempty_inter_closedPoints [JacobsonSpace X] {Z : Set X}
    (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z inter closedPoints X).Nonempty :=
  jacobsonSpace_iff_locallyClosed.mp inferInstance Z hZ hZ'

/--
theorem `JacobsonSpace.closure_inter_closedPoints_eq_closure` / 定理 `JacobsonSpace.closure_inter_closedPoints_eq_closure`

English:
theorem JacobsonSpace.closure_inter_closedPoints_eq_closure
  statement: [JacobsonSpace X]
  proof: by
  refine (closure_mono (Set.inter_subset_left)).antisymm ?_
  rw [IsClosed.closure_subset_iff isClosed_closure]
  intro x hx
  by_contra H
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := nonempty_inter_closedPoints (Z := S \ closure (S inter closedPoints X))
    ⟨x, hx, H⟩ (.inter hS isClosed_closure.isOpen_com

中文:
定理 JacobsonSpace.closure_inter_closedPoints_eq_closure
  结论: [JacobsonSpace X]
  证明: by
  refine (closure_mono (Set.inter_subset_left)).antisymm ?_
  rw [IsClosed.closure_subset_iff isClosed_closure]
  intro x hx
  by_contra H
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := nonempty_inter_closedPoints (Z := S \ closure (S inter closedPoints X))
    ⟨x, hx, H⟩ (.inter hS isClosed_closure.isOpen_com

Depends on / 依赖: IsClosed, IsClosed.closure_subset_iff, Set.inter_subset_left, antisymm, closedPoints, closure, closure_mono, closure_subset_iff, inter_subset_left, isClosed_closure, isClosed_closure.isOpen_compl.isLocallyClosed, isLocallyClosed, isOpen_compl, nonempty_inter_closedPoints, subset_closure
-/
theorem JacobsonSpace.closure_inter_closedPoints_eq_closure [JacobsonSpace X]
    {S : Set X} (hS : IsLocallyClosed S) : closure (S inter closedPoints X) = closure S := by
  refine (closure_mono (Set.inter_subset_left)).antisymm ?_
  rw [IsClosed.closure_subset_iff isClosed_closure]
  intro x hx
  by_contra H
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := nonempty_inter_closedPoints (Z := S \ closure (S inter closedPoints X))
    ⟨x, hx, H⟩ (.inter hS isClosed_closure.isOpen_compl.isLocallyClosed)
  exact hy₂ (subset_closure ⟨hy₁, hy₃⟩)

/--
lemma `isClosed_singleton_of_isLocallyClosed_singleton` / 引理 `isClosed_singleton_of_isLocallyClosed_singleton`

English:
lemma isClosed_singleton_of_isLocallyClosed_singleton
  statement: [JacobsonSpace X] {x : X}
  proof: by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
  exact hy'

中文:
引理 isClosed_singleton_of_isLocallyClosed_singleton
  结论: [JacobsonSpace X] {x : X}
  证明: by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
  exact hy'

Depends on / 依赖: Set.singleton_nonempty, nonempty_inter_closedPoints, singleton_nonempty
-/
lemma isClosed_singleton_of_isLocallyClosed_singleton [JacobsonSpace X] {x : X}
    (hx : IsLocallyClosed {x}) : IsClosed {x} := by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
  exact hy'

/--
lemma `Topology.IsOpenEmbedding.preimage_closedPoints` / 引理 `Topology.IsOpenEmbedding.preimage_closedPoints`

English:
lemma Topology.IsOpenEmbedding.preimage_closedPoints
  given: (hf : IsOpenEmbedding f) [JacobsonSpace Y]
  proof: by
  apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)

中文:
引理 Topology.IsOpenEmbedding.preimage_closedPoints
  条件: (hf : IsOpenEmbedding f) [JacobsonSpace Y]
  证明: by
  apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)

Depends on / 依赖: Set.image_singleton, continuous, hf.continuous, hf.injective, hf.isInducing, hf.isOpen_range.isLocallyClosed, hx.isLocallyClosed.image, image_singleton, injective, isClosed_singleton_of_isLocallyClosed_singleton, isInducing, isLocallyClosed, isOpen_range, preimage_closedPoints_subset, subset_antisymm
-/
lemma Topology.IsOpenEmbedding.preimage_closedPoints (hf : IsOpenEmbedding f) [JacobsonSpace Y] :
    f ⁻¹' closedPoints Y = closedPoints X := by
  apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)

/--
lemma `JacobsonSpace.of_isOpenEmbedding` / 引理 `JacobsonSpace.of_isOpenEmbedding`

English:
lemma JacobsonSpace.of_isOpenEmbedding
  given: [JacobsonSpace Y] (hf : IsOpenEmbedding f)
  proof: by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

中文:
引理 JacobsonSpace.of_isOpenEmbedding
  条件: [JacobsonSpace Y] (hf : IsOpenEmbedding f)
  证明: by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

Depends on / 依赖: hZ.image, hf.isInducing, hf.isOpen_range.isLocallyClosed, hf.preimage_closedPoints, isInducing, isLocallyClosed, isOpen_range, jacobsonSpace_iff_locallyClosed, nonempty_inter_closedPoints, preimage_closedPoints
-/
lemma JacobsonSpace.of_isOpenEmbedding [JacobsonSpace Y] (hf : IsOpenEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

/--
lemma `JacobsonSpace.of_isClosedEmbedding` / 引理 `JacobsonSpace.of_isClosedEmbedding`

English:
lemma JacobsonSpace.of_isClosedEmbedding
  given: [JacobsonSpace Y] (hf : IsClosedEmbedding f)
  proof: by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

中文:
引理 JacobsonSpace.of_isClosedEmbedding
  条件: [JacobsonSpace Y] (hf : IsClosedEmbedding f)
  证明: by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

Depends on / 依赖: hZ.image, hf.isClosed_range.isLocallyClosed, hf.isInducing, hf.preimage_closedPoints, isClosed_range, isInducing, isLocallyClosed, jacobsonSpace_iff_locallyClosed, nonempty_inter_closedPoints, preimage_closedPoints
-/
lemma JacobsonSpace.of_isClosedEmbedding [JacobsonSpace Y] (hf : IsClosedEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed]; rw [← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

/--
lemma `JacobsonSpace.discreteTopology` / 引理 `JacobsonSpace.discreteTopology`

English:
lemma JacobsonSpace.discreteTopology
  statement: [JacobsonSpace X]
  proof: by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff]; rw [← closure_closedPoints]; rw [closure_subset_iff_isClosed]; rw [← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ => id
  have inst : Finite X := Set.finite_univ_iff.mp (this ▸ h)
  rw [discreteT

中文:
引理 JacobsonSpace.discreteTopology
  结论: [JacobsonSpace X]
  证明: by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff]; rw [← closure_closedPoints]; rw [closure_subset_iff_isClosed]; rw [← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ => id
  have inst : Finite X := Set.finite_univ_iff.mp (this ▸ h)
  rw [discreteT

Depends on / 依赖: Finite, Set.finite_univ_iff.mp, Set.univ, Set.univ_subset_iff, biUnion_of_singleton, closedPoints, closure_closedPoints, closure_subset_iff_isClosed, discreteTopology_iff_forall_isOpen, finite_univ_iff, h.isClosed_biUnion, isClosed_biUnion, isClosed_compl_iff, mem_closedPoints_iff, toFinite, toFinite.isClosed_biUnion, univ_subset_iff
-/
lemma JacobsonSpace.discreteTopology [JacobsonSpace X]
    (h : (closedPoints X).Finite) : DiscreteTopology X := by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff]; rw [← closure_closedPoints]; rw [closure_subset_iff_isClosed]; rw [← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ => id
  have inst : Finite X := Set.finite_univ_iff.mp (this ▸ h)
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [← isClosed_compl_iff]; rw [← sᶜ.biUnion_of_singleton]
  refine sᶜ.toFinite.isClosed_biUnion fun x _ => ?_
  rw [← mem_closedPoints_iff]; rw [this]
  trivial

instance (priority := 100) [Finite X] [JacobsonSpace X] : DiscreteTopology X :=
  JacobsonSpace.discreteTopology (Set.toFinite _)

instance (priority := 100) [T1Space X] : JacobsonSpace X :=
  ⟨by simp [closedPoints_eq_univ, closure_eq_iff_isClosed]⟩

/--
lemma `TopologicalSpace.IsOpenCover.jacobsonSpace_iff` / 引理 `TopologicalSpace.IsOpenCover.jacobsonSpace_iff`

English:
lemma TopologicalSpace.IsOpenCover.jacobsonSpace_iff
  statement: {ι : Type*} {U : ι -> Opens X}
  proof: by
  refine ⟨fun H i => .of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal, fun H => ?_⟩
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  rw [← hU.iUnion_inter Z]; rw [Set.nonempty_iUnion] at hZ
  obtain ⟨i, x, hx, hx'⟩ := hZ
  obtain ⟨y, hy, hy'⟩ := (jacobsonSpace_iff_locallyClosed.mp 

中文:
引理 TopologicalSpace.IsOpenCover.jacobsonSpace_iff
  结论: {ι : 类型} {U : ι -> Opens X}
  证明: by
  refine ⟨fun H i => .of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal, fun H => ?_⟩
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  rw [← hU.iUnion_inter Z]; rw [Set.nonempty_iUnion] at hZ
  obtain ⟨i, x, hx, hx'⟩ := hZ
  obtain ⟨y, hy, hy'⟩ := (jacobsonSpace_iff_locallyClosed.mp 

Depends on / 依赖: IsClosed, Set.nonempty_iUnion, Subtype, continuous_subtype_val, convert_to, hU.iUnion_inter, hU.isClosed_iff_coe_preimage.mpr, iUnion_inter, isClosed_iff_coe_preimage, isOpenEmbedding_subtypeVal, jacobsonSpace_iff_locallyClosed, jacobsonSpace_iff_locallyClosed.mp, nonempty_iUnion, of_isOpenEmbedding, preimage
-/
lemma TopologicalSpace.IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι -> Opens X}
    (hU : IsOpenCover U) : JacobsonSpace X ↔ forall i, JacobsonSpace (U i) := by
  refine ⟨fun H i => .of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal, fun H => ?_⟩
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  rw [← hU.iUnion_inter Z]; rw [Set.nonempty_iUnion] at hZ
  obtain ⟨i, x, hx, hx'⟩ := hZ
  obtain ⟨y, hy, hy'⟩ := (jacobsonSpace_iff_locallyClosed.mp (H i)) _ ⟨⟨x, hx'⟩, hx⟩
    (hZ'.preimage continuous_subtype_val)
  refine ⟨y, hy, hU.isClosed_iff_coe_preimage.mpr fun j => ?_⟩
  by_cases h : (y : X) in U j
  · convert_to IsClosed {(⟨y, h⟩ : U j)}
    · ext; simp [← Subtype.coe_inj]
    apply isClosed_singleton_of_isLocallyClosed_singleton
    convert!
      (hy'.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
            (U i).2.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed).preimage
        continuous_subtype_val
    ext
    simp [← Subtype.coe_inj]
  · convert! isClosed_empty
    rw [Set.eq_empty_iff_forall_notMem]
    intro z (hz : z.1 = y.1)
    exact h (hz ▸ z.2)

/--
theorem `subsingleton_image_closure_of_finite_of_isPreirreducible` / 定理 `subsingleton_image_closure_of_finite_of_isPreirreducible`

English:
theorem subsingleton_image_closure_of_finite_of_isPreirreducible
  statement: [JacobsonSpace X]
  proof: by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  replace hS' : IsIrreducible S := ⟨hS'', hS'⟩
  have H₁ : IsIrreducible (S inter closedPoints X) := by
    rwa [← isIrreducible_iff_closure, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      isIrreducible_iff_closure] at hS'
  

中文:
定理 subsingleton_image_closure_of_finite_of_isPreirreducible
  结论: [JacobsonSpace X]
  证明: by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  replace hS' : IsIrreducible S := ⟨hS'', hS'⟩
  have H₁ : IsIrreducible (S inter closedPoints X) := by
    rwa [← isIrreducible_iff_closure, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      isIrreducible_iff_closure] at hS'
  

Depends on / 依赖: IsIrreducible, JacobsonSpace, JacobsonSpace.closure_inter_closedPoints_eq_closure, S.eq_empty_or_nonempty, Set.image_mono, Set.inter_subset_left, closedPoints, closure_inter_closedPoints_eq_closure, eq_empty_or_nonempty, hfS.subset, image_mono, inter_subset_left, isDiscrete_of_subset_closedPoints, isIrreducible_iff_closure, replace, subset, subseteq
-/
theorem subsingleton_image_closure_of_finite_of_isPreirreducible [JacobsonSpace X]
    {S : Set X} (hS : IsLocallyClosed S) (hS' : IsPreirreducible S)
    (hf₁ : Continuous f) (hf₂ : IsClosedMap f) (hfS : (f '' S).Finite) :
    (f '' closure S).Subsingleton := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  replace hS' : IsIrreducible S := ⟨hS'', hS'⟩
  have H₁ : IsIrreducible (S inter closedPoints X) := by
    rwa [← isIrreducible_iff_closure, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      isIrreducible_iff_closure] at hS'
  have H₂ : f '' (S inter closedPoints X) subseteq closedPoints Y := by
    rintro _ ⟨x, hx, rfl⟩; simpa using hf₂ _ hx.2
  have H₃ := ((hfS.subset (Set.image_mono Set.inter_subset_left)).isDiscrete_of_subset_closedPoints
    H₂).subsingleton_of_isPreirreducible (H₁.image _ hf₁.continuousOn).isPreirreducible
  have H₄ : IsClosed (f '' (S inter closedPoints X)) := by
    obtain (h | ⟨x, hx⟩) := Set.eq_empty_or_nonempty (f '' (S inter closedPoints X))
    · simp [h]
    · rw [H₃.eq_singleton_of_mem hx]; exact H₂ hx
  have := image_closure_subset_closure_image (s := S inter closedPoints X) hf₁
  rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hS]; rw [H₄.closure_eq] at this
  exact H₃.anti this
