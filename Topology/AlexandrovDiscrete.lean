/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Compactness.NhdsKer

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open. As such,
the intersection of all neighborhoods of a set is a neighborhood itself. Hence every set has a
minimal neighborhood, which we call the *neighborhoods kernel* of the set.

## Main declarations

* `AlexandrovDiscrete`: Prop-valued typeclass for a topological space to be Alexandrov-discrete

## Tags

Alexandroff, discrete, finitely generated, fg space
-/

public section

open Filter Set TopologicalSpace Topology

/-- A topological space is **Alexandrov-discrete** or **finitely generated** if the intersection of
a family of open sets is open. -/
@[mk_iff]
/--
Definition of `AlexandrovDiscrete` / `AlexandrovDiscrete` 的定义

English:
class AlexandrovDiscrete
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (1):
    - isOpen_sInter : forall S : Set (Set α), (forall s in S, IsOpen s) -> IsOpen (⋂₀ S)

中文:
类 AlexandrovDiscrete
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (1 个):
    - isOpen_sInter : 对任意 S : 集合 (集合 α), (对任意 s in S, 是开集 s) -> 是开集 (⋂₀ S)
-/
class AlexandrovDiscrete (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of a family of open sets is an open set. Use `isOpen_sInter` in the root
  namespace instead. -/
  protected isOpen_sInter : forall S : Set (Set α), (forall s in S, IsOpen s) -> IsOpen (⋂₀ S)

variable {ι : Sort*} {κ : ι -> Sort*} {α β : Type*}
section
variable [TopologicalSpace α] [TopologicalSpace β]

/--
lemma `alexandrovDiscrete_iff_isClosed` / 引理 `alexandrovDiscrete_iff_isClosed`

English:
lemma alexandrovDiscrete_iff_isClosed
  proof: by
  conv_lhs => tactic =>
    simp_rw +singlePass [alexandrovDiscrete_iff, compl_surjective.image_surjective.forall,
      forall_mem_image, ← compl_sUnion, isOpen_compl_iff]

中文:
引理 alexandrovDiscrete_iff_isClosed
  证明: by
  conv_lhs => tactic =>
    simp_rw +singlePass [alexandrovDiscrete_iff, compl_surjective.image_surjective.forall,
      forall_mem_image, ← compl_sUnion, isOpen_compl_iff]

Depends on / 依赖: alexandrovDiscrete_iff, compl_sUnion, compl_surjective, compl_surjective.image_surjective.forall, conv_lhs, forall_mem_image, image_surjective, isOpen_compl_iff, simp_rw, singlePass, tactic
-/
lemma alexandrovDiscrete_iff_isClosed :
    AlexandrovDiscrete α ↔ forall S : Set (Set α), (forall s in S, IsClosed s) -> IsClosed (⋃₀ S) := by
  conv_lhs => tactic =>
    simp_rw +singlePass [alexandrovDiscrete_iff, compl_surjective.image_surjective.forall,
      forall_mem_image, ← compl_sUnion, isOpen_compl_iff]

/--
Instance `IndiscreteTopology.toAlexandrovDiscrete` / 实例 `IndiscreteTopology.toAlexandrovDiscrete`

English:
instance IndiscreteTopology.toAlexandrovDiscrete
  signature: [IndiscreteTopology α]
  body: by grind [isOpen_iff]

中文:
实例 Indiscrete拓扑.toAlexandrovDiscrete
  签名: [Indiscrete拓扑 α]
  定义体: by grind [isOpen_iff]

Depends on / 依赖: isOpen_iff
-/
instance IndiscreteTopology.toAlexandrovDiscrete [IndiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter := by grind [isOpen_iff]

/--
Instance `DiscreteTopology.toAlexandrovDiscrete` / 实例 `DiscreteTopology.toAlexandrovDiscrete`

English:
instance DiscreteTopology.toAlexandrovDiscrete
  signature: [DiscreteTopology α]
  body: isOpen_discrete _

中文:
实例 离散拓扑.toAlexandrovDiscrete
  签名: [离散拓扑 α]
  定义体: isOpen_discrete _

Depends on / 依赖: isOpen_discrete
-/
instance DiscreteTopology.toAlexandrovDiscrete [DiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter _ _ := isOpen_discrete _

/--
Instance `Finite.toAlexandrovDiscrete` / 实例 `Finite.toAlexandrovDiscrete`

English:
instance Finite.toAlexandrovDiscrete
  signature: [Finite α]
  body: (toFinite S).isOpen_sInter

中文:
实例 有限.toAlexandrovDiscrete
  签名: [有限 α]
  定义体: (toFinite S).isOpen_sInter

Depends on / 依赖: isOpen_sInter, toFinite
-/
instance Finite.toAlexandrovDiscrete [Finite α] : AlexandrovDiscrete α where
  isOpen_sInter S := (toFinite S).isOpen_sInter

section AlexandrovDiscrete
variable [AlexandrovDiscrete α] {S : Set (Set α)} {f : ι -> Set α}

/--
lemma `isOpen_sInter` / 引理 `isOpen_sInter`

English:
lemma isOpen_sInter
  statement: (forall s in S, IsOpen s) -> IsOpen (⋂₀ S)
  proof: AlexandrovDiscrete.isOpen_sInter _

中文:
引理 isOpen_s整数er
  结论: (对任意 s in S, 是开集 s) -> 是开集 (⋂₀ S)
  证明: AlexandrovDiscrete.isOpen_sInter _

Depends on / 依赖: AlexandrovDiscrete, AlexandrovDiscrete.isOpen_sInter, isOpen_sInter
-/
lemma isOpen_sInter : (forall s in S, IsOpen s) -> IsOpen (⋂₀ S) := AlexandrovDiscrete.isOpen_sInter _

/--
lemma `isOpen_iInter` / 引理 `isOpen_iInter`

English:
lemma isOpen_iInter
  given: (hf : forall i, IsOpen (f i))
  statement: IsOpen (⋂ i, f i)
  proof: isOpen_sInter forall_mem_range.2 hf

中文:
引理 isOpen_i整数er
  条件: (hf : 对任意 i, 是开集 (f i))
  结论: 是开集 (⋂ i, f i)
  证明: isOpen_sInter forall_mem_range.2 hf

Depends on / 依赖: forall_mem_range, isOpen_sInter
-/
lemma isOpen_iInter (hf : forall i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
isOpen_sInter forall_mem_range.2 hf

/--
lemma `isOpen_iInter₂` / 引理 `isOpen_iInter₂`

English:
lemma isOpen_iInter₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsOpen (f i j))
  proof: isOpen_iInter fun _ => isOpen_iInter hf _

中文:
引理 isOpen_i整数er₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, 是开集 (f i j))
  证明: isOpen_iInter fun _ => isOpen_iInter hf _

Depends on / 依赖: isOpen_iInter
-/
lemma isOpen_iInter₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsOpen (f i j)) :
    IsOpen (⋂ i, ⋂ j, f i j) :=
isOpen_iInter fun _ => isOpen_iInter hf _

/--
lemma `isClosed_sUnion` / 引理 `isClosed_sUnion`

English:
lemma isClosed_sUnion
  given: (hS : forall s in S, IsClosed s)
  statement: IsClosed (⋃₀ S)
  proof: alexandrovDiscrete_iff_isClosed.mp inferInstance S hS

中文:
引理 isClosed_sUnion
  条件: (hS : 对任意 s in S, 是闭集 s)
  结论: 是闭集 (⋃₀ S)
  证明: alexandrovDiscrete_iff_isClosed.mp inferInstance S hS

Depends on / 依赖: alexandrovDiscrete_iff_isClosed, alexandrovDiscrete_iff_isClosed.mp
-/
lemma isClosed_sUnion (hS : forall s in S, IsClosed s) : IsClosed (⋃₀ S) :=
  alexandrovDiscrete_iff_isClosed.mp inferInstance S hS

/--
lemma `isClosed_iUnion` / 引理 `isClosed_iUnion`

English:
lemma isClosed_iUnion
  given: (hf : forall i, IsClosed (f i))
  statement: IsClosed (⋃ i, f i)
  proof: isClosed_sUnion forall_mem_range.2 hf

中文:
引理 isClosed_iUnion
  条件: (hf : 对任意 i, 是闭集 (f i))
  结论: 是闭集 (⋃ i, f i)
  证明: isClosed_sUnion forall_mem_range.2 hf

Depends on / 依赖: forall_mem_range, isClosed_sUnion
-/
lemma isClosed_iUnion (hf : forall i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
isClosed_sUnion forall_mem_range.2 hf

/--
lemma `isClosed_iUnion₂` / 引理 `isClosed_iUnion₂`

English:
lemma isClosed_iUnion₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsClosed (f i j))
  proof: isClosed_iUnion fun _ => isClosed_iUnion hf _

中文:
引理 isClosed_iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, 是闭集 (f i j))
  证明: isClosed_iUnion fun _ => isClosed_iUnion hf _

Depends on / 依赖: isClosed_iUnion
-/
lemma isClosed_iUnion₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsClosed (f i j)) :
    IsClosed (⋃ i, ⋃ j, f i j) :=
isClosed_iUnion fun _ => isClosed_iUnion hf _

/--
lemma `isClopen_sInter` / 引理 `isClopen_sInter`

English:
lemma isClopen_sInter
  given: (hS : forall s in S, IsClopen s)
  statement: IsClopen (⋂₀ S)
  proof: ⟨isClosed_sInter fun s hs => (hS s hs).1, isOpen_sInter fun s hs => (hS s hs).2⟩

中文:
引理 isClopen_s整数er
  条件: (hS : 对任意 s in S, IsClopen s)
  结论: IsClopen (⋂₀ S)
  证明: ⟨isClosed_sInter fun s hs => (hS s hs).1, isOpen_sInter fun s hs => (hS s hs).2⟩

Depends on / 依赖: isClosed_sInter, isOpen_sInter
-/
lemma isClopen_sInter (hS : forall s in S, IsClopen s) : IsClopen (⋂₀ S) :=
  ⟨isClosed_sInter fun s hs => (hS s hs).1, isOpen_sInter fun s hs => (hS s hs).2⟩

/--
lemma `isClopen_iInter` / 引理 `isClopen_iInter`

English:
lemma isClopen_iInter
  given: (hf : forall i, IsClopen (f i))
  statement: IsClopen (⋂ i, f i)
  proof: ⟨isClosed_iInter fun i => (hf i).1, isOpen_iInter fun i => (hf i).2⟩

中文:
引理 isClopen_i整数er
  条件: (hf : 对任意 i, IsClopen (f i))
  结论: IsClopen (⋂ i, f i)
  证明: ⟨isClosed_iInter fun i => (hf i).1, isOpen_iInter fun i => (hf i).2⟩

Depends on / 依赖: isClosed_iInter, isOpen_iInter
-/
lemma isClopen_iInter (hf : forall i, IsClopen (f i)) : IsClopen (⋂ i, f i) :=
  ⟨isClosed_iInter fun i => (hf i).1, isOpen_iInter fun i => (hf i).2⟩

/--
lemma `isClopen_iInter₂` / 引理 `isClopen_iInter₂`

English:
lemma isClopen_iInter₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsClopen (f i j))
  proof: isClopen_iInter fun _ => isClopen_iInter hf _

中文:
引理 isClopen_i整数er₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, IsClopen (f i j))
  证明: isClopen_iInter fun _ => isClopen_iInter hf _

Depends on / 依赖: isClopen_iInter
-/
lemma isClopen_iInter₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsClopen (f i j)) :
    IsClopen (⋂ i, ⋂ j, f i j) :=
isClopen_iInter fun _ => isClopen_iInter hf _

/--
lemma `isClopen_sUnion` / 引理 `isClopen_sUnion`

English:
lemma isClopen_sUnion
  given: (hS : forall s in S, IsClopen s)
  statement: IsClopen (⋃₀ S)
  proof: ⟨isClosed_sUnion fun s hs => (hS s hs).1, isOpen_sUnion fun s hs => (hS s hs).2⟩

中文:
引理 isClopen_sUnion
  条件: (hS : 对任意 s in S, IsClopen s)
  结论: IsClopen (⋃₀ S)
  证明: ⟨isClosed_sUnion fun s hs => (hS s hs).1, isOpen_sUnion fun s hs => (hS s hs).2⟩

Depends on / 依赖: isClosed_sUnion, isOpen_sUnion
-/
lemma isClopen_sUnion (hS : forall s in S, IsClopen s) : IsClopen (⋃₀ S) :=
  ⟨isClosed_sUnion fun s hs => (hS s hs).1, isOpen_sUnion fun s hs => (hS s hs).2⟩

/--
lemma `isClopen_iUnion` / 引理 `isClopen_iUnion`

English:
lemma isClopen_iUnion
  given: (hf : forall i, IsClopen (f i))
  statement: IsClopen (⋃ i, f i)
  proof: ⟨isClosed_iUnion fun i => (hf i).1, isOpen_iUnion fun i => (hf i).2⟩

中文:
引理 isClopen_iUnion
  条件: (hf : 对任意 i, IsClopen (f i))
  结论: IsClopen (⋃ i, f i)
  证明: ⟨isClosed_iUnion fun i => (hf i).1, isOpen_iUnion fun i => (hf i).2⟩

Depends on / 依赖: isClosed_iUnion, isOpen_iUnion
-/
lemma isClopen_iUnion (hf : forall i, IsClopen (f i)) : IsClopen (⋃ i, f i) :=
  ⟨isClosed_iUnion fun i => (hf i).1, isOpen_iUnion fun i => (hf i).2⟩

/--
lemma `isClopen_iUnion₂` / 引理 `isClopen_iUnion₂`

English:
lemma isClopen_iUnion₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsClopen (f i j))
  proof: isClopen_iUnion fun _ => isClopen_iUnion hf _

中文:
引理 isClopen_iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, IsClopen (f i j))
  证明: isClopen_iUnion fun _ => isClopen_iUnion hf _

Depends on / 依赖: isClopen_iUnion
-/
lemma isClopen_iUnion₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsClopen (f i j)) :
    IsClopen (⋃ i, ⋃ j, f i j) :=
isClopen_iUnion fun _ => isClopen_iUnion hf _

/--
lemma `interior_iInter` / 引理 `interior_iInter`

English:
lemma interior_iInter
  given: (f : ι -> Set α)
  statement: interior (⋂ i, f i) = ⋂ i, interior (f i)
  proof: (interior_maximal (iInter_mono fun _ => interior_subset) <| isOpen_iInter fun _ =>
    isOpen_interior).antisymm' <| subset_iInter fun _ => interior_mono <| iInter_subset _ _

中文:
引理 interior_i整数er
  条件: (f : ι -> 集合 α)
  结论: interior (⋂ i, f i) = ⋂ i, interior (f i)
  证明: (interior_maximal (iInter_mono fun _ => interior_subset) <| isOpen_iInter fun _ =>
    isOpen_interior).antisymm' <| subset_iInter fun _ => interior_mono <| iInter_subset _ _

Depends on / 依赖: antisymm, iInter_mono, iInter_subset, interior_maximal, interior_mono, interior_subset, isOpen_iInter, isOpen_interior, subset_iInter
-/
lemma interior_iInter (f : ι -> Set α) : interior (⋂ i, f i) = ⋂ i, interior (f i) :=
  (interior_maximal (iInter_mono fun _ => interior_subset) <| isOpen_iInter fun _ =>
    isOpen_interior).antisymm' <| subset_iInter fun _ => interior_mono <| iInter_subset _ _

/--
lemma `interior_sInter` / 引理 `interior_sInter`

English:
lemma interior_sInter
  given: (S : Set (Set α))
  statement: interior (⋂₀ S) = ⋂ s in S, interior s
  proof: by
  simp_rw [sInter_eq_biInter, interior_iInter]

中文:
引理 interior_s整数er
  条件: (S : 集合 (集合 α))
  结论: interior (⋂₀ S) = ⋂ s in S, interior s
  证明: by
  simp_rw [sInter_eq_biInter, interior_iInter]

Depends on / 依赖: interior_iInter, sInter_eq_biInter, simp_rw
-/
lemma interior_sInter (S : Set (Set α)) : interior (⋂₀ S) = ⋂ s in S, interior s := by
  simp_rw [sInter_eq_biInter, interior_iInter]

/--
lemma `closure_iUnion` / 引理 `closure_iUnion`

English:
lemma closure_iUnion
  given: (f : ι -> Set α)
  statement: closure (⋃ i, f i) = ⋃ i, closure (f i)
  proof: compl_injective by
    simpa only [← interior_compl, compl_iUnion] using interior_iInter fun i => (f i)ᶜ

中文:
引理 closure_iUnion
  条件: (f : ι -> 集合 α)
  结论: closure (⋃ i, f i) = ⋃ i, closure (f i)
  证明: compl_injective by
    simpa only [← interior_compl, compl_iUnion] using interior_iInter fun i => (f i)ᶜ

Depends on / 依赖: compl_iUnion, compl_injective, interior_compl, interior_iInter
-/
lemma closure_iUnion (f : ι -> Set α) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
compl_injective by
    simpa only [← interior_compl, compl_iUnion] using interior_iInter fun i => (f i)ᶜ

/--
lemma `closure_sUnion` / 引理 `closure_sUnion`

English:
lemma closure_sUnion
  given: (S : Set (Set α))
  statement: closure (⋃₀ S) = ⋃ s in S, closure s
  proof: by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

中文:
引理 closure_sUnion
  条件: (S : 集合 (集合 α))
  结论: closure (⋃₀ S) = ⋃ s in S, closure s
  证明: by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

Depends on / 依赖: closure_iUnion, sUnion_eq_biUnion, simp_rw
-/
lemma closure_sUnion (S : Set (Set α)) : closure (⋃₀ S) = ⋃ s in S, closure s := by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

end AlexandrovDiscrete

/--
lemma `Topology.IsInducing.alexandrovDiscrete` / 引理 `Topology.IsInducing.alexandrovDiscrete`

English:
lemma Topology.IsInducing.alexandrovDiscrete
  given: [AlexandrovDiscrete α] {f : β -> α} (h : IsInducing f)
  proof: by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

中文:
引理 拓扑.是Inducing.alexandrovDiscrete
  条件: [AlexandrovDiscrete α] {f : β -> α} (h : 是Inducing f)
  证明: by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

Depends on / 依赖: h.isOpen_iff, isOpen_iff, preimage_iInter, sInter_eq_biInter, simp_rw
-/
lemma Topology.IsInducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β -> α} (h : IsInducing f) :
    AlexandrovDiscrete β where
  isOpen_sInter S hS := by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

end

/--
lemma `AlexandrovDiscrete.sup` / 引理 `AlexandrovDiscrete.sup`

English:
lemma AlexandrovDiscrete.sup
  statement: {t₁ t₂ : TopologicalSpace α} (_ : @AlexandrovDiscrete α t₁)
  proof: @AlexandrovDiscrete.mk α (t₁ ⊔ t₂) fun _S hS =>
    ⟨@isOpen_sInter _ t₁ _ _ fun _s hs => (hS _ hs).1, isOpen_sInter fun _s hs => (hS _ hs).2⟩

中文:
引理 AlexandrovDiscrete.上确界
  结论: {t₁ t₂ : 拓扑空间 α} (_ : @AlexandrovDiscrete α t₁)
  证明: @AlexandrovDiscrete.mk α (t₁ ⊔ t₂) fun _S hS =>
    ⟨@isOpen_sInter _ t₁ _ _ fun _s hs => (hS _ hs).1, isOpen_sInter fun _s hs => (hS _ hs).2⟩

Depends on / 依赖: AlexandrovDiscrete, AlexandrovDiscrete.mk, isOpen_sInter
-/
lemma AlexandrovDiscrete.sup {t₁ t₂ : TopologicalSpace α} (_ : @AlexandrovDiscrete α t₁)
    (_ : @AlexandrovDiscrete α t₂) :
    @AlexandrovDiscrete α (t₁ ⊔ t₂) :=
  @AlexandrovDiscrete.mk α (t₁ ⊔ t₂) fun _S hS =>
    ⟨@isOpen_sInter _ t₁ _ _ fun _s hs => (hS _ hs).1, isOpen_sInter fun _s hs => (hS _ hs).2⟩

/--
lemma `alexandrovDiscrete_iSup` / 引理 `alexandrovDiscrete_iSup`

English:
lemma alexandrovDiscrete_iSup
  given: {t : ι -> TopologicalSpace α} (_ : forall i, @AlexandrovDiscrete α (t i))
  proof: @AlexandrovDiscrete.mk α (⨆ i, t i)
    fun _S hS => isOpen_iSup_iff.2
      fun i => @isOpen_sInter _ (t i) _ _
        fun _s hs => isOpen_iSup_iff.1 (hS _ hs) _

中文:
引理 alexandrovDiscrete_iSup
  条件: {t : ι -> 拓扑空间 α} (_ : 对任意 i, @AlexandrovDiscrete α (t i))
  证明: @AlexandrovDiscrete.mk α (⨆ i, t i)
    fun _S hS => isOpen_iSup_iff.2
      fun i => @isOpen_sInter _ (t i) _ _
        fun _s hs => isOpen_iSup_iff.1 (hS _ hs) _

Depends on / 依赖: AlexandrovDiscrete, AlexandrovDiscrete.mk, isOpen_iSup_iff, isOpen_sInter
-/
lemma alexandrovDiscrete_iSup {t : ι -> TopologicalSpace α} (_ : forall i, @AlexandrovDiscrete α (t i)) :
    @AlexandrovDiscrete α (⨆ i, t i) :=
  @AlexandrovDiscrete.mk α (⨆ i, t i)
    fun _S hS => isOpen_iSup_iff.2
      fun i => @isOpen_sInter _ (t i) _ _
        fun _s hs => isOpen_iSup_iff.1 (hS _ hs) _

section
variable [TopologicalSpace α] [TopologicalSpace β] [AlexandrovDiscrete α] [AlexandrovDiscrete β]
  {s t : Set α} {a : α}

/--
lemma `isOpen_nhdsKer` / 引理 `isOpen_nhdsKer`

English:
lemma isOpen_nhdsKer
  statement: IsOpen (nhdsKer s)
  proof: by
  rw [nhdsKer_def]; exact isOpen_sInter fun _ => And.left

中文:
引理 isOpen_nhdsKer
  结论: 是开集 (nhdsKer s)
  证明: by
  rw [nhdsKer_def]; exact isOpen_sInter fun _ => And.left
-/
@[simp] lemma isOpen_nhdsKer : IsOpen (nhdsKer s) := by
  rw [nhdsKer_def]; exact isOpen_sInter fun _ => And.left

/--
lemma `nhdsKer_mem_nhdsSet` / 引理 `nhdsKer_mem_nhdsSet`

English:
lemma nhdsKer_mem_nhdsSet
  statement: nhdsKer s in 𝓝ˢ s
  proof: isOpen_nhdsKer.mem_nhdsSet.2 subset_nhdsKer

中文:
引理 nhdsKer_mem_nhdsSet
  结论: nhdsKer s in 𝓝ˢ s
  证明: isOpen_nhdsKer.mem_nhdsSet.2 subset_nhdsKer

Depends on / 依赖: isOpen_nhdsKer, isOpen_nhdsKer.mem_nhdsSet, mem_nhdsSet, subset_nhdsKer
-/
lemma nhdsKer_mem_nhdsSet : nhdsKer s in 𝓝ˢ s := isOpen_nhdsKer.mem_nhdsSet.2 subset_nhdsKer

/--
lemma `nhdsKer_eq_iff_isOpen` / 引理 `nhdsKer_eq_iff_isOpen`

English:
lemma nhdsKer_eq_iff_isOpen
  statement: nhdsKer s = s ↔ IsOpen s
  proof: ⟨fun h => h ▸ isOpen_nhdsKer, IsOpen.nhdsKer_eq⟩

中文:
引理 nhdsKer_eq_iff_isOpen
  结论: nhdsKer s = s ↔ 是开集 s
  证明: ⟨fun h => h ▸ isOpen_nhdsKer, IsOpen.nhdsKer_eq⟩
-/
@[simp] lemma nhdsKer_eq_iff_isOpen : nhdsKer s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_nhdsKer, IsOpen.nhdsKer_eq⟩

/--
lemma `nhdsKer_subset_iff_isOpen` / 引理 `nhdsKer_subset_iff_isOpen`

English:
lemma nhdsKer_subset_iff_isOpen
  statement: nhdsKer s subseteq s ↔ IsOpen s
  proof: by
  simp only [nhdsKer_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_nhdsKer, and_true]

中文:
引理 nhdsKer_subset_iff_isOpen
  结论: nhdsKer s subseteq s ↔ 是开集 s
  证明: by
  simp only [nhdsKer_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_nhdsKer, and_true]
-/
@[simp] lemma nhdsKer_subset_iff_isOpen : nhdsKer s subseteq s ↔ IsOpen s := by
  simp only [nhdsKer_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_nhdsKer, and_true]

/--
lemma `nhdsKer_subset_iff` / 引理 `nhdsKer_subset_iff`

English:
lemma nhdsKer_subset_iff
  statement: nhdsKer s subseteq t ↔ exists U, IsOpen U ∧ s subseteq U ∧ U subseteq t
  proof: ⟨fun h => ⟨nhdsKer s, isOpen_nhdsKer, subset_nhdsKer, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ => (nhdsKer_minimal hsU hU).trans hUt⟩

中文:
引理 nhdsKer_subset_iff
  结论: nhdsKer s subseteq t ↔ 存在 U, 是开集 U ∧ s subseteq U ∧ U subseteq t
  证明: ⟨fun h => ⟨nhdsKer s, isOpen_nhdsKer, subset_nhdsKer, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ => (nhdsKer_minimal hsU hU).trans hUt⟩

Depends on / 依赖: isOpen_nhdsKer, nhdsKer, nhdsKer_minimal, subset_nhdsKer
-/
lemma nhdsKer_subset_iff : nhdsKer s subseteq t ↔ exists U, IsOpen U ∧ s subseteq U ∧ U subseteq t :=
  ⟨fun h => ⟨nhdsKer s, isOpen_nhdsKer, subset_nhdsKer, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ => (nhdsKer_minimal hsU hU).trans hUt⟩

/--
lemma `nhdsKer_subset_iff_mem_nhdsSet` / 引理 `nhdsKer_subset_iff_mem_nhdsSet`

English:
lemma nhdsKer_subset_iff_mem_nhdsSet
  statement: nhdsKer s subseteq t ↔ t in 𝓝ˢ s
  proof: nhdsKer_subset_iff.trans mem_nhdsSet_iff_exists.symm

中文:
引理 nhdsKer_subset_iff_mem_nhdsSet
  结论: nhdsKer s subseteq t ↔ t in 𝓝ˢ s
  证明: nhdsKer_subset_iff.trans mem_nhdsSet_iff_exists.symm

Depends on / 依赖: mem_nhdsSet_iff_exists, mem_nhdsSet_iff_exists.symm, nhdsKer_subset_iff, nhdsKer_subset_iff.trans
-/
lemma nhdsKer_subset_iff_mem_nhdsSet : nhdsKer s subseteq t ↔ t in 𝓝ˢ s :=
  nhdsKer_subset_iff.trans mem_nhdsSet_iff_exists.symm

/--
lemma `nhdsKer_singleton_subset_iff_mem_nhds` / 引理 `nhdsKer_singleton_subset_iff_mem_nhds`

English:
lemma nhdsKer_singleton_subset_iff_mem_nhds
  statement: nhdsKer {a} subseteq t ↔ t in 𝓝 a
  proof: by
  simp [nhdsKer_subset_iff_mem_nhdsSet]

中文:
引理 nhdsKer_singleton_subset_iff_mem_nhds
  结论: nhdsKer {a} subseteq t ↔ t in 𝓝 a
  证明: by
  simp [nhdsKer_subset_iff_mem_nhdsSet]

Depends on / 依赖: nhdsKer_subset_iff_mem_nhdsSet
-/
lemma nhdsKer_singleton_subset_iff_mem_nhds : nhdsKer {a} subseteq t ↔ t in 𝓝 a := by
  simp [nhdsKer_subset_iff_mem_nhdsSet]

/--
lemma `gc_nhdsKer_interior` / 引理 `gc_nhdsKer_interior`

English:
lemma gc_nhdsKer_interior
  statement: GaloisConnection (nhdsKer : Set α -> Set α) interior
  proof: fun s t => by simp [nhdsKer_subset_iff, subset_interior_iff]

中文:
引理 gc_nhdsKer_interior
  结论: GaloisConnection (nhdsKer : 集合 α -> 集合 α) interior
  证明: fun s t => by simp [nhdsKer_subset_iff, subset_interior_iff]

Depends on / 依赖: nhdsKer_subset_iff, subset_interior_iff
-/
lemma gc_nhdsKer_interior : GaloisConnection (nhdsKer : Set α -> Set α) interior :=
  fun s t => by simp [nhdsKer_subset_iff, subset_interior_iff]

/--
lemma `principal_nhdsKer` / 引理 `principal_nhdsKer`

English:
lemma principal_nhdsKer
  given: (s : Set α)
  statement: 𝓟 (nhdsKer s) = 𝓝ˢ s
  proof: by
  rw [← nhdsSet_nhdsKer]; rw [isOpen_nhdsKer.nhdsSet_eq]

中文:
引理 principal_nhdsKer
  条件: (s : 集合 α)
  结论: 𝓟 (nhdsKer s) = 𝓝ˢ s
  证明: by
  rw [← nhdsSet_nhdsKer]; rw [isOpen_nhdsKer.nhdsSet_eq]
-/
@[simp] lemma principal_nhdsKer (s : Set α) : 𝓟 (nhdsKer s) = 𝓝ˢ s := by
  rw [← nhdsSet_nhdsKer]; rw [isOpen_nhdsKer.nhdsSet_eq]

/--
lemma `principal_nhdsKer_singleton` / 引理 `principal_nhdsKer_singleton`

English:
lemma principal_nhdsKer_singleton
  given: (a : α)
  statement: 𝓟 (nhdsKer {a}) = 𝓝 a
  proof: by
  rw [principal_nhdsKer]; rw [nhdsSet_singleton]

中文:
引理 principal_nhdsKer_singleton
  条件: (a : α)
  结论: 𝓟 (nhdsKer {a}) = 𝓝 a
  证明: by
  rw [principal_nhdsKer]; rw [nhdsSet_singleton]

Depends on / 依赖: nhdsSet_singleton, principal_nhdsKer
-/
lemma principal_nhdsKer_singleton (a : α) : 𝓟 (nhdsKer {a}) = 𝓝 a := by
  rw [principal_nhdsKer]; rw [nhdsSet_singleton]

/--
lemma `nhdsSet_basis_nhdsKer` / 引理 `nhdsSet_basis_nhdsKer`

English:
lemma nhdsSet_basis_nhdsKer
  given: (s : Set α)
  proof: principal_nhdsKer s ▸ hasBasis_principal (nhdsKer s)

中文:
引理 nhdsSet_basis_nhdsKer
  条件: (s : 集合 α)
  证明: principal_nhdsKer s ▸ hasBasis_principal (nhdsKer s)

Depends on / 依赖: PartialOrder, PartialOrder.lift, UniformSpace, UniformSpace.ext, hasBasis_principal, nhdsKer, principal_nhdsKer
-/
lemma nhdsSet_basis_nhdsKer (s : Set α) :
    (𝓝ˢ s).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer s) :=
  principal_nhdsKer s ▸ hasBasis_principal (nhdsKer s)

/--
lemma `nhds_basis_nhdsKer_singleton` / 引理 `nhds_basis_nhdsKer_singleton`

English:
lemma nhds_basis_nhdsKer_singleton
  given: (a : α)
  proof: principal_nhdsKer_singleton a ▸ hasBasis_principal (nhdsKer {a})

中文:
引理 nhds_basis_nhdsKer_singleton
  条件: (a : α)
  证明: principal_nhdsKer_singleton a ▸ hasBasis_principal (nhdsKer {a})

Depends on / 依赖: UniformSpace, UniformSpace.ofCore, _mono, hasBasis_principal, iInf_le, iInf_le_of_le, le_iInf, le_rfl, le_trans, map_mono, nhdsKer, ofCore, principal_nhdsKer_singleton, toCore, u.comp, u.symm, u.toCore.refl, uniformity
-/
lemma nhds_basis_nhdsKer_singleton (a : α) :
    (𝓝 a).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer {a}) :=
  principal_nhdsKer_singleton a ▸ hasBasis_principal (nhdsKer {a})

/--
lemma `isOpen_iff_forall_specializes` / 引理 `isOpen_iff_forall_specializes`

English:
lemma isOpen_iff_forall_specializes
  statement: IsOpen s ↔ forall x y, x ⤳ y -> y in s -> x in s
  proof: by
  simp only [← nhdsKer_subset_iff_isOpen, Set.subset_def, mem_nhdsKer_iff_specializes, exists_imp,
    and_imp, @forall_comm (_ ⤳ _)]

omit [AlexandrovDiscrete α] in

中文:
引理 isOpen_iff_对任意_specializes
  结论: 是开集 s ↔ 对任意 x y, x ⤳ y -> y in s -> x in s
  证明: by
  simp only [← nhdsKer_subset_iff_isOpen, Set.subset_def, mem_nhdsKer_iff_specializes, exists_imp,
    and_imp, @forall_comm (_ ⤳ _)]

omit [AlexandrovDiscrete α] in

Depends on / 依赖: Set.subset_def, UniformSpace, UniformSpace.mk, and_imp, comap_top, exists_imp, forall_comm, le_top, mem_nhdsKer_iff_specializes, nhdsKer_subset_iff_isOpen, nhds_top, subset_def
-/
lemma isOpen_iff_forall_specializes : IsOpen s ↔ forall x y, x ⤳ y -> y in s -> x in s := by
  simp only [← nhdsKer_subset_iff_isOpen, Set.subset_def, mem_nhdsKer_iff_specializes, exists_imp,
    and_imp, @forall_comm (_ ⤳ _)]

omit [AlexandrovDiscrete α] in
/--
lemma `alexandrovDiscrete_iff_nhds` / 引理 `alexandrovDiscrete_iff_nhds`

English:
lemma alexandrovDiscrete_iff_nhds
  statement: AlexandrovDiscrete α ↔ (forall a : α, 𝓝 a = 𝓟 (nhdsKer {a})) where
  proof: principal_nhdsKer_singleton a
  mpr hα := by
    simp only [alexandrovDiscrete_iff_isClosed, isClosed_iff_clusterPt, ClusterPt, funext hα,
      inf_principal, principal_neBot_iff]
    intro S hS a ha
    rw [sUnion_eq_biUnion]; rw [inter_iUnion₂]; rw [nonempty_biUnion] at ha
    obtain ⟨s, hs, has⟩

中文:
引理 alexandrovDiscrete_iff_nhds
  结论: AlexandrovDiscrete α ↔ (对任意 a : α, 𝓝 a = 𝓟 (nhdsKer {a})) where
  证明: principal_nhdsKer_singleton a
  mpr hα := by
    simp only [alexandrovDiscrete_iff_isClosed, isClosed_iff_clusterPt, ClusterPt, funext hα,
      inf_principal, principal_neBot_iff]
    intro S hS a ha
    rw [sUnion_eq_biUnion]; rw [inter_iUnion₂]; rw [nonempty_biUnion] at ha
    obtain ⟨s, hs, has⟩

Depends on / 依赖: SetRel, SetRel.id, SetRel.id_comp, Tendsto, TopologicalSpace, discreteTopology_bot, id_comp, mem_principal_self, nhds_eq_comap_uniformity, principal_mono, principal_nhdsKer_singleton, subset, toTopologicalSpace, uniformity
-/
lemma alexandrovDiscrete_iff_nhds : AlexandrovDiscrete α ↔ (forall a : α, 𝓝 a = 𝓟 (nhdsKer {a})) where
.symm mp _ a := principal_nhdsKer_singleton a
  mpr hα := by
    simp only [alexandrovDiscrete_iff_isClosed, isClosed_iff_clusterPt, ClusterPt, funext hα,
      inf_principal, principal_neBot_iff]
    intro S hS a ha
    rw [sUnion_eq_biUnion]; rw [inter_iUnion₂]; rw [nonempty_biUnion] at ha
    obtain ⟨s, hs, has⟩ := ha
    specialize hS s hs a has
    exact mem_sUnion_of_mem hS hs

/--
lemma `alexandrovDiscrete_coinduced` / 引理 `alexandrovDiscrete_coinduced`

English:
lemma alexandrovDiscrete_coinduced
  given: {β : Type*} {f : α -> β}
  proof: @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS => by
    rw [isOpen_coinduced]; rw [preimage_sInter]; exact isOpen_iInter₂ hS

中文:
引理 alexandrovDiscrete_coinduced
  条件: {β : 类型} {f : α -> β}
  证明: @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS => by
    rw [isOpen_coinduced]; rw [preimage_sInter]; exact isOpen_iInter₂ hS

Depends on / 依赖: AlexandrovDiscrete, AlexandrovDiscrete.mk, coinduced, isOpen_coinduced, preimage_sInter
-/
lemma alexandrovDiscrete_coinduced {β : Type*} {f : α -> β} :
    @AlexandrovDiscrete β (coinduced f ‹_›) :=
  @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS => by
    rw [isOpen_coinduced]; rw [preimage_sInter]; exact isOpen_iInter₂ hS

/--
Instance `AlexandrovDiscrete.toFirstCountable` / 实例 `AlexandrovDiscrete.toFirstCountable`

English:
instance AlexandrovDiscrete.toFirstCountable
  signature: : FirstCountableTopology α where
  body: ⟨{nhdsKer {a}}, countable_singleton _, by simp⟩

中文:
实例 AlexandrovDiscrete.toFirstCountable
  签名: : 第一可数拓扑 α where
  定义体: ⟨{nhdsKer {a}}, countable_singleton _, by simp⟩

Depends on / 依赖: countable_singleton, nhdsKer
-/
instance AlexandrovDiscrete.toFirstCountable : FirstCountableTopology α where
  nhds_generated_countable a := ⟨{nhdsKer {a}}, countable_singleton _, by simp⟩

/--
Instance `AlexandrovDiscrete.toLocallyCompactSpace` / 实例 `AlexandrovDiscrete.toLocallyCompactSpace`

English:
instance AlexandrovDiscrete.toLocallyCompactSpace
  signature: : LocallyCompactSpace α where
  body: ⟨nhdsKer {a},
isOpen_nhdsKer.mem_nhds subset_nhdsKer mem_singleton _,
      nhdsKer_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.nhdsKer⟩

中文:
实例 AlexandrovDiscrete.toLocallyCompactSpace
  签名: : 局部紧空间 α where
  定义体: ⟨nhdsKer {a},
isOpen_nhdsKer.mem_nhds subset_nhdsKer mem_singleton _,
      nhdsKer_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.nhdsKer⟩

Depends on / 依赖: nhdsKer
-/
instance AlexandrovDiscrete.toLocallyCompactSpace : LocallyCompactSpace α where
  local_compact_nhds a _U hU := ⟨nhdsKer {a},
isOpen_nhdsKer.mem_nhds subset_nhdsKer mem_singleton _,
      nhdsKer_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.nhdsKer⟩

/--
Instance `Subtype.instAlexandrovDiscrete` / 实例 `Subtype.instAlexandrovDiscrete`

English:
instance Subtype.instAlexandrovDiscrete
  signature: {p : α -> Prop}
  body: IsInducing.subtypeVal.alexandrovDiscrete

中文:
实例 子类型.instAlexandrovDiscrete
  签名: {p : α -> 命题}
  定义体: IsInducing.subtypeVal.alexandrovDiscrete

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.alexandrovDiscrete, alexandrovDiscrete, subtypeVal
-/
instance Subtype.instAlexandrovDiscrete {p : α -> Prop} : AlexandrovDiscrete {a // p a} :=
  IsInducing.subtypeVal.alexandrovDiscrete

/--
Instance `Quotient.instAlexandrovDiscrete` / 实例 `Quotient.instAlexandrovDiscrete`

English:
instance Quotient.instAlexandrovDiscrete
  signature: {s : Setoid α}
  body: alexandrovDiscrete_coinduced

中文:
实例 商.instAlexandrovDiscrete
  签名: {s : 集合等价关系 α}
  定义体: alexandrovDiscrete_coinduced

Depends on / 依赖: alexandrovDiscrete_coinduced
-/
instance Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quotient s) :=
  alexandrovDiscrete_coinduced

/--
Instance `Sum.instAlexandrovDiscrete` / 实例 `Sum.instAlexandrovDiscrete`

English:
instance Sum.instAlexandrovDiscrete
  signature: : AlexandrovDiscrete (α oplus β)
  body: alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

中文:
实例 和.instAlexandrovDiscrete
  签名: : AlexandrovDiscrete (α oplus β)
  定义体: alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

Depends on / 依赖: alexandrovDiscrete_coinduced, alexandrovDiscrete_coinduced.sup
-/
instance Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α oplus β) :=
  alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

/--
Instance `Sigma.instAlexandrovDiscrete` / 实例 `Sigma.instAlexandrovDiscrete`

English:
instance Sigma.instAlexandrovDiscrete
  signature: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: alexandrovDiscrete_iSup fun _ => alexandrovDiscrete_coinduced

中文:
实例 依赖和类型.instAlexandrovDiscrete
  签名: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  定义体: alexandrovDiscrete_iSup fun _ => alexandrovDiscrete_coinduced

Depends on / 依赖: alexandrovDiscrete_coinduced, alexandrovDiscrete_iSup
-/
instance Sigma.instAlexandrovDiscrete {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, AlexandrovDiscrete (X i)] : AlexandrovDiscrete (Σ i, X i) :=
  alexandrovDiscrete_iSup fun _ => alexandrovDiscrete_coinduced

/--
Instance `Prod.instAlexandrovDiscrete` / 实例 `Prod.instAlexandrovDiscrete`

English:
instance Prod.instAlexandrovDiscrete
  signature: : AlexandrovDiscrete (α × β)
  body: by
  simp_rw [alexandrovDiscrete_iff_nhds, Prod.forall, nhds_prod_eq, ← principal_nhdsKer_singleton,
    prod_principal_principal, nhdsKer_pair, forall_true_iff]

中文:
实例 积类型.instAlexandrovDiscrete
  签名: : AlexandrovDiscrete (α × β)
  定义体: by
  simp_rw [alexandrovDiscrete_iff_nhds, Prod.forall, nhds_prod_eq, ← principal_nhdsKer_singleton,
    prod_principal_principal, nhdsKer_pair, forall_true_iff]

Depends on / 依赖: Prod.forall, alexandrovDiscrete_iff_nhds, forall_true_iff, nhdsKer_pair, nhds_prod_eq, principal_nhdsKer_singleton, prod_principal_principal, simp_rw
-/
instance Prod.instAlexandrovDiscrete : AlexandrovDiscrete (α × β) := by
  simp_rw [alexandrovDiscrete_iff_nhds, Prod.forall, nhds_prod_eq, ← principal_nhdsKer_singleton,
    prod_principal_principal, nhdsKer_pair, forall_true_iff]

/--
Instance `Pi.instAlexandrovDiscreteOfFinite` / 实例 `Pi.instAlexandrovDiscreteOfFinite`

English:
instance Pi.instAlexandrovDiscreteOfFinite
  signature: {ι : Type*} [Finite ι] {X : ι -> Type*}
  body: by
  simp_rw [alexandrovDiscrete_iff_nhds, nhds_pi, ← principal_nhdsKer_singleton,
    pi_principal, nhdsKer_singleton_pi, forall_true_iff]

中文:
实例 依赖函数类型.instAlexandrovDiscreteOfFinite
  签名: {ι : 类型} [有限 ι] {X : ι -> 类型}
  定义体: by
  simp_rw [alexandrovDiscrete_iff_nhds, nhds_pi, ← principal_nhdsKer_singleton,
    pi_principal, nhdsKer_singleton_pi, forall_true_iff]

Depends on / 依赖: alexandrovDiscrete_iff_nhds, forall_true_iff, nhdsKer_singleton_pi, nhds_pi, pi_principal, principal_nhdsKer_singleton, simp_rw
-/
instance Pi.instAlexandrovDiscreteOfFinite {ι : Type*} [Finite ι] {X : ι -> Type*}
    [Π i, TopologicalSpace (X i)] [forall i, AlexandrovDiscrete (X i)] :
    AlexandrovDiscrete (Π i, X i) := by
  simp_rw [alexandrovDiscrete_iff_nhds, nhds_pi, ← principal_nhdsKer_singleton,
    pi_principal, nhdsKer_singleton_pi, forall_true_iff]

end
