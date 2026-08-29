/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
module

public import Mathlib.Dynamics.Minimal

/-!
# Topologically transitive monoid actions

In this file we define an action of a monoid `M` on a topological space `α` to be
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m • U) ∩ V` is nonempty. We also provide an additive version of this definition
and prove basic facts about topologically transitive actions.

## Tags

group action, topologically transitive
-/

public section


open scoped Pointwise

/--
Definition of `AddAction.IsTopologicallyTransitive` / `AddAction.IsTopologicallyTransitive` 的定义

English:
class AddAction.IsTopologicallyTransitive
  parameters: (M α : Type*) [AddMonoid M] [TopologicalSpace α]
  axioms and operations (1):
    - exists_vadd_inter : forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V -> V.Nonempty -> exists m : M, ((m +ᵥ U) inter V).Nonempty

中文:
类 加法作用.是TopologicallyTransitive
  参数: (M α : 类型) [加法幺半群 M] [拓扑空间 α]
  公理与运算 (1 个):
    - exists_vadd_inter : 对任意 {U V : 集合 α}, 是开集 U -> U.非空 -> 是开集 V -> V.非空 -> 存在 m : M, ((m +ᵥ U) inter V).非空
-/
class AddAction.IsTopologicallyTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α]
    [AddAction M α] : Prop where
  exists_vadd_inter : forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V -> V.Nonempty ->
    exists m : M, ((m +ᵥ U) inter V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that `(m • U) ∩ V` is
nonempty. -/
@[to_additive]
/--
Definition of `MulAction.IsTopologicallyTransitive` / `MulAction.IsTopologicallyTransitive` 的定义

English:
class MulAction.IsTopologicallyTransitive
  parameters: (M α : Type*) [Monoid M] [TopologicalSpace α]
  axioms and operations (1):
    - exists_smul_inter : forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V -> V.Nonempty -> exists m : M, ((m • U) inter V).Nonempty

中文:
类 乘法作用.是TopologicallyTransitive
  参数: (M α : 类型) [幺半群 M] [拓扑空间 α]
  公理与运算 (1 个):
    - exists_smul_inter : 对任意 {U V : 集合 α}, 是开集 U -> U.非空 -> 是开集 V -> V.非空 -> 存在 m : M, ((m • U) inter V).非空
-/
class MulAction.IsTopologicallyTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  exists_smul_inter : forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V -> V.Nonempty ->
    exists m : M, ((m • U) inter V).Nonempty

open MulAction Set

variable (M : Type*) {α : Type*} [TopologicalSpace α] [Monoid M] [MulAction M α]

section IsTopologicallyTransitive

@[to_additive]
/--
theorem `MulAction.isTopologicallyTransitive_iff` / 定理 `MulAction.isTopologicallyTransitive_iff`

English:
theorem MulAction.isTopologicallyTransitive_iff
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 乘法作用.isTopologicallyTransitive_iff
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem MulAction.isTopologicallyTransitive_iff :
    IsTopologicallyTransitive M α ↔ forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V ->
    V.Nonempty -> exists m : M, ((m • U) inter V).Nonempty := ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union over the elements of `M` of images of `U` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union over the elements of `M` of images of `U` is
dense in `α`. -/]
/--
theorem `MulAction.isTopologicallyTransitive_iff_dense_iUnion` / 定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion`

English:
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion
  proof: by
  simp only [isTopologicallyTransitive_iff, inter_comm, dense_iff_inter_open, inter_iUnion,
    nonempty_iUnion]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h h₁ h₂ h₃ h₄, fun h _ _ h₁ h₂ h₃ h₄ => h h₁ h₂ _ h₃ h₄⟩

中文:
定理 乘法作用.isTopologicallyTransitive_iff_dense_iUnion
  证明: by
  simp only [isTopologicallyTransitive_iff, inter_comm, dense_iff_inter_open, inter_iUnion,
    nonempty_iUnion]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h h₁ h₂ h₃ h₄, fun h _ _ h₁ h₂ h₃ h₄ => h h₁ h₂ _ h₃ h₄⟩

Depends on / 依赖: dense_iff_inter_open, inter_comm, inter_iUnion, isTopologicallyTransitive_iff, nonempty_iUnion
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion :
    IsTopologicallyTransitive M α ↔
    forall {U : Set α}, IsOpen U -> U.Nonempty -> Dense (⋃ m : M, m • U) := by
  simp only [isTopologicallyTransitive_iff, inter_comm, dense_iff_inter_open, inter_iUnion,
    nonempty_iUnion]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h h₁ h₂ h₃ h₄, fun h _ _ h₁ h₂ h₃ h₄ => h h₁ h₂ _ h₃ h₄⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union of the preimages of `U` over the elements of `M` is dense in `α`.
-/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union of the preimages of `U` over the elements of
`M` is dense in `α`. -/]
/--
theorem `MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage` / 定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage`

English:
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage
  proof: by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h.1 h₃ h₄ h₁ h₂, fun h => ⟨fun h₁ h₂ h₃ h₄ => h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]

中文:
定理 乘法作用.isTopologicallyTransitive_iff_dense_iUnion_preimage
  证明: by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h.1 h₃ h₄ h₁ h₂, fun h => ⟨fun h₁ h₂ h₃ h₄ => h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]

Depends on / 依赖: dense_iff_inter_open, image_inter_nonempty_iff, inter_iUnion, nonempty_iUnion
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage :
    IsTopologicallyTransitive M α ↔
    forall {U : Set α}, IsOpen U -> U.Nonempty -> Dense (⋃ m : M, (m • ·) ⁻¹' U) := by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ => h.1 h₃ h₄ h₁ h₂, fun h => ⟨fun h₁ h₂ h₃ h₄ => h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]
/--
theorem `IsOpen.dense_iUnion_smul` / 定理 `IsOpen.dense_iUnion_smul`

English:
theorem IsOpen.dense_iUnion_smul
  statement: [h : IsTopologicallyTransitive M α] {U : Set α}
  proof: (isTopologicallyTransitive_iff_dense_iUnion M).mp h hUo hUne

@[to_additive]

中文:
定理 是开集.dense_iUnion_smul
  结论: [h : 是TopologicallyTransitive M α] {U : 集合 α}
  证明: (isTopologicallyTransitive_iff_dense_iUnion M).mp h hUo hUne

@[to_additive]

Depends on / 依赖: isTopologicallyTransitive_iff_dense_iUnion
-/
theorem IsOpen.dense_iUnion_smul [h : IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, m • U) :=
  (isTopologicallyTransitive_iff_dense_iUnion M).mp h hUo hUne

@[to_additive]
/--
theorem `IsOpen.dense_iUnion_preimage_smul` / 定理 `IsOpen.dense_iUnion_preimage_smul`

English:
theorem IsOpen.dense_iUnion_preimage_smul
  statement: [h : IsTopologicallyTransitive M α]
  proof: (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mp h hUo hUne

中文:
定理 是开集.dense_iUnion_preimage_smul
  结论: [h : 是TopologicallyTransitive M α]
  证明: (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mp h hUo hUne

Depends on / 依赖: _spec, f.map_units, isTopologicallyTransitive_iff_dense_iUnion_preimage, map_eq_zero_iff, map_units, mul_left_inj, zero_mul
-/
theorem IsOpen.dense_iUnion_preimage_smul [h : IsTopologicallyTransitive M α]
    {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, (m • ·) ⁻¹' U) :=
  (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mp h hUo hUne

/-- Let `M` be a monoid with a topologically transitive action on `α`. If `U` is a nonempty open
subset of `α` and `(m • ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in `α`. -/
@[to_additive /-- Let `M` be an additive monoid with a topologically transitive action on `α`. If
`U` is a nonempty open subset of `α` and `(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in
`α`. -/]
/--
theorem `IsOpen.dense_of_preimage_smul_invariant` / 定理 `IsOpen.dense_of_preimage_smul_invariant`

English:
theorem IsOpen.dense_of_preimage_smul_invariant
  statement: [IsTopologicallyTransitive M α] {U : Set α}
  proof: .mono (by simpa only [iUnion_subset_iff]) (hUo.dense_iUnion_preimage_smul M hUne)

中文:
定理 是开集.dense_of_preimage_smul_invariant
  结论: [是TopologicallyTransitive M α] {U : 集合 α}
  证明: .mono (by simpa only [iUnion_subset_iff]) (hUo.dense_iUnion_preimage_smul M hUne)

Depends on / 依赖: dense_iUnion_preimage_smul, hUo.dense_iUnion_preimage_smul, iUnion_subset_iff
-/
theorem IsOpen.dense_of_preimage_smul_invariant [IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hUinv : forall m : M, (m • ·) ⁻¹' U subseteq U) : Dense U :=
  .mono (by simpa only [iUnion_subset_iff]) (hUo.dense_iUnion_preimage_smul M hUne)

/-- An action of a monoid `M` on `α` that is continuous in the second argument is topologically
transitive if and only if any nonempty open subset `U` of `α` with `(m • ·) ⁻¹' U ⊆ U` for all
`m : M` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` that is continuous in the second
argument is topologically transitive if and only if any nonempty open subset `U` of `α` with
`(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` is dense in `α`. -/]
/--
theorem `MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant` / 定理 `MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant`

English:
theorem MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant
  proof: by
  refine ⟨fun _ _ h₀ h₁ h₂ => h₀.dense_of_preimage_smul_invariant M h₁ h₂, fun h₄ => ?_⟩
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr ?_
  refine fun hU _ => h₄ (isOpen_iUnion fun a => hU.preimage (h.1 a)) ?_ fun b _ => ?_
  · exact nonempty_iUnion.mpr ⟨1, by simpa only [o

中文:
定理 乘法作用.isTopologicallyTransitive_iff_dense_of_preimage_invariant
  证明: by
  refine ⟨fun _ _ h₀ h₁ h₂ => h₀.dense_of_preimage_smul_invariant M h₁ h₂, fun h₄ => ?_⟩
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr ?_
  refine fun hU _ => h₄ (isOpen_iUnion fun a => hU.preimage (h.1 a)) ?_ fun b _ => ?_
  · exact nonempty_iUnion.mpr ⟨1, by simpa only [o

Depends on / 依赖: dense_of_preimage_smul_invariant, forall_exists_index, hU.preimage, isOpen_iUnion, isTopologicallyTransitive_iff_dense_iUnion_preimage, mem_iUnion, mem_preimage, nonempty_iUnion, nonempty_iUnion.mpr, one_smul, preimage, preimage_iUnion, smul_smul
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant
    [h : ContinuousConstSMul M α] : IsTopologicallyTransitive M α ↔
    forall {U : Set α}, IsOpen U -> U.Nonempty -> (forall m : M, (m • ·) ⁻¹' U subseteq U) -> Dense U := by
  refine ⟨fun _ _ h₀ h₁ h₂ => h₀.dense_of_preimage_smul_invariant M h₁ h₂, fun h₄ => ?_⟩
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr ?_
  refine fun hU _ => h₄ (isOpen_iUnion fun a => hU.preimage (h.1 a)) ?_ fun b _ => ?_
  · exact nonempty_iUnion.mpr ⟨1, by simpa only [one_smul]⟩
  · simp only [preimage_iUnion, mem_iUnion, mem_preimage, smul_smul, forall_exists_index]
    exact fun c hc => ⟨c * b, hc⟩

@[to_additive]
/--
Instance `MulAction.isTopologicallyTransitive_of_isMinimal` / 实例 `MulAction.isTopologicallyTransitive_of_isMinimal`

English:
instance MulAction.isTopologicallyTransitive_of_isMinimal
  signature: [IsMinimal M α]
  body: by
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr fun h hn => ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

中文:
实例 乘法作用.isTopologicallyTransitive_of_isMinimal
  签名: [是极小 M α]
  定义体: by
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr fun h hn => ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

Depends on / 依赖: dense_univ, h.iUnion_preimage_smul, iUnion_preimage_smul, isTopologicallyTransitive_iff_dense_iUnion_preimage
-/
instance MulAction.isTopologicallyTransitive_of_isMinimal [IsMinimal M α] :
    IsTopologicallyTransitive M α := by
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr fun h hn => ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

end IsTopologicallyTransitive
