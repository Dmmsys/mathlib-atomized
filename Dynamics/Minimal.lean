/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Minimal action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/

public section


open scoped Pointwise

/--
Definition of `AddAction.IsMinimal` / `AddAction.IsMinimal` 的定义

English:
class AddAction.IsMinimal
  parameters: (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α]
  axioms and operations (1):
    - dense_orbit : forall x : α, Dense (AddAction.orbit M x)

中文:
类 AddAction.IsMinimal
  参数: (M α : 类型) [AddMonoid M] [TopologicalSpace α] [AddAction M α]
  公理与运算 (1 个):
    - dense_orbit : 对任意 x : α, Dense (AddAction.orbit M x)
-/
class AddAction.IsMinimal (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where
  dense_orbit : forall x : α, Dense (AddAction.orbit M x)

/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[to_additive]
/--
Definition of `MulAction.IsMinimal` / `MulAction.IsMinimal` 的定义

English:
class MulAction.IsMinimal
  parameters: (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α]
  axioms and operations (1):
    - dense_orbit : forall x : α, Dense (MulAction.orbit M x)

中文:
类 MulAction.IsMinimal
  参数: (M α : 类型) [Monoid M] [TopologicalSpace α] [MulAction M α]
  公理与运算 (1 个):
    - dense_orbit : 对任意 x : α, Dense (MulAction.orbit M x)
-/
class MulAction.IsMinimal (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α] :
    Prop where
  dense_orbit : forall x : α, Dense (MulAction.orbit M x)

open MulAction Set

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

@[to_additive]
/--
theorem `MulAction.dense_orbit` / 定理 `MulAction.dense_orbit`

English:
theorem MulAction.dense_orbit
  given: [IsMinimal M α] (x : α)
  statement: Dense (orbit M x)
  proof: MulAction.IsMinimal.dense_orbit x

@[to_additive]

中文:
定理 MulAction.dense_orbit
  条件: [IsMinimal M α] (x : α)
  结论: Dense (orbit M x)
  证明: MulAction.IsMinimal.dense_orbit x

@[to_additive]

Depends on / 依赖: IsMinimal, MulAction, MulAction.IsMinimal.dense_orbit, dense_orbit
-/
theorem MulAction.dense_orbit [IsMinimal M α] (x : α) : Dense (orbit M x) :=
  MulAction.IsMinimal.dense_orbit x

@[to_additive]
/--
theorem `denseRange_smul` / 定理 `denseRange_smul`

English:
theorem denseRange_smul
  given: [IsMinimal M α] (x : α)
  statement: DenseRange fun c : M => c • x
  proof: MulAction.dense_orbit M x

@[to_additive]

中文:
定理 denseRange_smul
  条件: [IsMinimal M α] (x : α)
  结论: DenseRange fun c : M => c • x
  证明: MulAction.dense_orbit M x

@[to_additive]

Depends on / 依赖: MulAction, MulAction.dense_orbit, dense_orbit
-/
theorem denseRange_smul [IsMinimal M α] (x : α) : DenseRange fun c : M => c • x :=
  MulAction.dense_orbit M x

@[to_additive]
instance (priority := 100) MulAction.isMinimal_of_pretransitive [IsPretransitive M α] :
    IsMinimal M α :=
  ⟨fun x => (surjective_smul M x).denseRange⟩

@[to_additive]
/--
theorem `IsOpen.exists_smul_mem` / 定理 `IsOpen.exists_smul_mem`

English:
theorem IsOpen.exists_smul_mem
  statement: [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
  proof: (denseRange_smul M x).exists_mem_open hUo hne

@[to_additive]

中文:
定理 IsOpen.exists_smul_mem
  结论: [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
  证明: (denseRange_smul M x).exists_mem_open hUo hne

@[to_additive]

Depends on / 依赖: denseRange_smul, exists_mem_open
-/
theorem IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : exists c : M, c • x in U :=
  (denseRange_smul M x).exists_mem_open hUo hne

@[to_additive]
/--
theorem `IsOpen.iUnion_preimage_smul` / 定理 `IsOpen.iUnion_preimage_smul`

English:
theorem IsOpen.iUnion_preimage_smul
  statement: [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
  proof: iUnion_eq_univ_iff.2 fun x => hUo.exists_smul_mem M x hne

@[to_additive]

中文:
定理 IsOpen.iUnion_preimage_smul
  结论: [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
  证明: iUnion_eq_univ_iff.2 fun x => hUo.exists_smul_mem M x hne

@[to_additive]

Depends on / 依赖: exists_smul_mem, hUo.exists_smul_mem, iUnion_eq_univ_iff
-/
theorem IsOpen.iUnion_preimage_smul [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ⋃ c : M, (c • ·) ⁻¹' U = univ :=
  iUnion_eq_univ_iff.2 fun x => hUo.exists_smul_mem M x hne

@[to_additive]
/--
theorem `IsOpen.iUnion_smul` / 定理 `IsOpen.iUnion_smul`

English:
theorem IsOpen.iUnion_smul
  given: [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty)
  proof: iUnion_eq_univ_iff.2 fun x =>
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]

中文:
定理 IsOpen.iUnion_smul
  条件: [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty)
  证明: iUnion_eq_univ_iff.2 fun x =>
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]

Depends on / 依赖: exists_smul_mem, hUo.exists_smul_mem, iUnion_eq_univ_iff, inv_smul_smul
-/
theorem IsOpen.iUnion_smul [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) :
    ⋃ g : G, g • U = univ :=
  iUnion_eq_univ_iff.2 fun x =>
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
/--
theorem `IsCompact.exists_finite_cover_smul` / 定理 `IsCompact.exists_finite_cover_smul`

English:
theorem IsCompact.exists_finite_cover_smul
  statement: [IsMinimal G α] [ContinuousConstSMul G α]
  proof: (hK.elim_finite_subcover (fun g => g • U) fun _ => hUo.smul _) calc
    K subseteq univ := subset_univ K
    _ = ⋃ g : G, g • U := (hUo.iUnion_smul G hne).symm

@[to_additive]

中文:
定理 IsCompact.exists_finite_cover_smul
  结论: [IsMinimal G α] [ContinuousConstSMul G α]
  证明: (hK.elim_finite_subcover (fun g => g • U) fun _ => hUo.smul _) calc
    K subseteq univ := subset_univ K
    _ = ⋃ g : G, g • U := (hUo.iUnion_smul G hne).symm

@[to_additive]

Depends on / 依赖: elim_finite_subcover, hK.elim_finite_subcover, hUo.iUnion_smul, hUo.smul, iUnion_smul, subset_univ, subseteq
-/
theorem IsCompact.exists_finite_cover_smul [IsMinimal G α] [ContinuousConstSMul G α]
    {K U : Set α} (hK : IsCompact K) (hUo : IsOpen U) (hne : U.Nonempty) :
    exists I : Finset G, K subseteq ⋃ g in I, g • U :=
(hK.elim_finite_subcover (fun g => g • U) fun _ => hUo.smul _) calc
    K subseteq univ := subset_univ K
    _ = ⋃ g : G, g • U := (hUo.iUnion_smul G hne).symm

@[to_additive]
/--
theorem `dense_of_nonempty_smul_invariant` / 定理 `dense_of_nonempty_smul_invariant`

English:
theorem dense_of_nonempty_smul_invariant
  statement: [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
  proof: let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c => hsmul c ⟨x, hx, rfl⟩)

@[to_additive]

中文:
定理 dense_of_nonempty_smul_invariant
  结论: [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
  证明: let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c => hsmul c ⟨x, hx, rfl⟩)

@[to_additive]

Depends on / 依赖: MulAction, MulAction.dense_orbit, dense_orbit, range_subset_iff
-/
theorem dense_of_nonempty_smul_invariant [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
    (hsmul : forall c : M, c • s subseteq s) : Dense s :=
  let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c => hsmul c ⟨x, hx, rfl⟩)

@[to_additive]
/--
theorem `eq_empty_or_univ_of_smul_invariant_closed` / 定理 `eq_empty_or_univ_of_smul_invariant_closed`

English:
theorem eq_empty_or_univ_of_smul_invariant_closed
  statement: [IsMinimal M α] {s : Set α} (hs : IsClosed s)
  proof: s.eq_empty_or_nonempty.imp_right fun hne =>
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[to_additive]

中文:
定理 eq_empty_or_univ_of_smul_invariant_closed
  结论: [IsMinimal M α] {s : Set α} (hs : IsClosed s)
  证明: s.eq_empty_or_nonempty.imp_right fun hne =>
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[to_additive]

Depends on / 依赖: closure_eq, dense_of_nonempty_smul_invariant, eq_empty_or_nonempty, hs.closure_eq, imp_right, s.eq_empty_or_nonempty.imp_right
-/
theorem eq_empty_or_univ_of_smul_invariant_closed [IsMinimal M α] {s : Set α} (hs : IsClosed s)
    (hsmul : forall c : M, c • s subseteq s) : s = ∅ ∨ s = univ :=
  s.eq_empty_or_nonempty.imp_right fun hne =>
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[to_additive]
/--
theorem `isMinimal_iff_isClosed_smul_invariant` / 定理 `isMinimal_iff_isClosed_smul_invariant`

English:
theorem isMinimal_iff_isClosed_smul_invariant
  given: [ContinuousConstSMul M α]
  proof: by
  constructor
  · intro _ _
    exact eq_empty_or_univ_of_smul_invariant_closed M
refine fun H => ⟨fun _ => dense_iff_closure_eq.2 (H _ ?_ ?_).resolve_left ?_⟩
  exacts [isClosed_closure, fun _ => smul_closure_orbit_subset _ _,
    (nonempty_orbit _).closure.ne_empty]

中文:
定理 isMinimal_iff_isClosed_smul_invariant
  条件: [ContinuousConstSMul M α]
  证明: by
  constructor
  · intro _ _
    exact eq_empty_or_univ_of_smul_invariant_closed M
refine fun H => ⟨fun _ => dense_iff_closure_eq.2 (H _ ?_ ?_).resolve_left ?_⟩
  exacts [isClosed_closure, fun _ => smul_closure_orbit_subset _ _,
    (nonempty_orbit _).closure.ne_empty]

Depends on / 依赖: closure, closure.ne_empty, dense_iff_closure_eq, eq_empty_or_univ_of_smul_invariant_closed, exacts, isClosed_closure, ne_empty, nonempty_orbit, resolve_left, smul_closure_orbit_subset
-/
theorem isMinimal_iff_isClosed_smul_invariant [ContinuousConstSMul M α] :
    IsMinimal M α ↔ forall s : Set α, IsClosed s -> (forall c : M, c • s subseteq s) -> s = ∅ ∨ s = univ := by
  constructor
  · intro _ _
    exact eq_empty_or_univ_of_smul_invariant_closed M
refine fun H => ⟨fun _ => dense_iff_closure_eq.2 (H _ ?_ ?_).resolve_left ?_⟩
  exacts [isClosed_closure, fun _ => smul_closure_orbit_subset _ _,
    (nonempty_orbit _).closure.ne_empty]
