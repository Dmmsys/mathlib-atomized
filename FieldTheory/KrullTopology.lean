/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Krull topology

We define the Krull topology on `Gal(L/K)` for an arbitrary field extension `L/K`. In order to do
this, we first define a `GroupFilterBasis` on `Gal(L/K)`, whose sets are `E.fixingSubgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finiteExts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixedByFinite K L`. Given a field extension `L/K`, `fixedByFinite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `galBasis K L`. Given a field extension `L/K`, this is the filter basis on `Gal(L/K)` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `galGroupBasis K L`. This is the same as `galBasis K L`, but with the added structure
  that it is a group filter basis on `Gal(L/K)`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `Gal(L/K)`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_isTotallySeparated K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally separated.

- `stabilizer_isOpen_of_isIntegral`: For an integral field extension `L/K`, the stabilizer
  in `Gal(L/K)` of any element in `L` is open for the Krull topology.

## Notation

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `Gal(L/K)` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `Gal(L/E)` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `Gal(L/K)`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/

@[expose] public section

open scoped Pointwise

/--
Definition of `finiteExts` / `finiteExts` 的定义

English:
definition finiteExts
  signature: (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  body: {E | FiniteDimensional K E}

中文:
定义 finiteExts
  签名: (K : 类型) [域 K] (L : 类型) [域 L] [代数 K L]
  定义体: {E | FiniteDimensional K E}

Depends on / 依赖: FiniteDimensional
-/
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

/--
Definition of `fixedByFinite` / `fixedByFinite` 的定义

English:
definition fixedByFinite
  signature: (K L : Type*) [Field K] [Field L] [Algebra K L]
  body: IntermediateField.fixingSubgroup '' finiteExts K L

中文:
定义 fixedByFinite
  签名: (K L : 类型) [域 K] [域 L] [代数 K L]
  定义体: IntermediateField.fixingSubgroup '' finiteExts K L

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup, finiteExts, fixingSubgroup
-/
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup Gal(L/K)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

/--
theorem `top_fixedByFinite` / 定理 `top_fixedByFinite`

English:
theorem top_fixedByFinite
  given: {K L : Type*} [Field K] [Field L] [Algebra K L]
  proof: ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

中文:
定理 top_fixedByFinite
  条件: {K L : 类型} [域 K] [域 L] [代数 K L]
  证明: ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup_bot, IntermediateField.instFiniteSubtypeMemBot, fixingSubgroup_bot, instFiniteSubtypeMemBot
-/
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ in fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

/--
Definition of `galBasis` / `galBasis` 的定义

English:
definition galBasis
  signature: (K L : Type*) [Field K] [Field L] [Algebra K L]
  body: (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrie

中文:
定义 galBasis
  签名: (K L : 类型) [域 K] [域 L] [代数 K L]
  定义体: (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrie

Depends on / 依赖: carrier, fixedByFinite, g.carrier
-/
def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis Gal(L/K) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrier, ⟨_, ⟨_, E1.finiteDimensional_sup E2, rfl⟩, rfl⟩, ?_⟩
    exact Set.subset_inter (E1.fixingSubgroup_le le_sup_left) (E2.fixingSubgroup_le le_sup_right)

/--
theorem `mem_galBasis_iff` / 定理 `mem_galBasis_iff`

English:
theorem mem_galBasis_iff
  given: (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set Gal(L/K))
  proof: Iff.rfl

中文:
定理 mem_galBasis_iff
  条件: (K L : 类型) [域 K] [域 L] [代数 K L] (U : 集合 Gal(L/K))
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set Gal(L/K)) :
    U in galBasis K L ↔ U in (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl

/-- For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `Gal(L/K)`
whose sets are `Gal(L/E)` for finite subextensions `E/K`. -/
@[instance_reducible]
/--
Definition of `galGroupBasis` / `galGroupBasis` 的定义

English:
definition galGroupBasis
  signature: (K L : Type*) [Field K] [Field L] [Algebra K L]
  body: galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by

中文:
定义 galGroupBasis
  签名: (K L : 类型) [域 K] [域 L] [代数 K L]
  定义体: galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by

Depends on / 依赖: galBasis
-/
def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis Gal(L/K) where
  toFilterBasis := galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    let F : IntermediateField K L := E.map σ.symm.toAlgHom
    refine ⟨F.fixingSubgroup.carrier, ⟨⟨F.fixingSubgroup, ⟨F, ?_, rfl⟩, rfl⟩, fun g hg => ?_⟩⟩
    · have : FiniteDimensional K E := hE
      exact IntermediateField.finiteDimensional_map σ.symm.toAlgHom
    change σ * g * σ⁻¹ in E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x in F := ⟨x, hx, by dsimp⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier]; rw [IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x

/--
Instance `krullTopology` / 实例 `krullTopology`

English:
instance krullTopology
  signature: (K L : Type*) [Field K] [Field L] [Algebra K L]
  body: GroupFilterBasis.topology (galGroupBasis K L)

中文:
实例 krullTopology
  签名: (K L : 类型) [域 K] [域 L] [代数 K L]
  定义体: GroupFilterBasis.topology (galGroupBasis K L)

Depends on / 依赖: GroupFilterBasis, GroupFilterBasis.topology, galGroupBasis, topology
-/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace Gal(L/K) :=
  GroupFilterBasis.topology (galGroupBasis K L)

/-- For a field extension `L/K`, the Krull topology on `Gal(L/K)` makes it a topological group. -/
@[stacks 0BMJ "We define Krull topology directly without proving the universal property"]
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : IsTopologicalGroup Gal(L/K) :=
  GroupFilterBasis.isTopologicalGroup (galGroupBasis K L)

open scoped Topology in
/--
lemma `krullTopology_mem_nhds_one_iff` / 引理 `krullTopology_mem_nhds_one_iff`

English:
lemma krullTopology_mem_nhds_one_iff
  statement: (K L : Type*) [Field K] [Field L] [Algebra K L]
  proof: by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨E, fin, rfl⟩, rfl⟩, hE⟩
    exact ⟨E, fin, hE⟩
  · rintro ⟨E, fin, hE⟩
    exact ⟨E.fixingSubgroup, ⟨E.fixingSubgroup, ⟨E, fin, rfl⟩, rfl⟩, hE⟩

中文:
引理 krullTopology_mem_nhds_one_iff
  结论: (K L : 类型) [域 K] [域 L] [代数 K L]
  证明: by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨E, fin, rfl⟩, rfl⟩, hE⟩
    exact ⟨E, fin, hE⟩
  · rintro ⟨E, fin, hE⟩
    exact ⟨E.fixingSubgroup, ⟨E.fixingSubgroup, ⟨E, fin, rfl⟩, rfl⟩, hE⟩

Depends on / 依赖: E.fixingSubgroup, GroupFilterBasis, GroupFilterBasis.nhds_one_eq, fixingSubgroup, nhds_one_eq
-/
lemma krullTopology_mem_nhds_one_iff (K L : Type*) [Field K] [Field L] [Algebra K L]
    (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E : IntermediateField K L,
    FiniteDimensional K E ∧ (E.fixingSubgroup : Set Gal(L/K)) subseteq s := by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨E, fin, rfl⟩, rfl⟩, hE⟩
    exact ⟨E, fin, hE⟩
  · rintro ⟨E, fin, hE⟩
    exact ⟨E.fixingSubgroup, ⟨E.fixingSubgroup, ⟨E, fin, rfl⟩, rfl⟩, hE⟩

open scoped Topology in
/--
lemma `krullTopology_mem_nhds_one_iff_of_normal` / 引理 `krullTopology_mem_nhds_one_iff_of_normal`

English:
lemma krullTopology_mem_nhds_one_iff_of_normal
  statement: (K L : Type*) [Field K] [Field L] [Algebra K L]
  proof: by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ => ?_, fun ⟨E, hE⟩ => ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_norma

中文:
引理 krullTopology_mem_nhds_one_iff_of_normal
  结论: (K L : 类型) [域 K] [域 L] [代数 K L]
  证明: by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ => ?_, fun ⟨E, hE⟩ => ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_norma

Depends on / 依赖: E.fixingSubgroup_antitone, E.le_normalClosure, IntermediateField, IntermediateField.normalClosure, fixingSubgroup_antitone, is_finiteDimensional, krullTopology_mem_nhds_one_iff, le_normalClosure, le_trans, normal, normalClosure, normalClosure.is_finiteDimensional, normalClosure.normal, true_and
-/
lemma krullTopology_mem_nhds_one_iff_of_normal (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Normal K L] (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E : IntermediateField K L,
    FiniteDimensional K E ∧ Normal K E ∧ (E.fixingSubgroup : Set Gal(L/K)) subseteq s := by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ => ?_, fun ⟨E, hE⟩ => ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_normalClosure) hE

section KrullT2

open scoped Topology Filter

/--
theorem `IntermediateField.fixingSubgroup_isOpen` / 定理 `IntermediateField.fixingSubgroup_isOpen`

English:
theorem IntermediateField.fixingSubgroup_isOpen
  statement: {K L : Type*} [Field K] [Field L] [Algebra K L]
  proof: by
  have h_basis : E.fixingSubgroup.carrier in galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  exact Subgroup.isOpen_of_mem_nhds _ h_nhds

中文:
定理 中间域.fixingSubgroup_isOpen
  结论: {K L : 类型} [域 K] [域 L] [代数 K L]
  证明: by
  have h_basis : E.fixingSubgroup.carrier in galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  exact Subgroup.isOpen_of_mem_nhds _ h_nhds

Depends on / 依赖: E.fixingSubgroup, E.fixingSubgroup.carrier, GroupFilterBasis, GroupFilterBasis.mem_nhds_one, Subgroup, Subgroup.isOpen_of_mem_nhds, carrier, fixingSubgroup, galGroupBasis, h_basis, h_nhds, isOpen_of_mem_nhds, mem_nhds_one
-/
theorem IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) := by
  have h_basis : E.fixingSubgroup.carrier in galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  exact Subgroup.isOpen_of_mem_nhds _ h_nhds

/--
theorem `IntermediateField.fixingSubgroup_isClosed` / 定理 `IntermediateField.fixingSubgroup_isClosed`

English:
theorem IntermediateField.fixingSubgroup_isClosed
  statement: {K L : Type*} [Field K] [Field L] [Algebra K L]
  proof: OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

中文:
定理 中间域.fixingSubgroup_isClosed
  结论: {K L : 类型} [域 K] [域 L] [代数 K L]
  证明: OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

Depends on / 依赖: E.fixingSubgroup, E.fixingSubgroup_isOpen, OpenSubgroup, OpenSubgroup.isClosed, fixingSubgroup, fixingSubgroup_isOpen, isClosed
-/
theorem IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E.fixingSubgroup : Set Gal(L/K)) :=
  OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

/--
theorem `krullTopology_t2` / 定理 `krullTopology_t2`

English:
theorem krullTopology_t2
  statement: {K L : Type*} [Field K] [Field L] [Algebra K L]
  proof: { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      obtain ⟨x, hx⟩ := DFunLike.exists_ne hfg
      have hφx : φ x != x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) != f x
        rw [AlgEquiv.apply_symm_apply f (g x)]; rw [ne_comm]
        exact hx
      let E : Intermedia

中文:
定理 krullTopology_t2
  结论: {K L : 类型} [域 K] [域 L] [代数 K L]
  证明: { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      obtain ⟨x, hx⟩ := DFunLike.exists_ne hfg
      have hφx : φ x != x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) != f x
        rw [AlgEquiv.apply_symm_apply f (g x)]; rw [ne_comm]
        exact hx
      let E : Intermedia

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, Algebra, Algebra.IsIntegral.isIntegral, DFunLike, DFunLike.exists_ne, E.fixingSubgroup, FiniteDimensional, IntermediateField, IntermediateField.adjoin, IntermediateField.adjoin.finiteDimensional, IsIntegral, adjoin, apply_symm_apply, exists_ne, f.symm, finiteDimensional, fixingSubgroup, galGroupBasis, h_basis
-/
theorem krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      obtain ⟨x, hx⟩ := DFunLike.exists_ne hfg
      have hφx : φ x != x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) != f x
        rw [AlgEquiv.apply_symm_apply f (g x)]; rw [ne_comm]
        exact hx
      let E : IntermediateField K L := IntermediateField.adjoin K {x}
      let h_findim : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
      let H := E.fixingSubgroup
      have h_basis : (H : Set Gal(L/K)) in galGroupBasis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩
      have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
      rw [mem_nhds_iff] at h_nhds
      rcases h_nhds with ⟨W, hWH, hW_open, hW_1⟩
      refine ⟨f • W, g • W,
        ⟨hW_open.leftCoset f, hW_open.leftCoset g, ⟨1, hW_1, mul_one _⟩, ⟨1, hW_1, mul_one _⟩, ?_⟩⟩
      rw [Set.disjoint_left]
      rintro σ ⟨w1, hw1, h⟩ ⟨w2, hw2, rfl⟩
      dsimp at h
      rw [eq_inv_mul_iff_mul_eq.symm]; rw [← mul_assoc]; rw [mul_inv_eq_iff_eq_mul.symm] at h
      have h_in_H : w1 * w2⁻¹ in H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2))
      rw [h] at h_in_H
      change φ in E.fixingSubgroup at h_in_H
      rw [IntermediateField.mem_fixingSubgroup_iff] at h_in_H
      specialize h_in_H x
      have hxE : x in E := by
        apply IntermediateField.subset_adjoin
        apply Set.mem_singleton
      exact hφx (h_in_H hxE) }

end KrullT2

section TotallySeparated

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] :
    TotallySeparatedSpace Gal(L/K) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ h_diff
  have hστ : σ⁻¹ * τ != 1 := by rwa [Ne, inv_mul_eq_one]
  rcases DFunLike.exists_ne hστ with ⟨x, hx : (σ⁻¹ * τ) x != x⟩
  let E := IntermediateField.adjoin K ({x} : Set L)
  have := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) x)
  refine ⟨σ • E.fixingSubgroup,
    ⟨E.fixingSubgroup_isClosed.leftCoset σ, E.fixingSubgroup_isOpen.leftCoset σ⟩,
    ⟨1, E.fixingSubgroup.one_mem', mul_one σ⟩, ?_⟩
  simp only [Set.mem_compl_iff, mem_leftCoset_iff, SetLike.mem_coe,
    IntermediateField.mem_fixingSubgroup_iff, not_forall]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self K x, hx⟩

/--
theorem `krullTopology_isTotallySeparated` / 定理 `krullTopology_isTotallySeparated`

English:
theorem krullTopology_isTotallySeparated
  statement: {K L : Type*} [Field K] [Field L] [Algebra K L]
  proof: (totallySeparatedSpace_iff _).mp inferInstance

中文:
定理 krullTopology_isTotallySeparated
  结论: {K L : 类型} [域 K] [域 L] [代数 K L]
  证明: (totallySeparatedSpace_iff _).mp inferInstance

Depends on / 依赖: totallySeparatedSpace_iff
-/
theorem krullTopology_isTotallySeparated {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : IsTotallySeparated (Set.univ : Set Gal(L/K)) :=
  (totallySeparatedSpace_iff _).mp inferInstance

end TotallySeparated

/--
Instance `krullTopology_discreteTopology_of_finiteDimensional` / 实例 `krullTopology_discreteTopology_of_finiteDimensional`

English:
instance krullTopology_discreteTopology_of_finiteDimensional
  signature: (K L : Type*) [Field K] [Field L]
  body: by
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen ((⊥ : Subgroup Gal(L/K)) : Set Gal(L/K))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤

中文:
实例 krullTopology_discreteTopology_of_finiteDimensional
  签名: (K L : 类型) [域 K] [域 L]
  定义体: by
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen ((⊥ : Subgroup Gal(L/K)) : Set Gal(L/K))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup_isOpen, IntermediateField.fixingSubgroup_top, IsOpen, Subgroup, discreteTopology_iff_isOpen_singleton_one, fixingSubgroup_isOpen, fixingSubgroup_top
-/
instance krullTopology_discreteTopology_of_finiteDimensional (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : DiscreteTopology Gal(L/K) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen ((⊥ : Subgroup Gal(L/K)) : Set Gal(L/K))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤

section MulAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
theorem `stabilizer_isOpen_of_isIntegral` / 定理 `stabilizer_isOpen_of_isIntegral`

English:
theorem stabilizer_isOpen_of_isIntegral
  given: [Algebra.IsIntegral K L] (x : L)
  proof: by
  open IntermediateField in
  let E := adjoin K {x}
  have hL : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  convert! fixingSubgroup_isOpen E
  ext g
  simpa using (forall_mem_adjoin_smul_eq_self_iff K (S := {x}) g).symm

中文:
定理 stabilizer_isOpen_of_is整数egral
  条件: [代数.是整 K L] (x : L)
  证明: by
  open IntermediateField in
  let E := adjoin K {x}
  have hL : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  convert! fixingSubgroup_isOpen E
  ext g
  simpa using (forall_mem_adjoin_smul_eq_self_iff K (S := {x}) g).symm

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, FiniteDimensional, IntermediateField, IsIntegral, adjoin, adjoin.finiteDimensional, convert, finiteDimensional, fixingSubgroup_isOpen, forall_mem_adjoin_smul_eq_self_iff, isIntegral
-/
theorem stabilizer_isOpen_of_isIntegral [Algebra.IsIntegral K L] (x : L) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  open IntermediateField in
  let E := adjoin K {x}
  have hL : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  convert! fixingSubgroup_isOpen E
  ext g
  simpa using (forall_mem_adjoin_smul_eq_self_iff K (S := {x}) g).symm

end MulAction
