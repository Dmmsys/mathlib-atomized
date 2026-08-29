/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Equiv

import Mathlib.Topology.Algebra.UniformRing -- shake: keep (used in `example` only)

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `IsAdic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `WithIdeal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `Ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `Ideal.adicTopology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `Ideal.nonarchimedean`: the adic topology is non-archimedean
* `isAdic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `WithIdeal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as an `R`-module.

-/

@[expose] public section


variable {R : Type*} [CommRing R]

open Set IsTopologicalAddGroup Submodule Filter

open Topology Pointwise

namespace Ideal

/--
theorem `adic_basis` / 定理 `adic_basis`

English:
theorem adic_basis
  given: (I : Ideal R)
  statement: SubmodulesRingBasis fun n : Nat => (I ^ n • ⊤ : Ideal R)
  proof: { inter := by
      suffices forall i j : Nat, exists k, I ^ k <= I ^ i ∧ I ^ k <= I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.algebraMap_self, map_id, le_inf_iff] using! this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices forall (a : R) (i : Nat), exists j : Nat, a • I ^ j <= I ^ i by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices forall i : Nat, exists j : Nat, (↑(I ^ j) * ↑(I ^ j) : Set R) subseteq (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }

中文:
定理 adic_basis
  条件: (I : 理想 R)
  结论: SubmodulesRingBasis fun n : 自然数 => (I ^ n • ⊤ : 理想 R)
  证明: { inter := by
      suffices forall i j : Nat, exists k, I ^ k <= I ^ i ∧ I ^ k <= I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.algebraMap_self, map_id, le_inf_iff] using! this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices forall (a : R) (i : Nat), exists j : Nat, a • I ^ j <= I ^ i by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices forall i : Nat, exists j : Nat, (↑(I ^ j) * ↑(I ^ j) : Set R) subseteq (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }

Depends on / 依赖: Algebra, Algebra.algebraMap_self, algebraMap_self, le_inf_iff, le_max_left, le_max_right, leftMul, map_id, mul_top, pow_le_pow_right, smul_eq_mul, smul_mem, smul_top_eq_map
-/
theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : Nat => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices forall i j : Nat, exists k, I ^ k <= I ^ i ∧ I ^ k <= I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.algebraMap_self, map_id, le_inf_iff] using! this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices forall (a : R) (i : Nat), exists j : Nat, a • I ^ j <= I ^ i by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices forall i : Nat, exists j : Nat, (↑(I ^ j) * ↑(I ^ j) : Set R) subseteq (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
@[instance_reducible]
/--
Definition of `ringFilterBasis` / `ringFilterBasis` 的定义

English:
definition ringFilterBasis
  signature: (I : Ideal R)
  body: I.adic_basis.toRing_subgroups_basis.toRingFilterBasis

中文:
定义 ringFilterBasis
  签名: (I : 理想 R)
  定义体: I.adic_basis.toRing_subgroups_basis.toRingFilterBasis

Depends on / 依赖: I.adic_basis.toRing_subgroups_basis.toRingFilterBasis, adic_basis, toRingFilterBasis, toRing_subgroups_basis
-/
def ringFilterBasis (I : Ideal R) :=
  I.adic_basis.toRing_subgroups_basis.toRingFilterBasis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
@[instance_reducible]
/--
Definition of `adicTopology` / `adicTopology` 的定义

English:
definition adicTopology
  signature: (I : Ideal R)
  body: (adic_basis I).topology

中文:
定义 adicTopology
  签名: (I : 理想 R)
  定义体: (adic_basis I).topology

Depends on / 依赖: adic_basis, topology
-/
def adicTopology (I : Ideal R) : TopologicalSpace R :=
  (adic_basis I).topology

/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  given: (I : Ideal R)
  statement: @NonarchimedeanRing R _ I.adicTopology
  proof: I.adic_basis.toRing_subgroups_basis.nonarchimedean

中文:
定理 nonarchimedean
  条件: (I : 理想 R)
  结论: @Nonarchimedean环 R _ I.adicTopology
  证明: I.adic_basis.toRing_subgroups_basis.nonarchimedean

Depends on / 依赖: I.adic_basis.toRing_subgroups_basis.nonarchimedean, adic_basis, nonarchimedean, toRing_subgroups_basis
-/
theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology :=
  I.adic_basis.toRing_subgroups_basis.nonarchimedean

/--
theorem `hasBasis_nhds_zero_adic` / 定理 `hasBasis_nhds_zero_adic`

English:
theorem hasBasis_nhds_zero_adic
  given: (I : Ideal R)
  proof: ⟨by
    intro U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) subseteq U := by simpa using h
      exact ⟨i, trivial, h⟩
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩

中文:
定理 hasBasis_nhds_zero_adic
  条件: (I : 理想 R)
  证明: ⟨by
    intro U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) subseteq U := by simpa using h
      exact ⟨i, trivial, h⟩
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩

Depends on / 依赖: I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff, mem_iff, nhds_zero_hasBasis, replace, ringFilterBasis, subseteq, toAddGroupFilterBasis
-/
theorem hasBasis_nhds_zero_adic (I : Ideal R) :
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n =>
      ((I ^ n : Ideal R) : Set R) :=
  ⟨by
    intro U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) subseteq U := by simpa using h
      exact ⟨i, trivial, h⟩
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩

/--
theorem `hasBasis_nhds_adic` / 定理 `hasBasis_nhds_adic`

English:
theorem hasBasis_nhds_adic
  given: (I : Ideal R) (x : R)
  proof: by
  let := I.adicTopology
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this

中文:
定理 hasBasis_nhds_adic
  条件: (I : 理想 R) (x : R)
  证明: by
  let := I.adicTopology
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this

Depends on / 依赖: I.adicTopology, I.hasBasis_nhds_zero_adic.map, adicTopology, hasBasis_nhds_zero_adic, map_add_left_nhds_zero
-/
theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun _n : Nat => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) := by
  let := I.adicTopology
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this

/--
theorem `isLinearTopology` / 定理 `isLinearTopology`

English:
theorem isLinearTopology
  given: (I : Ideal R)
  statement: @IsLinearTopology R R _ _ _ I.adicTopology
  proof: letI := I.adicTopology
  IsLinearTopology.mk_of_hasBasis _ I.hasBasis_nhds_zero_adic

中文:
定理 isLinearTopology
  条件: (I : 理想 R)
  结论: @是线性拓扑 R R _ _ _ I.adicTopology
  证明: letI := I.adicTopology
  IsLinearTopology.mk_of_hasBasis _ I.hasBasis_nhds_zero_adic

Depends on / 依赖: I.adicTopology, I.hasBasis_nhds_zero_adic, IsLinearTopology, IsLinearTopology.mk_of_hasBasis, adicTopology, hasBasis_nhds_zero_adic, mk_of_hasBasis
-/
theorem isLinearTopology (I : Ideal R) : @IsLinearTopology R R _ _ _ I.adicTopology :=
  letI := I.adicTopology
  IsLinearTopology.mk_of_hasBasis _ I.hasBasis_nhds_zero_adic

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/--
theorem `adic_module_basis` / 定理 `adic_module_basis`

English:
theorem adic_module_basis
  proof: { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
⟨smul_mono_left pow_le_pow_right (le_max_left i j),
smul_mono_left pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a in I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }

中文:
定理 adic_module_basis
  证明: { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
⟨smul_mono_left pow_le_pow_right (le_max_left i j),
smul_mono_left pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a in I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }

Depends on / 依赖: a_in, le_inf_iff, le_inf_iff.mpr, le_max_left, le_max_right, mem_top, mul_top, pow_le_pow_right, replace, smul_mem_smul, smul_mono_left
-/
theorem adic_module_basis :
    I.ringFilterBasis.SubmodulesBasis fun n : Nat => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
⟨smul_mono_left pow_le_pow_right (le_max_left i j),
smul_mono_left pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a in I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
@[instance_reducible]
/--
Definition of `adicModuleTopology` / `adicModuleTopology` 的定义

English:
definition adicModuleTopology
  signature: : TopologicalSpace M
  body: @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))

中文:
定义 adicModuleTopology
  签名: : 拓扑空间 M
  定义体: @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))

Depends on / 依赖: I.adic_basis.topology, I.adic_module_basis, I.ringFilterBasis.moduleFilterBasis, ModuleFilterBasis, ModuleFilterBasis.topology, adic_basis, adic_module_basis, moduleFilterBasis, ringFilterBasis, topology
-/
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))

/--
Definition of `openAddSubgroup` / `openAddSubgroup` 的定义

English:
definition openAddSubgroup
  signature: (n : Nat)
  body: by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert! (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp

中文:
定义 openAddSubgroup
  签名: (n : 自然数)
  定义体: by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert! (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp

Depends on / 依赖: I.adicTopology, I.adic_basis.toRing_subgroups_basis.openAddSubgroup, adicTopology, adic_basis, convert, isOpen, openAddSubgroup, toAddSubgroup, toRing_subgroups_basis
-/
def openAddSubgroup (n : Nat) : @OpenAddSubgroup R _ I.adicTopology := by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert! (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp

end Ideal

section IsAdic

/--
Definition of `IsAdic` / `IsAdic` 的定义

English:
definition IsAdic
  signature: [H : TopologicalSpace R] (J : Ideal R)
  body: H = J.adicTopology

中文:
定义 IsAdic
  签名: [H : 拓扑空间 R] (J : 理想 R)
  定义体: H = J.adicTopology

Depends on / 依赖: J.adicTopology, adicTopology
-/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology

/--
theorem `isAdic_iff` / 定理 `isAdic_iff`

English:
theorem isAdic_iff
  given: [top : TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R}
  proof: by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    let := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply IsTopologicalAddGroup.ext
    · apply @IsTopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      let := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩

中文:
定理 isAdic_iff
  条件: [top : 拓扑空间 R] [是拓扑环 R] {J : 理想 R}
  证明: by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    let := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply IsTopologicalAddGroup.ext
    · apply @IsTopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      let := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩

Depends on / 依赖: Ideal.adic_basis, IsTopologicalAddGroup, IsTopologicalAddGroup.ext, IsTopologicalRing, IsTopologicalRing.to_topologicalAddGroup, J.adicTopology, J.hasBasis_nhds_zero_adic.mem_iff, J.hasBasis_nhds_zero_adic.mem_iff.mp, J.openAddSubgroup, RingSubgroupsBasis, RingSubgroupsBasis.toRingFilterBasis, adicTopology, adic_basis, hasBasis_nhds_zero_adic, isOpen, isTopologicalAddGroup, mem_iff, openAddSubgroup, toAddGroupFilterBasis, toAddGroupFilterBasis.isTopologicalAddGroup
-/
theorem isAdic_iff [top : TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (forall n : Nat, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        forall s in 𝓝 (0 : R), exists n : Nat, ((J ^ n : Ideal R) : Set R) subseteq s := by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    let := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply IsTopologicalAddGroup.ext
    · apply @IsTopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      let := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩

variable [TopologicalSpace R] [IsTopologicalRing R]

/--
theorem `is_ideal_adic_pow` / 定理 `is_ideal_adic_pow`

English:
theorem is_ideal_adic_pow
  given: {J : Ideal R} (h : IsAdic J) {n : Nat} (hn : 0 < n)
  statement: IsAdic (J ^ n)
  proof: by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    obtain ⟨m, hm⟩ := h.right V hV
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul]; rw [Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left

中文:
定理 is_ideal_adic_pow
  条件: {J : 理想 R} (h : IsAdic J) {n : 自然数} (hn : 0 < n)
  结论: IsAdic (J ^ n)
  证明: by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    obtain ⟨m, hm⟩ := h.right V hV
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul]; rw [Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left

Depends on / 依赖: Ideal.pow_le_pow_right, Nat.le_add_left, Nat.not_succ_le_zero, Nat.succ_mul, Set.Subset.trans, Subset, h.left, h.right, isAdic_iff, le_add_left, not_succ_le_zero, pow_le_pow_right, pow_mul, succ_mul
-/
theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : Nat} (hn : 0 < n) : IsAdic (J ^ n) := by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    obtain ⟨m, hm⟩ := h.right V hV
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul]; rw [Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left

/--
theorem `is_bot_adic_iff` / 定理 `is_bot_adic_iff`

English:
theorem is_bot_adic_iff
  given: {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  proof: by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]

omit [IsTopologicalRing R] in

中文:
定理 is_bot_adic_iff
  条件: {A : 类型} [交换环 A] [拓扑空间 A] [是拓扑环 A]
  证明: by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]

omit [IsTopologicalRing R] in

Depends on / 依赖: U_nhds, discreteTopology_iff_isOpen_singleton_zero, intros, isAdic_iff, mem_of_mem_nhds
-/
theorem is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A := by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]

omit [IsTopologicalRing R] in
/--
theorem `IsAdic.hasBasis_nhds_zero` / 定理 `IsAdic.hasBasis_nhds_zero`

English:
theorem IsAdic.hasBasis_nhds_zero
  given: {I : Ideal R} (hI : IsAdic I)
  proof: hI ▸ Ideal.hasBasis_nhds_zero_adic I

omit [IsTopologicalRing R] in

中文:
定理 IsAdic.hasBasis_nhds_zero
  条件: {I : 理想 R} (hI : IsAdic I)
  证明: hI ▸ Ideal.hasBasis_nhds_zero_adic I

omit [IsTopologicalRing R] in

Depends on / 依赖: Ideal.hasBasis_nhds_zero_adic, hasBasis_nhds_zero_adic
-/
theorem IsAdic.hasBasis_nhds_zero {I : Ideal R} (hI : IsAdic I) :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun n => ↑(I ^ n) :=
  hI ▸ Ideal.hasBasis_nhds_zero_adic I

omit [IsTopologicalRing R] in
/--
theorem `IsAdic.hasBasis_nhds` / 定理 `IsAdic.hasBasis_nhds`

English:
theorem IsAdic.hasBasis_nhds
  given: {I : Ideal R} (hI : IsAdic I) (x : R)
  proof: hI ▸ Ideal.hasBasis_nhds_adic I x

中文:
定理 IsAdic.hasBasis_nhds
  条件: {I : 理想 R} (hI : IsAdic I) (x : R)
  证明: hI ▸ Ideal.hasBasis_nhds_adic I x

Depends on / 依赖: Ideal.hasBasis_nhds_adic, hasBasis_nhds_adic
-/
theorem IsAdic.hasBasis_nhds {I : Ideal R} (hI : IsAdic I) (x : R) :
    (𝓝 x).HasBasis (fun _ => True) fun n => (x + ·) '' ↑(I ^ n) :=
  hI ▸ Ideal.hasBasis_nhds_adic I x

end IsAdic

/--
Definition of `WithIdeal` / `WithIdeal` 的定义

English:
class WithIdeal
  parameters: (R : Type*) [CommRing R]
  axioms and operations (1):
    - i : Ideal R

中文:
类 With理想
  参数: (R : 类型) [交换环 R]
  公理与运算 (1 个):
    - i : 理想 R
-/
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R

namespace WithIdeal

variable (R)
variable [WithIdeal R]

instance (priority := 100) : TopologicalSpace R :=
  i.adicTopology

instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _

instance (priority := 100) : UniformSpace R :=
  IsTopologicalAddGroup.rightUniformSpace R

instance (priority := 100) : IsUniformAddGroup R :=
  isUniformAddGroup_of_addCommGroup

instance (priority := 100) : IsLinearTopology R R := i.isLinearTopology

variable {R} in
/--
theorem `uniformContinuous_of_map_le` / 定理 `uniformContinuous_of_map_le`

English:
theorem uniformContinuous_of_map_le
  statement: {S : Type*} [CommRing S] [WithIdeal S] {f : R ->+* S}
  proof: uniformContinuous_of_continuousAt_zero f (by
  rw [ContinuousAt]; rw [map_zero]; rw [i.hasBasis_nhds_zero_adic.tendsto_iff i.hasBasis_nhds_zero_adic]
  refine fun n _ => ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono hf n)

中文:
定理 uniformContinuous_of_map_le
  结论: {S : 类型} [交换环 S] [With理想 S] {f : R ->+* S}
  证明: uniformContinuous_of_continuousAt_zero f (by
  rw [ContinuousAt]; rw [map_zero]; rw [i.hasBasis_nhds_zero_adic.tendsto_iff i.hasBasis_nhds_zero_adic]
  refine fun n _ => ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono hf n)

Depends on / 依赖: ContinuousAt, Ideal.map_le_iff_le_comap.mp, Ideal.map_pow, Ideal.pow_right_mono, hasBasis_nhds_zero_adic, i.hasBasis_nhds_zero_adic, i.hasBasis_nhds_zero_adic.tendsto_iff, map_le_iff_le_comap, map_pow, map_zero, pow_right_mono, tendsto_iff, uniformContinuous_of_continuousAt_zero
-/
theorem uniformContinuous_of_map_le {S : Type*} [CommRing S] [WithIdeal S] {f : R ->+* S}
    (hf : i.map f <= i) : UniformContinuous f := uniformContinuous_of_continuousAt_zero f (by
  rw [ContinuousAt]; rw [map_zero]; rw [i.hasBasis_nhds_zero_adic.tendsto_iff i.hasBasis_nhds_zero_adic]
  refine fun n _ => ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono hf n)

variable {R} in
/--
Definition of `uniformEquiv` / `uniformEquiv` 的定义

English:
definition uniformEquiv
  signature: {S : Type*} [CommRing S] [WithIdeal S] (e : R ≃+* S)
  body: e
  uniformContinuous_toFun := uniformContinuous_of_map_le (f := e.toRingHom) (by rw [h])
  uniformContinuous_invFun := uniformContinuous_of_map_le (f := e.symm.toRingHom) (by simp [← h])

中文:
定义 uniformEquiv
  签名: {S : 类型} [交换环 S] [With理想 S] (e : R ≃+* S)
  定义体: e
  uniformContinuous_toFun := uniformContinuous_of_map_le (f := e.toRingHom) (by rw [h])
  uniformContinuous_invFun := uniformContinuous_of_map_le (f := e.symm.toRingHom) (by simp [← h])
-/
def uniformEquiv {S : Type*} [CommRing S] [WithIdeal S] (e : R ≃+* S)
    (h : i.map e.toRingHom = i) : UniformEquiv R S where
  __ := e
  uniformContinuous_toFun := uniformContinuous_of_map_le (f := e.toRingHom) (by rw [h])
  uniformContinuous_invFun := uniformContinuous_of_map_le (f := e.symm.toRingHom) (by simp [← h])

variable {R} in
/--
lemma `isTopologicallyNilpotent_of_mem` / 引理 `isTopologicallyNilpotent_of_mem`

English:
lemma isTopologicallyNilpotent_of_mem
  given: {a : R} (ha : a in i)
  statement: IsTopologicallyNilpotent a
  proof: by
  suffices forall m : Nat, exists n₀, forall n, n₀ <= n -> a ^ n in i ^ m by
    simpa [IsTopologicallyNilpotent, i.hasBasis_nhds_zero_adic.tendsto_right_iff]
  exact fun m => ⟨m, fun n hn => Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

中文:
引理 isTopologicallyNilpotent_of_mem
  条件: {a : R} (ha : a in i)
  结论: IsTopologicallyNilpotent a
  证明: by
  suffices forall m : Nat, exists n₀, forall n, n₀ <= n -> a ^ n in i ^ m by
    simpa [IsTopologicallyNilpotent, i.hasBasis_nhds_zero_adic.tendsto_right_iff]
  exact fun m => ⟨m, fun n hn => Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

Depends on / 依赖: Ideal.pow_le_pow_right, Ideal.pow_mem_pow, IsTopologicallyNilpotent, hasBasis_nhds_zero_adic, i.hasBasis_nhds_zero_adic.tendsto_right_iff, pow_le_pow_right, pow_mem_pow, tendsto_right_iff
-/
lemma isTopologicallyNilpotent_of_mem {a : R} (ha : a in i) : IsTopologicallyNilpotent a := by
  suffices forall m : Nat, exists n₀, forall n, n₀ <= n -> a ^ n in i ^ m by
    simpa [IsTopologicallyNilpotent, i.hasBasis_nhds_zero_adic.tendsto_right_iff]
  exact fun m => ⟨m, fun n hn => Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

/-- The adic topology on an `R` module coming from the ideal `WithIdeal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
@[instance_reducible]
/--
Definition of `topologicalSpaceModule` / `topologicalSpaceModule` 的定义

English:
definition topologicalSpaceModule
  signature: (M : Type*) [AddCommGroup M] [Module R M]
  body: (i : Ideal R).adicModuleTopology M

中文:
定义 topologicalSpaceModule
  签名: (M : 类型) [加法交换群 M] [模 R M]
  定义体: (i : Ideal R).adicModuleTopology M

Depends on / 依赖: adicModuleTopology
-/
def topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicModuleTopology M

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
example : NonarchimedeanRing R := by infer_instance

example : IsTopologicalRing (UniformSpace.Completion R) := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @IsTopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal
