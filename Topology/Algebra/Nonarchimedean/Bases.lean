/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Neighborhood bases for non-archimedean rings and modules

This file contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `RingSubgroupsBasis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`RingSubgroupsBasis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular, the given subgroups become open subgroups
(bundled in `RingSubgroupsBasis.openAddSubgroup`) and we get a non-archimedean topological ring
(`RingSubgroupsBasis.nonarchimedean`).

A special case of this construction is given by `SubmodulesBasis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rise to the adic topology
(studied in its own file).
-/

@[expose] public section

open Set Filter Function Lattice

open Topology Filter Pointwise

/--
Definition of `RingSubgroupsBasis` / `RingSubgroupsBasis` 的定义

English:
structure RingSubgroupsBasis
  parameters: {A ι : Type*} [Ring A] (B : ι -> AddSubgroup A)
  axioms and operations (4):
    - inter : forall i j, exists k, B k <= B i ⊓ B j
    - mul : forall i, exists j, (B j : Set A) * B j subseteq B i
    - leftMul : forall x : A, forall i, exists j, (B j : Set A) subseteq (x * ·) ⁻¹' B i
    - rightMul : forall x : A, forall i, exists j, (B j : Set A) subseteq (· * x) ⁻¹' B i

中文:
结构 RingSubgroupsBasis
  参数: {A ι : 类型} [Ring A] (B : ι -> AddSubgroup A)
  公理与运算 (4 个):
    - inter : 对任意 i j, 存在 k, B k <= B i ⊓ B j
    - mul : 对任意 i, 存在 j, (B j : Set A) * B j subseteq B i
    - leftMul : 对任意 x : A, 对任意 i, 存在 j, (B j : Set A) subseteq (x * ·) ⁻¹' B i
    - rightMul : 对任意 x : A, 对任意 i, 存在 j, (B j : Set A) subseteq (· * x) ⁻¹' B i
-/
structure RingSubgroupsBasis {A ι : Type*} [Ring A] (B : ι -> AddSubgroup A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : forall i j, exists k, B k <= B i ⊓ B j
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : forall i, exists j, (B j : Set A) * B j subseteq B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `B' * x` is in `B`. -/
  leftMul : forall x : A, forall i, exists j, (B j : Set A) subseteq (x * ·) ⁻¹' B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `x * B'` is in `B`. -/
  rightMul : forall x : A, forall i, exists j, (B j : Set A) subseteq (· * x) ⁻¹' B i

namespace RingSubgroupsBasis

variable {A ι : Type*} [Ring A]

/--
theorem `of_comm` / 定理 `of_comm`

English:
theorem of_comm
  statement: {A ι : Type*} [CommRing A] (B : ι -> AddSubgroup A)
  proof: { inter
    mul
    leftMul
    rightMul := fun x i => (leftMul x i).imp fun j hj => by simpa only [mul_comm] using hj }

中文:
定理 of_comm
  结论: {A ι : 类型} [CommRing A] (B : ι -> AddSubgroup A)
  证明: { inter
    mul
    leftMul
    rightMul := fun x i => (leftMul x i).imp fun j hj => by simpa only [mul_comm] using hj }

Depends on / 依赖: leftMul, mul_comm, rightMul
-/
theorem of_comm {A ι : Type*} [CommRing A] (B : ι -> AddSubgroup A)
    (inter : forall i j, exists k, B k <= B i ⊓ B j) (mul : forall i, exists j, (B j : Set A) * B j subseteq B i)
    (leftMul : forall x : A, forall i, exists j, (B j : Set A) subseteq (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := fun x i => (leftMul x i).imp fun j hj => by simpa only [mul_comm] using hj }

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
@[instance_reducible]
/--
Definition of `toRingFilterBasis` / `toRingFilterBasis` 的定义

English:
definition toRingFilterBasis
  signature: [Nonempty ι] {B : ι -> AddSubgroup A} (hB : RingSubgroupsBasis B)
  body: { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  ad

中文:
定义 toRingFilterBasis
  签名: [Nonempty ι] {B : ι -> AddSubgroup A} (hB : RingSubgroupsBasis B)
  定义体: { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  ad
-/
def toRingFilterBasis [Nonempty ι] {B : ι -> AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.mul i
    use B k
    constructor
    · use k
    · exact hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.leftMul x₀ i
    use B k
    constructor
    · use k
    · exact hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.rightMul x₀ i
    use B k
    constructor
    · use k
    · exact hk

variable [Nonempty ι] {B : ι -> AddSubgroup A} (hB : RingSubgroupsBasis B)

/--
theorem `mem_addGroupFilterBasis_iff` / 定理 `mem_addGroupFilterBasis_iff`

English:
theorem mem_addGroupFilterBasis_iff
  given: {V : Set A}
  proof: Iff.rfl

中文:
定理 mem_addGroupFilterBasis_iff
  条件: {V : Set A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V in hB.toRingFilterBasis.toAddGroupFilterBasis ↔ exists i, V = B i :=
  Iff.rfl

/--
theorem `mem_addGroupFilterBasis` / 定理 `mem_addGroupFilterBasis`

English:
theorem mem_addGroupFilterBasis
  given: (i)
  statement: (B i : Set A) in hB.toRingFilterBasis.toAddGroupFilterBasis
  proof: ⟨i, rfl⟩

中文:
定理 mem_addGroupFilterBasis
  条件: (i)
  结论: (B i : Set A) in hB.toRingFilterBasis.toAddGroupFilterBasis
  证明: ⟨i, rfl⟩
-/
theorem mem_addGroupFilterBasis (i) : (B i : Set A) in hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
@[instance_reducible]
/--
Definition of `topology` / `topology` 的定义

English:
definition topology
  signature: : TopologicalSpace A
  body: hB.toRingFilterBasis.toAddGroupFilterBasis.topology

中文:
定义 topology
  签名: : TopologicalSpace A
  定义体: hB.toRingFilterBasis.toAddGroupFilterBasis.topology

Depends on / 依赖: hB.toRingFilterBasis.toAddGroupFilterBasis.topology, toAddGroupFilterBasis, toRingFilterBasis, topology
-/
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  statement: HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i
  proof: ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩

中文:
定理 hasBasis_nhds_zero
  结论: HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i
  证明: ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩

Depends on / 依赖: hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff, mem_iff, nhds_zero_hasBasis, toAddGroupFilterBasis, toRingFilterBasis
-/
theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩

/--
theorem `hasBasis_nhds` / 定理 `hasBasis_nhds`

English:
theorem hasBasis_nhds
  given: (a : A)
  proof: ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a in B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp o

中文:
定理 hasBasis_nhds
  条件: (a : A)
  证明: ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a in B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp o

Depends on / 依赖: b_in, hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis, image_add_left, image_subset_iff, mem_iff, neg_add_eq_sub, nhds_hasBasis, toAddGroupFilterBasis, toRingFilterBasis, true_and
-/
theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a in B i } :=
  ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a in B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp only [image_add_left, neg_add_eq_sub]
      ext b
      simp
    · rintro ⟨i, hi⟩
      use B i
      constructor
      · use i
      · rw [image_subset_iff]
        rintro b b_in
        apply hi
        simpa using b_in⟩

/--
Definition of `openAddSubgroup` / `openAddSubgroup` 的定义

English:
definition openAddSubgroup
  signature: (i : ι)
  body: let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }

中文:
定义 openAddSubgroup
  签名: (i : ι)
  定义体: let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }

Depends on / 依赖: a_in, add_mem, b_in, hB.hasBasis_nhds, hB.topology, hasBasis_nhds, isOpen, isOpen_iff_mem_nhds, mem_iff, topology
-/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }

-- See note [non-Archimedean non-instances]
/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  statement: @NonarchimedeanRing A _ hB.topology
  proof: by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) subseteq U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

中文:
定理 nonarchimedean
  结论: @NonarchimedeanRing A _ hB.topology
  证明: by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) subseteq U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

Depends on / 依赖: hB.hasBasis_nhds_zero.mem_iff.mp, hB.openAddSubgroup, hB.topology, hasBasis_nhds_zero, mem_iff, openAddSubgroup, subseteq, topology
-/
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) subseteq U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

end RingSubgroupsBasis

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/--
Definition of `SubmodulesRingBasis` / `SubmodulesRingBasis` 的定义

English:
structure SubmodulesRingBasis
  parameters: (B : ι -> Submodule R A)
  axioms and operations (3):
    - inter : forall i j, exists k, B k <= B i ⊓ B j
    - leftMul : forall (a : A) (i), exists j, a • B j <= B i
    - mul : forall i, exists j, (B j : Set A) * B j subseteq B i

中文:
结构 SubmodulesRingBasis
  参数: (B : ι -> Submodule R A)
  公理与运算 (3 个):
    - inter : 对任意 i j, 存在 k, B k <= B i ⊓ B j
    - leftMul : 对任意 (a : A) (i), 存在 j, a • B j <= B i
    - mul : 对任意 i, 存在 j, (B j : Set A) * B j subseteq B i
-/
structure SubmodulesRingBasis (B : ι -> Submodule R A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : forall i j, exists k, B k <= B i ⊓ B j
  /-- For any element `a : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `a • B'` is in `B`. -/
  leftMul : forall (a : A) (i), exists j, a • B j <= B i
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : forall i, exists j, (B j : Set A) * B j subseteq B i

namespace SubmodulesRingBasis

variable {B : ι -> Submodule R A} (hB : SubmodulesRingBasis B)

/--
theorem `toRing_subgroups_basis` / 定理 `toRing_subgroups_basis`

English:
theorem toRing_subgroups_basis
  given: (hB : SubmodulesRingBasis B)
  proof: by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b in B j)
  exact hj ⟨b, b_in, rfl⟩

中文:
定理 toRing_subgroups_basis
  条件: (hB : SubmodulesRingBasis B)
  证明: by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b in B j)
  exact hj ⟨b, b_in, rfl⟩

Depends on / 依赖: RingSubgroupsBasis, RingSubgroupsBasis.of_comm, b_in, hB.inter, hB.leftMul, hB.mul, leftMul, of_comm, toAddSubgroup
-/
theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup := by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b in B j)
  exact hj ⟨b, b_in, rfl⟩

/-- The topology associated to a basis of submodules in an algebra. -/
@[instance_reducible]
/--
Definition of `topology` / `topology` 的定义

English:
definition topology
  signature: [Nonempty ι] (hB : SubmodulesRingBasis B)
  body: hB.toRing_subgroups_basis.topology

中文:
定义 topology
  签名: [Nonempty ι] (hB : SubmodulesRingBasis B)
  定义体: hB.toRing_subgroups_basis.topology

Depends on / 依赖: hB.toRing_subgroups_basis.topology, toRing_subgroups_basis, topology
-/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology

end SubmodulesRingBasis

variable {M : Type*} [AddCommGroup M] [Module R M]

/--
Definition of `SubmodulesBasis` / `SubmodulesBasis` 的定义

English:
structure SubmodulesBasis
  parameters: [TopologicalSpace R] (B : ι -> Submodule R M)
  axioms and operations (2):
    - inter : forall i j, exists k, B k <= B i ⊓ B j
    - smul : forall (m : M) (i : ι), forallᶠ a in 𝓝 (0 : R), a • m in B i

中文:
结构 SubmodulesBasis
  参数: [TopologicalSpace R] (B : ι -> Submodule R M)
  公理与运算 (2 个):
    - inter : 对任意 i j, 存在 k, B k <= B i ⊓ B j
    - smul : 对任意 (m : M) (i : ι), 对任意ᶠ a in 𝓝 (0 : R), a • m in B i
-/
structure SubmodulesBasis [TopologicalSpace R] (B : ι -> Submodule R M) : Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : forall i j, exists k, B k <= B i ⊓ B j
  /-- For any element `m : M` and any set `B` in the basis, `a • m` lies in `B` for all
  `a` sufficiently close to `0`. -/
  smul : forall (m : M) (i : ι), forallᶠ a in 𝓝 (0 : R), a • m in B i

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι -> Submodule R M} (hB : SubmodulesBasis B)

/--
Definition of `toModuleFilterBasis` / `toModuleFilterBasis` 的定义

English:
definition toModuleFilterBasis
  signature: : ModuleFilterBasis R M where
  body: { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  ad

中文:
定义 toModuleFilterBasis
  签名: : ModuleFilterBasis R M where
  定义体: { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  ad
-/
def toModuleFilterBasis : ModuleFilterBasis R M where
  sets := { U | exists i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ
    constructor
    · exact univ_mem
    · use B i
      constructor
      · use i
      · rintro _ ⟨a, -, m, hm, rfl⟩
        exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro m
      exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i

/-- The topology associated to a basis of submodules in a module. -/
@[instance_reducible]
/--
Definition of `topology` / `topology` 的定义

English:
definition topology
  signature: : TopologicalSpace M
  body: hB.toModuleFilterBasis.toAddGroupFilterBasis.topology

中文:
定义 topology
  签名: : TopologicalSpace M
  定义体: hB.toModuleFilterBasis.toAddGroupFilterBasis.topology

Depends on / 依赖: hB.toModuleFilterBasis.toAddGroupFilterBasis.topology, toAddGroupFilterBasis, toModuleFilterBasis, topology
-/
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology

/--
Definition of `openAddSubgroup` / `openAddSubgroup` 的定义

English:
definition openAddSubgroup
  signature: (i : ι)
  body: let _ := hB.topology
  { (B i).toAddSubgroup with
    isOpen' := by
      let := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rf

中文:
定义 openAddSubgroup
  签名: (i : ι)
  定义体: let _ := hB.topology
  { (B i).toAddSubgroup with
    isOpen' := by
      let := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rf

Depends on / 依赖: a_in, add_mem, b_in, hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis, hB.topology, isOpen, isOpen_iff_mem_nhds, mem_iff, nhds_hasBasis, toAddGroupFilterBasis, toAddSubgroup, toModuleFilterBasis, topology
-/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology
  { (B i).toAddSubgroup with
    isOpen' := by
      let := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rfl⟩
        exact (B i).add_mem a_in b_in }

-- See note [non-Archimedean non-instances]
/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  given: (hB : SubmodulesBasis B)
  statement: @NonarchimedeanAddGroup M _ hB.topology
  proof: by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) subseteq U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note «non-Archimedean non-instances» /--
The non-Archimedean subgr

中文:
定理 nonarchimedean
  条件: (hB : SubmodulesBasis B)
  结论: @NonarchimedeanAddGroup M _ hB.topology
  证明: by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) subseteq U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note «non-Archimedean non-instances» /--
The non-Archimedean subgr

Depends on / 依赖: hB.openAddSubgroup, hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp, hB.topology, mem_iff, nhds_zero_hasBasis, openAddSubgroup, subseteq, toAddGroupFilterBasis, toModuleFilterBasis, topology
-/
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) subseteq U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note «non-Archimedean non-instances» /--
The non-Archimedean subgroup basis lemmas cannot be instances because some instances
(such as `MeasureTheory.AEEqFun.instAddMonoid` or `IsTopologicalAddGroup.toContinuousAdd`)
cause the search for `@IsTopologicalAddGroup β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/


end SubmodulesBasis

section

/-
In this section, we check that in an `R`-algebra `A` over a ring equipped with a topology,
a basis of `R`-submodules which is compatible with the topology on `R` is also a submodule basis
in the sense of `R`-modules (forgetting about the ring structure on `A`) and those two points of
view definitionaly gives the same topology on `A`.
-/
variable [TopologicalSpace R] {B : ι -> Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : forall (m : A) (i : ι), forallᶠ a : R in 𝓝 0, a • m in B i)
include hB hsmul

/--
theorem `SubmodulesRingBasis.toSubmodulesBasis` / 定理 `SubmodulesRingBasis.toSubmodulesBasis`

English:
theorem SubmodulesRingBasis.toSubmodulesBasis
  statement: SubmodulesBasis B
  proof: { inter := hB.inter
    smul := hsmul }

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

中文:
定理 SubmodulesRingBasis.toSubmodulesBasis
  结论: SubmodulesBasis B
  证明: { inter := hB.inter
    smul := hsmul }

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

Depends on / 依赖: hB.inter
-/
theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

end

/--
Definition of `RingFilterBasis.SubmodulesBasis` / `RingFilterBasis.SubmodulesBasis` 的定义

English:
structure RingFilterBasis.SubmodulesBasis
  parameters: (BR : RingFilterBasis R) (B : ι -> Submodule R M)
  axioms and operations (2):
    - inter : forall i j, exists k, B k <= B i ⊓ B j
    - smul : forall (m : M) (i : ι), exists U in BR, U subseteq (· • m) ⁻¹' B i

中文:
结构 RingFilterBasis.SubmodulesBasis
  参数: (BR : RingFilterBasis R) (B : ι -> Submodule R M)
  公理与运算 (2 个):
    - inter : 对任意 i j, 存在 k, B k <= B i ⊓ B j
    - smul : 对任意 (m : M) (i : ι), 存在 U in BR, U subseteq (· • m) ⁻¹' B i
-/
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι -> Submodule R M) :
    Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : forall i j, exists k, B k <= B i ⊓ B j
  /-- For any element `m : M` and any set `B i` in the submodule basis on `M`,
  there is a `U` in the ring filter basis on `R` such that `U * m` is in `B i`. -/
  smul : forall (m : M) (i : ι), exists U in BR, U subseteq (· • m) ⁻¹' B i

/--
theorem `RingFilterBasis.submodulesBasisIsBasis` / 定理 `RingFilterBasis.submodulesBasisIsBasis`

English:
theorem RingFilterBasis.submodulesBasisIsBasis
  statement: (BR : RingFilterBasis R) {B : ι -> Submodule R M}
  proof: let _ := BR.topology
  { inter := hB.inter
    smul := by
      let := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }

中文:
定理 RingFilterBasis.submodulesBasisIsBasis
  结论: (BR : RingFilterBasis R) {B : ι -> Submodule R M}
  证明: let _ := BR.topology
  { inter := hB.inter
    smul := by
      let := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }

Depends on / 依赖: BR.toAddGroupFilterBasis.mem_nhds_zero, BR.topology, V_in, hB.inter, hB.smul, mem_nhds_zero, mem_of_superset, toAddGroupFilterBasis, topology
-/
theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι -> Submodule R M}
    (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _ BR.topology B :=
  let _ := BR.topology
  { inter := hB.inter
    smul := by
      let := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }

/--
Definition of `RingFilterBasis.moduleFilterBasis` / `RingFilterBasis.moduleFilterBasis` 的定义

English:
definition RingFilterBasis.moduleFilterBasis
  signature: [Nonempty ι] (BR : RingFilterBasis R) {B : ι -> Submodule R M}
  body: @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)

中文:
定义 RingFilterBasis.moduleFilterBasis
  签名: [Nonempty ι] (BR : RingFilterBasis R) {B : ι -> Submodule R M}
  定义体: @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)

Depends on / 依赖: BR.submodulesBasisIsBasis, BR.topology, SubmodulesBasis, SubmodulesBasis.toModuleFilterBasis, submodulesBasisIsBasis, toModuleFilterBasis, topology
-/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι -> Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)
