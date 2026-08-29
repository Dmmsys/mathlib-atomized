/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.RingTheory.IdealFilter.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.FilterBasis

/-!
# Topologies associated to ideal filters

This file constructs topological structures on a ring from an `IdealFilter` and characterizes
uniform ideal filters in terms of ring filter bases.

## Main definitions
* `WithIdealFilter`: Type synonym for a ring that depends on a choice of ideal filter. This can be
  used to assign and infer instances on a ring that depend on an ideal filter.
* `IdealFilter.addGroupFilterBasis`: the `AddGroupFilterBasis` with sets the ideals of `F`.
* `IdealFilter.ringFilterBasis`: under `[F.IsUniform]`, the `RingFilterBasis` with sets the ideals
  of `F`.

## Main statements

* `IdealFilter.isUniform_iff_exists_ringFilterBasis`: An `IdealFilter` on a ring `A` is uniform if
  and only if its ideals form a `RingFilterBasis` for `A`.

## References

* [nLab: Uniform filter](https://ncatlab.org/nlab/show/uniform+filter)

## Tags

ring theory, ideal, filter, linear topology
-/

@[expose] public section

open scoped Pointwise Topology

namespace IdealFilter

/-- The additive-group filter basis whose sets are the ideals belonging to the ideal filter `F`. -/
@[instance_reducible]
/--
Definition of `addGroupFilterBasis` / `addGroupFilterBasis` 的定义

English:
definition addGroupFilterBasis
  signature: {A : Type*} [Ring A] (F : IdealFilter A)
  body: {(I : Set A) | I in F}
  nonempty := ⟨_, ⟨_, F.nonempty.choose_spec, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, hI, rfl⟩ ⟨J, hJ, rfl⟩
    exact ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem hI hJ, rfl⟩, fun _ h => h⟩
  zero' := by aesop
  add' := by aesop
  neg' := by aesop
  conj' := by aesop

中文:
定义 addGroupFilterBasis
  签名: {A : 类型} [Ring A] (F : IdealFilter A)
  定义体: {(I : Set A) | I in F}
  nonempty := ⟨_, ⟨_, F.nonempty.choose_spec, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, hI, rfl⟩ ⟨J, hJ, rfl⟩
    exact ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem hI hJ, rfl⟩, fun _ h => h⟩
  zero' := by aesop
  add' := by aesop
  neg' := by aesop
  conj' := by aesop
-/
def addGroupFilterBasis {A : Type*} [Ring A] (F : IdealFilter A) : AddGroupFilterBasis A where
  sets := {(I : Set A) | I in F}
  nonempty := ⟨_, ⟨_, F.nonempty.choose_spec, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, hI, rfl⟩ ⟨J, hJ, rfl⟩
    exact ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem hI hJ, rfl⟩, fun _ h => h⟩
  zero' := by aesop
  add' := by aesop
  neg' := by aesop
  conj' := by aesop

/-- Under `[F.IsUniform]`, the ring filter basis obtained from `addGroupFilterBasis`. -/
@[simps! -isSimp sets, instance_reducible]
/--
Definition of `ringFilterBasis` / `ringFilterBasis` 的定义

English:
definition ringFilterBasis
  signature: {A : Type*} [Ring A] {F : IdealFilter A} [F.IsUniform]
  body: F.addGroupFilterBasis
  mul' := by
    rintro U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ => mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, fun a ha => Ideal.mul_mem_left I x₀ ha⟩
  mul_right' := by
    rintro x₀ U ⟨I, hI

中文:
定义 ringFilterBasis
  签名: {A : 类型} [Ring A] {F : IdealFilter A} [F.IsUniform]
  定义体: F.addGroupFilterBasis
  mul' := by
    rintro U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ => mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, fun a ha => Ideal.mul_mem_left I x₀ ha⟩
  mul_right' := by
    rintro x₀ U ⟨I, hI

Depends on / 依赖: F.addGroupFilterBasis, addGroupFilterBasis
-/
def ringFilterBasis {A : Type*} [Ring A] {F : IdealFilter A} [F.IsUniform] :
    RingFilterBasis A where
  __ := F.addGroupFilterBasis
  mul' := by
    rintro U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ => mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, fun a ha => Ideal.mul_mem_left I x₀ ha⟩
  mul_right' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    refine ⟨I.colon {x₀}, ⟨I.colon {x₀}, IsUniform.colon_mem hI x₀, rfl⟩,
      fun a ha => Set.mem_preimage.mpr (Submodule.mem_colon_singleton.mp ha)⟩

/--
theorem `isUniform_iff_exists_ringFilterBasis` / 定理 `isUniform_iff_exists_ringFilterBasis`

English:
theorem isUniform_iff_exists_ringFilterBasis
  given: {A : Type*} [Ring A] {F : IdealFilter A}
  proof: by
  refine ⟨fun _ => ⟨F.ringFilterBasis, rfl⟩, fun ⟨B, hB⟩ => ⟨fun {I} hI a => ?_⟩⟩
  obtain ⟨V, hbasis, hsub⟩ := B.mul_right a (U := I) (hB.ge (by simpa))
  obtain ⟨J, hJ, rfl⟩ := hB.le hbasis
  exact Order.PFilter.mem_of_le (fun x hx => by simpa using (hsub hx)) hJ

中文:
定理 isUniform_iff_exists_ringFilterBasis
  条件: {A : 类型} [Ring A] {F : IdealFilter A}
  证明: by
  refine ⟨fun _ => ⟨F.ringFilterBasis, rfl⟩, fun ⟨B, hB⟩ => ⟨fun {I} hI a => ?_⟩⟩
  obtain ⟨V, hbasis, hsub⟩ := B.mul_right a (U := I) (hB.ge (by simpa))
  obtain ⟨J, hJ, rfl⟩ := hB.le hbasis
  exact Order.PFilter.mem_of_le (fun x hx => by simpa using (hsub hx)) hJ

Depends on / 依赖: B.mul_right, F.ringFilterBasis, Order.PFilter.mem_of_le, PFilter, hB.ge, hB.le, hbasis, mem_of_le, mul_right, ringFilterBasis
-/
theorem isUniform_iff_exists_ringFilterBasis {A : Type*} [Ring A] {F : IdealFilter A} :
    F.IsUniform ↔ exists B : RingFilterBasis A, B.sets = {(I : Set A) | I in F} := by
  refine ⟨fun _ => ⟨F.ringFilterBasis, rfl⟩, fun ⟨B, hB⟩ => ⟨fun {I} hI a => ?_⟩⟩
  obtain ⟨V, hbasis, hsub⟩ := B.mul_right a (U := I) (hB.ge (by simpa))
  obtain ⟨J, hJ, rfl⟩ := hB.le hbasis
  exact Order.PFilter.mem_of_le (fun x hx => by simpa using (hsub hx)) hJ

end IdealFilter

/-- Type synonym for a ring that depends on a choice of ideal filter. We use this to assign a
topology generated by the ideal filter. -/
@[nolint unusedArguments]
/--
Definition of `WithIdealFilter` / `WithIdealFilter` 的定义

English:
definition WithIdealFilter
  signature: {A : Type*} [Ring A]
  body: fun _ => A
deriving Ring

中文:
定义 WithIdealFilter
  签名: {A : 类型} [Ring A]
  定义体: fun _ => A
deriving Ring
-/
def WithIdealFilter {A : Type*} [Ring A] : IdealFilter A -> Type _ := fun _ => A
deriving Ring

namespace WithIdealFilter

open IdealFilter

variable {A : Type*} [Ring A] {F : IdealFilter A}

/--
Definition of `idealSet` / `idealSet` 的定义

English:
abbreviation idealSet
  signature: (I : Ideal A)
  body: (I : Set A)

中文:
缩写 idealSet
  签名: (I : Ideal A)
  定义体: (I : Set A)
-/
abbrev idealSet (I : Ideal A) : Set (WithIdealFilter F) := (I : Set A)

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (WithIdealFilter F)
  body: fast_instance% F.addGroupFilterBasis.topology

中文:
实例 instTopologicalSpace
  签名: : TopologicalSpace (WithIdealFilter F)
  定义体: fast_instance% F.addGroupFilterBasis.topology

Depends on / 依赖: F.addGroupFilterBasis.topology, addGroupFilterBasis, fast_instance, topology
-/
instance instTopologicalSpace : TopologicalSpace (WithIdealFilter F) :=
  fast_instance% F.addGroupFilterBasis.topology

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (WithIdealFilter F)
  body: F.addGroupFilterBasis.isTopologicalAddGroup

中文:
实例 instIsTopologicalAddGroup
  签名: : IsTopologicalAddGroup (WithIdealFilter F)
  定义体: F.addGroupFilterBasis.isTopologicalAddGroup

Depends on / 依赖: F.addGroupFilterBasis.isTopologicalAddGroup, addGroupFilterBasis, isTopologicalAddGroup
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WithIdealFilter F) :=
  F.addGroupFilterBasis.isTopologicalAddGroup

/--
lemma `mem_nhds_iff` / 引理 `mem_nhds_iff`

English:
lemma mem_nhds_iff
  given: {a : (WithIdealFilter F)} {s : Set (WithIdealFilter F)}
  proof: by
  constructor
  · intro hs
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 hs with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨I, ⟨I, hI, rfl⟩, hIs⟩

中文:
引理 mem_nhds_iff
  条件: {a : (WithIdealFilter F)} {s : Set (WithIdealFilter F)}
  证明: by
  constructor
  · intro hs
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 hs with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨I, ⟨I, hI, rfl⟩, hIs⟩

Depends on / 依赖: F.addGroupFilterBasis, addGroupFilterBasis, mem_iff, nhds_hasBasis
-/
lemma mem_nhds_iff {a : (WithIdealFilter F)} {s : Set (WithIdealFilter F)} :
    s in 𝓝 a ↔ exists I in F, a +ᵥ idealSet I subseteq s := by
  constructor
  · intro hs
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 hs with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨I, ⟨I, hI, rfl⟩, hIs⟩

/--
lemma `mem_nhds_zero_iff` / 引理 `mem_nhds_zero_iff`

English:
lemma mem_nhds_zero_iff
  given: {s : Set (WithIdealFilter F)}
  proof: by
  simpa [zero_vadd] using mem_nhds_iff (a := 0) (s := s)

中文:
引理 mem_nhds_zero_iff
  条件: {s : Set (WithIdealFilter F)}
  证明: by
  simpa [zero_vadd] using mem_nhds_iff (a := 0) (s := s)

Depends on / 依赖: mem_nhds_iff, zero_vadd
-/
lemma mem_nhds_zero_iff {s : Set (WithIdealFilter F)} :
    s in 𝓝 0 ↔ exists I in F, idealSet I subseteq s := by
  simpa [zero_vadd] using mem_nhds_iff (a := 0) (s := s)

/--
Instance `instIsLinearTopology` / 实例 `instIsLinearTopology`

English:
instance instIsLinearTopology
  signature: : IsLinearTopology (WithIdealFilter F) (WithIdealFilter F)
  body: IsLinearTopology.mk_of_hasBasis' (R := (WithIdealFilter F))
    (M := (WithIdealFilter F))
    (ι := Ideal A) (S := Ideal A)
    (p := fun I : Ideal A => I in F) (s := fun I : Ideal A => I)
    ⟨fun _ => mem_nhds_zero_iff⟩
    (fun I a _ hm => Submodule.smul_mem I a hm)

中文:
实例 instIsLinearTopology
  签名: : IsLinearTopology (WithIdealFilter F) (WithIdealFilter F)
  定义体: IsLinearTopology.mk_of_hasBasis' (R := (WithIdealFilter F))
    (M := (WithIdealFilter F))
    (ι := Ideal A) (S := Ideal A)
    (p := fun I : Ideal A => I in F) (s := fun I : Ideal A => I)
    ⟨fun _ => mem_nhds_zero_iff⟩
    (fun I a _ hm => Submodule.smul_mem I a hm)

Depends on / 依赖: IsLinearTopology, IsLinearTopology.mk_of_hasBasis, Submodule, Submodule.smul_mem, WithIdealFilter, mem_nhds_zero_iff, mk_of_hasBasis, smul_mem
-/
instance instIsLinearTopology : IsLinearTopology (WithIdealFilter F) (WithIdealFilter F) :=
  IsLinearTopology.mk_of_hasBasis' (R := (WithIdealFilter F))
    (M := (WithIdealFilter F))
    (ι := Ideal A) (S := Ideal A)
    (p := fun I : Ideal A => I in F) (s := fun I : Ideal A => I)
    ⟨fun _ => mem_nhds_zero_iff⟩
    (fun I a _ hm => Submodule.smul_mem I a hm)

/--
Instance `instIsTopologicalRing` / 实例 `instIsTopologicalRing`

English:
instance instIsTopologicalRing
  signature: [F.IsUniform]
  body: F.ringFilterBasis.isTopologicalRing

中文:
实例 instIsTopologicalRing
  签名: [F.IsUniform]
  定义体: F.ringFilterBasis.isTopologicalRing

Depends on / 依赖: F.ringFilterBasis.isTopologicalRing, isTopologicalRing, ringFilterBasis
-/
instance instIsTopologicalRing [F.IsUniform] : IsTopologicalRing (WithIdealFilter F) :=
  F.ringFilterBasis.isTopologicalRing

end WithIdealFilter
