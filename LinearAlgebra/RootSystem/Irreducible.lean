/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.RootPositive
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.RepresentationTheory.Submodule

/-!
# Irreducible root pairings

This file contains basic definitions and results about irreducible root systems.

## Main definitions / results:
* `RootPairing.isSimpleModule_weylGroupRootRep_iff`: a criterion for the representation of the Weyl
  group on root space to be irreducible.
* `RootPairing.IsIrreducible`: a typeclass encoding the fact that a root pairing is irreducible.
* `RootPairing.IsIrreducible.mk'`: an alternative constructor for irreducibility when the
  coefficients are a field.

-/

@[expose] public section

open Function Set
open Submodule (span span_le)
open LinearMap (ker)
open MulAction (orbit mem_orbit_self mem_orbit_iff)
open Module.End (invtSubmodule)
open scoped MonoidAlgebra

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/--
Definition of `invtRootSubmodule` / `invtRootSubmodule` 的定义

English:
definition invtRootSubmodule
  signature: : Sublattice (Submodule R M)
  body: ⨅ i, invtSubmodule (P.reflection i)

中文:
定义 invtRootSubmodule
  签名: : Sublattice (Submodule R M)
  定义体: ⨅ i, invtSubmodule (P.reflection i)

Depends on / 依赖: P.reflection, invtSubmodule, reflection
-/
def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)

/--
lemma `mem_invtRootSubmodule_iff` / 引理 `mem_invtRootSubmodule_iff`

English:
lemma mem_invtRootSubmodule_iff
  given: {q : Submodule R M}
  proof: by
  simp [invtRootSubmodule]

中文:
引理 mem_invtRootSubmodule_iff
  条件: {q : Submodule R M}
  证明: by
  simp [invtRootSubmodule]

Depends on / 依赖: invtRootSubmodule
-/
lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]

/--
lemma `invtRootSubmodule.top_mem` / 引理 `invtRootSubmodule.top_mem`

English:
lemma invtRootSubmodule.top_mem
  statement: ⊤ in P.invtRootSubmodule
  proof: by
  simp [invtRootSubmodule]

中文:
引理 invtRootSubmodule.top_mem
  结论: ⊤ in P.invtRootSubmodule
  证明: by
  simp [invtRootSubmodule]
-/
@[simp] protected lemma invtRootSubmodule.top_mem : ⊤ in P.invtRootSubmodule := by
  simp [invtRootSubmodule]

/--
lemma `invtRootSubmodule.bot_mem` / 引理 `invtRootSubmodule.bot_mem`

English:
lemma invtRootSubmodule.bot_mem
  statement: ⊥ in P.invtRootSubmodule
  proof: by
  simp [invtRootSubmodule]

中文:
引理 invtRootSubmodule.bot_mem
  结论: ⊥ in P.invtRootSubmodule
  证明: by
  simp [invtRootSubmodule]
-/
@[simp] protected lemma invtRootSubmodule.bot_mem : ⊥ in P.invtRootSubmodule := by
  simp [invtRootSubmodule]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder P.invtRootSubmodule
  body: ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

中文:
实例 :
  签名: BoundedOrder P.invtRootSubmodule
  定义体: ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

Depends on / 依赖: invtRootSubmodule, invtRootSubmodule.top_mem, top_mem
-/
instance : BoundedOrder P.invtRootSubmodule where
  top := ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial P.invtRootSubmodule where
  body: ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

中文:
实例 [Nontrivial
  签名: M] : Nontrivial P.invtRootSubmodule where
  定义体: ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, bot_ne_top, ext_iff, ne_eq
-/
instance [Nontrivial M] : Nontrivial P.invtRootSubmodule where
  exists_pair_ne := ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥
  proof: rfl

中文:
引理 coe_bot
  结论: ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥
  证明: rfl
-/
@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤
  proof: rfl

中文:
引理 coe_top
  结论: ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤
  证明: rfl
-/
@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl

/--
lemma `eq_zero_iff_forall_coroot'_eq_zero` / 引理 `eq_zero_iff_forall_coroot'_eq_zero`

English:
lemma eq_zero_iff_forall_coroot'_eq_zero
  given: [P.IsRootSystem] {x : M}
  proof: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : x in ⨅ i, ker (P.coroot' i) := by aesop
  simpa [← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] using h

中文:
引理 eq_zero_iff_forall_coroot'_eq_zero
  条件: [P.IsRootSystem] {x : M}
  证明: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : x in ⨅ i, ker (P.coroot' i) := by aesop
  simpa [← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] using h

Depends on / 依赖: P.coroot, P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, coroot, corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, replace
-/
lemma eq_zero_iff_forall_coroot'_eq_zero [P.IsRootSystem] {x : M} :
    x = 0 ↔ forall i, P.coroot' i x = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : x in ⨅ i, ker (P.coroot' i) := by aesop
  simpa [← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] using h

/--
lemma `invtRootSubmodule.le_ker_coroot'` / 引理 `invtRootSubmodule.le_ker_coroot'`

English:
lemma invtRootSubmodule.le_ker_coroot'
  statement: {K : Type*} [Field K] [NeZero (2 : K)]
  proof: (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two k)
    (Submodule.disjoint_span_singleton_of_notMem hk)).mp
    (P.mem_invtRootSubmodule_iff.mp q.property k)

中文:
引理 invtRootSubmodule.le_ker_coroot'
  结论: {K : 类型} [Field K] [NeZero (2 : K)]
  证明: (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two k)
    (Submodule.disjoint_span_singleton_of_notMem hk)).mp
    (P.mem_invtRootSubmodule_iff.mp q.property k)

Depends on / 依赖: P.flip.root_coroot_two, P.mem_invtRootSubmodule_iff.mp, Submodule, Submodule.disjoint_span_singleton_of_notMem, Submodule.mem_invtSubmodule_reflection_iff, disjoint_span_singleton_of_notMem, mem_invtRootSubmodule_iff, mem_invtSubmodule_reflection_iff, property, q.property, root_coroot_two
-/
lemma invtRootSubmodule.le_ker_coroot' {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N}
    (q : P.invtRootSubmodule) {k : ι} (hk : P.root k ∉ (q : Submodule K M)) :
    (q : Submodule K M) <= LinearMap.ker (P.coroot' k) :=
  (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two k)
    (Submodule.disjoint_span_singleton_of_notMem hk)).mp
    (P.mem_invtRootSubmodule_iff.mp q.property k)

/--
lemma `invtRootSubmodule.eq_bot_iff` / 引理 `invtRootSubmodule.eq_bot_iff`

English:
lemma invtRootSubmodule.eq_bot_iff
  statement: {K : Type*} [Field K] [NeZero (2 : K)]
  proof: by
  refine ⟨fun h => by simp [h, P.ne_zero], fun h => ?_⟩
  simp_rw [Subtype.mk_eq_bot_iff (invtRootSubmodule.bot_mem P), Submodule.eq_bot_iff,
    P.eq_zero_iff_forall_coroot'_eq_zero, ← LinearMap.mem_ker]
  exact fun x hx i => invtRootSubmodule.le_ker_coroot' q (h i) hx

中文:
引理 invtRootSubmodule.eq_bot_iff
  结论: {K : 类型} [Field K] [NeZero (2 : K)]
  证明: by
  refine ⟨fun h => by simp [h, P.ne_zero], fun h => ?_⟩
  simp_rw [Subtype.mk_eq_bot_iff (invtRootSubmodule.bot_mem P), Submodule.eq_bot_iff,
    P.eq_zero_iff_forall_coroot'_eq_zero, ← LinearMap.mem_ker]
  exact fun x hx i => invtRootSubmodule.le_ker_coroot' q (h i) hx

Depends on / 依赖: LinearMap, LinearMap.mem_ker, P.eq_zero_iff_forall_coroot, P.ne_zero, Submodule, Submodule.eq_bot_iff, Subtype, Subtype.mk_eq_bot_iff, _eq_zero, bot_mem, eq_bot_iff, eq_zero_iff_forall_coroot, invtRootSubmodule, invtRootSubmodule.bot_mem, invtRootSubmodule.le_ker_coroot, le_ker_coroot, mem_ker, mk_eq_bot_iff, ne_zero, simp_rw
-/
lemma invtRootSubmodule.eq_bot_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊥ ↔ forall i, P.root i ∉ (q : Submodule K M) := by
  refine ⟨fun h => by simp [h, P.ne_zero], fun h => ?_⟩
  simp_rw [Subtype.mk_eq_bot_iff (invtRootSubmodule.bot_mem P), Submodule.eq_bot_iff,
    P.eq_zero_iff_forall_coroot'_eq_zero, ← LinearMap.mem_ker]
  exact fun x hx i => invtRootSubmodule.le_ker_coroot' q (h i) hx

/--
lemma `invtRootSubmodule.eq_top_iff` / 引理 `invtRootSubmodule.eq_top_iff`

English:
lemma invtRootSubmodule.eq_top_iff
  statement: {K : Type*} [Field K] [Module K M] [Module K N]
  proof: ⟨fun h => by simp [h], fun h => by simpa using Submodule.span_mono h (R := K)⟩

中文:
引理 invtRootSubmodule.eq_top_iff
  结论: {K : 类型} [Field K] [Module K M] [Module K N]
  证明: ⟨fun h => by simp [h], fun h => by simpa using Submodule.span_mono h (R := K)⟩

Depends on / 依赖: SigmaFinite, SigmaFinite.of_isFiniteMeasureOnCompacts, Submodule, Submodule.span_mono, TopologicalSpace, of_isFiniteMeasureOnCompacts, span_mono
-/
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [Module K M] [Module K N]
    {P : RootPairing ι K M N} [P.IsRootSystem] (q : P.invtRootSubmodule) :
    q = ⊤ ↔ range P.root subseteq q :=
  ⟨fun h => by simp [h], fun h => by simpa using Submodule.span_mono h (R := K)⟩

/--
lemma `invtRootSubmodule.eq_span_root` / 引理 `invtRootSubmodule.eq_span_root`

English:
lemma invtRootSubmodule.eq_span_root
  statement: {K : Type*} [Field K] [NeZero (2 : K)]
  proof: by
  set Q := (q : Submodule K M)
  have hSQ : span K (P.root '' {i | P.root i in Q}) <= Q :=
    span_le.mpr (Set.image_subset_iff.mpr fun _ h => h)
  refine le_antisymm ?_ hSQ
  set S := span K (P.root '' {i | P.root i in Q})
  set T := span K (P.root '' {i | P.root i ∉ Q})
  have h_sup : S ⊔ T = 

中文:
引理 invtRootSubmodule.eq_span_root
  结论: {K : 类型} [Field K] [NeZero (2 : K)]
  证明: by
  set Q := (q : Submodule K M)
  have hSQ : span K (P.root '' {i | P.root i in Q}) <= Q :=
    span_le.mpr (Set.image_subset_iff.mpr fun _ h => h)
  refine le_antisymm ?_ hSQ
  set S := span K (P.root '' {i | P.root i in Q})
  set T := span K (P.root '' {i | P.root i ∉ Q})
  have h_sup : S ⊔ T = 

Depends on / 依赖: P.root, Set.image_subset_iff.mpr, Set.image_union, Set.image_univ, Set.univ, Submodule, Submodule.span_union, TopologicalSpace, h_sup, image_subset_iff, image_union, image_univ, le_antisymm, sigmaFinite_of_locallyFinite, span_le, span_le.mpr, span_union
-/
lemma invtRootSubmodule.eq_span_root {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    (q : Submodule K M) = span K (P.root '' {i | P.root i in (q : Submodule K M)}) := by
  set Q := (q : Submodule K M)
  have hSQ : span K (P.root '' {i | P.root i in Q}) <= Q :=
    span_le.mpr (Set.image_subset_iff.mpr fun _ h => h)
  refine le_antisymm ?_ hSQ
  set S := span K (P.root '' {i | P.root i in Q})
  set T := span K (P.root '' {i | P.root i ∉ Q})
  have h_sup : S ⊔ T = ⊤ := by
    rw [← Submodule.span_union]; rw [← Set.image_union]
    have : {i | P.root i in Q} union {i | P.root i ∉ Q} = Set.univ := by ext; simp [em]
    rw [this]; rw [Set.image_univ]
    simp
  intro v hv
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h_sup ▸ Submodule.mem_top (x := v))
  suffices t = 0 by rw [this, add_zero]; exact hs
  have htQ : t in Q := by simpa using Q.sub_mem hv (hSQ hs)
  have h_ker : forall k, P.coroot' k t = 0 := by
    intro k
    by_cases hk : P.root k in Q
    · refine LinearMap.mem_ker.mp (span_le.mpr ?_ ht)
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe]; rw [LinearMap.mem_ker]; rw [P.root_coroot'_eq_pairing]; rw [P.pairing_eq_zero_iff']; rw [← P.root_coroot'_eq_pairing]
      exact LinearMap.mem_ker.mp (invtRootSubmodule.le_ker_coroot' q hj hk)
    · exact LinearMap.mem_ker.mp (invtRootSubmodule.le_ker_coroot' q hk htQ)
  exact P.eq_zero_iff_forall_coroot'_eq_zero.mpr h_ker

/--
lemma `isSimpleModule_weylGroupRootRep_iff` / 引理 `isSimpleModule_weylGroupRootRep_iff`

English:
lemma isSimpleModule_weylGroupRootRep_iff
  given: [Nontrivial M]
  proof: by
  rw [isSimpleModule_iff]; rw [← P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun h q hq₁ hq₂ => ?_, fun h => ⟨fun q => ?_⟩⟩
  · suffices forall g : P.weylGroup, q in invtSubmodule (P.weylGroupRootRep g) by
      let q' : P.weylGroupRootRep.invtSubmodule :=
        ⟨q, (Representa

中文:
引理 isSimpleModule_weylGroupRootRep_iff
  条件: [Nontrivial M]
  证明: by
  rw [isSimpleModule_iff]; rw [← P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun h q hq₁ hq₂ => ?_, fun h => ⟨fun q => ?_⟩⟩
  · suffices forall g : P.weylGroup, q in invtSubmodule (P.weylGroupRootRep g) by
      let q' : P.weylGroupRootRep.invtSubmodule :=
        ⟨q, (Representa

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, P.weylGroup, P.weylGroupRootRep, P.weylGroupRootRep.invtSubmodule, P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff, Representation, Representation.mem_invtSubmodule, eq_bot_or_eq_top, invtSubmodule, isSimpleModule_iff, isSimpleOrder_iff, mapSubmodule, mem_invtSubmodule, resolve_left, weylGroup, weylGroup.induction, weylGroupRootRep
-/
lemma isSimpleModule_weylGroupRootRep_iff [Nontrivial M] :
    IsSimpleModule R[P.weylGroup] P.weylGroupRootRep.asModule ↔
    forall (q : Submodule R M), (forall i, q in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤ := by
  rw [isSimpleModule_iff]; rw [← P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun h q hq₁ hq₂ => ?_, fun h => ⟨fun q => ?_⟩⟩
  · suffices forall g : P.weylGroup, q in invtSubmodule (P.weylGroupRootRep g) by
      let q' : P.weylGroupRootRep.invtSubmodule :=
        ⟨q, (Representation.mem_invtSubmodule P.weylGroupRootRep).mpr this⟩
      suffices q' = ⊤ by simpa [q']
      apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
      simpa [q']
    rintro ⟨g, hg⟩
    induction hg using weylGroup.induction with
    | mem i => exact hq₁ i
    | one => simp [← Submonoid.one_def]
    | mul x y hx hy hx' hy' => apply invtSubmodule.comp <;> assumption
  · rcases eq_or_ne q ⊥ with rfl | hq; · tauto
    suffices (q : Submodule R M) = ⊤ by right; simpa using this
    refine h q (fun i => ?_) (by simpa using hq)
    exact P.weylGroupRootRep.mem_invtSubmodule.mp q.property ⟨_, P.reflection_mem_weylGroup i⟩

/--
Definition of `IsIrreducible` / `IsIrreducible` 的定义

English:
class IsIrreducible
  parameters: : Prop where
  axioms and operations (4):
    - nontrivial : Nontrivial M
    - nontrivial' : Nontrivial N
    - eq_top_of_invtSubmodule_reflection((q : Submodule R M)) : (forall i, q in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤
    - eq_top_of_invtSubmodule_coreflection((q : Submodule R N)) : (forall i, q in invtSubmodule (P.coreflection i)) -> q != ⊥ -> q = ⊤

中文:
类 IsIrreducible
  参数: : 命题 where
  公理与运算 (4 个):
    - nontrivial : Nontrivial M
    - nontrivial' : Nontrivial N
    - eq_top_of_invtSubmodule_reflection((q : Submodule R M)) : (对任意 i, q in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤
    - eq_top_of_invtSubmodule_coreflection((q : Submodule R N)) : (对任意 i, q in invtSubmodule (P.coreflection i)) -> q != ⊥ -> q = ⊤
-/
@[mk_iff] class IsIrreducible : Prop where
  nontrivial : Nontrivial M
  nontrivial' : Nontrivial N
  eq_top_of_invtSubmodule_reflection (q : Submodule R M) :
    (forall i, q in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤
  eq_top_of_invtSubmodule_coreflection (q : Submodule R N) :
    (forall i, q in invtSubmodule (P.coreflection i)) -> q != ⊥ -> q = ⊤

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsIrreducible]
  signature: : P.flip.IsIrreducible where
  body: IsIrreducible.nontrivial' P
  nontrivial' := IsIrreducible.nontrivial P
  eq_top_of_invtSubmodule_reflection := IsIrreducible.eq_top_of_invtSubmodule_coreflection (P := P)
  eq_top_of_invtSubmodule_coreflection := IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P)

中文:
实例 [P.IsIrreducible]
  签名: : P.flip.IsIrreducible where
  定义体: IsIrreducible.nontrivial' P
  nontrivial' := IsIrreducible.nontrivial P
  eq_top_of_invtSubmodule_reflection := IsIrreducible.eq_top_of_invtSubmodule_coreflection (P := P)
  eq_top_of_invtSubmodule_coreflection := IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P)

Depends on / 依赖: IsIrreducible, IsIrreducible.nontrivial, nontrivial
-/
instance [P.IsIrreducible] : P.flip.IsIrreducible where
  nontrivial := IsIrreducible.nontrivial' P
  nontrivial' := IsIrreducible.nontrivial P
  eq_top_of_invtSubmodule_reflection := IsIrreducible.eq_top_of_invtSubmodule_coreflection (P := P)
  eq_top_of_invtSubmodule_coreflection := IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P)

/--
lemma `isSimpleModule_weylGroupRootRep` / 引理 `isSimpleModule_weylGroupRootRep`

English:
lemma isSimpleModule_weylGroupRootRep
  given: [P.IsIrreducible]
  proof: have := IsIrreducible.nontrivial P
  P.isSimpleModule_weylGroupRootRep_iff.mpr IsIrreducible.eq_top_of_invtSubmodule_reflection

@[nontriviality]

中文:
引理 isSimpleModule_weylGroupRootRep
  条件: [P.IsIrreducible]
  证明: have := IsIrreducible.nontrivial P
  P.isSimpleModule_weylGroupRootRep_iff.mpr IsIrreducible.eq_top_of_invtSubmodule_reflection

@[nontriviality]

Depends on / 依赖: IsIrreducible, IsIrreducible.eq_top_of_invtSubmodule_reflection, IsIrreducible.nontrivial, P.isSimpleModule_weylGroupRootRep_iff.mpr, eq_top_of_invtSubmodule_reflection, isSimpleModule_weylGroupRootRep_iff, nontrivial
-/
lemma isSimpleModule_weylGroupRootRep [P.IsIrreducible] :
    IsSimpleModule R[P.weylGroup] P.weylGroupRootRep.asModule :=
  have := IsIrreducible.nontrivial P
  P.isSimpleModule_weylGroupRootRep_iff.mpr IsIrreducible.eq_top_of_invtSubmodule_reflection

@[nontriviality]
/--
lemma `not_isIrreducible_of_subsingleton` / 引理 `not_isIrreducible_of_subsingleton`

English:
lemma not_isIrreducible_of_subsingleton
  given: [Subsingleton M]
  proof: fun contra => not_nontrivial _ contra.nontrivial

中文:
引理 not_isIrreducible_of_subsingleton
  条件: [Subsingleton M]
  证明: fun contra => not_nontrivial _ contra.nontrivial

Depends on / 依赖: contra, contra.nontrivial, nontrivial, not_nontrivial
-/
lemma not_isIrreducible_of_subsingleton [Subsingleton M] :
    ¬ P.IsIrreducible :=
  fun contra => not_nontrivial _ contra.nontrivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: ι] [NeZero (2 : R)] [P.IsIrreducible] : P.IsRootSystem where
  body: IsIrreducible.eq_top_of_invtSubmodule_reflection
    (P.rootSpan R) P.rootSpan_mem_invtSubmodule_reflection (P.rootSpan_ne_bot R)
  span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
    (P.corootSpan R) P.corootSpan_mem_invtSubmodule_coreflection (P.corootSpan_ne_bot R)

中文:
实例 [Nonempty
  签名: ι] [NeZero (2 : R)] [P.IsIrreducible] : P.IsRootSystem where
  定义体: IsIrreducible.eq_top_of_invtSubmodule_reflection
    (P.rootSpan R) P.rootSpan_mem_invtSubmodule_reflection (P.rootSpan_ne_bot R)
  span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
    (P.corootSpan R) P.corootSpan_mem_invtSubmodule_coreflection (P.corootSpan_ne_bot R)

Depends on / 依赖: IsIrreducible, IsIrreducible.eq_top_of_invtSubmodule_reflection, eq_top_of_invtSubmodule_reflection
-/
instance [Nonempty ι] [NeZero (2 : R)] [P.IsIrreducible] : P.IsRootSystem where
  span_root_eq_top := IsIrreducible.eq_top_of_invtSubmodule_reflection
    (P.rootSpan R) P.rootSpan_mem_invtSubmodule_reflection (P.rootSpan_ne_bot R)
  span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
    (P.corootSpan R) P.corootSpan_mem_invtSubmodule_coreflection (P.corootSpan_ne_bot R)

/--
lemma `invtSubmodule_reflection_of_invtSubmodule_coreflection` / 引理 `invtSubmodule_reflection_of_invtSubmodule_coreflection`

English:
lemma invtSubmodule_reflection_of_invtSubmodule_coreflection
  statement: (i : ι) (q : Submodule R N)
  proof: by
  rw [LinearEquiv.map_mem_invtSubmodule_iff]; rw [LinearEquiv.symm_symm]; rw [toPerfPair_conj_reflection]; rw [Module.End.mem_invtSubmodule]; rw [← Submodule.map_le_iff_le_comap]
exact (Submodule.dualAnnihilator_map_dualMap_le _ _).trans Submodule.dualAnnihilator_anti hq

中文:
引理 invtSubmodule_reflection_of_invtSubmodule_coreflection
  结论: (i : ι) (q : Submodule R N)
  证明: by
  rw [LinearEquiv.map_mem_invtSubmodule_iff]; rw [LinearEquiv.symm_symm]; rw [toPerfPair_conj_reflection]; rw [Module.End.mem_invtSubmodule]; rw [← Submodule.map_le_iff_le_comap]
exact (Submodule.dualAnnihilator_map_dualMap_le _ _).trans Submodule.dualAnnihilator_anti hq

Depends on / 依赖: LinearEquiv, LinearEquiv.map_mem_invtSubmodule_iff, LinearEquiv.symm_symm, Module, Module.End.mem_invtSubmodule, Submodule, Submodule.dualAnnihilator_anti, Submodule.dualAnnihilator_map_dualMap_le, Submodule.map_le_iff_le_comap, dualAnnihilator_anti, dualAnnihilator_map_dualMap_le, map_le_iff_le_comap, map_mem_invtSubmodule_iff, mem_invtSubmodule, symm_symm, toPerfPair_conj_reflection
-/
lemma invtSubmodule_reflection_of_invtSubmodule_coreflection (i : ι) (q : Submodule R N)
    (hq : q in invtSubmodule (P.coreflection i)) :
    q.dualAnnihilator.map (P.toPerfPair.symm : Module.Dual R N ->ₗ[R] M) in
      invtSubmodule (P.reflection i) := by
  rw [LinearEquiv.map_mem_invtSubmodule_iff]; rw [LinearEquiv.symm_symm]; rw [toPerfPair_conj_reflection]; rw [Module.End.mem_invtSubmodule]; rw [← Submodule.map_le_iff_le_comap]
exact (Submodule.dualAnnihilator_map_dualMap_le _ _).trans Submodule.dualAnnihilator_anti hq

/--
lemma `IsIrreducible.mk'` / 引理 `IsIrreducible.mk'`

English:
lemma IsIrreducible.mk'
  statement: {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M]
  proof: inferInstance
  nontrivial' := (Module.nontrivial_dual_iff K).mp P.toPerfPair.symm.nontrivial
  eq_top_of_invtSubmodule_reflection := h
  eq_top_of_invtSubmodule_coreflection q stab ne_bot := by
    specialize h (q.dualAnnihilator.map P.toPerfPair.symm)
      fun i => invtSubmodule_reflection_of_inv

中文:
引理 IsIrreducible.mk'
  结论: {K : 类型} [Field K] [Module K M] [Module K N] [Nontrivial M]
  证明: inferInstance
  nontrivial' := (Module.nontrivial_dual_iff K).mp P.toPerfPair.symm.nontrivial
  eq_top_of_invtSubmodule_reflection := h
  eq_top_of_invtSubmodule_coreflection q stab ne_bot := by
    specialize h (q.dualAnnihilator.map P.toPerfPair.symm)
      fun i => invtSubmodule_reflection_of_inv
-/
lemma IsIrreducible.mk' {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M]
    (P : RootPairing ι K M N)
    (h : forall (q : Submodule K M), (forall i, q in invtSubmodule (P.reflection i)) -> q != ⊥ -> q = ⊤) :
    P.IsIrreducible where
  nontrivial := inferInstance
  nontrivial' := (Module.nontrivial_dual_iff K).mp P.toPerfPair.symm.nontrivial
  eq_top_of_invtSubmodule_reflection := h
  eq_top_of_invtSubmodule_coreflection q stab ne_bot := by
    specialize h (q.dualAnnihilator.map P.toPerfPair.symm)
      fun i => invtSubmodule_reflection_of_invtSubmodule_coreflection P i q (stab i)
    rw [Submodule.map_eq_top_iff]; rw [not_imp_comm] at h
    replace ne_bot : q.dualAnnihilator != ⊤ := by simpa
    simpa using h ne_bot

/--
lemma `isIrreducible_iff_invtRootSubmodule` / 引理 `isIrreducible_iff_invtRootSubmodule`

English:
lemma isIrreducible_iff_invtRootSubmodule
  proof: by
  refine ⟨fun h => ⟨fun ⟨q, hq⟩ => ?_⟩, fun h => IsIrreducible.mk' P fun q hq hq' => ?_⟩
  · simp only [invtRootSubmodule.bot_mem, invtRootSubmodule.top_mem, Subtype.mk_eq_bot_iff,
      Subtype.mk_eq_top_iff]
    rw [mem_invtRootSubmodule_iff] at hq
    have := IsIrreducible.eq_top_of_invtSubmod

中文:
引理 isIrreducible_iff_invtRootSubmodule
  证明: by
  refine ⟨fun h => ⟨fun ⟨q, hq⟩ => ?_⟩, fun h => IsIrreducible.mk' P fun q hq hq' => ?_⟩
  · simp only [invtRootSubmodule.bot_mem, invtRootSubmodule.top_mem, Subtype.mk_eq_bot_iff,
      Subtype.mk_eq_top_iff]
    rw [mem_invtRootSubmodule_iff] at hq
    have := IsIrreducible.eq_top_of_invtSubmod

Depends on / 依赖: IsIrreducible, IsIrreducible.eq_top_of_invtSubmodule_reflection, IsIrreducible.mk, IsSimpleOrder, IsSimpleOrder.bot_lt_iff_eq_top, P.invtRootSubmodule, P.mem_invtRootSubmodule_iff.mpr, Subtype, Subtype.mk_eq_bot_iff, Subtype.mk_eq_top_iff, bot_lt_iff_eq_top, bot_lt_iff_ne_bot, bot_mem, eq_top_of_invtSubmodule_reflection, invtRootSubmodule, invtRootSubmodule.bot_mem, invtRootSubmodule.top_mem, mem_invtRootSubmodule_iff, mk_eq_bot_iff, mk_eq_top_iff
-/
lemma isIrreducible_iff_invtRootSubmodule
    {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M] (P : RootPairing ι K M N) :
    P.IsIrreducible ↔ IsSimpleOrder P.invtRootSubmodule := by
  refine ⟨fun h => ⟨fun ⟨q, hq⟩ => ?_⟩, fun h => IsIrreducible.mk' P fun q hq hq' => ?_⟩
  · simp only [invtRootSubmodule.bot_mem, invtRootSubmodule.top_mem, Subtype.mk_eq_bot_iff,
      Subtype.mk_eq_top_iff]
    rw [mem_invtRootSubmodule_iff] at hq
    have := IsIrreducible.eq_top_of_invtSubmodule_reflection q hq
    tauto
  · let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
    replace hq' : ⊥ < q' := by simpa [q', bot_lt_iff_ne_bot, -IsSimpleOrder.bot_lt_iff_eq_top]
    suffices q' = ⊤ by simpa [q'] using this
    exact IsSimpleOrder.eq_top_of_lt hq'

/--
lemma `exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule` / 引理 `exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule`

English:
lemma exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule
  proof: by
  refine ⟨{i | ¬ Disjoint q (R ∙ P.root i)}, by simp, fun i hi => ?_⟩
  simp only [mem_ofPred_eq, not_not] at hi
  rw [← Submodule.mem_invtSubmodule_reflection_iff (by simp) hi]
  exact hq i

中文:
引理 exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule
  证明: by
  refine ⟨{i | ¬ Disjoint q (R ∙ P.root i)}, by simp, fun i hi => ?_⟩
  simp only [mem_ofPred_eq, not_not] at hi
  rw [← Submodule.mem_invtSubmodule_reflection_iff (by simp) hi]
  exact hq i

Depends on / 依赖: Disjoint, P.root, Submodule, Submodule.mem_invtSubmodule_reflection_iff, mem_invtSubmodule_reflection_iff, mem_ofPred_eq, not_not
-/
lemma exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule
    [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] (q : Submodule R M)
    (hq : forall i, q in invtSubmodule (P.reflection i)) :
    exists Φ : Set ι, (forall i in Φ, ¬ Disjoint q (R ∙ P.root i)) ∧ (forall i ∉ Φ, q <= ker (P.coroot' i)) := by
  refine ⟨{i | ¬ Disjoint q (R ∙ P.root i)}, by simp, fun i hi => ?_⟩
  simp only [mem_ofPred_eq, not_not] at hi
  rw [← Submodule.mem_invtSubmodule_reflection_iff (by simp) hi]
  exact hq i

variable [NeZero (2 : R)] [P.IsIrreducible]

/--
lemma `span_orbit_eq_top` / 引理 `span_orbit_eq_top`

English:
lemma span_orbit_eq_top
  given: (i : ι)
  proof: by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j => ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, mem_orbit_self _, P.ne_zero i⟩

中文:
引理 span_orbit_eq_top
  条件: (i : ι)
  证明: by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j => ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, mem_orbit_self _, P.ne_zero i⟩

Depends on / 依赖: Equiv.reflection, IsIrreducible, IsIrreducible.eq_top_of_invtSubmodule_reflection, Module, Module.End.span_orbit_mem_invtSubmodule, P.ne_zero, P.reflection_mem_weylGroup, P.root, P.weylGroup, eq_top_of_invtSubmodule_reflection, mem_orbit_self, ne_zero, reflection, reflection_mem_weylGroup, span_orbit_mem_invtSubmodule, weylGroup
-/
lemma span_orbit_eq_top (i : ι) :
    span R (orbit P.weylGroup (P.root i)) = ⊤ := by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j => ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, mem_orbit_self _, P.ne_zero i⟩

/--
lemma `exists_form_eq_form_and_form_ne_zero` / 引理 `exists_form_eq_form_and_form_ne_zero`

English:
lemma exists_form_eq_form_and_form_ne_zero
  given: (B : P.InvariantForm) (i j : ι)
  proof: by
  by_contra! contra
  suffices span R (orbit P.weylGroup (P.root j)) <= ker (B.form (P.root i)) from
B.apply_root_ne_zero i by simpa [span_orbit_eq_top] using this
  refine span_le.mpr fun v hv => ?_
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  simp only [P.weylGroup_apply_root, SetLike.mem_coe, Li

中文:
引理 exists_form_eq_form_and_form_ne_zero
  条件: (B : P.InvariantForm) (i j : ι)
  证明: by
  by_contra! contra
  suffices span R (orbit P.weylGroup (P.root j)) <= ker (B.form (P.root i)) from
B.apply_root_ne_zero i by simpa [span_orbit_eq_top] using this
  refine span_le.mpr fun v hv => ?_
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  simp only [P.weylGroup_apply_root, SetLike.mem_coe, Li

Depends on / 依赖: B.apply_root_ne_zero, B.form, LinearMap, LinearMap.mem_ker, P.root, P.weylGroup, P.weylGroup_apply_root, SetLike, SetLike.mem_coe, Subgroup, Subgroup.smul_def, apply_root_ne_zero, contra, mem_coe, mem_ker, mem_orbit_iff, mem_orbit_iff.mp, smul_def, span_le, span_le.mpr
-/
lemma exists_form_eq_form_and_form_ne_zero (B : P.InvariantForm) (i j : ι) :
    exists k, B.form (P.root k) (P.root k) = B.form (P.root j) (P.root j) ∧
         B.form (P.root i) (P.root k) != 0 := by
  by_contra! contra
  suffices span R (orbit P.weylGroup (P.root j)) <= ker (B.form (P.root i)) from
B.apply_root_ne_zero i by simpa [span_orbit_eq_top] using this
  refine span_le.mpr fun v hv => ?_
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  simp only [P.weylGroup_apply_root, SetLike.mem_coe, LinearMap.mem_ker]
  apply contra
  simp [← Subgroup.smul_def g]

/--
lemma `span_root_image_eq_top_of_forall_orthogonal` / 引理 `span_root_image_eq_top_of_forall_orthogonal`

English:
lemma span_root_image_eq_top_of_forall_orthogonal
  statement: (s : Set ι)
  proof: by
  have hq (j : ι) : span R (P.root '' s) in Module.End.invtSubmodule (P.reflection j) := by
    by_cases hj : P.root j in span R (P.root '' s)
    · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ hj
    · refine (Module.End.mem_invtSubmodule _).mpr fun x hx => ?_
      rwa [Submodule.mem

中文:
引理 span_root_image_eq_top_of_forall_orthogonal
  结论: (s : Set ι)
  证明: by
  have hq (j : ι) : span R (P.root '' s) in Module.End.invtSubmodule (P.reflection j) := by
    by_cases hj : P.root j in span R (P.root '' s)
    · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ hj
    · refine (Module.End.mem_invtSubmodule _).mpr fun x hx => ?_
      rwa [Submodule.mem

Depends on / 依赖: IsIrreducible, IsIrreducible.eq_top_of_invtSubmodule_reflection, LinearEquiv, LinearEquiv.coe_coe, Module, Module.End.invtSubmodule, Module.End.mem_invtSubmodule, P.ne_zero, P.reflection, P.root, Submodule, Submodule.mem_comap, Submodule.mem_invtSubmodule_reflection_of_mem, choose_spec, coe_coe, eq_top_of_invtSubmodule_reflection, hne.choose, hne.choose_spec, invtSubmodule, isFixedPt_reflection_of_isOrthogonal
-/
lemma span_root_image_eq_top_of_forall_orthogonal (s : Set ι)
    (hne : s.Nonempty) (h : forall j, P.root j ∉ span R (P.root '' s) -> forall i in s, P.IsOrthogonal j i) :
    span R (P.root '' s) = ⊤ := by
  have hq (j : ι) : span R (P.root '' s) in Module.End.invtSubmodule (P.reflection j) := by
    by_cases hj : P.root j in span R (P.root '' s)
    · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ hj
    · refine (Module.End.mem_invtSubmodule _).mpr fun x hx => ?_
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe,
        (isFixedPt_reflection_of_isOrthogonal (h _ hj) hx).eq]
  apply IsIrreducible.eq_top_of_invtSubmodule_reflection _ hq
  simpa using ⟨hne.choose, hne.choose_spec, P.ne_zero _⟩

/--
lemma `eq_top_of_mem_invtSubmodule_of_forall_eq_univ` / 引理 `eq_top_of_mem_invtSubmodule_of_forall_eq_univ`

English:
lemma eq_top_of_mem_invtSubmodule_of_forall_eq_univ
  proof: by
  obtain ⟨Φ, b, c⟩ := P.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule q h₁
  rcases Φ.eq_empty_or_nonempty with rfl | hΦ
  · replace c : q <= ⨅ i, LinearMap.ker (P.coroot' i) := by simpa using! c
    simp [h₀, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] at c
  · repl

中文:
引理 eq_top_of_mem_invtSubmodule_of_forall_eq_univ
  证明: by
  obtain ⟨Φ, b, c⟩ := P.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule q h₁
  rcases Φ.eq_empty_or_nonempty with rfl | hΦ
  · replace c : q <= ⨅ i, LinearMap.ker (P.coroot' i) := by simpa using! c
    simp [h₀, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] at c
  · repl

Depends on / 依赖: LinearMap, LinearMap.ker, MeasurableInf, OrderDual, OrderDual.instMeasurableSup, P.coroot, P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, P.exist_set_root_not_disjoint_and_le_ker_coroot, P.ne_zero, P.root, Submodule, Submodule.disjoint_span_singleton, _of_invtSubmodule, coroot, corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot, disjoint_span_singleton, eq_empty_or_nonempty, exist_set_root_not_disjoint_and_le_ker_coroot, instMeasurableSup, ne_zero
-/
lemma eq_top_of_mem_invtSubmodule_of_forall_eq_univ
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N]
    (P : RootPairing ι K M N) [P.IsRootSystem]
    (q : Submodule K M)
    (h₀ : q != ⊥)
    (h₁ : forall i, q in invtSubmodule (P.reflection i))
    (h₂ : forall Φ, Φ.Nonempty -> P.root '' Φ subseteq q -> (forall i ∉ Φ, q <= ker (P.coroot' i)) -> Φ = univ) :
    q = ⊤ := by
  obtain ⟨Φ, b, c⟩ := P.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule q h₁
  rcases Φ.eq_empty_or_nonempty with rfl | hΦ
  · replace c : q <= ⨅ i, LinearMap.ker (P.coroot' i) := by simpa using! c
    simp [h₀, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] at c
  · replace b : P.root '' Φ subseteq q := by
      simpa [Submodule.disjoint_span_singleton' (P.ne_zero _)] using! b
    simpa [h₂ Φ hΦ b c, ← span_le] using! b

end RootPairing
