/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Topology.NhdsSet
public import Mathlib.Topology.Inseparable

/-!
# Neighborhoods kernel of a set

In `Mathlib/Topology/Defs/Filter.lean`, `nhdsKer s` is defined to be the intersection of all
neighborhoods of `s`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

public section

open Set Filter
open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

/--
lemma `nhdsKer_singleton_eq_ker_nhds` / 引理 `nhdsKer_singleton_eq_ker_nhds`

English:
lemma nhdsKer_singleton_eq_ker_nhds
  given: (x : X)
  statement: nhdsKer {x} = (𝓝 x).ker
  proof: by simp [nhdsKer]

@[simp]

中文:
引理 nhdsKer_singleton_eq_ker_nhds
  条件: (x : X)
  结论: nhdsKer {x} = (𝓝 x).ker
  证明: by simp [nhdsKer]

@[simp]

Depends on / 依赖: nhdsKer
-/
lemma nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker := by simp [nhdsKer]

@[simp]
/--
theorem `mem_nhdsKer_singleton` / 定理 `mem_nhdsKer_singleton`

English:
theorem mem_nhdsKer_singleton
  statement: x in nhdsKer {y} ↔ x ⤳ y
  proof: by
  rw [nhdsKer_singleton_eq_ker_nhds]; rw [ker_nhds_eq_specializes]; rw [mem_ofPred]

中文:
定理 mem_nhdsKer_singleton
  结论: x in nhdsKer {y} ↔ x ⤳ y
  证明: by
  rw [nhdsKer_singleton_eq_ker_nhds]; rw [ker_nhds_eq_specializes]; rw [mem_ofPred]

Depends on / 依赖: ker_nhds_eq_specializes, mem_ofPred, nhdsKer_singleton_eq_ker_nhds
-/
theorem mem_nhdsKer_singleton : x in nhdsKer {y} ↔ x ⤳ y := by
  rw [nhdsKer_singleton_eq_ker_nhds]; rw [ker_nhds_eq_specializes]; rw [mem_ofPred]

/--
lemma `nhdsKer_def` / 引理 `nhdsKer_def`

English:
lemma nhdsKer_def
  given: (s : Set X)
  statement: nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s subseteq t}
  proof: (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

中文:
引理 nhdsKer_def
  条件: (s : 集合 X)
  结论: nhdsKer s = ⋂₀ {t : 集合 X | 是开集 t ∧ s subseteq t}
  证明: (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

Depends on / 依赖: hasBasis_nhdsSet, ker.trans, sInter_eq_biInter, sInter_eq_biInter.symm
-/
lemma nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s subseteq t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

/--
lemma `mem_nhdsKer` / 引理 `mem_nhdsKer`

English:
lemma mem_nhdsKer
  statement: x in nhdsKer s ↔ forall U, IsOpen U -> s subseteq U -> x in U
  proof: by simp [nhdsKer_def]

中文:
引理 mem_nhdsKer
  结论: x in nhdsKer s ↔ 对任意 U, 是开集 U -> s subseteq U -> x in U
  证明: by simp [nhdsKer_def]

Depends on / 依赖: nhdsKer_def
-/
lemma mem_nhdsKer : x in nhdsKer s ↔ forall U, IsOpen U -> s subseteq U -> x in U := by simp [nhdsKer_def]

/--
lemma `subset_nhdsKer_iff` / 引理 `subset_nhdsKer_iff`

English:
lemma subset_nhdsKer_iff
  statement: s subseteq nhdsKer t ↔ forall U, IsOpen U -> t subseteq U -> s subseteq U
  proof: by
  simp [nhdsKer_def]

中文:
引理 subset_nhdsKer_iff
  结论: s subseteq nhdsKer t ↔ 对任意 U, 是开集 U -> t subseteq U -> s subseteq U
  证明: by
  simp [nhdsKer_def]

Depends on / 依赖: nhdsKer_def
-/
lemma subset_nhdsKer_iff : s subseteq nhdsKer t ↔ forall U, IsOpen U -> t subseteq U -> s subseteq U := by
  simp [nhdsKer_def]

/--
lemma `subset_nhdsKer` / 引理 `subset_nhdsKer`

English:
lemma subset_nhdsKer
  statement: s subseteq nhdsKer s
  proof: subset_nhdsKer_iff.2 fun _ _ => id

中文:
引理 subset_nhdsKer
  结论: s subseteq nhdsKer s
  证明: subset_nhdsKer_iff.2 fun _ _ => id

Depends on / 依赖: subset_nhdsKer_iff
-/
lemma subset_nhdsKer : s subseteq nhdsKer s := subset_nhdsKer_iff.2 fun _ _ => id

/--
lemma `nhdsKer_minimal` / 引理 `nhdsKer_minimal`

English:
lemma nhdsKer_minimal
  given: (h₁ : s subseteq t) (h₂ : IsOpen t)
  statement: nhdsKer s subseteq t
  proof: by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

中文:
引理 nhdsKer_minimal
  条件: (h₁ : s subseteq t) (h₂ : 是开集 t)
  结论: nhdsKer s subseteq t
  证明: by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

Depends on / 依赖: nhdsKer_def, sInter_subset_of_mem
-/
lemma nhdsKer_minimal (h₁ : s subseteq t) (h₂ : IsOpen t) : nhdsKer s subseteq t := by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

/--
lemma `IsOpen.nhdsKer_eq` / 引理 `IsOpen.nhdsKer_eq`

English:
lemma IsOpen.nhdsKer_eq
  given: (h : IsOpen s)
  statement: nhdsKer s = s
  proof: (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer

中文:
引理 是开集.nhdsKer_eq
  条件: (h : 是开集 s)
  结论: nhdsKer s = s
  证明: (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer

Depends on / 依赖: Subset, Subset.rfl, antisymm, nhdsKer_minimal, subset_nhdsKer
-/
lemma IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s :=
  (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer

/--
lemma `IsOpen.nhdsKer_subset` / 引理 `IsOpen.nhdsKer_subset`

English:
lemma IsOpen.nhdsKer_subset
  given: (ht : IsOpen t)
  statement: nhdsKer s subseteq t ↔ s subseteq t
  proof: ⟨subset_nhdsKer.trans, fun h => nhdsKer_minimal h ht⟩

@[simp]

中文:
引理 是开集.nhdsKer_subset
  条件: (ht : 是开集 t)
  结论: nhdsKer s subseteq t ↔ s subseteq t
  证明: ⟨subset_nhdsKer.trans, fun h => nhdsKer_minimal h ht⟩

@[simp]

Depends on / 依赖: nhdsKer_minimal, subset_nhdsKer, subset_nhdsKer.trans
-/
lemma IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s subseteq t ↔ s subseteq t :=
  ⟨subset_nhdsKer.trans, fun h => nhdsKer_minimal h ht⟩

@[simp]
/--
theorem `nhdsKer_iUnion` / 定理 `nhdsKer_iUnion`

English:
theorem nhdsKer_iUnion
  given: (s : ι -> Set X)
  statement: nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i)
  proof: by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]

中文:
定理 nhdsKer_iUnion
  条件: (s : ι -> 集合 X)
  结论: nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i)
  证明: by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]

Depends on / 依赖: ker_iSup, nhdsKer, nhdsSet_iUnion
-/
theorem nhdsKer_iUnion (s : ι -> Set X) : nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i) := by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]

/--
theorem `nhdsKer_biUnion` / 定理 `nhdsKer_biUnion`

English:
theorem nhdsKer_biUnion
  given: {ι : Type*} (s : Set ι) (t : ι -> Set X)
  proof: by
  simp only [nhdsKer_iUnion]

@[simp]

中文:
定理 nhdsKer_biUnion
  条件: {ι : 类型} (s : 集合 ι) (t : ι -> 集合 X)
  证明: by
  simp only [nhdsKer_iUnion]

@[simp]

Depends on / 依赖: nhdsKer_iUnion
-/
theorem nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι -> Set X) :
    nhdsKer (⋃ i in s, t i) = ⋃ i in s, nhdsKer (t i) := by
  simp only [nhdsKer_iUnion]

@[simp]
/--
theorem `nhdsKer_union` / 定理 `nhdsKer_union`

English:
theorem nhdsKer_union
  given: (s t : Set X)
  statement: nhdsKer (s union t) = nhdsKer s union nhdsKer t
  proof: by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[simp]

中文:
定理 nhdsKer_union
  条件: (s t : 集合 X)
  结论: nhdsKer (s union t) = nhdsKer s union nhdsKer t
  证明: by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[simp]

Depends on / 依赖: ker_sup, nhdsKer, nhdsSet_union
-/
theorem nhdsKer_union (s t : Set X) : nhdsKer (s union t) = nhdsKer s union nhdsKer t := by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[simp]
/--
theorem `nhdsKer_sUnion` / 定理 `nhdsKer_sUnion`

English:
theorem nhdsKer_sUnion
  given: (S : Set (Set X))
  statement: nhdsKer (⋃₀ S) = ⋃ s in S, nhdsKer s
  proof: by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]

中文:
定理 nhdsKer_sUnion
  条件: (S : 集合 (集合 X))
  结论: nhdsKer (⋃₀ S) = ⋃ s in S, nhdsKer s
  证明: by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]

Depends on / 依赖: nhdsKer_iUnion, sUnion_eq_biUnion
-/
theorem nhdsKer_sUnion (S : Set (Set X)) : nhdsKer (⋃₀ S) = ⋃ s in S, nhdsKer s := by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]

/--
theorem `mem_nhdsKer_iff_specializes` / 定理 `mem_nhdsKer_iff_specializes`

English:
theorem mem_nhdsKer_iff_specializes
  statement: x in nhdsKer s ↔ exists y in s, x ⤳ y
  proof: calc
  x in nhdsKer s ↔ x in nhdsKer (⋃ y in s, {y}) := by simp
  _ ↔ exists y in s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]

中文:
定理 mem_nhdsKer_iff_specializes
  结论: x in nhdsKer s ↔ 存在 y in s, x ⤳ y
  证明: calc
  x in nhdsKer s ↔ x in nhdsKer (⋃ y in s, {y}) := by simp
  _ ↔ exists y in s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]
-/
theorem mem_nhdsKer_iff_specializes : x in nhdsKer s ↔ exists y in s, x ⤳ y := calc
  x in nhdsKer s ↔ x in nhdsKer (⋃ y in s, {y}) := by simp
  _ ↔ exists y in s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]

/--
lemma `nhdsKer_mono` / 引理 `nhdsKer_mono`

English:
lemma nhdsKer_mono
  statement: Monotone (nhdsKer : Set X -> Set X)
  proof: fun _s _t h => ker_mono nhdsSet_mono h

中文:
引理 nhdsKer_mono
  结论: 递增 (nhdsKer : 集合 X -> 集合 X)
  证明: fun _s _t h => ker_mono nhdsSet_mono h
-/
@[gcongr, mono] lemma nhdsKer_mono : Monotone (nhdsKer : Set X -> Set X) :=
fun _s _t h => ker_mono nhdsSet_mono h

/--
lemma `nhdsKer_subset_nhdsKer` / 引理 `nhdsKer_subset_nhdsKer`

English:
lemma nhdsKer_subset_nhdsKer
  given: (h : s subseteq t)
  statement: nhdsKer s subseteq nhdsKer t
  proof: nhdsKer_mono h

中文:
引理 nhdsKer_subset_nhdsKer
  条件: (h : s subseteq t)
  结论: nhdsKer s subseteq nhdsKer t
  证明: nhdsKer_mono h
-/
@[gcongr] lemma nhdsKer_subset_nhdsKer (h : s subseteq t) : nhdsKer s subseteq nhdsKer t := nhdsKer_mono h

/--
lemma `nhdsKer_subset_nhdsKer_iff_nhdsSet` / 引理 `nhdsKer_subset_nhdsKer_iff_nhdsSet`

English:
lemma nhdsKer_subset_nhdsKer_iff_nhdsSet
  statement: nhdsKer s subseteq nhdsKer t ↔ 𝓝ˢ s <= 𝓝ˢ t
  proof: by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]

中文:
引理 nhdsKer_subset_nhdsKer_iff_nhdsSet
  结论: nhdsKer s subseteq nhdsKer t ↔ 𝓝ˢ s <= 𝓝ˢ t
  证明: by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]
-/
@[simp] lemma nhdsKer_subset_nhdsKer_iff_nhdsSet : nhdsKer s subseteq nhdsKer t ↔ 𝓝ˢ s <= 𝓝ˢ t := by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]

/--
theorem `nhdsKer_eq_nhdsKer_iff_nhdsSet` / 定理 `nhdsKer_eq_nhdsKer_iff_nhdsSet`

English:
theorem nhdsKer_eq_nhdsKer_iff_nhdsSet
  statement: nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t
  proof: by
  simp [le_antisymm_iff]

中文:
定理 nhdsKer_eq_nhdsKer_iff_nhdsSet
  结论: nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t
  证明: by
  simp [le_antisymm_iff]

Depends on / 依赖: le_antisymm_iff
-/
theorem nhdsKer_eq_nhdsKer_iff_nhdsSet : nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]

/--
lemma `specializes_iff_nhdsKer_subset` / 引理 `specializes_iff_nhdsKer_subset`

English:
lemma specializes_iff_nhdsKer_subset
  statement: x ⤳ y ↔ nhdsKer {x} subseteq nhdsKer {y}
  proof: by
  simp [Specializes]

中文:
引理 specializes_iff_nhdsKer_subset
  结论: x ⤳ y ↔ nhdsKer {x} subseteq nhdsKer {y}
  证明: by
  simp [Specializes]

Depends on / 依赖: Specializes
-/
lemma specializes_iff_nhdsKer_subset : x ⤳ y ↔ nhdsKer {x} subseteq nhdsKer {y} := by
  simp [Specializes]

/--
theorem `nhdsKer_iInter_subset` / 定理 `nhdsKer_iInter_subset`

English:
theorem nhdsKer_iInter_subset
  given: {s : ι -> Set X}
  statement: nhdsKer (⋂ i, s i) subseteq ⋂ i, nhdsKer (s i)
  proof: nhdsKer_mono.map_iInf_le

中文:
定理 nhdsKer_i整数er_subset
  条件: {s : ι -> 集合 X}
  结论: nhdsKer (⋂ i, s i) subseteq ⋂ i, nhdsKer (s i)
  证明: nhdsKer_mono.map_iInf_le

Depends on / 依赖: map_iInf_le, nhdsKer_mono, nhdsKer_mono.map_iInf_le
-/
theorem nhdsKer_iInter_subset {s : ι -> Set X} : nhdsKer (⋂ i, s i) subseteq ⋂ i, nhdsKer (s i) :=
  nhdsKer_mono.map_iInf_le

/--
theorem `nhdsKer_inter_subset` / 定理 `nhdsKer_inter_subset`

English:
theorem nhdsKer_inter_subset
  given: {s t : Set X}
  statement: nhdsKer (s inter t) subseteq nhdsKer s inter nhdsKer t
  proof: nhdsKer_mono.map_inf_le _ _

中文:
定理 nhdsKer_inter_subset
  条件: {s t : 集合 X}
  结论: nhdsKer (s inter t) subseteq nhdsKer s inter nhdsKer t
  证明: nhdsKer_mono.map_inf_le _ _

Depends on / 依赖: map_inf_le, nhdsKer_mono, nhdsKer_mono.map_inf_le
-/
theorem nhdsKer_inter_subset {s t : Set X} : nhdsKer (s inter t) subseteq nhdsKer s inter nhdsKer t :=
  nhdsKer_mono.map_inf_le _ _

/--
theorem `nhdsKer_sInter_subset` / 定理 `nhdsKer_sInter_subset`

English:
theorem nhdsKer_sInter_subset
  given: {s : Set (Set X)}
  statement: nhdsKer (⋂₀ s) subseteq ⋂ x in s, nhdsKer x
  proof: nhdsKer_mono.map_sInf_le

中文:
定理 nhdsKer_s整数er_subset
  条件: {s : 集合 (集合 X)}
  结论: nhdsKer (⋂₀ s) subseteq ⋂ x in s, nhdsKer x
  证明: nhdsKer_mono.map_sInf_le

Depends on / 依赖: map_sInf_le, nhdsKer_mono, nhdsKer_mono.map_sInf_le
-/
theorem nhdsKer_sInter_subset {s : Set (Set X)} : nhdsKer (⋂₀ s) subseteq ⋂ x in s, nhdsKer x :=
  nhdsKer_mono.map_sInf_le

/--
lemma `nhdsKer_empty` / 引理 `nhdsKer_empty`

English:
lemma nhdsKer_empty
  statement: nhdsKer (∅ : Set X) = ∅
  proof: isOpen_empty.nhdsKer_eq

中文:
引理 nhdsKer_empty
  结论: nhdsKer (∅ : 集合 X) = ∅
  证明: isOpen_empty.nhdsKer_eq
-/
@[simp] lemma nhdsKer_empty : nhdsKer (∅ : Set X) = ∅ := isOpen_empty.nhdsKer_eq

/--
lemma `nhdsKer_univ` / 引理 `nhdsKer_univ`

English:
lemma nhdsKer_univ
  statement: nhdsKer (univ : Set X) = univ
  proof: isOpen_univ.nhdsKer_eq

中文:
引理 nhdsKer_univ
  结论: nhdsKer (univ : 集合 X) = univ
  证明: isOpen_univ.nhdsKer_eq
-/
@[simp] lemma nhdsKer_univ : nhdsKer (univ : Set X) = univ := isOpen_univ.nhdsKer_eq

/--
lemma `nhdsKer_eq_empty` / 引理 `nhdsKer_eq_empty`

English:
lemma nhdsKer_eq_empty
  statement: nhdsKer s = ∅ ↔ s = ∅
  proof: ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩

中文:
引理 nhdsKer_eq_empty
  结论: nhdsKer s = ∅ ↔ s = ∅
  证明: ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩
-/
@[simp] lemma nhdsKer_eq_empty : nhdsKer s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩

/--
lemma `nhdsSet_nhdsKer` / 引理 `nhdsSet_nhdsKer`

English:
lemma nhdsSet_nhdsKer
  given: (s : Set X)
  statement: 𝓝ˢ (nhdsKer s) = 𝓝ˢ s
  proof: by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
exact fun U ⟨hUo, hsU⟩ => hUo.mem_nhdsSet.2 hUo.nhdsKer_subset.2 hsU

中文:
引理 nhdsSet_nhdsKer
  条件: (s : 集合 X)
  结论: 𝓝ˢ (nhdsKer s) = 𝓝ˢ s
  证明: by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
exact fun U ⟨hUo, hsU⟩ => hUo.mem_nhdsSet.2 hUo.nhdsKer_subset.2 hsU
-/
@[simp] lemma nhdsSet_nhdsKer (s : Set X) : 𝓝ˢ (nhdsKer s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
exact fun U ⟨hUo, hsU⟩ => hUo.mem_nhdsSet.2 hUo.nhdsKer_subset.2 hsU

/--
lemma `nhdsKer_nhdsKer` / 引理 `nhdsKer_nhdsKer`

English:
lemma nhdsKer_nhdsKer
  given: (s : Set X)
  statement: nhdsKer (nhdsKer s) = nhdsKer s
  proof: by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]

中文:
引理 nhdsKer_nhdsKer
  条件: (s : 集合 X)
  结论: nhdsKer (nhdsKer s) = nhdsKer s
  证明: by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]
-/
@[simp] lemma nhdsKer_nhdsKer (s : Set X) : nhdsKer (nhdsKer s) = nhdsKer s := by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]

/--
lemma `nhdsKer_pair` / 引理 `nhdsKer_pair`

English:
lemma nhdsKer_pair
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, ker_prod]

中文:
引理 nhdsKer_pair
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  证明: by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, ker_prod]

Depends on / 依赖: ker_prod, nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, simp_rw
-/
lemma nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y} := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, ker_prod]

/--
lemma `nhdsKer_prod` / 引理 `nhdsKer_prod`

English:
lemma nhdsKer_prod
  given: {Y : Type*} [TopologicalSpace Y] (s : Set X) (t : Set Y)
  proof: calc
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (s ×ˢ t), nhdsKer_biUnion]
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p.1} ×ˢ nhdsKer {p.2} := by
    congr! with ⟨x, y⟩ _; rw [nhdsKer_pair]
  _ = (⋃ x in s, nhdsKer {x}) ×ˢ (⋃ y in t, nhdsKer {y}) :=
    biUnion_prod s t (fun x => nhdsKer {x}) (fun y => nhdsKer {y})
  _ = nhdsKer s ×ˢ nhdsKer t := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]

中文:
引理 nhdsKer_prod
  条件: {Y : 类型} [拓扑空间 Y] (s : 集合 X) (t : 集合 Y)
  证明: calc
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (s ×ˢ t), nhdsKer_biUnion]
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p.1} ×ˢ nhdsKer {p.2} := by
    congr! with ⟨x, y⟩ _; rw [nhdsKer_pair]
  _ = (⋃ x in s, nhdsKer {x}) ×ˢ (⋃ y in t, nhdsKer {y}) :=
    biUnion_prod s t (fun x => nhdsKer {x}) (fun y => nhdsKer {y})
  _ = nhdsKer s ×ˢ nhdsKer t := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
-/
lemma nhdsKer_prod {Y : Type*} [TopologicalSpace Y] (s : Set X) (t : Set Y) :
    nhdsKer (s ×ˢ t) = nhdsKer s ×ˢ nhdsKer t := calc
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (s ×ˢ t), nhdsKer_biUnion]
  _ = ⋃ (p in s ×ˢ t), nhdsKer {p.1} ×ˢ nhdsKer {p.2} := by
    congr! with ⟨x, y⟩ _; rw [nhdsKer_pair]
  _ = (⋃ x in s, nhdsKer {x}) ×ˢ (⋃ y in t, nhdsKer {y}) :=
    biUnion_prod s t (fun x => nhdsKer {x}) (fun y => nhdsKer {y})
  _ = nhdsKer s ×ˢ nhdsKer t := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]

/--
lemma `nhdsKer_singleton_pi` / 引理 `nhdsKer_singleton_pi`

English:
lemma nhdsKer_singleton_pi
  statement: {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalSpace (X i)]
  proof: by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_pi, ker_pi]

中文:
引理 nhdsKer_singleton_pi
  结论: {ι : 类型} {X : ι -> 类型} [Π (i : ι), 拓扑空间 (X i)]
  证明: by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_pi, ker_pi]

Depends on / 依赖: ker_pi, nhdsKer_singleton_eq_ker_nhds, nhds_pi, simp_rw
-/
lemma nhdsKer_singleton_pi {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalSpace (X i)]
    (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi (fun i => nhdsKer {p i}) := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_pi, ker_pi]

/--
lemma `nhdsKer_pi` / 引理 `nhdsKer_pi`

English:
lemma nhdsKer_pi
  statement: {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalSpace (X i)]
  proof: calc
  _ = ⋃ (p in univ.pi s), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (univ.pi s), nhdsKer_biUnion]
  _ = ⋃ (p in univ.pi s), univ.pi fun i => nhdsKer {p i} := by
    congr! with p _; rw [nhdsKer_singleton_pi]
  _ = univ.pi fun i => ⋃ x in s i, nhdsKer {x} :=
    biUnion_univ_pi s fun i x => nhdsKer {x}
  _ = univ.pi (fun i => nhdsKer (s i)) := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]

中文:
引理 nhdsKer_pi
  结论: {ι : 类型} {X : ι -> 类型} [Π (i : ι), 拓扑空间 (X i)]
  证明: calc
  _ = ⋃ (p in univ.pi s), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (univ.pi s), nhdsKer_biUnion]
  _ = ⋃ (p in univ.pi s), univ.pi fun i => nhdsKer {p i} := by
    congr! with p _; rw [nhdsKer_singleton_pi]
  _ = univ.pi fun i => ⋃ x in s i, nhdsKer {x} :=
    biUnion_univ_pi s fun i x => nhdsKer {x}
  _ = univ.pi (fun i => nhdsKer (s i)) := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
-/
lemma nhdsKer_pi {ι : Type*} {X : ι -> Type*} [Π (i : ι), TopologicalSpace (X i)]
    (s : Π (i : ι), Set (X i)) : nhdsKer (univ.pi s) = univ.pi (fun i => nhdsKer (s i)) := calc
  _ = ⋃ (p in univ.pi s), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (univ.pi s), nhdsKer_biUnion]
  _ = ⋃ (p in univ.pi s), univ.pi fun i => nhdsKer {p i} := by
    congr! with p _; rw [nhdsKer_singleton_pi]
  _ = univ.pi fun i => ⋃ x in s i, nhdsKer {x} :=
    biUnion_univ_pi s fun i x => nhdsKer {x}
  _ = univ.pi (fun i => nhdsKer (s i)) := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
