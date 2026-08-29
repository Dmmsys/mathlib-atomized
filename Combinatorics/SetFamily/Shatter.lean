/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `Finset.Shatters`: The shattering property.
* `Finset.shatterer`: The set family of sets shattered by a set family.
* `Finset.vcDim`: The Vapnik-Chervonenkis dimension.

## TODO

* Order-shattering
* Strong shattering
-/

@[expose] public section

open scoped FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α}

/--
Definition of `Shatters` / `Shatters` 的定义

English:
definition Shatters
  signature: (𝒜 : Finset (Finset α)) (s : Finset α)
  body: forall ⦃t⦄, t subseteq s -> exists u in 𝒜, s inter u = t

中文:
定义 Shatters
  签名: (𝒜 : Finset (Finset α)) (s : Finset α)
  定义体: forall ⦃t⦄, t subseteq s -> exists u in 𝒜, s inter u = t

Depends on / 依赖: subseteq
-/
def Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop := forall ⦃t⦄, t subseteq s -> exists u in 𝒜, s inter u = t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred 𝒜.Shatters
  body: fun _s => decidableForallOfDecidableSubsets

中文:
实例 :
  签名: DecidablePred 𝒜.Shatters
  定义体: fun _s => decidableForallOfDecidableSubsets

Depends on / 依赖: decidableForallOfDecidableSubsets
-/
instance : DecidablePred 𝒜.Shatters := fun _s => decidableForallOfDecidableSubsets

/--
lemma `Shatters.exists_inter_eq_singleton` / 引理 `Shatters.exists_inter_eq_singleton`

English:
lemma Shatters.exists_inter_eq_singleton
  given: (hs : Shatters 𝒜 s) (ha : a in s)
  statement: exists t in 𝒜, s inter t = {a}
  proof: hs singleton_subset_iff.2 ha

中文:
引理 Shatters.exists_inter_eq_singleton
  条件: (hs : Shatters 𝒜 s) (ha : a in s)
  结论: 存在 t in 𝒜, s inter t = {a}
  证明: hs singleton_subset_iff.2 ha

Depends on / 依赖: singleton_subset_iff
-/
lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 s) (ha : a in s) : exists t in 𝒜, s inter t = {a} :=
hs singleton_subset_iff.2 ha

/--
lemma `Shatters.mono_left` / 引理 `Shatters.mono_left`

English:
lemma Shatters.mono_left
  given: (h : 𝒜 subseteq ℬ) (h𝒜 : 𝒜.Shatters s)
  statement: ℬ.Shatters s
  proof: fun _t ht => let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩

中文:
引理 Shatters.mono_left
  条件: (h : 𝒜 subseteq ℬ) (h𝒜 : 𝒜.Shatters s)
  结论: ℬ.Shatters s
  证明: fun _t ht => let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩
-/
lemma Shatters.mono_left (h : 𝒜 subseteq ℬ) (h𝒜 : 𝒜.Shatters s) : ℬ.Shatters s :=
  fun _t ht => let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩

/--
lemma `Shatters.mono_right` / 引理 `Shatters.mono_right`

English:
lemma Shatters.mono_right
  given: (h : t subseteq s) (hs : 𝒜.Shatters s)
  statement: 𝒜.Shatters t
  proof: fun u hu => by
obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu inf_le_of_left_le h⟩

中文:
引理 Shatters.mono_right
  条件: (h : t subseteq s) (hs : 𝒜.Shatters s)
  结论: 𝒜.Shatters t
  证明: fun u hu => by
obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu inf_le_of_left_le h⟩

Depends on / 依赖: hu.trans, inf_congr_right, inf_le_of_left_le
-/
lemma Shatters.mono_right (h : t subseteq s) (hs : 𝒜.Shatters s) : 𝒜.Shatters t := fun u hu => by
obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu inf_le_of_left_le h⟩

/--
lemma `Shatters.exists_superset` / 引理 `Shatters.exists_superset`

English:
lemma Shatters.exists_superset
  given: (h : 𝒜.Shatters s)
  statement: exists t in 𝒜, s subseteq t
  proof: let ⟨t, ht, hst⟩ := h Subset.rfl; ⟨t, ht, inter_eq_left.1 hst⟩

中文:
引理 Shatters.exists_superset
  条件: (h : 𝒜.Shatters s)
  结论: 存在 t in 𝒜, s subseteq t
  证明: let ⟨t, ht, hst⟩ := h Subset.rfl; ⟨t, ht, inter_eq_left.1 hst⟩

Depends on / 依赖: Subset, Subset.rfl, inter_eq_left
-/
lemma Shatters.exists_superset (h : 𝒜.Shatters s) : exists t in 𝒜, s subseteq t :=
  let ⟨t, ht, hst⟩ := h Subset.rfl; ⟨t, ht, inter_eq_left.1 hst⟩

/--
lemma `shatters_of_forall_subset` / 引理 `shatters_of_forall_subset`

English:
lemma shatters_of_forall_subset
  given: (h : forall t, t subseteq s -> t in 𝒜)
  statement: 𝒜.Shatters s
  proof: fun t ht => ⟨t, h _ ht, inter_eq_right.2 ht⟩

中文:
引理 shatters_of_forall_subset
  条件: (h : 对任意 t, t subseteq s -> t in 𝒜)
  结论: 𝒜.Shatters s
  证明: fun t ht => ⟨t, h _ ht, inter_eq_right.2 ht⟩

Depends on / 依赖: inter_eq_right
-/
lemma shatters_of_forall_subset (h : forall t, t subseteq s -> t in 𝒜) : 𝒜.Shatters s :=
  fun t ht => ⟨t, h _ ht, inter_eq_right.2 ht⟩

/--
lemma `Shatters.nonempty` / 引理 `Shatters.nonempty`

English:
lemma Shatters.nonempty
  given: (h : 𝒜.Shatters s)
  statement: 𝒜.Nonempty
  proof: let ⟨t, ht, _⟩ := h Subset.rfl; ⟨t, ht⟩

中文:
引理 Shatters.nonempty
  条件: (h : 𝒜.Shatters s)
  结论: 𝒜.Nonempty
  证明: let ⟨t, ht, _⟩ := h Subset.rfl; ⟨t, ht⟩
-/
protected lemma Shatters.nonempty (h : 𝒜.Shatters s) : 𝒜.Nonempty :=
  let ⟨t, ht, _⟩ := h Subset.rfl; ⟨t, ht⟩

/--
lemma `shatters_empty` / 引理 `shatters_empty`

English:
lemma shatters_empty
  statement: 𝒜.Shatters ∅ ↔ 𝒜.Nonempty
  proof: ⟨Shatters.nonempty, fun ⟨s, hs⟩ t ht => ⟨s, hs, by rwa [empty_inter, eq_comm, ← subset_empty]⟩⟩

中文:
引理 shatters_empty
  结论: 𝒜.Shatters ∅ ↔ 𝒜.Nonempty
  证明: ⟨Shatters.nonempty, fun ⟨s, hs⟩ t ht => ⟨s, hs, by rwa [empty_inter, eq_comm, ← subset_empty]⟩⟩
-/
@[simp] lemma shatters_empty : 𝒜.Shatters ∅ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨s, hs⟩ t ht => ⟨s, hs, by rwa [empty_inter, eq_comm, ← subset_empty]⟩⟩

/--
lemma `Shatters.subset_iff` / 引理 `Shatters.subset_iff`

English:
lemma Shatters.subset_iff
  given: (h : 𝒜.Shatters s)
  statement: t subseteq s ↔ exists u in 𝒜, s inter u = t
  proof: ⟨fun ht => h ht, by rintro ⟨u, _, rfl⟩; exact inter_subset_left⟩

中文:
引理 Shatters.subset_iff
  条件: (h : 𝒜.Shatters s)
  结论: t subseteq s ↔ 存在 u in 𝒜, s inter u = t
  证明: ⟨fun ht => h ht, by rintro ⟨u, _, rfl⟩; exact inter_subset_left⟩
-/
protected lemma Shatters.subset_iff (h : 𝒜.Shatters s) : t subseteq s ↔ exists u in 𝒜, s inter u = t :=
  ⟨fun ht => h ht, by rintro ⟨u, _, rfl⟩; exact inter_subset_left⟩

/--
lemma `shatters_iff` / 引理 `shatters_iff`

English:
lemma shatters_iff
  statement: 𝒜.Shatters s ↔ 𝒜.image (fun t => s inter t) = s.powerset
  proof: ⟨fun h => by ext t; rw [mem_image, mem_powerset, h.subset_iff],
    fun h t ht => by rwa [← mem_powerset, ← h, mem_image] at ht⟩

中文:
引理 shatters_iff
  结论: 𝒜.Shatters s ↔ 𝒜.image (fun t => s inter t) = s.powerset
  证明: ⟨fun h => by ext t; rw [mem_image, mem_powerset, h.subset_iff],
    fun h t ht => by rwa [← mem_powerset, ← h, mem_image] at ht⟩

Depends on / 依赖: h.subset_iff, mem_image, mem_powerset, subset_iff
-/
lemma shatters_iff : 𝒜.Shatters s ↔ 𝒜.image (fun t => s inter t) = s.powerset :=
  ⟨fun h => by ext t; rw [mem_image, mem_powerset, h.subset_iff],
    fun h t ht => by rwa [← mem_powerset, ← h, mem_image] at ht⟩

/--
lemma `univ_shatters` / 引理 `univ_shatters`

English:
lemma univ_shatters
  given: [Fintype α]
  statement: univ.Shatters s
  proof: shatters_of_forall_subset fun _ _ => mem_univ _

中文:
引理 univ_shatters
  条件: [Fintype α]
  结论: univ.Shatters s
  证明: shatters_of_forall_subset fun _ _ => mem_univ _

Depends on / 依赖: mem_univ, shatters_of_forall_subset
-/
lemma univ_shatters [Fintype α] : univ.Shatters s :=
  shatters_of_forall_subset fun _ _ => mem_univ _

/--
lemma `shatters_univ` / 引理 `shatters_univ`

English:
lemma shatters_univ
  given: [Fintype α]
  statement: 𝒜.Shatters univ ↔ 𝒜 = univ
  proof: by
  rw [shatters_iff]; rw [powerset_univ]; simp_rw [univ_inter, image_id']

中文:
引理 shatters_univ
  条件: [Fintype α]
  结论: 𝒜.Shatters univ ↔ 𝒜 = univ
  证明: by
  rw [shatters_iff]; rw [powerset_univ]; simp_rw [univ_inter, image_id']
-/
@[simp] lemma shatters_univ [Fintype α] : 𝒜.Shatters univ ↔ 𝒜 = univ := by
  rw [shatters_iff]; rw [powerset_univ]; simp_rw [univ_inter, image_id']

/--
Definition of `shatterer` / `shatterer` 的定义

English:
definition shatterer
  signature: (𝒜 : Finset (Finset α))
  body: {s in 𝒜.biUnion powerset | 𝒜.Shatters s}

中文:
定义 shatterer
  签名: (𝒜 : Finset (Finset α))
  定义体: {s in 𝒜.biUnion powerset | 𝒜.Shatters s}

Depends on / 依赖: Shatters, biUnion, powerset
-/
def shatterer (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s in 𝒜.biUnion powerset | 𝒜.Shatters s}

/--
lemma `mem_shatterer` / 引理 `mem_shatterer`

English:
lemma mem_shatterer
  statement: s in 𝒜.shatterer ↔ 𝒜.Shatters s
  proof: by
refine mem_filter.trans and_iff_right_of_imp fun h => ?_
  simp_rw [mem_biUnion, mem_powerset]
  exact h.exists_superset

中文:
引理 mem_shatterer
  结论: s in 𝒜.shatterer ↔ 𝒜.Shatters s
  证明: by
refine mem_filter.trans and_iff_right_of_imp fun h => ?_
  simp_rw [mem_biUnion, mem_powerset]
  exact h.exists_superset
-/
@[simp] lemma mem_shatterer : s in 𝒜.shatterer ↔ 𝒜.Shatters s := by
refine mem_filter.trans and_iff_right_of_imp fun h => ?_
  simp_rw [mem_biUnion, mem_powerset]
  exact h.exists_superset

/--
lemma `shatterer_mono` / 引理 `shatterer_mono`

English:
lemma shatterer_mono
  given: (h : 𝒜 subseteq ℬ)
  statement: 𝒜.shatterer subseteq ℬ.shatterer
  proof: fun _ => by simpa using Shatters.mono_left h

中文:
引理 shatterer_mono
  条件: (h : 𝒜 subseteq ℬ)
  结论: 𝒜.shatterer subseteq ℬ.shatterer
  证明: fun _ => by simpa using Shatters.mono_left h
-/
@[gcongr] lemma shatterer_mono (h : 𝒜 subseteq ℬ) : 𝒜.shatterer subseteq ℬ.shatterer :=
  fun _ => by simpa using Shatters.mono_left h

/--
lemma `subset_shatterer` / 引理 `subset_shatterer`

English:
lemma subset_shatterer
  given: (h : IsLowerSet (𝒜 : Set (Finset α)))
  statement: 𝒜 subseteq 𝒜.shatterer
  proof: fun _s hs => mem_shatterer.2 fun t ht => ⟨t, h ht hs, inter_eq_right.2 ht⟩

中文:
引理 subset_shatterer
  条件: (h : IsLowerSet (𝒜 : Set (Finset α)))
  结论: 𝒜 subseteq 𝒜.shatterer
  证明: fun _s hs => mem_shatterer.2 fun t ht => ⟨t, h ht hs, inter_eq_right.2 ht⟩

Depends on / 依赖: inter_eq_right, mem_shatterer
-/
lemma subset_shatterer (h : IsLowerSet (𝒜 : Set (Finset α))) : 𝒜 subseteq 𝒜.shatterer :=
  fun _s hs => mem_shatterer.2 fun t ht => ⟨t, h ht hs, inter_eq_right.2 ht⟩

/--
lemma `isLowerSet_shatterer` / 引理 `isLowerSet_shatterer`

English:
lemma isLowerSet_shatterer
  given: (𝒜 : Finset (Finset α))
  proof: fun s t => by simpa using Shatters.mono_right

中文:
引理 isLowerSet_shatterer
  条件: (𝒜 : Finset (Finset α))
  证明: fun s t => by simpa using Shatters.mono_right
-/
@[simp] lemma isLowerSet_shatterer (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜.shatterer : Set (Finset α)) := fun s t => by simpa using Shatters.mono_right

/--
lemma `shatterer_eq` / 引理 `shatterer_eq`

English:
lemma shatterer_eq
  statement: 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α))
  proof: by
refine ⟨fun h => ?_, fun h => Subset.antisymm (fun s hs => ?_) subset_shatterer h⟩
  · rw [← h]
    exact isLowerSet_shatterer _
  · obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset
    exact h hst ht

中文:
引理 shatterer_eq
  结论: 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α))
  证明: by
refine ⟨fun h => ?_, fun h => Subset.antisymm (fun s hs => ?_) subset_shatterer h⟩
  · rw [← h]
    exact isLowerSet_shatterer _
  · obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset
    exact h hst ht
-/
@[simp] lemma shatterer_eq : 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α)) := by
refine ⟨fun h => ?_, fun h => Subset.antisymm (fun s hs => ?_) subset_shatterer h⟩
  · rw [← h]
    exact isLowerSet_shatterer _
  · obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset
    exact h hst ht

/--
lemma `shatterer_idem` / 引理 `shatterer_idem`

English:
lemma shatterer_idem
  statement: 𝒜.shatterer.shatterer = 𝒜.shatterer
  proof: by simp

中文:
引理 shatterer_idem
  结论: 𝒜.shatterer.shatterer = 𝒜.shatterer
  证明: by simp
-/
@[simp] lemma shatterer_idem : 𝒜.shatterer.shatterer = 𝒜.shatterer := by simp

/--
lemma `shatters_shatterer` / 引理 `shatters_shatterer`

English:
lemma shatters_shatterer
  statement: 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s
  proof: by
  simp_rw [← mem_shatterer, shatterer_idem]

protected alias ⟨_, Shatters.shatterer⟩ := shatters_shatterer

中文:
引理 shatters_shatterer
  结论: 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s
  证明: by
  simp_rw [← mem_shatterer, shatterer_idem]

protected alias ⟨_, Shatters.shatterer⟩ := shatters_shatterer
-/
@[simp] lemma shatters_shatterer : 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s := by
  simp_rw [← mem_shatterer, shatterer_idem]

protected alias ⟨_, Shatters.shatterer⟩ := shatters_shatterer

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: (h : forall t in 𝒜, a ∉ t) (ht : 𝒜.Shatters t)
  statement: a ∉ t
  proof: by
obtain ⟨u, hu, htu⟩ := ht.exists_superset; exact notMem_mono htu h u hu

中文:
引理 aux
  条件: (h : 对任意 t in 𝒜, a ∉ t) (ht : 𝒜.Shatters t)
  结论: a ∉ t
  证明: by
obtain ⟨u, hu, htu⟩ := ht.exists_superset; exact notMem_mono htu h u hu
-/
private lemma aux (h : forall t in 𝒜, a ∉ t) (ht : 𝒜.Shatters t) : a ∉ t := by
obtain ⟨u, hu, htu⟩ := ht.exists_superset; exact notMem_mono htu h u hu

/--
lemma `card_le_card_shatterer` / 引理 `card_le_card_shatterer`

English:
lemma card_le_card_shatterer
  given: (𝒜 : Finset (Finset α))
  statement: #𝒜 <= #𝒜.shatterer
  proof: by
  refine memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · rfl
  intro a 𝒜 ih₀ ih₁
  set ℬ : Finset (Finset α) :=
    ((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatterer).image (insert a)
  have hℬ : #ℬ = #((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatt

中文:
引理 card_le_card_shatterer
  条件: (𝒜 : Finset (Finset α))
  结论: #𝒜 <= #𝒜.shatterer
  证明: by
  refine memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · rfl
  intro a 𝒜 ih₀ ih₁
  set ℬ : Finset (Finset α) :=
    ((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatterer).image (insert a)
  have hℬ : #ℬ = #((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatt

Depends on / 依赖: Finset, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.subset_def, and_imp, card_image_of_injOn, coe_inter, injOn.mono, insert, insert_erase_invOn, mem_coe, mem_inter_iff, mem_ofPred_eq, mem_shatterer, memberFamily_induction_on, memberSubfamily, nonMemberSubfamily, shatterer, subset_def
-/
lemma card_le_card_shatterer (𝒜 : Finset (Finset α)) : #𝒜 <= #𝒜.shatterer := by
  refine memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · rfl
  intro a 𝒜 ih₀ ih₁
  set ℬ : Finset (Finset α) :=
    ((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatterer).image (insert a)
  have hℬ : #ℬ = #((memberSubfamily a 𝒜).shatterer inter (nonMemberSubfamily a 𝒜).shatterer) := by
refine card_image_of_injOn insert_erase_invOn.2.injOn.mono ?_
    simp only [coe_inter, Set.subset_def, Set.mem_inter_iff, mem_coe, Set.mem_ofPred_eq, and_imp,
      mem_shatterer]
    exact fun s _ => aux (fun t ht => (mem_filter.1 ht).2)
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily a]
  refine (Nat.add_le_add ih₁ ih₀).trans ?_
  rw [← card_union_add_card_inter]; rw [← hℬ]; rw [← card_union_of_disjoint]
  swap
  · simp only [ℬ, disjoint_left, mem_union, mem_shatterer, mem_image, not_exists, not_and]
    rintro _ (hs | hs) s - rfl
· exact aux (fun t ht => (mem_memberSubfamily.1 ht).2) hs mem_insert_self _ _
· exact aux (fun t ht => (mem_nonMemberSubfamily.1 ht).2) hs mem_insert_self _ _
refine card_mono union_subset (union_subset ?_ <| shatterer_mono <| filter_subset _ _) ?_
  · simp only [subset_iff, mem_shatterer]
    rintro s hs t ht
    obtain ⟨u, hu, rfl⟩ := hs ht
    rw [mem_memberSubfamily] at hu
    refine ⟨insert a u, hu.1, inter_insert_of_notMem fun ha => ?_⟩
    obtain ⟨v, hv, hsv⟩ := hs.exists_inter_eq_singleton ha
    rw [mem_memberSubfamily] at hv
    rw [← singleton_subset_iff (a := a)]; rw [← hsv] at hv
    exact hv.2 inter_subset_right
  · refine forall_mem_image.2 fun s hs => mem_shatterer.2 fun t ht => ?_
    simp only [mem_inter, mem_shatterer] at hs
    rw [subset_insert_iff] at ht
    by_cases ha : a in t
    · obtain ⟨u, hu, hsu⟩ := hs.1 ht
      rw [mem_memberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rw [← insert_inter_distrib]; rw [hsu]; rw [insert_erase ha]
    · obtain ⟨u, hu, hsu⟩ := hs.2 ht
      rw [mem_nonMemberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rwa [insert_inter_of_notMem hu.2, hsu, erase_eq_self]

/--
lemma `Shatters.of_compression` / 引理 `Shatters.of_compression`

English:
lemma Shatters.of_compression
  given: (hs : (𝓓 a 𝒜).Shatters s)
  statement: 𝒜.Shatters s
  proof: by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := hs ht
  rw [Down.mem_compression] at hu
  obtain hu | hu := hu
  · exact ⟨u, hu.1, rfl⟩
  by_cases ha : a in s
· obtain ⟨v, hv, hsv⟩ := hs insert_subset ha ht
    rw [Down.mem_compression] at hv
    obtain hv | hv := hv
    · refine ⟨erase v a, hv.2, ?_⟩
    

中文:
引理 Shatters.of_compression
  条件: (hs : (𝓓 a 𝒜).Shatters s)
  结论: 𝒜.Shatters s
  证明: by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := hs ht
  rw [Down.mem_compression] at hu
  obtain hu | hu := hu
  · exact ⟨u, hu.1, rfl⟩
  by_cases ha : a in s
· obtain ⟨v, hv, hsv⟩ := hs insert_subset ha ht
    rw [Down.mem_compression] at hv
    obtain hv | hv := hv
    · refine ⟨erase v a, hv.2, ?_⟩
    

Depends on / 依赖: Down.mem_compression, erase_insert, insert_eq_self, insert_subset, inter_erase, inter_subset_right, mem_compression, mem_insert_self, mem_inter
-/
lemma Shatters.of_compression (hs : (𝓓 a 𝒜).Shatters s) : 𝒜.Shatters s := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := hs ht
  rw [Down.mem_compression] at hu
  obtain hu | hu := hu
  · exact ⟨u, hu.1, rfl⟩
  by_cases ha : a in s
· obtain ⟨v, hv, hsv⟩ := hs insert_subset ha ht
    rw [Down.mem_compression] at hv
    obtain hv | hv := hv
    · refine ⟨erase v a, hv.2, ?_⟩
      rw [inter_erase]; rw [hsv]; rw [erase_insert]
      rintro ha
      rw [insert_eq_self.2 (mem_inter.1 ha).2] at hu
      exact hu.1 hu.2
    rw [insert_eq_self.2 <| inter_subset_right (s₁ := s) ?_] at hv
    cases hv.1 hv.2
    rw [hsv]
    exact mem_insert_self _ _
  · refine ⟨insert a u, hu.2, ?_⟩
    rw [inter_insert_of_notMem ha]

/--
lemma `shatterer_compress_subset_shatterer` / 引理 `shatterer_compress_subset_shatterer`

English:
lemma shatterer_compress_subset_shatterer
  given: (a : α) (𝒜 : Finset (Finset α))
  proof: by
  simp only [subset_iff, mem_shatterer]; exact fun s hs => hs.of_compression

中文:
引理 shatterer_compress_subset_shatterer
  条件: (a : α) (𝒜 : Finset (Finset α))
  证明: by
  simp only [subset_iff, mem_shatterer]; exact fun s hs => hs.of_compression

Depends on / 依赖: hs.of_compression, mem_shatterer, of_compression, subset_iff
-/
lemma shatterer_compress_subset_shatterer (a : α) (𝒜 : Finset (Finset α)) :
    (𝓓 a 𝒜).shatterer subseteq 𝒜.shatterer := by
  simp only [subset_iff, mem_shatterer]; exact fun s hs => hs.of_compression

/-! ### Vapnik-Chervonenkis dimension -/

/--
Definition of `vcDim` / `vcDim` 的定义

English:
definition vcDim
  signature: (𝒜 : Finset (Finset α))
  body: 𝒜.shatterer.sup card

中文:
定义 vcDim
  签名: (𝒜 : Finset (Finset α))
  定义体: 𝒜.shatterer.sup card

Depends on / 依赖: shatterer, shatterer.sup
-/
def vcDim (𝒜 : Finset (Finset α)) : Nat := 𝒜.shatterer.sup card

/--
lemma `vcDim_mono` / 引理 `vcDim_mono`

English:
lemma vcDim_mono
  given: (h𝒜ℬ : 𝒜 subseteq ℬ)
  statement: 𝒜.vcDim <= ℬ.vcDim
  proof: by unfold vcDim; gcongr

中文:
引理 vcDim_mono
  条件: (h𝒜ℬ : 𝒜 subseteq ℬ)
  结论: 𝒜.vcDim <= ℬ.vcDim
  证明: by unfold vcDim; gcongr
-/
@[gcongr] lemma vcDim_mono (h𝒜ℬ : 𝒜 subseteq ℬ) : 𝒜.vcDim <= ℬ.vcDim := by unfold vcDim; gcongr

/--
lemma `Shatters.card_le_vcDim` / 引理 `Shatters.card_le_vcDim`

English:
lemma Shatters.card_le_vcDim
  given: (hs : 𝒜.Shatters s)
  statement: #s <= 𝒜.vcDim
  proof: le_sup mem_shatterer.2 hs

中文:
引理 Shatters.card_le_vcDim
  条件: (hs : 𝒜.Shatters s)
  结论: #s <= 𝒜.vcDim
  证明: le_sup mem_shatterer.2 hs

Depends on / 依赖: le_sup, mem_shatterer
-/
lemma Shatters.card_le_vcDim (hs : 𝒜.Shatters s) : #s <= 𝒜.vcDim := le_sup mem_shatterer.2 hs

/--
lemma `vcDim_compress_le` / 引理 `vcDim_compress_le`

English:
lemma vcDim_compress_le
  given: (a : α) (𝒜 : Finset (Finset α))
  statement: (𝓓 a 𝒜).vcDim <= 𝒜.vcDim
  proof: sup_mono shatterer_compress_subset_shatterer _ _

中文:
引理 vcDim_compress_le
  条件: (a : α) (𝒜 : Finset (Finset α))
  结论: (𝓓 a 𝒜).vcDim <= 𝒜.vcDim
  证明: sup_mono shatterer_compress_subset_shatterer _ _

Depends on / 依赖: shatterer_compress_subset_shatterer, sup_mono
-/
lemma vcDim_compress_le (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).vcDim <= 𝒜.vcDim :=
sup_mono shatterer_compress_subset_shatterer _ _

/--
lemma `card_shatterer_le_sum_vcDim` / 引理 `card_shatterer_le_sum_vcDim`

English:
lemma card_shatterer_le_sum_vcDim
  given: [Fintype α]
  proof: by
  simp_rw [← card_univ, ← card_powersetCard]
  refine (card_le_card fun s hs => mem_biUnion.2 ⟨#s, ?_⟩).trans card_biUnion_le
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vcDim, mem_powersetCard_univ.2 rfl⟩

中文:
引理 card_shatterer_le_sum_vcDim
  条件: [Fintype α]
  证明: by
  simp_rw [← card_univ, ← card_powersetCard]
  refine (card_le_card fun s hs => mem_biUnion.2 ⟨#s, ?_⟩).trans card_biUnion_le
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vcDim, mem_powersetCard_univ.2 rfl⟩

Depends on / 依赖: card_biUnion_le, card_le_card, card_le_vcDim, card_powersetCard, card_univ, mem_Iic, mem_biUnion, mem_powersetCard_univ, mem_shatterer, simp_rw
-/
lemma card_shatterer_le_sum_vcDim [Fintype α] :
    #𝒜.shatterer <= ∑ k in Iic 𝒜.vcDim, (Fintype.card α).choose k := by
  simp_rw [← card_univ, ← card_powersetCard]
  refine (card_le_card fun s hs => mem_biUnion.2 ⟨#s, ?_⟩).trans card_biUnion_le
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vcDim, mem_powersetCard_univ.2 rfl⟩

end Finset
