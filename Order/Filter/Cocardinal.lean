/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  a regular cardinal `c` that satisfies `Cardinal.aleph0 < c`.
  Such filters are `CardinalInterFilter` with cardinality `c`.

-/

@[expose] public section

open Set Filter Cardinal

universe u
variable {α : Type u} {c : Cardinal.{u}} {hreg : c.IsRegular}

namespace Filter

variable (α) in
/--
Definition of `cocardinal` / `cocardinal` 的定义

English:
definition cocardinal
  signature: (hreg : c.IsRegular)
  body: by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (natCast_lt_aleph0.trans_le hreg.aleph0_le)
· refine fun s hS hSc => lt_of_le_of_lt (mk_sUnion_le _) mul_lt_of_lt hreg.aleph0_le hS ?_
    apply iSup_lt_of_lt_cof_ord _ fun i => hSc i.1 i.2
    rwa [hreg.cof_ord]
  · exact fun _ hSc _ ht => lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc

@[simp]

中文:
定义 cocardinal
  签名: (hreg : c.是正则)
  定义体: by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (natCast_lt_aleph0.trans_le hreg.aleph0_le)
· refine fun s hS hSc => lt_of_le_of_lt (mk_sUnion_le _) mul_lt_of_lt hreg.aleph0_le hS ?_
    apply iSup_lt_of_lt_cof_ord _ fun i => hSc i.1 i.2
    rwa [hreg.cof_ord]
  · exact fun _ hSc _ ht => lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc

@[simp]

Depends on / 依赖: Cardinal, Cardinal.mk, aleph0_le, cof_ord, hreg.aleph0_le, hreg.cof_ord, iSup_lt_of_lt_cof_ord, lt_of_le_of_lt, mk_le_mk_of_subset, mk_sUnion_le, mul_lt_of_lt, natCast_lt_aleph0, natCast_lt_aleph0.trans_le, ofCardinalUnion, trans_le
-/
def cocardinal (hreg : c.IsRegular) : Filter α := by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (natCast_lt_aleph0.trans_le hreg.aleph0_le)
· refine fun s hS hSc => lt_of_le_of_lt (mk_sUnion_le _) mul_lt_of_lt hreg.aleph0_le hS ?_
    apply iSup_lt_of_lt_cof_ord _ fun i => hSc i.1 i.2
    rwa [hreg.cof_ord]
  · exact fun _ hSc _ ht => lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc

@[simp]
/--
theorem `mem_cocardinal` / 定理 `mem_cocardinal`

English:
theorem mem_cocardinal
  given: {s : Set α}
  proof: Iff.rfl

中文:
定理 mem_cocardinal
  条件: {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cocardinal {s : Set α} :
    s in cocardinal α hreg ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl

/--
lemma `cocardinal_aleph0_eq_cofinite` / 引理 `cocardinal_aleph0_eq_cofinite`

English:
lemma cocardinal_aleph0_eq_cofinite
  proof: by
  aesop

中文:
引理 cocardinal_aleph0_eq_cofinite
  证明: by
  aesop
-/
@[simp] lemma cocardinal_aleph0_eq_cofinite :
    cocardinal (α := α) isRegular_aleph0 = cofinite := by
  aesop

/--
Instance `instCardinalInterFilter_cocardinal` / 实例 `instCardinalInterFilter_cocardinal`

English:
instance instCardinalInterFilter_cocardinal
  signature: : CardinalInterFilter (cocardinal (α := α) hreg) c where
  body: by
    grw [mem_cocardinal, Set.compl_sInter, mk_sUnion_le]
    apply mul_lt_of_lt hreg.aleph0_le (mk_image_le.trans_lt hS) (iSup_lt_of_lt_cof_ord ..)
    · rw [hreg.cof_ord]
      exact mk_image_le.trans_lt hS
    · aesop

@[simp]

中文:
实例 instCardinal整数erFilter_cocardinal
  签名: : Cardinal整数erFilter (cocardinal (α := α) hreg) c where
  定义体: by
    grw [mem_cocardinal, Set.compl_sInter, mk_sUnion_le]
    apply mul_lt_of_lt hreg.aleph0_le (mk_image_le.trans_lt hS) (iSup_lt_of_lt_cof_ord ..)
    · rw [hreg.cof_ord]
      exact mk_image_le.trans_lt hS
    · aesop

@[simp]
-/
instance instCardinalInterFilter_cocardinal : CardinalInterFilter (cocardinal (α := α) hreg) c where
  cardinal_sInter_mem S hS hSs := by
    grw [mem_cocardinal, Set.compl_sInter, mk_sUnion_le]
    apply mul_lt_of_lt hreg.aleph0_le (mk_image_le.trans_lt hS) (iSup_lt_of_lt_cof_ord ..)
    · rw [hreg.cof_ord]
      exact mk_image_le.trans_lt hS
    · aesop

@[simp]
/--
theorem `eventually_cocardinal` / 定理 `eventually_cocardinal`

English:
theorem eventually_cocardinal
  given: {p : α -> Prop}
  proof: Iff.rfl

中文:
定理 eventually_cocardinal
  条件: {p : α -> 命题}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventually_cocardinal {p : α -> Prop} :
    (forallᶠ x in cocardinal α hreg, p x) ↔ #{ x | ¬p x } < c := Iff.rfl

/--
theorem `hasBasis_cocardinal` / 定理 `hasBasis_cocardinal`

English:
theorem hasBasis_cocardinal
  statement: HasBasis (cocardinal α hreg) (fun s : Set α => #s < c) compl
  proof: ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩

中文:
定理 hasBasis_cocardinal
  结论: 有基 (cocardinal α hreg) (fun s : 集合 α => #s < c) compl
  证明: ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩

Depends on / 依赖: Cardinal, Cardinal.mk_le_mk_of_subset, compl_compl, compl_subset_comm, lt_of_le_of_lt, mem_cocardinal, mk_le_mk_of_subset, subset
-/
theorem hasBasis_cocardinal : HasBasis (cocardinal α hreg) (fun s : Set α => #s < c) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩

/--
theorem `frequently_cocardinal` / 定理 `frequently_cocardinal`

English:
theorem frequently_cocardinal
  given: {p : α -> Prop}
  proof: by
  simp only [Filter.Frequently, eventually_cocardinal, not_not, coe_ofPred, not_lt]

中文:
定理 frequently_cocardinal
  条件: {p : α -> 命题}
  证明: by
  simp only [Filter.Frequently, eventually_cocardinal, not_not, coe_ofPred, not_lt]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, coe_ofPred, eventually_cocardinal, not_lt, not_not
-/
theorem frequently_cocardinal {p : α -> Prop} :
    (existsᶠ x in cocardinal α hreg, p x) ↔ c <= #{ x | p x } := by
  simp only [Filter.Frequently, eventually_cocardinal, not_not, coe_ofPred, not_lt]

/--
lemma `frequently_cocardinal_mem` / 引理 `frequently_cocardinal_mem`

English:
lemma frequently_cocardinal_mem
  given: {s : Set α}
  proof: frequently_cocardinal

@[simp]

中文:
引理 frequently_cocardinal_mem
  条件: {s : 集合 α}
  证明: frequently_cocardinal

@[simp]

Depends on / 依赖: frequently_cocardinal
-/
lemma frequently_cocardinal_mem {s : Set α} :
    (existsᶠ x in cocardinal α hreg, x in s) ↔ c <= #s := frequently_cocardinal

@[simp]
/--
lemma `cocardinal_inf_principal_neBot_iff` / 引理 `cocardinal_inf_principal_neBot_iff`

English:
lemma cocardinal_inf_principal_neBot_iff
  given: {s : Set α}
  proof: frequently_mem_iff_neBot.symm.trans frequently_cocardinal

中文:
引理 cocardinal_inf_principal_neBot_iff
  条件: {s : 集合 α}
  证明: frequently_mem_iff_neBot.symm.trans frequently_cocardinal

Depends on / 依赖: frequently_cocardinal, frequently_mem_iff_neBot, frequently_mem_iff_neBot.symm.trans
-/
lemma cocardinal_inf_principal_neBot_iff {s : Set α} :
    (cocardinal α hreg ⊓ 𝓟 s).NeBot ↔ c <= #s :=
  frequently_mem_iff_neBot.symm.trans frequently_cocardinal

/--
theorem `compl_mem_cocardinal_of_card_lt` / 定理 `compl_mem_cocardinal_of_card_lt`

English:
theorem compl_mem_cocardinal_of_card_lt
  given: {s : Set α} (hs : #s < c)
  proof: mem_cocardinal.2 (compl_compl s).symm ▸ hs

中文:
定理 compl_mem_cocardinal_of_card_lt
  条件: {s : 集合 α} (hs : #s < c)
  证明: mem_cocardinal.2 (compl_compl s).symm ▸ hs

Depends on / 依赖: compl_compl, mem_cocardinal
-/
theorem compl_mem_cocardinal_of_card_lt {s : Set α} (hs : #s < c) :
    sᶜ in cocardinal α hreg :=
mem_cocardinal.2 (compl_compl s).symm ▸ hs

/--
theorem `_root_.Set.Finite.compl_mem_cocardinal` / 定理 `_root_.Set.Finite.compl_mem_cocardinal`

English:
theorem _root_.Set.Finite.compl_mem_cocardinal
  given: {s : Set α} (hs : s.Finite)
  proof: compl_mem_cocardinal_of_card_lt lt_of_lt_of_le (Finite.lt_aleph0 hs) (hreg.aleph0_le)

中文:
定理 _root_.集合.有限.compl_mem_cocardinal
  条件: {s : 集合 α} (hs : s.有限)
  证明: compl_mem_cocardinal_of_card_lt lt_of_lt_of_le (Finite.lt_aleph0 hs) (hreg.aleph0_le)

Depends on / 依赖: Finite, Finite.lt_aleph0, aleph0_le, compl_mem_cocardinal_of_card_lt, hreg.aleph0_le, lt_aleph0, lt_of_lt_of_le
-/
theorem _root_.Set.Finite.compl_mem_cocardinal {s : Set α} (hs : s.Finite) :
    sᶜ in cocardinal α hreg :=
compl_mem_cocardinal_of_card_lt lt_of_lt_of_le (Finite.lt_aleph0 hs) (hreg.aleph0_le)

/--
theorem `eventually_cocardinal_notMem_of_card_lt` / 定理 `eventually_cocardinal_notMem_of_card_lt`

English:
theorem eventually_cocardinal_notMem_of_card_lt
  given: {s : Set α} (hs : #s < c)
  proof: compl_mem_cocardinal_of_card_lt hs

中文:
定理 eventually_cocardinal_notMem_of_card_lt
  条件: {s : 集合 α} (hs : #s < c)
  证明: compl_mem_cocardinal_of_card_lt hs

Depends on / 依赖: compl_mem_cocardinal_of_card_lt
-/
theorem eventually_cocardinal_notMem_of_card_lt {s : Set α} (hs : #s < c) :
    forallᶠ x in cocardinal α hreg, x ∉ s :=
  compl_mem_cocardinal_of_card_lt hs

/--
theorem `_root_.Finset.eventually_cocardinal_notMem` / 定理 `_root_.Finset.eventually_cocardinal_notMem`

English:
theorem _root_.Finset.eventually_cocardinal_notMem
  given: (s : Finset α)
  proof: eventually_cocardinal_notMem_of_card_lt (finset_card_lt_aleph0 s).trans_le (hreg.aleph0_le)

中文:
定理 _root_.有限集.eventually_cocardinal_notMem
  条件: (s : 有限集 α)
  证明: eventually_cocardinal_notMem_of_card_lt (finset_card_lt_aleph0 s).trans_le (hreg.aleph0_le)

Depends on / 依赖: aleph0_le, eventually_cocardinal_notMem_of_card_lt, finset_card_lt_aleph0, hreg.aleph0_le, trans_le
-/
theorem _root_.Finset.eventually_cocardinal_notMem (s : Finset α) :
    forallᶠ x in cocardinal α hreg, x ∉ s :=
eventually_cocardinal_notMem_of_card_lt (finset_card_lt_aleph0 s).trans_le (hreg.aleph0_le)

/--
theorem `eventually_cocardinal_ne` / 定理 `eventually_cocardinal_ne`

English:
theorem eventually_cocardinal_ne
  given: (x : α)
  statement: forallᶠ a in cocardinal α hreg, a != x
  proof: by
  simpa [Set.finite_singleton x] using hreg.nat_lt 1

中文:
定理 eventually_cocardinal_ne
  条件: (x : α)
  结论: 对任意ᶠ a in cocardinal α hreg, a != x
  证明: by
  simpa [Set.finite_singleton x] using hreg.nat_lt 1

Depends on / 依赖: Set.finite_singleton, finite_singleton, hreg.nat_lt, nat_lt
-/
theorem eventually_cocardinal_ne (x : α) : forallᶠ a in cocardinal α hreg, a != x := by
  simpa [Set.finite_singleton x] using hreg.nat_lt 1

/--
Definition of `cocountable` / `cocountable` 的定义

English:
abbreviation cocountable
  signature: : Filter α
  body: cocardinal α Cardinal.isRegular_aleph_one

中文:
缩写 cocountable
  签名: : 滤子 α
  定义体: cocardinal α Cardinal.isRegular_aleph_one

Depends on / 依赖: Cardinal, Cardinal.isRegular_aleph_one, cocardinal, isRegular_aleph_one
-/
noncomputable abbrev cocountable : Filter α := cocardinal α Cardinal.isRegular_aleph_one

/--
theorem `mem_cocountable` / 定理 `mem_cocountable`

English:
theorem mem_cocountable
  given: {s : Set α}
  statement: s in cocountable ↔ (sᶜ : Set α).Countable
  proof: by
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [mem_cocardinal]; rw [lt_aleph_one_iff]

中文:
定理 mem_cocountable
  条件: {s : 集合 α}
  结论: s in cocountable ↔ (sᶜ : 集合 α).可数
  证明: by
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [mem_cocardinal]; rw [lt_aleph_one_iff]

Depends on / 依赖: Cardinal, Cardinal.le_aleph0_iff_set_countable, le_aleph0_iff_set_countable, lt_aleph_one_iff, mem_cocardinal
-/
theorem mem_cocountable {s : Set α} : s in cocountable ↔ (sᶜ : Set α).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [mem_cocardinal]; rw [lt_aleph_one_iff]

end Filter
