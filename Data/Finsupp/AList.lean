/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.List.AList

/-!
# Connections between `Finsupp` and `AList`

## Main definitions

* `Finsupp.toAList`
* `AList.lookupFinsupp`: converts an association list into a finitely supported function
  via `AList.lookup`, sending absent keys to zero.

-/

@[expose] public section


namespace Finsupp

variable {α M : Type*} [Zero M]

/-- Produce an association list for the finsupp over its support using choice. -/
@[simps]
/--
Definition of `toAList` / `toAList` 的定义

English:
definition toAList
  signature: (f : α ->₀ M)
  body: ⟨f.graph.toList.map Prod.toSigma,
    by
      rw [List.NodupKeys]; rw [List.keys]; rw [List.map_map]; rw [Prod.fst_comp_toSigma]; rw [List.nodup_map_iff_inj_on]
      · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
        rw [Finset.mem_toList]; rw [Finsupp.mem_graph_iff] at hb hc
        dsimp at hb h

中文:
定义 toAList
  签名: (f : α ->₀ M)
  定义体: ⟨f.graph.toList.map Prod.toSigma,
    by
      rw [List.NodupKeys]; rw [List.keys]; rw [List.map_map]; rw [Prod.fst_comp_toSigma]; rw [List.nodup_map_iff_inj_on]
      · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
        rw [Finset.mem_toList]; rw [Finsupp.mem_graph_iff] at hb hc
        dsimp at hb h

Depends on / 依赖: Finset, Finset.mem_toList, Finset.nodup_toList, Finsupp, Finsupp.mem_graph_iff, List.NodupKeys, List.keys, List.map_map, List.nodup_map_iff_inj_on, NodupKeys, Prod.fst_comp_toSigma, Prod.toSigma, f.graph.toList.map, fst_comp_toSigma, map_map, mem_graph_iff, mem_toList, nodup_map_iff_inj_on, nodup_toList, toList
-/
noncomputable def toAList (f : α ->₀ M) : AList fun _x : α => M :=
  ⟨f.graph.toList.map Prod.toSigma,
    by
      rw [List.NodupKeys]; rw [List.keys]; rw [List.map_map]; rw [Prod.fst_comp_toSigma]; rw [List.nodup_map_iff_inj_on]
      · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
        rw [Finset.mem_toList]; rw [Finsupp.mem_graph_iff] at hb hc
        dsimp at hb hc
        rw [← hc.1]; rw [hb.1]
      · apply Finset.nodup_toList⟩

@[simp]
/--
theorem `toAList_keys_toFinset` / 定理 `toAList_keys_toFinset`

English:
theorem toAList_keys_toFinset
  given: [DecidableEq α] (f : α ->₀ M)
  proof: by
  ext
  simp [toAList, AList.keys, List.keys]

@[simp]

中文:
定理 toAList_keys_toFinset
  条件: [DecidableEq α] (f : α ->₀ M)
  证明: by
  ext
  simp [toAList, AList.keys, List.keys]

@[simp]

Depends on / 依赖: AList.keys, List.keys, toAList
-/
theorem toAList_keys_toFinset [DecidableEq α] (f : α ->₀ M) :
    f.toAList.keys.toFinset = f.support := by
  ext
  simp [toAList, AList.keys, List.keys]

@[simp]
/--
theorem `mem_toAlist` / 定理 `mem_toAlist`

English:
theorem mem_toAlist
  given: {f : α ->₀ M} {x : α}
  statement: x in f.toAList ↔ f x != 0
  proof: by
  classical rw [AList.mem_keys, ← List.mem_toFinset, toAList_keys_toFinset, mem_support_iff]

中文:
定理 mem_toAlist
  条件: {f : α ->₀ M} {x : α}
  结论: x in f.toAList ↔ f x != 0
  证明: by
  classical rw [AList.mem_keys, ← List.mem_toFinset, toAList_keys_toFinset, mem_support_iff]

Depends on / 依赖: AList.mem_keys, List.mem_toFinset, classical, mem_keys, mem_support_iff, mem_toFinset, toAList_keys_toFinset
-/
theorem mem_toAlist {f : α ->₀ M} {x : α} : x in f.toAList ↔ f x != 0 := by
  classical rw [AList.mem_keys, ← List.mem_toFinset, toAList_keys_toFinset, mem_support_iff]

end Finsupp

namespace AList

variable {α M : Type*} [Zero M]

open List

/--
Definition of `lookupFinsupp` / `lookupFinsupp` 的定义

English:
definition lookupFinsupp
  signature: (l : AList fun _x : α => M)
  body: by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact (l.1.filter fun x => Sigma.snd x != 0).keys.toFinset
  toFun a :=
    haveI := Classical.decEq α
    (l.lookup a).getD 0
  mem_support_toFun a := by
    classical
      simp_rw [mem_toFinset, List.mem_keys, List.mem_filter, ← me

中文:
定义 lookupFinsupp
  签名: (l : AList fun _x : α => M)
  定义体: by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact (l.1.filter fun x => Sigma.snd x != 0).keys.toFinset
  toFun a :=
    haveI := Classical.decEq α
    (l.lookup a).getD 0
  mem_support_toFun a := by
    classical
      simp_rw [mem_toFinset, List.mem_keys, List.mem_filter, ← me

Depends on / 依赖: Classical, Classical.decEq, List.mem_filter, List.mem_keys, Sigma.snd, classical, filter, keys.toFinset, l.lookup, lookup, mem_filter, mem_keys, mem_lookup_iff, mem_support_toFun, mem_toFinset, simp_rw, toFinset
-/
noncomputable def lookupFinsupp (l : AList fun _x : α => M) : α ->₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact (l.1.filter fun x => Sigma.snd x != 0).keys.toFinset
  toFun a :=
    haveI := Classical.decEq α
    (l.lookup a).getD 0
  mem_support_toFun a := by
    classical
      simp_rw [mem_toFinset, List.mem_keys, List.mem_filter, ← mem_lookup_iff]
      cases lookup a l <;> simp

@[simp]
/--
theorem `lookupFinsupp_apply` / 定理 `lookupFinsupp_apply`

English:
theorem lookupFinsupp_apply
  given: [DecidableEq α] (l : AList fun _x : α => M) (a : α)
  proof: by
  simp only [lookupFinsupp, ne_eq, Finsupp.coe_mk]
  congr

@[simp]

中文:
定理 lookupFinsupp_apply
  条件: [DecidableEq α] (l : AList fun _x : α => M) (a : α)
  证明: by
  simp only [lookupFinsupp, ne_eq, Finsupp.coe_mk]
  congr

@[simp]

Depends on / 依赖: Finsupp, Finsupp.coe_mk, coe_mk, lookupFinsupp, ne_eq
-/
theorem lookupFinsupp_apply [DecidableEq α] (l : AList fun _x : α => M) (a : α) :
    l.lookupFinsupp a = (l.lookup a).getD 0 := by
  simp only [lookupFinsupp, ne_eq, Finsupp.coe_mk]
  congr

@[simp]
/--
theorem `lookupFinsupp_support` / 定理 `lookupFinsupp_support`

English:
theorem lookupFinsupp_support
  given: [DecidableEq α] [DecidableEq M] (l : AList fun _x : α => M)
  proof: by
  dsimp only [lookupFinsupp]
  congr!

中文:
定理 lookupFinsupp_support
  条件: [DecidableEq α] [DecidableEq M] (l : AList fun _x : α => M)
  证明: by
  dsimp only [lookupFinsupp]
  congr!

Depends on / 依赖: lookupFinsupp
-/
theorem lookupFinsupp_support [DecidableEq α] [DecidableEq M] (l : AList fun _x : α => M) :
    l.lookupFinsupp.support = (l.1.filter fun x => Sigma.snd x != 0).keys.toFinset := by
  dsimp only [lookupFinsupp]
  congr!

/--
theorem `lookupFinsupp_eq_iff_of_ne_zero` / 定理 `lookupFinsupp_eq_iff_of_ne_zero`

English:
theorem lookupFinsupp_eq_iff_of_ne_zero
  statement: [DecidableEq α] {l : AList fun _x : α => M} {a : α} {x : M}
  proof: by
  rw [lookupFinsupp_apply]
  rcases lookup a l with - | m <;> simp [hx.symm]

中文:
定理 lookupFinsupp_eq_iff_of_ne_zero
  结论: [DecidableEq α] {l : AList fun _x : α => M} {a : α} {x : M}
  证明: by
  rw [lookupFinsupp_apply]
  rcases lookup a l with - | m <;> simp [hx.symm]

Depends on / 依赖: hx.symm, lookup, lookupFinsupp_apply
-/
theorem lookupFinsupp_eq_iff_of_ne_zero [DecidableEq α] {l : AList fun _x : α => M} {a : α} {x : M}
    (hx : x != 0) : l.lookupFinsupp a = x ↔ x in l.lookup a := by
  rw [lookupFinsupp_apply]
  rcases lookup a l with - | m <;> simp [hx.symm]

/--
theorem `lookupFinsupp_eq_zero_iff` / 定理 `lookupFinsupp_eq_zero_iff`

English:
theorem lookupFinsupp_eq_zero_iff
  given: [DecidableEq α] {l : AList fun _x : α => M} {a : α}
  proof: by
  rw [lookupFinsupp_apply]; rw [← lookup_eq_none]
  rcases lookup a l with - | m <;> simp

@[simp]

中文:
定理 lookupFinsupp_eq_zero_iff
  条件: [DecidableEq α] {l : AList fun _x : α => M} {a : α}
  证明: by
  rw [lookupFinsupp_apply]; rw [← lookup_eq_none]
  rcases lookup a l with - | m <;> simp

@[simp]

Depends on / 依赖: lookup, lookupFinsupp_apply, lookup_eq_none
-/
theorem lookupFinsupp_eq_zero_iff [DecidableEq α] {l : AList fun _x : α => M} {a : α} :
    l.lookupFinsupp a = 0 ↔ a ∉ l ∨ (0 : M) in l.lookup a := by
  rw [lookupFinsupp_apply]; rw [← lookup_eq_none]
  rcases lookup a l with - | m <;> simp

@[simp]
/--
theorem `empty_lookupFinsupp` / 定理 `empty_lookupFinsupp`

English:
theorem empty_lookupFinsupp
  statement: lookupFinsupp (∅ : AList fun _x : α => M) = 0
  proof: rfl

@[simp]

中文:
定理 empty_lookupFinsupp
  结论: lookupFinsupp (∅ : AList fun _x : α => M) = 0
  证明: rfl

@[simp]
-/
theorem empty_lookupFinsupp : lookupFinsupp (∅ : AList fun _x : α => M) = 0 := rfl

@[simp]
/--
theorem `insert_lookupFinsupp` / 定理 `insert_lookupFinsupp`

English:
theorem insert_lookupFinsupp
  given: [DecidableEq α] (l : AList fun _x : α => M) (a : α) (m : M)
  proof: by
  ext b
  by_cases h : b = a <;> simp [h]

@[simp]

中文:
定理 insert_lookupFinsupp
  条件: [DecidableEq α] (l : AList fun _x : α => M) (a : α) (m : M)
  证明: by
  ext b
  by_cases h : b = a <;> simp [h]

@[simp]
-/
theorem insert_lookupFinsupp [DecidableEq α] (l : AList fun _x : α => M) (a : α) (m : M) :
    (l.insert a m).lookupFinsupp = l.lookupFinsupp.update a m := by
  ext b
  by_cases h : b = a <;> simp [h]

@[simp]
/--
theorem `singleton_lookupFinsupp` / 定理 `singleton_lookupFinsupp`

English:
theorem singleton_lookupFinsupp
  given: (a : α) (m : M)
  proof: by
  classical
  simp [← AList.insert_empty]

@[simp]

中文:
定理 singleton_lookupFinsupp
  条件: (a : α) (m : M)
  证明: by
  classical
  simp [← AList.insert_empty]

@[simp]

Depends on / 依赖: AList.insert_empty, classical, insert_empty
-/
theorem singleton_lookupFinsupp (a : α) (m : M) :
    (singleton a m).lookupFinsupp = Finsupp.single a m := by
  classical
  simp [← AList.insert_empty]

@[simp]
/--
theorem `_root_.Finsupp.toAList_lookupFinsupp` / 定理 `_root_.Finsupp.toAList_lookupFinsupp`

English:
theorem _root_.Finsupp.toAList_lookupFinsupp
  given: (f : α ->₀ M)
  statement: f.toAList.lookupFinsupp = f
  proof: by
  ext a
  classical
    by_cases h : f a = 0
    · suffices f.toAList.lookup a = none by simp [h, this]
      simp [lookup_eq_none, h]
    · suffices f.toAList.lookup a = some (f a) by simp [this]
      apply mem_lookup_iff.2
      simpa using h

中文:
定理 _root_.有限支撑.toAList_lookupFinsupp
  条件: (f : α ->₀ M)
  结论: f.toAList.lookupFinsupp = f
  证明: by
  ext a
  classical
    by_cases h : f a = 0
    · suffices f.toAList.lookup a = none by simp [h, this]
      simp [lookup_eq_none, h]
    · suffices f.toAList.lookup a = some (f a) by simp [this]
      apply mem_lookup_iff.2
      simpa using h

Depends on / 依赖: classical, f.toAList.lookup, lookup, lookup_eq_none, mem_lookup_iff, toAList
-/
theorem _root_.Finsupp.toAList_lookupFinsupp (f : α ->₀ M) : f.toAList.lookupFinsupp = f := by
  ext a
  classical
    by_cases h : f a = 0
    · suffices f.toAList.lookup a = none by simp [h, this]
      simp [lookup_eq_none, h]
    · suffices f.toAList.lookup a = some (f a) by simp [this]
      apply mem_lookup_iff.2
      simpa using h

/--
theorem `lookupFinsupp_surjective` / 定理 `lookupFinsupp_surjective`

English:
theorem lookupFinsupp_surjective
  statement: Function.Surjective (@lookupFinsupp α M _)
  proof: fun f =>
  ⟨_, Finsupp.toAList_lookupFinsupp f⟩

中文:
定理 lookupFinsupp_surjective
  结论: 函数.满射 (@lookupFinsupp α M _)
  证明: fun f =>
  ⟨_, Finsupp.toAList_lookupFinsupp f⟩
-/
theorem lookupFinsupp_surjective : Function.Surjective (@lookupFinsupp α M _) := fun f =>
  ⟨_, Finsupp.toAList_lookupFinsupp f⟩

end AList
