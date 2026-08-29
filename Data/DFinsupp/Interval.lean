/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Order
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/

@[expose] public section


open DFinsupp Finset

open scoped Pointwise

variable {ι : Type*} {α : ι -> Type*}

namespace Finset

variable [DecidableEq ι] [forall i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : forall i, Finset (α i)}

/--
Definition of `dfinsupp` / `dfinsupp` 的定义

English:
definition dfinsupp
  signature: (s : Finset ι) (t : forall i, Finset (α i))
  body: (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert! congr_fun h ⟨i, hi⟩⟩

@[simp]

中文:
定义 dfinsupp
  签名: (s : 有限集 ι) (t : 对任意 i, 有限集 (α i))
  定义体: (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert! congr_fun h ⟨i, hi⟩⟩

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.mk, congr_fun, convert, mk_injective, s.pi
-/
def dfinsupp (s : Finset ι) (t : forall i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert! congr_fun h ⟨i, hi⟩⟩

@[simp]
/--
theorem `card_dfinsupp` / 定理 `card_dfinsupp`

English:
theorem card_dfinsupp
  given: (s : Finset ι) (t : forall i, Finset (α i))
  statement: #(s.dfinsupp t) = ∏ i in s, #(t i)
  proof: (card_map _).trans card_pi _ _

中文:
定理 card_dfinsupp
  条件: (s : 有限集 ι) (t : 对任意 i, 有限集 (α i))
  结论: #(s.dfinsupp t) = ∏ i in s, #(t i)
  证明: (card_map _).trans card_pi _ _

Depends on / 依赖: card_map, card_pi
-/
theorem card_dfinsupp (s : Finset ι) (t : forall i, Finset (α i)) : #(s.dfinsupp t) = ∏ i in s, #(t i) :=
(card_map _).trans card_pi _ _

variable [forall i, DecidableEq (α i)]

/--
theorem `mem_dfinsupp_iff` / 定理 `mem_dfinsupp_iff`

English:
theorem mem_dfinsupp_iff
  statement: f in s.dfinsupp t ↔ f.support subseteq s ∧ forall i in s, f i in t i
  proof: by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Function.Embedding.coeFn_mk]
    refine ⟨support_mk_subset, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact mk_of_mem hi
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    dsimp
    exact ite_eq_left_iff.2 f

中文:
定理 mem_dfinsupp_iff
  结论: f in s.dfinsupp t ↔ f.support subseteq s ∧ 对任意 i in s, f i in t i
  证明: by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Function.Embedding.coeFn_mk]
    refine ⟨support_mk_subset, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact mk_of_mem hi
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    dsimp
    exact ite_eq_left_iff.2 f

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, coeFn_mk, convert, ite_eq_left_iff, mem_map, mem_map.trans, mem_pi, mk_of_mem, notMem_support_iff, support_mk_subset, zipLeft
-/
theorem mem_dfinsupp_iff : f in s.dfinsupp t ↔ f.support subseteq s ∧ forall i in s, f i in t i := by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Function.Embedding.coeFn_mk]
    refine ⟨support_mk_subset, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact mk_of_mem hi
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    dsimp
    exact ite_eq_left_iff.2 fun hi => (notMem_support_iff.1 fun H => hi <| h.1 H).symm

/-- When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is pointwise in `t`.
-/
@[simp]
/--
theorem `mem_dfinsupp_iff_of_support_subset` / 定理 `mem_dfinsupp_iff_of_support_subset`

English:
theorem mem_dfinsupp_iff_of_support_subset
  given: {t : Π₀ i, Finset (α i)} (ht : t.support subseteq s)
  proof: by
  refine mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => ?_,
fun h => ⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff

中文:
定理 mem_dfinsupp_iff_of_support_subset
  条件: {t : Π₀ i, 有限集 (α i)} (ht : t.support subseteq s)
  证明: by
  refine mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => ?_,
fun h => ⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff

Depends on / 依赖: forall_and, forall_and.symm.trans, forall_congr, mem_dfinsupp_iff, mem_dfinsupp_iff.trans, mem_support_iff, mem_zero, notMem_mono, notMem_support_iff, zero_mem_zero
-/
theorem mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.support subseteq s) :
    f in s.dfinsupp t ↔ forall i, f i in t i := by
  refine mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => ?_,
fun h => ⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff.1 (notMem_mono ht hi)]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h

end Finset

namespace DFinsupp

section BundledSingleton

variable [forall i, Zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (f : Π₀ i, α i)
  body: {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩

中文:
定义 singleton
  签名: (f : Π₀ i, α i)
  定义体: {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩
-/
def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩

/--
theorem `mem_singleton_apply_iff` / 定理 `mem_singleton_apply_iff`

English:
theorem mem_singleton_apply_iff
  statement: a in f.singleton i ↔ a = f i
  proof: mem_singleton

中文:
定理 mem_singleton_apply_iff
  结论: a in f.singleton i ↔ a = f i
  证明: mem_singleton

Depends on / 依赖: mem_singleton
-/
theorem mem_singleton_apply_iff : a in f.singleton i ↔ a = f i :=
  mem_singleton

end BundledSingleton

section BundledIcc

variable [forall i, Zero (α i)] [forall i, PartialOrder (α i)] [forall i, LocallyFiniteOrder (α i)]
  {f g : Π₀ i, α i} {i : ι} {a : α i}

/--
Definition of `rangeIcc` / `rangeIcc` 的定义

English:
definition rangeIcc
  signature: (f g : Π₀ i, α i)
  body: Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        ha

中文:
定义 rangeIcc
  签名: (f g : Π₀ i, α i)
  定义体: Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        ha

Depends on / 依赖: zipRight
-/
def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        have hg : g i = 0 := (gs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_left _ _) h)
        simp_rw [hf, hg]
        exact Icc_self _⟩

@[simp]
/--
theorem `rangeIcc_apply` / 定理 `rangeIcc_apply`

English:
theorem rangeIcc_apply
  given: (f g : Π₀ i, α i) (i : ι)
  statement: f.rangeIcc g i = Icc (f i) (g i)
  proof: rfl

中文:
定理 rangeIcc_apply
  条件: (f g : Π₀ i, α i) (i : ι)
  结论: f.rangeIcc g i = 闭区间 (f i) (g i)
  证明: rfl
-/
theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl

/--
theorem `mem_rangeIcc_apply_iff` / 定理 `mem_rangeIcc_apply_iff`

English:
theorem mem_rangeIcc_apply_iff
  statement: a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
  proof: mem_Icc

中文:
定理 mem_rangeIcc_apply_iff
  结论: a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
  证明: mem_Icc

Depends on / 依赖: mem_Icc
-/
theorem mem_rangeIcc_apply_iff : a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i := mem_Icc

/--
theorem `support_rangeIcc_subset` / 定理 `support_rangeIcc_subset`

English:
theorem support_rangeIcc_subset
  given: [DecidableEq ι] [forall i, DecidableEq (α i)]
  proof: by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 ?_ hx
  rw [rangeIcc_apply]; rw [notMem_support_iff.1 (notMem_mono subset_union_left h)]; rw [notMem_support_iff.1 (notMem_mono subset_union_right h)]
  exact Icc_self _

中文:
定理 support_rangeIcc_subset
  条件: [DecidableEq ι] [对任意 i, DecidableEq (α i)]
  证明: by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 ?_ hx
  rw [rangeIcc_apply]; rw [notMem_support_iff.1 (notMem_mono subset_union_left h)]; rw [notMem_support_iff.1 (notMem_mono subset_union_right h)]
  exact Icc_self _

Depends on / 依赖: Icc_self, notMem_mono, notMem_support_iff, rangeIcc_apply, subset_union_left, subset_union_right
-/
theorem support_rangeIcc_subset [DecidableEq ι] [forall i, DecidableEq (α i)] :
    (f.rangeIcc g).support subseteq f.support union g.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 ?_ hx
  rw [rangeIcc_apply]; rw [notMem_support_iff.1 (notMem_mono subset_union_left h)]; rw [notMem_support_iff.1 (notMem_mono subset_union_right h)]
  exact Icc_self _

end BundledIcc

section Pi

variable [forall i, Zero (α i)] [DecidableEq ι] [forall i, DecidableEq (α i)]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : Π₀ i, Finset (α i))
  body: f.support.dfinsupp f

@[simp]

中文:
定义 pi
  签名: (f : Π₀ i, 有限集 (α i))
  定义体: f.support.dfinsupp f

@[simp]

Depends on / 依赖: dfinsupp, f.support.dfinsupp, support
-/
def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) := f.support.dfinsupp f

@[simp]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i}
  statement: g in f.pi ↔ forall i, g i in f i
  proof: mem_dfinsupp_iff_of_support_subset Subset.refl _

@[simp]

中文:
定理 mem_pi
  条件: {f : Π₀ i, 有限集 (α i)} {g : Π₀ i, α i}
  结论: g in f.pi ↔ 对任意 i, g i in f i
  证明: mem_dfinsupp_iff_of_support_subset Subset.refl _

@[simp]

Depends on / 依赖: Subset, Subset.refl, mem_dfinsupp_iff_of_support_subset
-/
theorem mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g in f.pi ↔ forall i, g i in f i :=
mem_dfinsupp_iff_of_support_subset Subset.refl _

@[simp]
/--
theorem `card_pi` / 定理 `card_pi`

English:
theorem card_pi
  given: (f : Π₀ i, Finset (α i))
  statement: #f.pi = f.prod fun i => #(f i)
  proof: by
  rw [pi]; rw [card_dfinsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

中文:
定理 card_pi
  条件: (f : Π₀ i, 有限集 (α i))
  结论: #f.pi = f.乘积 fun i => #(f i)
  证明: by
  rw [pi]; rw [card_dfinsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

Depends on / 依赖: Finset, Finset.prod_congr, Nat.cast_id, Pi.natCast_apply, card_dfinsupp, cast_id, natCast_apply, prod_congr
-/
theorem card_pi (f : Π₀ i, Finset (α i)) : #f.pi = f.prod fun i => #(f i) := by
  rw [pi]; rw [card_dfinsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

end Pi

section PartialOrder

variable [DecidableEq ι] [forall i, DecidableEq (α i)]
variable [forall i, PartialOrder (α i)] [forall i, Zero (α i)] [forall i, LocallyFiniteOrder (α i)]

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (Π₀ i, α i)
  body: LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support union g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans ?_
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      rfl)

中文:
实例 instLocallyFiniteOrder
  签名: : 局部有限序 (Π₀ i, α i)
  定义体: LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support union g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans ?_
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      rfl)

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, dfinsupp, f.rangeIcc, f.support, forall_and, g.support, mem_dfinsupp_iff_of_support_subset, mem_rangeIcc_apply_iff, rangeIcc, simp_rw, support, support_rangeIcc_subset
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Π₀ i, α i) :=
  LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support union g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans ?_
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      rfl)

variable (f g : Π₀ i, α i)

/--
theorem `Icc_eq` / 定理 `Icc_eq`

English:
theorem Icc_eq
  statement: Icc f g = (f.support union g.support).dfinsupp (f.rangeIcc g)
  proof: rfl

中文:
定理 Icc_eq
  结论: 闭区间 f g = (f.support union g.support).dfinsupp (f.rangeIcc g)
  证明: rfl
-/
theorem Icc_eq : Icc f g = (f.support union g.support).dfinsupp (f.rangeIcc g) := rfl

/--
lemma `card_Icc` / 引理 `card_Icc`

English:
lemma card_Icc
  statement: #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i))
  proof: card_dfinsupp _ _

中文:
引理 card_Icc
  结论: #(闭区间 f g) = ∏ i in f.support union g.support, #(闭区间 (f i) (g i))
  证明: card_dfinsupp _ _

Depends on / 依赖: card_dfinsupp
-/
lemma card_Icc : #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) :=
  card_dfinsupp _ _

/--
lemma `card_Ico` / 引理 `card_Ico`

English:
lemma card_Ico
  statement: #(Ico f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 1
  proof: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
引理 card_Ico
  结论: #(左闭右开区间 f g) = (∏ i in f.support union g.support, #(闭区间 (f i) (g i))) - 1
  证明: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ico_eq_card_Icc_sub_one
-/
lemma card_Ico : #(Ico f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

/--
lemma `card_Ioc` / 引理 `card_Ioc`

English:
lemma card_Ioc
  statement: #(Ioc f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 1
  proof: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
引理 card_Ioc
  结论: #(左开右闭区间 f g) = (∏ i in f.support union g.support, #(闭区间 (f i) (g i))) - 1
  证明: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioc_eq_card_Icc_sub_one
-/
lemma card_Ioc : #(Ioc f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

/--
lemma `card_Ioo` / 引理 `card_Ioo`

English:
lemma card_Ioo
  statement: #(Ioo f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 2
  proof: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

中文:
引理 card_Ioo
  结论: #(开区间 f g) = (∏ i in f.support union g.support, #(闭区间 (f i) (g i))) - 2
  证明: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioo_eq_card_Icc_sub_two
-/
lemma card_Ioo : #(Ioo f g) = (∏ i in f.support union g.support, #(Icc (f i) (g i))) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

end PartialOrder

section Lattice
variable [DecidableEq ι] [forall i, DecidableEq (α i)] [forall i, Lattice (α i)] [forall i, Zero (α i)]
  [forall i, LocallyFiniteOrder (α i)] (f g : Π₀ i, α i)

/--
lemma `card_uIcc` / 引理 `card_uIcc`

English:
lemma card_uIcc
  statement: #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (g i))
  proof: by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _

中文:
引理 card_uIcc
  结论: #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (g i))
  证明: by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _

Depends on / 依赖: card_Icc, support_inf_union_support_sup
-/
lemma card_uIcc : #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _

end Lattice

section IsBotZeroClass

variable [DecidableEq ι] [forall i, DecidableEq (α i)]
variable [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, IsBotZeroClass (α i)]
  [forall i, OrderBot (α i)] [forall i, LocallyFiniteOrder (α i)]
variable (f : Π₀ i, α i)

/--
lemma `card_Iic` / 引理 `card_Iic`

English:
lemma card_Iic
  statement: #(Iic f) = ∏ i in f.support, #(Iic (f i))
  proof: by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

中文:
引理 card_Iic
  结论: #(左无界右闭区间 f) = ∏ i in f.support, #(左无界右闭区间 (f i))
  证明: by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

Depends on / 依赖: Iic_eq_Icc, bot_eq_zero, card_Icc
-/
lemma card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i)) := by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

/--
lemma `card_Iio` / 引理 `card_Iio`

English:
lemma card_Iio
  statement: #(Iio f) = (∏ i in f.support, #(Iic (f i))) - 1
  proof: by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

中文:
引理 card_Iio
  结论: #(左无界右开区间 f) = (∏ i in f.support, #(左无界右闭区间 (f i))) - 1
  证明: by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

Depends on / 依赖: card_Iic, card_Iio_eq_card_Iic_sub_one
-/
lemma card_Iio : #(Iio f) = (∏ i in f.support, #(Iic (f i))) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

end IsBotZeroClass

end DFinsupp
