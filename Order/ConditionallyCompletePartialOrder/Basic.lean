/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs

import Mathlib.Data.Set.Lattice

/-! # Basic results on conditionally complete partial orders

This file contains some basic results on conditionally complete partial orders, and is intended
to parallel the API for conditionally complete lattices where possible. For the reason, the
theorems here are mostly protected within the `DirectedOn` namespace, unless such an assumption is
unnecessary. Otherwise the names here share the same names as their counterparts in
`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`.

-/
public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

namespace OrderDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompletePartialOrderSup
  signature: α] :
  body: h_dir.isLUB_csSup (α := α) h_non h_bdd

中文:
实例 [余nditionallyCompletePartialOrderSup
  签名: α] :
  定义体: h_dir.isLUB_csSup (α := α) h_non h_bdd

Depends on / 依赖: h_bdd, h_dir, h_dir.isLUB_csSup, h_non, isLUB_csSup
-/
instance [ConditionallyCompletePartialOrderSup α] :
    ConditionallyCompletePartialOrderInf αᵒᵈ where
  isGLB_csInf_of_directed _ h_dir h_non h_bdd := h_dir.isLUB_csSup (α := α) h_non h_bdd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompletePartialOrderInf
  signature: α] :
  body: h_dir.isGLB_csInf (α := α) h_non h_bdd

中文:
实例 [余nditionallyCompletePartialOrderInf
  签名: α] :
  定义体: h_dir.isGLB_csInf (α := α) h_non h_bdd

Depends on / 依赖: h_bdd, h_dir, h_dir.isGLB_csInf, h_non, isGLB_csInf
-/
instance [ConditionallyCompletePartialOrderInf α] :
    ConditionallyCompletePartialOrderSup αᵒᵈ where
  isLUB_csSup_of_directed _ h_dir h_non h_bdd := h_dir.isGLB_csInf (α := α) h_non h_bdd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompletePartialOrder
  signature: α] :

中文:
实例 [余nditionallyCompletePartial序
  签名: α] :
-/
instance [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder αᵒᵈ where

end OrderDual

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {s t : Set α} {a b : α}

@[to_dual csInf_le_of_le]
/--
theorem `DirectedOn.le_csSup_of_le` / 定理 `DirectedOn.le_csSup_of_le`

English:
theorem DirectedOn.le_csSup_of_le
  statement: (hd : DirectedOn (· <= ·) s)
  proof: le_trans h (hd.le_csSup hs hb)

@[to_dual (attr := gcongr low)]

中文:
定理 DirectedOn.le_csSup_of_le
  结论: (hd : DirectedOn (· <= ·) s)
  证明: le_trans h (hd.le_csSup hs hb)

@[to_dual (attr := gcongr low)]
-/
protected theorem DirectedOn.le_csSup_of_le (hd : DirectedOn (· <= ·) s)
    (hs : BddAbove s) (hb : b in s) (h : a <= b) : a <= sSup s :=
  le_trans h (hd.le_csSup hs hb)

@[to_dual (attr := gcongr low)]
/--
theorem `DirectedOn.csSup_le_csSup` / 定理 `DirectedOn.csSup_le_csSup`

English:
theorem DirectedOn.csSup_le_csSup
  statement: (hds : DirectedOn (· <= ·) s)
  proof: hds.csSup_le hs fun _ ha => hdt.le_csSup ht (h ha)

@[to_dual csInf_le_iff]

中文:
定理 DirectedOn.csSup_le_csSup
  结论: (hds : DirectedOn (· <= ·) s)
  证明: hds.csSup_le hs fun _ ha => hdt.le_csSup ht (h ha)

@[to_dual csInf_le_iff]
-/
protected theorem DirectedOn.csSup_le_csSup (hds : DirectedOn (· <= ·) s)
    (hdt : DirectedOn (· <= ·) t) (ht : BddAbove t) (hs : s.Nonempty) (h : s subseteq t) :
    sSup s <= sSup t :=
  hds.csSup_le hs fun _ ha => hdt.le_csSup ht (h ha)

@[to_dual csInf_le_iff]
/--
theorem `DirectedOn.le_csSup_iff` / 定理 `DirectedOn.le_csSup_iff`

English:
theorem DirectedOn.le_csSup_iff
  statement: (hd : DirectedOn (· <= ·) s) (h : BddAbove s)
  proof: ⟨fun h _ hb => le_trans h (hd.csSup_le hs hb), fun hb => hb _ fun _ => hd.le_csSup h⟩

@[to_dual]

中文:
定理 DirectedOn.le_csSup_iff
  结论: (hd : DirectedOn (· <= ·) s) (h : BddAbove s)
  证明: ⟨fun h _ hb => le_trans h (hd.csSup_le hs hb), fun hb => hb _ fun _ => hd.le_csSup h⟩

@[to_dual]
-/
protected theorem DirectedOn.le_csSup_iff (hd : DirectedOn (· <= ·) s) (h : BddAbove s)
    (hs : s.Nonempty) : a <= sSup s ↔ forall b, b in upperBounds s -> a <= b :=
  ⟨fun h _ hb => le_trans h (hd.csSup_le hs hb), fun hb => hb _ fun _ => hd.le_csSup h⟩

@[to_dual]
/--
theorem `IsGreatest.directedOn` / 定理 `IsGreatest.directedOn`

English:
theorem IsGreatest.directedOn
  given: (H : IsGreatest s a)
  statement: DirectedOn (· <= ·) s
  proof: fun _ h₁ _ h₂ => ⟨a, H.1, H.2 h₁, H.2 h₂⟩

中文:
定理 IsGreatest.directedOn
  条件: (H : IsGreatest s a)
  结论: DirectedOn (· <= ·) s
  证明: fun _ h₁ _ h₂ => ⟨a, H.1, H.2 h₁, H.2 h₂⟩
-/
theorem IsGreatest.directedOn (H : IsGreatest s a) : DirectedOn (· <= ·) s :=
  fun _ h₁ _ h₂ => ⟨a, H.1, H.2 h₁, H.2 h₂⟩

/-- A greatest element of a set is the supremum of this set. -/
@[to_dual /-- A least element of a set is the infimum of this set. -/]
/--
theorem `IsGreatest.csSup_eq` / 定理 `IsGreatest.csSup_eq`

English:
theorem IsGreatest.csSup_eq
  given: (H : IsGreatest s a)
  statement: sSup s = a
  proof: .unique H.isLUB H.directedOn.isLUB_csSup H.nonempty ⟨a, H.2⟩

@[to_dual]

中文:
定理 IsGreatest.csSup_eq
  条件: (H : IsGreatest s a)
  结论: sSup s = a
  证明: .unique H.isLUB H.directedOn.isLUB_csSup H.nonempty ⟨a, H.2⟩

@[to_dual]

Depends on / 依赖: H.directedOn.isLUB_csSup, H.isLUB, H.nonempty, directedOn, isLUB_csSup, nonempty, unique
-/
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
.unique H.isLUB H.directedOn.isLUB_csSup H.nonempty ⟨a, H.2⟩

@[to_dual]
/--
theorem `IsGreatest.csSup_mem` / 定理 `IsGreatest.csSup_mem`

English:
theorem IsGreatest.csSup_mem
  given: (H : IsGreatest s a)
  statement: sSup s in s
  proof: H.csSup_eq.symm ▸ H.1

@[to_dual le_csInf_iff]

中文:
定理 IsGreatest.csSup_mem
  条件: (H : IsGreatest s a)
  结论: sSup s in s
  证明: H.csSup_eq.symm ▸ H.1

@[to_dual le_csInf_iff]

Depends on / 依赖: H.csSup_eq.symm, csSup_eq
-/
theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s in s :=
  H.csSup_eq.symm ▸ H.1

@[to_dual le_csInf_iff]
/--
theorem `DirectedOn.csSup_le_iff` / 定理 `DirectedOn.csSup_le_iff`

English:
theorem DirectedOn.csSup_le_iff
  statement: (hd : DirectedOn (· <= ·) s)
  proof: isLUB_le_iff (hd.isLUB_csSup hs hb)

@[to_dual notMem_of_lt_csInf]

中文:
定理 DirectedOn.csSup_le_iff
  结论: (hd : DirectedOn (· <= ·) s)
  证明: isLUB_le_iff (hd.isLUB_csSup hs hb)

@[to_dual notMem_of_lt_csInf]
-/
protected theorem DirectedOn.csSup_le_iff (hd : DirectedOn (· <= ·) s)
    (hb : BddAbove s) (hs : s.Nonempty) : sSup s <= a ↔ forall b in s, b <= a :=
  isLUB_le_iff (hd.isLUB_csSup hs hb)

@[to_dual notMem_of_lt_csInf]
/--
theorem `DirectedOn.notMem_of_csSup_lt` / 定理 `DirectedOn.notMem_of_csSup_lt`

English:
theorem DirectedOn.notMem_of_csSup_lt
  statement: {x : α} {s : Set α} (hd : DirectedOn (· <= ·) s)
  proof: fun hx => lt_irrefl _ (hd.le_csSup hs hx).trans_lt h

中文:
定理 DirectedOn.notMem_of_csSup_lt
  结论: {x : α} {s : 集合 α} (hd : DirectedOn (· <= ·) s)
  证明: fun hx => lt_irrefl _ (hd.le_csSup hs hx).trans_lt h
-/
protected theorem DirectedOn.notMem_of_csSup_lt {x : α} {s : Set α} (hd : DirectedOn (· <= ·) s)
    (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
fun hx => lt_irrefl _ (hd.le_csSup hs hx).trans_lt h

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual DirectedOn.csInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/ ]
/--
theorem `DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt
  proof: (eq_of_le_of_not_lt (hd.csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le hd.le_csSup ⟨b, H⟩ ha

中文:
定理 DirectedOn.csSup_eq_of_对任意_le_of_对任意_lt_存在_gt
  证明: (eq_of_le_of_not_lt (hd.csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le hd.le_csSup ⟨b, H⟩ ha
-/
protected theorem DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (hd : DirectedOn (· <= ·) s) (hs : s.Nonempty) (H : forall a in s, a <= b)
    (H' : forall w, w < b -> exists a in s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (hd.csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le hd.le_csSup ⟨b, H⟩ ha

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
@[to_dual DirectedOn.csInf_lt_of_lt
/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/ ]
/--
theorem `DirectedOn.lt_csSup_of_lt` / 定理 `DirectedOn.lt_csSup_of_lt`

English:
theorem DirectedOn.lt_csSup_of_lt
  statement: (hd : DirectedOn (· <= ·) s) (hs : BddAbove s)
  proof: lt_of_lt_of_le h (hd.le_csSup hs ha)

中文:
定理 DirectedOn.lt_csSup_of_lt
  结论: (hd : DirectedOn (· <= ·) s) (hs : BddAbove s)
  证明: lt_of_lt_of_le h (hd.le_csSup hs ha)
-/
protected theorem DirectedOn.lt_csSup_of_lt (hd : DirectedOn (· <= ·) s) (hs : BddAbove s)
    (ha : a in s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (hd.le_csSup hs ha)

/-- The supremum of a singleton is the element of the singleton -/
@[to_dual (attr := simp)]
/--
theorem `csSup_singleton` / 定理 `csSup_singleton`

English:
theorem csSup_singleton
  given: (a : α)
  statement: sSup {a} = a
  proof: isGreatest_singleton.csSup_eq

@[simp]

中文:
定理 csSup_singleton
  条件: (a : α)
  结论: sSup {a} = a
  证明: isGreatest_singleton.csSup_eq

@[simp]

Depends on / 依赖: csSup_eq, isGreatest_singleton, isGreatest_singleton.csSup_eq
-/
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq

@[simp]
/--
theorem `csInf_Ici` / 定理 `csInf_Ici`

English:
theorem csInf_Ici
  given: {α : Type*} [ConditionallyCompletePartialOrderInf α] {a : α}
  proof: isLeast_Ici.csInf_eq

@[simp]

中文:
定理 csInf_Ici
  条件: {α : 类型} [余nditionallyCompletePartialOrderInf α] {a : α}
  证明: isLeast_Ici.csInf_eq

@[simp]

Depends on / 依赖: csInf_eq, isLeast_Ici, isLeast_Ici.csInf_eq
-/
theorem csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α] {a : α} :
    sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq

@[simp]
/--
theorem `csInf_Ico` / 定理 `csInf_Ico`

English:
theorem csInf_Ico
  given: {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (h : a < b)
  proof: (isLeast_Ico h).csInf_eq

@[simp]

中文:
定理 csInf_Ico
  条件: {α : 类型} [余nditionallyCompletePartialOrderInf α] {a b : α} (h : a < b)
  证明: (isLeast_Ico h).csInf_eq

@[simp]

Depends on / 依赖: csInf_eq, isLeast_Ico
-/
theorem csInf_Ico {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (h : a < b) :
    sInf (Ico a b) = a :=
  (isLeast_Ico h).csInf_eq

@[simp]
/--
theorem `csInf_Icc` / 定理 `csInf_Icc`

English:
theorem csInf_Icc
  statement: {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α}
  proof: (isLeast_Icc h).csInf_eq

@[to_dual existing, simp]

中文:
定理 csInf_Icc
  结论: {α : 类型} [余nditionallyCompletePartialOrderInf α] {a b : α}
  证明: (isLeast_Icc h).csInf_eq

@[to_dual existing, simp]

Depends on / 依赖: csInf_eq, isLeast_Icc
-/
theorem csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α}
    (h : a <= b) : sInf (Icc a b) = a :=
  (isLeast_Icc h).csInf_eq

@[to_dual existing, simp]
/--
theorem `csSup_Iic` / 定理 `csSup_Iic`

English:
theorem csSup_Iic
  statement: sSup (Iic a) = a
  proof: isGreatest_Iic.csSup_eq

@[to_dual existing, simp]

中文:
定理 csSup_Iic
  结论: sSup (左无界右闭区间 a) = a
  证明: isGreatest_Iic.csSup_eq

@[to_dual existing, simp]

Depends on / 依赖: csSup_eq, isGreatest_Iic, isGreatest_Iic.csSup_eq
-/
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq

@[to_dual existing, simp]
/--
theorem `csSup_Ioc` / 定理 `csSup_Ioc`

English:
theorem csSup_Ioc
  given: (h : a < b)
  statement: sSup (Ioc a b) = b
  proof: (isGreatest_Ioc h).csSup_eq

@[simp]

中文:
定理 csSup_Ioc
  条件: (h : a < b)
  结论: sSup (左开右闭区间 a b) = b
  证明: (isGreatest_Ioc h).csSup_eq

@[simp]

Depends on / 依赖: csSup_eq, isGreatest_Ioc
-/
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isGreatest_Ioc h).csSup_eq

@[simp]
/--
theorem `csSup_Icc` / 定理 `csSup_Icc`

English:
theorem csSup_Icc
  given: {a b : α} (h : a <= b)
  statement: sSup (Icc a b) = b
  proof: (isGreatest_Icc h).csSup_eq

@[to_dual]

中文:
定理 csSup_Icc
  条件: {a b : α} (h : a <= b)
  结论: sSup (闭区间 a b) = b
  证明: (isGreatest_Icc h).csSup_eq

@[to_dual]

Depends on / 依赖: csSup_eq, isGreatest_Icc
-/
theorem csSup_Icc {a b : α} (h : a <= b) : sSup (Icc a b) = b :=
  (isGreatest_Icc h).csSup_eq

@[to_dual]
/--
lemma `sup_eq_top_of_top_mem` / 引理 `sup_eq_top_of_top_mem`

English:
lemma sup_eq_top_of_top_mem
  given: [OrderTop α] (h : ⊤ in s)
  statement: sSup s = ⊤
  proof: IsGreatest.csSup_eq ⟨h, fun _ _ => le_top⟩

中文:
引理 sup_eq_top_of_top_mem
  条件: [有顶序 α] (h : ⊤ in s)
  结论: sSup s = ⊤
  证明: IsGreatest.csSup_eq ⟨h, fun _ _ => le_top⟩

Depends on / 依赖: IsGreatest, IsGreatest.csSup_eq, csSup_eq, le_top
-/
lemma sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ in s) : sSup s = ⊤ :=
  IsGreatest.csSup_eq ⟨h, fun _ _ => le_top⟩

end ConditionallyCompletePartialOrderSup

section ConditionallyCompletePartialOrder

variable [ConditionallyCompletePartialOrder α] {s t : Set α} {a b : α}

/--
theorem `DirectedOn.subset_Icc_csInf_csSup` / 定理 `DirectedOn.subset_Icc_csInf_csSup`

English:
theorem DirectedOn.subset_Icc_csInf_csSup
  statement: (hdb : DirectedOn (· >= ·) s)
  proof: fun _ hx => ⟨hdb.csInf_le hb hx, hda.le_csSup ha hx⟩

中文:
定理 DirectedOn.subset_Icc_csInf_csSup
  结论: (hdb : DirectedOn (· >= ·) s)
  证明: fun _ hx => ⟨hdb.csInf_le hb hx, hda.le_csSup ha hx⟩
-/
protected theorem DirectedOn.subset_Icc_csInf_csSup (hdb : DirectedOn (· >= ·) s)
    (hda : DirectedOn (· <= ·) s) (hb : BddBelow s) (ha : BddAbove s) :
    s subseteq Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨hdb.csInf_le hb hx, hda.le_csSup ha hx⟩

/--
theorem `DirectedOn.csInf_le_csSup` / 定理 `DirectedOn.csInf_le_csSup`

English:
theorem DirectedOn.csInf_le_csSup
  statement: (hdb : DirectedOn (· >= ·) s)
  proof: isGLB_le_isLUB (hdb.isGLB_csInf ne hb) (hda.isLUB_csSup ne ha) ne

中文:
定理 DirectedOn.csInf_le_csSup
  结论: (hdb : DirectedOn (· >= ·) s)
  证明: isGLB_le_isLUB (hdb.isGLB_csInf ne hb) (hda.isLUB_csSup ne ha) ne
-/
protected theorem DirectedOn.csInf_le_csSup (hdb : DirectedOn (· >= ·) s)
    (hda : DirectedOn (· <= ·) s) (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) :
    sInf s <= sSup s :=
  isGLB_le_isLUB (hdb.isGLB_csInf ne hb) (hda.isLUB_csSup ne ha) ne

end ConditionallyCompletePartialOrder
