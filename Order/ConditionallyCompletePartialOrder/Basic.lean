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

/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ConditionallyCompletePartialOrderSup α] :
    ConditionallyCompletePartialOrderInf αᵒᵈ where
  isGLB_csInf_of_directed _ h_dir h_non h_bdd := h_dir.isLUB_csSup (α := α) h_non h_bdd
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ConditionallyCompletePartialOrderInf α] :
    ConditionallyCompletePartialOrderSup αᵒᵈ where
  isLUB_csSup_of_directed _ h_dir h_non h_bdd := h_dir.isGLB_csInf (α := α) h_non h_bdd
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder αᵒᵈ where

end OrderDual

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {s t : Set α} {a b : α}

@[to_dual csInf_le_of_le]
/-
**DirectedOn.le_csSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a b : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAbove s → b ∈ s → a ≤ b
 → a ≤ sSup s
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.le_csSup_of_le (hd : DirectedOn (· ≤ ·) s)
    (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (hd.le_csSup hs hb)

@[to_dual (attr := gcongr low)]
/-
**DirectedOn.csSup_le_csSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s t : Se
t α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s →     DirectedOn (fun x1 x2 => x1 ≤ 
x2) t → BddAbove t → s.Nonempty → s ⊆ t → sSup s ≤ sSup t
参数：fun x1 x2 => x1 ≤ x2；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.csSup_le`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Non
empty → (…
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.csSup_le_csSup (hds : DirectedOn (· ≤ ·) s)
    (hdt : DirectedOn (· ≤ ·) t) (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) :
    sSup s ≤ sSup t :=
  hds.csSup_le hs fun _ ha => hdt.le_csSup ht (h ha)

@[to_dual csInf_le_iff]
/-
**DirectedOn.le_csSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAbove s → s.Nonempty → (a
 ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b)
参数：fun x1 x2 => x1 ≤ x2；a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `DirectedOn.csSup_le`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Non
empty → (…
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.le_csSup_iff (hd : DirectedOn (· ≤ ·) s) (h : BddAbove s)
    (hs : s.Nonempty) : a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (hd.csSup_le hs hb), fun hb => hb _ fun _ => hd.le_csSup h⟩

@[to_dual]
/-
**IsGreatest.directedOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.directedOn (H : IsGreatest s a) : DirectedOn (· <= ·) s
参数：H : IsGreatest s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsGreatest.directedOn (H : IsGreatest s a) : DirectedOn (· ≤ ·) s :=
  fun _ h₁ _ h₂ ↦ ⟨a, H.1, H.2 h₁, H.2 h₂⟩

/-- A greatest element of a set is the supremum of this set. -/
@[to_dual /-- A least element of a set is the infimum of this set. -/]
/-
**IsGreatest.csSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a
参数：H : IsGreatest s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
· 使用定理 `IsGreatest.directedOn`：IsGreatest.directedOn (H : IsGreatest s a) : Dire
ctedOn (· <= ·) s
· 使用定理 `IsGreatest.nonempty`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a
 : α}, IsGreatest s a → s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a

--- 原说明 ---
A greatest element of a set is the supremum of this set.
-/
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.directedOn.isLUB_csSup H.nonempty ⟨a, H.2⟩ |>.unique H.isLUB

@[to_dual]
/-
**IsGreatest.csSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s in s
参数：H : IsGreatest s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
-/
theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1

@[to_dual le_csInf_iff]
/-
**DirectedOn.csSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAbove s → s.Nonempty → (s
Sup s ≤ a ↔ ∀ b ∈ s, b ≤ a)
参数：fun x1 x2 => x1 ≤ x2；sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
-/
protected theorem DirectedOn.csSup_le_iff (hd : DirectedOn (· ≤ ·) s)
    (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (hd.isLUB_csSup hs hb)

@[to_dual notMem_of_lt_csInf]
/-
**DirectedOn.notMem_of_csSup_lt** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {x : α} {
s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → sSup s < x → BddAbove s → x 
∉ s
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.notMem_of_csSup_lt {x : α} {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  fun hx ↦ lt_irrefl _ <| (hd.le_csSup hs hx).trans_lt h

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual DirectedOn.csInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/ ]
/-
**DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命
名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {b : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty → (∀ a ∈ s, a ≤ b
) → (∀ w < b, ∃ a ∈ s, w < a) → sSup s = b
参数：fun x1 x2 => x1 ≤ x2；∀ a ∈ s, a ≤ b；∀ w < b, ∃ a ∈ s, w < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `DirectedOn.csSup_le`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Non
empty → (…
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (hd : DirectedOn (· ≤ ·) s) (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (hd.csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| hd.le_csSup ⟨b, H⟩ ha

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
/-
**DirectedOn.lt_csSup_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a b : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAbove s → a ∈ s → b < a
 → b < sSup s
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.lt_csSup_of_lt (hd : DirectedOn (· ≤ ·) s) (hs : BddAbove s)
    (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (hd.le_csSup hs ha)

/-- The supremum of a singleton is the element of the singleton -/
@[to_dual (attr := simp)]
/-
**csSup_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_singleton (a : α) : sSup {a} = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `isGreatest_singleton`：isGreatest_singleton : IsGreatest {a} a

--- 原说明 ---
The supremum of a singleton is the element of the singleton
-/
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq

@[simp]
/-
**csInf_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α] {a : α} : s
Inf (Ici a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a
-/
theorem csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α] {a : α} :
    sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq

@[simp]
/-
**csInf_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_Ico {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (
h : a < b) : sInf (Ico a b) = a
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `isLeast_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → IsL
east (Set.Ico b a) b
-/
theorem csInf_Ico {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (h : a < b) :
    sInf (Ico a b) = a :=
  (isLeast_Ico h).csInf_eq

@[simp]
/-
**csInf_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (
h : a <= b) : sInf (Icc a b) = a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `isLeast_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ a → IsL
east (Set.Icc b a) b
-/
theorem csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α}
    (h : a ≤ b) : sInf (Icc a b) = a :=
  (isLeast_Icc h).csInf_eq

@[to_dual existing, simp]
/-
**csSup_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Iic : sSup (Iic a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `isGreatest_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGreatest
 (Set.Iic a) a
-/
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq

@[to_dual existing, simp]
/-
**csSup_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Ioc (h : a < b) : sSup (Ioc a b) = b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `isGreatest_Ioc`：isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b
-/
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isGreatest_Ioc h).csSup_eq

@[simp]
/-
**csSup_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Icc {a b : α} (h : a <= b) : sSup (Icc a b) = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `isGreatest_Icc`：isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b
-/
theorem csSup_Icc {a b : α} (h : a ≤ b) : sSup (Icc a b) = b :=
  (isGreatest_Icc h).csSup_eq

@[to_dual]
/-
**sup_eq_top_of_top_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ in s) : sSup s = ⊤
参数：h : ⊤ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ ∈ s) : sSup s = ⊤ :=
  IsGreatest.csSup_eq ⟨h, fun _ _ ↦ le_top⟩

end ConditionallyCompletePartialOrderSup

section ConditionallyCompletePartialOrder

variable [ConditionallyCompletePartialOrder α] {s t : Set α} {a b : α}

/-
**DirectedOn.subset_Icc_csInf_csSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrder α] {s : Set α},
   DirectedOn (fun x1 x2 => x1 ≥ x2) s →     DirectedOn (fun x1 x2 => x1 ≤ x2) s
 → BddBelow s → BddAbove s → s ⊆ Set.Icc (sInf s) (sSup s)
参数：fun x1 x2 => x1 ≥ x2；fun x1 x2 => x1 ≤ x2；sInf s；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.csInf_le`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderInf α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x2 ≤ x1) s → BddBe
low s → a…
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
-/
protected theorem DirectedOn.subset_Icc_csInf_csSup (hdb : DirectedOn (· ≥ ·) s)
    (hda : DirectedOn (· ≤ ·) s) (hb : BddBelow s) (ha : BddAbove s) :
    s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨hdb.csInf_le hb hx, hda.le_csSup ha hx⟩

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
/-
**DirectedOn.csInf_le_csSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrder α] {s : Set α},
   DirectedOn (fun x1 x2 => x1 ≥ x2) s →     DirectedOn (fun x1 x2 => x1 ≤ x2) s
 → BddBelow s → BddAbove s → s.Nonempty → sInf s ≤ sSup s
参数：fun x1 x2 => x1 ≥ x2；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_le_isLUB`：isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s
.Nonempty) : a <= b
· 使用定理 `DirectedOn.isGLB_csInf`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderInf α] {s : Set α},   DirectedOn (fun x1 x2 => x2 ≤ x1) s → s.Nonempty
 → BddBelow …
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …

--- 原说明 ---
If a set is bounded below and above, and nonempty, its infimum is less than or e
qual to
its supremum.
-/
protected theorem DirectedOn.csInf_le_csSup (hdb : DirectedOn (· ≥ ·) s)
    (hda : DirectedOn (· ≤ ·) s) (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) :
    sInf s ≤ sSup s :=
  isGLB_le_isLUB (hdb.isGLB_csInf ne hb) (hda.isLUB_csSup ne ha) ne

end ConditionallyCompletePartialOrder

