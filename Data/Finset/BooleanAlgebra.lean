/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs

/-!
# `Finset`s are a Boolean algebra

This file provides the `BooleanAlgebra (Finset α)` instance, under the assumption that `α` is a
`Fintype`.

## Main results

* `Finset.boundedOrder`: `Finset.univ` is the top element of `Finset α`
* `Finset.booleanAlgebra`: `Finset α` is a Boolean algebra if `α` is finite
-/

public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

namespace Finset

variable {s t : Finset α}

section Fintypeα

variable [Fintype α]

/--
theorem `Nonempty.eq_univ` / 定理 `Nonempty.eq_univ`

English:
theorem Nonempty.eq_univ
  given: [Subsingleton α]
  statement: s.Nonempty -> s = univ
  proof: by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

中文:
定理 Nonempty.eq_univ
  条件: [Subsingleton α]
  结论: s.Nonempty -> s = univ
  证明: by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

Depends on / 依赖: Subsingleton, Subsingleton.elim, eq_univ_of_forall
-/
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty -> s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

/--
theorem `univ_nonempty_iff` / 定理 `univ_nonempty_iff`

English:
theorem univ_nonempty_iff
  statement: (univ : Finset α).Nonempty ↔ Nonempty α
  proof: by
  rw [← coe_nonempty]; rw [coe_univ]; rw [Set.nonempty_iff_univ_nonempty]

@[simp, aesop unsafe apply (rule_sets := [finsetNonempty])]

中文:
定理 univ_nonempty_iff
  结论: (univ : Finset α).Nonempty ↔ Nonempty α
  证明: by
  rw [← coe_nonempty]; rw [coe_univ]; rw [Set.nonempty_iff_univ_nonempty]

@[simp, aesop unsafe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: Set.nonempty_iff_univ_nonempty, coe_nonempty, coe_univ, nonempty_iff_univ_nonempty
-/
theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty]; rw [coe_univ]; rw [Set.nonempty_iff_univ_nonempty]

@[simp, aesop unsafe apply (rule_sets := [finsetNonempty])]
/--
theorem `univ_nonempty` / 定理 `univ_nonempty`

English:
theorem univ_nonempty
  given: [Nonempty α]
  statement: (univ : Finset α).Nonempty
  proof: univ_nonempty_iff.2 ‹_›

中文:
定理 univ_nonempty
  条件: [Nonempty α]
  结论: (univ : Finset α).Nonempty
  证明: univ_nonempty_iff.2 ‹_›

Depends on / 依赖: univ_nonempty_iff
-/
theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›

/--
theorem `univ_eq_empty_iff` / 定理 `univ_eq_empty_iff`

English:
theorem univ_eq_empty_iff
  statement: (univ : Finset α) = ∅ ↔ IsEmpty α
  proof: by
  contrapose!; exact univ_nonempty_iff

中文:
定理 univ_eq_empty_iff
  结论: (univ : Finset α) = ∅ ↔ IsEmpty α
  证明: by
  contrapose!; exact univ_nonempty_iff

Depends on / 依赖: contrapose, univ_nonempty_iff
-/
theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  contrapose!; exact univ_nonempty_iff

/--
theorem `univ_nontrivial_iff` / 定理 `univ_nontrivial_iff`

English:
theorem univ_nontrivial_iff
  proof: by
  rw [Finset.Nontrivial]; rw [Finset.coe_univ]; rw [Set.nontrivial_univ_iff]

中文:
定理 univ_nontrivial_iff
  证明: by
  rw [Finset.Nontrivial]; rw [Finset.coe_univ]; rw [Set.nontrivial_univ_iff]

Depends on / 依赖: Finset, Finset.Nontrivial, Finset.coe_univ, Nontrivial, Set.nontrivial_univ_iff, coe_univ, nontrivial_univ_iff
-/
theorem univ_nontrivial_iff :
    (Finset.univ : Finset α).Nontrivial ↔ Nontrivial α := by
  rw [Finset.Nontrivial]; rw [Finset.coe_univ]; rw [Set.nontrivial_univ_iff]

/--
lemma `univ_neq_empty` / 引理 `univ_neq_empty`

English:
lemma univ_neq_empty
  given: (α : Type*) [Fintype α] [Nonempty α]
  proof: fun h => (Finset.univ_eq_empty_iff.1 h).elim (Classical.arbitrary _)

中文:
引理 univ_neq_empty
  条件: (α : 类型) [Fintype α] [Nonempty α]
  证明: fun h => (Finset.univ_eq_empty_iff.1 h).elim (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, Finset, Finset.univ_eq_empty_iff, arbitrary, univ_eq_empty_iff
-/
lemma univ_neq_empty (α : Type*) [Fintype α] [Nonempty α] :
    (Finset.univ : Finset α) != ∅ :=
  fun h => (Finset.univ_eq_empty_iff.1 h).elim (Classical.arbitrary _)

/--
theorem `univ_nontrivial` / 定理 `univ_nontrivial`

English:
theorem univ_nontrivial
  given: [h : Nontrivial α]
  proof: univ_nontrivial_iff.mpr h

中文:
定理 univ_nontrivial
  条件: [h : Nontrivial α]
  证明: univ_nontrivial_iff.mpr h

Depends on / 依赖: univ_nontrivial_iff, univ_nontrivial_iff.mpr
-/
theorem univ_nontrivial [h : Nontrivial α] :
    (Finset.univ : Finset α).Nontrivial :=
  univ_nontrivial_iff.mpr h

/--
lemma `singleton_ne_univ` / 引理 `singleton_ne_univ`

English:
lemma singleton_ne_univ
  given: [Nontrivial α] (a : α)
  statement: {a} != univ
  proof: by
  apply SetLike.coe_ne_coe.1
  simp

@[simp]

中文:
引理 singleton_ne_univ
  条件: [Nontrivial α] (a : α)
  结论: {a} != univ
  证明: by
  apply SetLike.coe_ne_coe.1
  simp

@[simp]
-/
@[simp] lemma singleton_ne_univ [Nontrivial α] (a : α) : {a} != univ := by
  apply SetLike.coe_ne_coe.1
  simp

@[simp]
/--
theorem `univ_eq_empty` / 定理 `univ_eq_empty`

English:
theorem univ_eq_empty
  given: [IsEmpty α]
  statement: (univ : Finset α) = ∅
  proof: univ_eq_empty_iff.2 ‹_›

@[simp]

中文:
定理 univ_eq_empty
  条件: [IsEmpty α]
  结论: (univ : Finset α) = ∅
  证明: univ_eq_empty_iff.2 ‹_›

@[simp]

Depends on / 依赖: univ_eq_empty_iff
-/
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
/--
theorem `univ_unique` / 定理 `univ_unique`

English:
theorem univ_unique
  given: [Unique α]
  statement: (univ : Finset α) = {default}
  proof: Finset.ext fun x => iff_of_true (mem_univ _) mem_singleton.2 Subsingleton.elim x default

中文:
定理 univ_unique
  条件: [Unique α]
  结论: (univ : Finset α) = {default}
  证明: Finset.ext fun x => iff_of_true (mem_univ _) mem_singleton.2 Subsingleton.elim x default

Depends on / 依赖: Finset, Finset.ext, Subsingleton, Subsingleton.elim, iff_of_true, mem_singleton, mem_univ
-/
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
Finset.ext fun x => iff_of_true (mem_univ _) mem_singleton.2 Subsingleton.elim x default

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: : BoundedOrder (Finset α)
  body: { (inferInstance : OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]

中文:
实例 boundedOrder
  签名: : BoundedOrder (Finset α)
  定义体: { (inferInstance : OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]

Depends on / 依赖: Finset, OrderBot, le_top, subset_univ
-/
instance boundedOrder : BoundedOrder (Finset α) :=
  { (inferInstance : OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]
/--
theorem `top_eq_univ` / 定理 `top_eq_univ`

English:
theorem top_eq_univ
  statement: (⊤ : Finset α) = univ
  proof: rfl

中文:
定理 top_eq_univ
  结论: (⊤ : Finset α) = univ
  证明: rfl
-/
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl

/--
theorem `ssubset_univ_iff` / 定理 `ssubset_univ_iff`

English:
theorem ssubset_univ_iff
  given: {s : Finset α}
  statement: s ⊂ univ ↔ s != univ
  proof: lt_top_iff_ne_top

@[simp]

中文:
定理 ssubset_univ_iff
  条件: {s : Finset α}
  结论: s ⊂ univ ↔ s != univ
  证明: lt_top_iff_ne_top

@[simp]

Depends on / 依赖: lt_top_iff_ne_top
-/
theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s != univ :=
  lt_top_iff_ne_top

@[simp]
/--
theorem `univ_subset_iff` / 定理 `univ_subset_iff`

English:
theorem univ_subset_iff
  given: {s : Finset α}
  statement: univ subseteq s ↔ s = univ
  proof: top_le_iff

中文:
定理 univ_subset_iff
  条件: {s : Finset α}
  结论: univ subseteq s ↔ s = univ
  证明: top_le_iff

Depends on / 依赖: top_le_iff
-/
theorem univ_subset_iff {s : Finset α} : univ subseteq s ↔ s = univ :=
  top_le_iff

/--
theorem `codisjoint_left` / 定理 `codisjoint_left`

English:
theorem codisjoint_left
  statement: Codisjoint s t ↔ forall ⦃a⦄, a ∉ s -> a in t
  proof: by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]

中文:
定理 codisjoint_left
  结论: Codisjoint s t ↔ 对任意 ⦃a⦄, a ∉ s -> a in t
  证明: by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]

Depends on / 依赖: classical, codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left
-/
theorem codisjoint_left : Codisjoint s t ↔ forall ⦃a⦄, a ∉ s -> a in t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]

/--
theorem `codisjoint_right` / 定理 `codisjoint_right`

English:
theorem codisjoint_right
  statement: Codisjoint s t ↔ forall ⦃a⦄, a ∉ t -> a in s
  proof: codisjoint_comm.trans codisjoint_left

中文:
定理 codisjoint_right
  结论: Codisjoint s t ↔ 对任意 ⦃a⦄, a ∉ t -> a in s
  证明: codisjoint_comm.trans codisjoint_left

Depends on / 依赖: codisjoint_comm, codisjoint_comm.trans, codisjoint_left
-/
theorem codisjoint_right : Codisjoint s t ↔ forall ⦃a⦄, a ∉ t -> a in s :=
  codisjoint_comm.trans codisjoint_left

/--
Instance `booleanAlgebra` / 实例 `booleanAlgebra`

English:
instance booleanAlgebra
  signature: [DecidableEq α]
  body: GeneralizedBooleanAlgebra.toBooleanAlgebra

中文:
实例 booleanAlgebra
  签名: [DecidableEq α]
  定义体: GeneralizedBooleanAlgebra.toBooleanAlgebra

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.toBooleanAlgebra, toBooleanAlgebra
-/
instance booleanAlgebra [DecidableEq α] : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra

section BooleanAlgebra
variable [DecidableEq α] {a : α}

open symmDiff

/--
theorem `sdiff_eq_inter_compl` / 定理 `sdiff_eq_inter_compl`

English:
theorem sdiff_eq_inter_compl
  given: (s t : Finset α)
  statement: s \ t = s inter tᶜ
  proof: sdiff_eq

中文:
定理 sdiff_eq_inter_compl
  条件: (s t : Finset α)
  结论: s \ t = s inter tᶜ
  证明: sdiff_eq

Depends on / 依赖: sdiff_eq
-/
theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s inter tᶜ :=
  sdiff_eq

/--
theorem `compl_eq_univ_sdiff` / 定理 `compl_eq_univ_sdiff`

English:
theorem compl_eq_univ_sdiff
  given: (s : Finset α)
  statement: sᶜ = univ \ s
  proof: rfl

@[simp]

中文:
定理 compl_eq_univ_sdiff
  条件: (s : Finset α)
  结论: sᶜ = univ \ s
  证明: rfl

@[simp]
-/
theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl

@[simp]
/--
theorem `mem_compl` / 定理 `mem_compl`

English:
theorem mem_compl
  statement: a in sᶜ ↔ a ∉ s
  proof: by simp [compl_eq_univ_sdiff]

中文:
定理 mem_compl
  结论: a in sᶜ ↔ a ∉ s
  证明: by simp [compl_eq_univ_sdiff]

Depends on / 依赖: compl_eq_univ_sdiff
-/
theorem mem_compl : a in sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]

/--
theorem `notMem_compl` / 定理 `notMem_compl`

English:
theorem notMem_compl
  statement: a ∉ sᶜ ↔ a in s
  proof: by rw [mem_compl, not_not]

中文:
定理 notMem_compl
  结论: a ∉ sᶜ ↔ a in s
  证明: by rw [mem_compl, not_not]

Depends on / 依赖: mem_compl, not_not
-/
theorem notMem_compl : a ∉ sᶜ ↔ a in s := by rw [mem_compl, not_not]

/--
theorem `mem_himp_iff` / 定理 `mem_himp_iff`

English:
theorem mem_himp_iff
  statement: a in s ⇨ t ↔ a in s -> a in t
  proof: by simp [himp_eq, imp_iff_or_not]

中文:
定理 mem_himp_iff
  结论: a in s ⇨ t ↔ a in s -> a in t
  证明: by simp [himp_eq, imp_iff_or_not]
-/
@[simp] theorem mem_himp_iff : a in s ⇨ t ↔ a in s -> a in t := by simp [himp_eq, imp_iff_or_not]

/--
theorem `himp_def` / 定理 `himp_def`

English:
theorem himp_def
  statement: s ⇨ t = t union sᶜ
  proof: himp_eq ..

中文:
定理 himp_def
  结论: s ⇨ t = t union sᶜ
  证明: himp_eq ..
-/
protected theorem himp_def : s ⇨ t = t union sᶜ := himp_eq ..

/--
theorem `mem_bihimp_iff` / 定理 `mem_bihimp_iff`

English:
theorem mem_bihimp_iff
  statement: a in s ⇔ t ↔ (a in s ↔ a in t)
  proof: by simp [bihimp, iff_def']

中文:
定理 mem_bihimp_iff
  结论: a in s ⇔ t ↔ (a in s ↔ a in t)
  证明: by simp [bihimp, iff_def']
-/
@[simp] theorem mem_bihimp_iff : a in s ⇔ t ↔ (a in s ↔ a in t) := by simp [bihimp, iff_def']

/--
theorem `bihimp_def` / 定理 `bihimp_def`

English:
theorem bihimp_def
  statement: s ⇔ t = (s union tᶜ) inter (t union sᶜ)
  proof: bihimp_eq ..

@[simp, norm_cast]

中文:
定理 bihimp_def
  结论: s ⇔ t = (s union tᶜ) inter (t union sᶜ)
  证明: bihimp_eq ..

@[simp, norm_cast]
-/
protected theorem bihimp_def : s ⇔ t = (s union tᶜ) inter (t union sᶜ) := bihimp_eq ..

@[simp, norm_cast]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (s : Finset α)
  statement: ↑sᶜ = (↑s : Set α)ᶜ
  proof: Set.ext fun _ => mem_compl

中文:
定理 coe_compl
  条件: (s : Finset α)
  结论: ↑sᶜ = (↑s : Set α)ᶜ
  证明: Set.ext fun _ => mem_compl

Depends on / 依赖: Set.ext, mem_compl
-/
theorem coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ :=
  Set.ext fun _ => mem_compl

/--
lemma `compl_subset_compl` / 引理 `compl_subset_compl`

English:
lemma compl_subset_compl
  statement: sᶜ subseteq tᶜ ↔ t subseteq s
  proof: compl_le_compl_iff_le

中文:
引理 compl_subset_compl
  结论: sᶜ subseteq tᶜ ↔ t subseteq s
  证明: compl_le_compl_iff_le

Depends on / 依赖: compl_le_compl_iff_le
-/
lemma compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq s := compl_le_compl_iff_le
/--
lemma `compl_ssubset_compl` / 引理 `compl_ssubset_compl`

English:
lemma compl_ssubset_compl
  statement: sᶜ ⊂ tᶜ ↔ t ⊂ s
  proof: compl_lt_compl_iff_lt

中文:
引理 compl_ssubset_compl
  结论: sᶜ ⊂ tᶜ ↔ t ⊂ s
  证明: compl_lt_compl_iff_lt

Depends on / 依赖: compl_lt_compl_iff_lt
-/
lemma compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := compl_lt_compl_iff_lt

/--
lemma `subset_compl_comm` / 引理 `subset_compl_comm`

English:
lemma subset_compl_comm
  statement: s subseteq tᶜ ↔ t subseteq sᶜ
  proof: le_compl_iff_le_compl

中文:
引理 subset_compl_comm
  结论: s subseteq tᶜ ↔ t subseteq sᶜ
  证明: le_compl_iff_le_compl

Depends on / 依赖: le_compl_iff_le_compl
-/
lemma subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ := le_compl_iff_le_compl

/--
lemma `subset_compl_iff_disjoint_right` / 引理 `subset_compl_iff_disjoint_right`

English:
lemma subset_compl_iff_disjoint_right
  statement: s subseteq tᶜ ↔ Disjoint s t
  proof: le_compl_iff_disjoint_right

中文:
引理 subset_compl_iff_disjoint_right
  结论: s subseteq tᶜ ↔ Disjoint s t
  证明: le_compl_iff_disjoint_right

Depends on / 依赖: le_compl_iff_disjoint_right
-/
lemma subset_compl_iff_disjoint_right : s subseteq tᶜ ↔ Disjoint s t :=
  le_compl_iff_disjoint_right

/--
lemma `subset_compl_iff_disjoint_left` / 引理 `subset_compl_iff_disjoint_left`

English:
lemma subset_compl_iff_disjoint_left
  statement: s subseteq tᶜ ↔ Disjoint t s
  proof: le_compl_iff_disjoint_left

中文:
引理 subset_compl_iff_disjoint_left
  结论: s subseteq tᶜ ↔ Disjoint t s
  证明: le_compl_iff_disjoint_left

Depends on / 依赖: le_compl_iff_disjoint_left
-/
lemma subset_compl_iff_disjoint_left : s subseteq tᶜ ↔ Disjoint t s :=
  le_compl_iff_disjoint_left

/--
lemma `subset_compl_singleton` / 引理 `subset_compl_singleton`

English:
lemma subset_compl_singleton
  statement: s subseteq {a}ᶜ ↔ a ∉ s
  proof: by
  rw [subset_compl_comm]; rw [singleton_subset_iff]; rw [mem_compl]

@[simp]

中文:
引理 subset_compl_singleton
  结论: s subseteq {a}ᶜ ↔ a ∉ s
  证明: by
  rw [subset_compl_comm]; rw [singleton_subset_iff]; rw [mem_compl]

@[simp]
-/
@[simp] lemma subset_compl_singleton : s subseteq {a}ᶜ ↔ a ∉ s := by
  rw [subset_compl_comm]; rw [singleton_subset_iff]; rw [mem_compl]

@[simp]
/--
theorem `compl_empty` / 定理 `compl_empty`

English:
theorem compl_empty
  statement: (∅ : Finset α)ᶜ = univ
  proof: compl_bot

@[simp]

中文:
定理 compl_empty
  结论: (∅ : Finset α)ᶜ = univ
  证明: compl_bot

@[simp]

Depends on / 依赖: compl_bot
-/
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot

@[simp]
/--
theorem `compl_univ` / 定理 `compl_univ`

English:
theorem compl_univ
  statement: (univ : Finset α)ᶜ = ∅
  proof: compl_top

@[simp]

中文:
定理 compl_univ
  结论: (univ : Finset α)ᶜ = ∅
  证明: compl_top

@[simp]

Depends on / 依赖: compl_top
-/
theorem compl_univ : (univ : Finset α)ᶜ = ∅ :=
  compl_top

@[simp]
/--
theorem `compl_eq_empty_iff` / 定理 `compl_eq_empty_iff`

English:
theorem compl_eq_empty_iff
  given: (s : Finset α)
  statement: sᶜ = ∅ ↔ s = univ
  proof: compl_eq_bot

@[simp]

中文:
定理 compl_eq_empty_iff
  条件: (s : Finset α)
  结论: sᶜ = ∅ ↔ s = univ
  证明: compl_eq_bot

@[simp]

Depends on / 依赖: compl_eq_bot
-/
theorem compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
/--
theorem `compl_eq_univ_iff` / 定理 `compl_eq_univ_iff`

English:
theorem compl_eq_univ_iff
  given: (s : Finset α)
  statement: sᶜ = univ ↔ s = ∅
  proof: compl_eq_top

@[simp]

中文:
定理 compl_eq_univ_iff
  条件: (s : Finset α)
  结论: sᶜ = univ ↔ s = ∅
  证明: compl_eq_top

@[simp]

Depends on / 依赖: compl_eq_top
-/
theorem compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

@[simp]
/--
theorem `union_compl` / 定理 `union_compl`

English:
theorem union_compl
  given: (s : Finset α)
  statement: s union sᶜ = univ
  proof: sup_compl_eq_top

@[simp]

中文:
定理 union_compl
  条件: (s : Finset α)
  结论: s union sᶜ = univ
  证明: sup_compl_eq_top

@[simp]

Depends on / 依赖: sup_compl_eq_top
-/
theorem union_compl (s : Finset α) : s union sᶜ = univ :=
  sup_compl_eq_top

@[simp]
/--
theorem `inter_compl` / 定理 `inter_compl`

English:
theorem inter_compl
  given: (s : Finset α)
  statement: s inter sᶜ = ∅
  proof: inf_compl_eq_bot

@[simp]

中文:
定理 inter_compl
  条件: (s : Finset α)
  结论: s inter sᶜ = ∅
  证明: inf_compl_eq_bot

@[simp]

Depends on / 依赖: inf_compl_eq_bot
-/
theorem inter_compl (s : Finset α) : s inter sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
/--
theorem `compl_union` / 定理 `compl_union`

English:
theorem compl_union
  given: (s t : Finset α)
  statement: (s union t)ᶜ = sᶜ inter tᶜ
  proof: compl_sup

@[simp]

中文:
定理 compl_union
  条件: (s t : Finset α)
  结论: (s union t)ᶜ = sᶜ inter tᶜ
  证明: compl_sup

@[simp]

Depends on / 依赖: compl_sup
-/
theorem compl_union (s t : Finset α) : (s union t)ᶜ = sᶜ inter tᶜ :=
  compl_sup

@[simp]
/--
theorem `compl_inter` / 定理 `compl_inter`

English:
theorem compl_inter
  given: (s t : Finset α)
  statement: (s inter t)ᶜ = sᶜ union tᶜ
  proof: compl_inf

@[simp]

中文:
定理 compl_inter
  条件: (s t : Finset α)
  结论: (s inter t)ᶜ = sᶜ union tᶜ
  证明: compl_inf

@[simp]

Depends on / 依赖: compl_inf
-/
theorem compl_inter (s t : Finset α) : (s inter t)ᶜ = sᶜ union tᶜ :=
  compl_inf

@[simp]
/--
theorem `compl_erase` / 定理 `compl_erase`

English:
theorem compl_erase
  statement: (s.erase a)ᶜ = insert a sᶜ
  proof: by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]

@[simp]

中文:
定理 compl_erase
  结论: (s.erase a)ᶜ = insert a sᶜ
  证明: by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]

@[simp]

Depends on / 依赖: mem_compl, mem_erase, mem_insert, not_and, or_iff_not_imp_left
-/
theorem compl_erase : (s.erase a)ᶜ = insert a sᶜ := by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]

@[simp]
/--
theorem `compl_insert` / 定理 `compl_insert`

English:
theorem compl_insert
  statement: (insert a s)ᶜ = sᶜ.erase a
  proof: by
  ext
  simp only [not_or, mem_insert, mem_compl, mem_erase]

中文:
定理 compl_insert
  结论: (insert a s)ᶜ = sᶜ.erase a
  证明: by
  ext
  simp only [not_or, mem_insert, mem_compl, mem_erase]

Depends on / 依赖: mem_compl, mem_erase, mem_insert, not_or
-/
theorem compl_insert : (insert a s)ᶜ = sᶜ.erase a := by
  ext
  simp only [not_or, mem_insert, mem_compl, mem_erase]

/--
theorem `insert_compl_insert` / 定理 `insert_compl_insert`

English:
theorem insert_compl_insert
  given: (ha : a ∉ s)
  statement: insert a (insert a s)ᶜ = sᶜ
  proof: by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]

中文:
定理 insert_compl_insert
  条件: (ha : a ∉ s)
  结论: insert a (insert a s)ᶜ = sᶜ
  证明: by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]

Depends on / 依赖: compl_insert, insert_erase, mem_compl, simp_rw
-/
theorem insert_compl_insert (ha : a ∉ s) : insert a (insert a s)ᶜ = sᶜ := by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]
/--
theorem `insert_compl_self` / 定理 `insert_compl_self`

English:
theorem insert_compl_self
  given: (x : α)
  statement: insert x ({x}ᶜ : Finset α) = univ
  proof: by
  rw [← compl_erase]; rw [erase_singleton]; rw [compl_empty]

@[simp]

中文:
定理 insert_compl_self
  条件: (x : α)
  结论: insert x ({x}ᶜ : Finset α) = univ
  证明: by
  rw [← compl_erase]; rw [erase_singleton]; rw [compl_empty]

@[simp]

Depends on / 依赖: compl_empty, compl_erase, erase_singleton
-/
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase]; rw [erase_singleton]; rw [compl_empty]

@[simp]
/--
theorem `compl_filter` / 定理 `compl_filter`

English:
theorem compl_filter
  given: (p : α -> Prop) [DecidablePred p] [forall x, Decidable ¬p x]
  proof: ext by simp

中文:
定理 compl_filter
  条件: (p : α -> 命题) [DecidablePred p] [对任意 x, Decidable ¬p x]
  证明: ext by simp
-/
theorem compl_filter (p : α -> Prop) [DecidablePred p] [forall x, Decidable ¬p x] :
    (univ.filter p)ᶜ = univ.filter fun x => ¬p x :=
ext by simp

/--
theorem `compl_ne_univ_iff_nonempty` / 定理 `compl_ne_univ_iff_nonempty`

English:
theorem compl_ne_univ_iff_nonempty
  given: (s : Finset α)
  statement: sᶜ != univ ↔ s.Nonempty
  proof: by
  simp [eq_univ_iff_forall, Finset.Nonempty]

中文:
定理 compl_ne_univ_iff_nonempty
  条件: (s : Finset α)
  结论: sᶜ != univ ↔ s.Nonempty
  证明: by
  simp [eq_univ_iff_forall, Finset.Nonempty]

Depends on / 依赖: Finset, Finset.Nonempty, Int.emod_lt_of_pos, Int.natCast_pos.mpr, Int.toNat_lt_toNat, Int.toNat_natCast, Nat.pos_of_ne_zero, Nonempty, Subtype, Subtype.coe_mk, chineseRemainder, coe_mk, dif_neg, emod_lt_of_pos, eq_univ_iff_forall, lcm_ne_zero, lcm_pos, natCast_pos, pos_of_ne_zero, toNat_lt_toNat
-/
theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ != univ ↔ s.Nonempty := by
  simp [eq_univ_iff_forall, Finset.Nonempty]

/--
theorem `compl_singleton` / 定理 `compl_singleton`

English:
theorem compl_singleton
  given: (a : α)
  statement: ({a} : Finset α)ᶜ = univ.erase a
  proof: by
  rw [compl_eq_univ_sdiff]; rw [sdiff_singleton_eq_erase]

中文:
定理 compl_singleton
  条件: (a : α)
  结论: ({a} : Finset α)ᶜ = univ.erase a
  证明: by
  rw [compl_eq_univ_sdiff]; rw [sdiff_singleton_eq_erase]

Depends on / 依赖: compl_eq_univ_sdiff, sdiff_singleton_eq_erase
-/
theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff]; rw [sdiff_singleton_eq_erase]

/--
theorem `insert_inj_on'` / 定理 `insert_inj_on'`

English:
theorem insert_inj_on'
  given: (s : Finset α)
  statement: Set.InjOn (fun a => insert a s) (sᶜ : Finset α)
  proof: by
  rw [coe_compl]
  exact s.insert_inj_on

中文:
定理 insert_inj_on'
  条件: (s : Finset α)
  结论: Set.InjOn (fun a => insert a s) (sᶜ : Finset α)
  证明: by
  rw [coe_compl]
  exact s.insert_inj_on

Depends on / 依赖: coe_compl, insert_inj_on, s.insert_inj_on
-/
theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) := by
  rw [coe_compl]
  exact s.insert_inj_on

/--
theorem `image_univ_of_surjective` / 定理 `image_univ_of_surjective`

English:
theorem image_univ_of_surjective
  given: [Fintype β] {f : β -> α} (hf : Surjective f)
  proof: eq_univ_of_forall hf.forall.2 fun _ => mem_image_of_mem _ mem_univ _

@[simp]

中文:
定理 image_univ_of_surjective
  条件: [Fintype β] {f : β -> α} (hf : Surjective f)
  证明: eq_univ_of_forall hf.forall.2 fun _ => mem_image_of_mem _ mem_univ _

@[simp]

Depends on / 依赖: eq_univ_of_forall, hf.forall, mem_image_of_mem, mem_univ
-/
theorem image_univ_of_surjective [Fintype β] {f : β -> α} (hf : Surjective f) :
    univ.image f = univ :=
eq_univ_of_forall hf.forall.2 fun _ => mem_image_of_mem _ mem_univ _

@[simp]
/--
theorem `image_univ_equiv` / 定理 `image_univ_equiv`

English:
theorem image_univ_equiv
  given: [Fintype β] (f : β ≃ α)
  statement: univ.image f = univ
  proof: Finset.image_univ_of_surjective f.surjective

中文:
定理 image_univ_equiv
  条件: [Fintype β] (f : β ≃ α)
  结论: univ.image f = univ
  证明: Finset.image_univ_of_surjective f.surjective

Depends on / 依赖: Finset, Finset.image_univ_of_surjective, f.surjective, image_univ_of_surjective, surjective
-/
theorem image_univ_equiv [Fintype β] (f : β ≃ α) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective

/--
lemma `univ_inter` / 引理 `univ_inter`

English:
lemma univ_inter
  given: (s : Finset α)
  statement: univ inter s = s
  proof: by ext a; simp

中文:
引理 univ_inter
  条件: (s : Finset α)
  结论: univ inter s = s
  证明: by ext a; simp
-/
@[simp] lemma univ_inter (s : Finset α) : univ inter s = s := by ext a; simp

/--
lemma `inter_univ` / 引理 `inter_univ`

English:
lemma inter_univ
  given: (s : Finset α)
  statement: s inter univ = s
  proof: by rw [inter_comm, univ_inter]

中文:
引理 inter_univ
  条件: (s : Finset α)
  结论: s inter univ = s
  证明: by rw [inter_comm, univ_inter]
-/
@[simp] lemma inter_univ (s : Finset α) : s inter univ = s := by rw [inter_comm, univ_inter]

/--
lemma `inter_eq_univ` / 引理 `inter_eq_univ`

English:
lemma inter_eq_univ
  statement: s inter t = univ ↔ s = univ ∧ t = univ
  proof: inf_eq_top_iff

中文:
引理 inter_eq_univ
  结论: s inter t = univ ↔ s = univ ∧ t = univ
  证明: inf_eq_top_iff
-/
@[simp] lemma inter_eq_univ : s inter t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff

end BooleanAlgebra

-- @[simp] --Note this would loop with `Finset.univ_unique`
/--
lemma `singleton_eq_univ` / 引理 `singleton_eq_univ`

English:
lemma singleton_eq_univ
  given: [Subsingleton α] (a : α)
  statement: ({a} : Finset α) = univ
  proof: by
  ext b; simp [Subsingleton.elim a b]

中文:
引理 singleton_eq_univ
  条件: [Subsingleton α] (a : α)
  结论: ({a} : Finset α) = univ
  证明: by
  ext b; simp [Subsingleton.elim a b]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by
  ext b; simp [Subsingleton.elim a b]


/--
theorem `map_univ_of_surjective` / 定理 `map_univ_of_surjective`

English:
theorem map_univ_of_surjective
  given: [Fintype β] {f : β ↪ α} (hf : Surjective f)
  statement: univ.map f = univ
  proof: eq_univ_of_forall hf.forall.2 fun _ => mem_map_of_mem _ mem_univ _

@[simp]

中文:
定理 map_univ_of_surjective
  条件: [Fintype β] {f : β ↪ α} (hf : Surjective f)
  结论: univ.map f = univ
  证明: eq_univ_of_forall hf.forall.2 fun _ => mem_map_of_mem _ mem_univ _

@[simp]

Depends on / 依赖: eq_univ_of_forall, hf.forall, mem_map_of_mem, mem_univ
-/
theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
eq_univ_of_forall hf.forall.2 fun _ => mem_map_of_mem _ mem_univ _

@[simp]
/--
theorem `map_univ_equiv` / 定理 `map_univ_equiv`

English:
theorem map_univ_equiv
  given: [Fintype β] (f : β ≃ α)
  statement: univ.map f.toEmbedding = univ
  proof: map_univ_of_surjective f.surjective

中文:
定理 map_univ_equiv
  条件: [Fintype β] (f : β ≃ α)
  结论: univ.map f.toEmbedding = univ
  证明: map_univ_of_surjective f.surjective

Depends on / 依赖: f.surjective, map_univ_of_surjective, surjective
-/
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.surjective

/--
theorem `univ_map_equiv_to_embedding` / 定理 `univ_map_equiv_to_embedding`

English:
theorem univ_map_equiv_to_embedding
  given: {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
  proof: eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩

@[simp]

中文:
定理 univ_map_equiv_to_embedding
  条件: {α β : 类型} [Fintype α] [Fintype β] (e : α ≃ β)
  证明: eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩

@[simp]

Depends on / 依赖: e.symm, eq_univ_iff_forall, eq_univ_iff_forall.mpr, mem_map, mem_map.mpr, mem_univ
-/
theorem univ_map_equiv_to_embedding {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩

@[simp]
/--
theorem `univ_filter_exists` / 定理 `univ_filter_exists`

English:
theorem univ_filter_exists
  statement: (f : α -> β) [Fintype β] [DecidablePred fun y => exists x, f x = y]
  proof: by
  ext
  simp

中文:
定理 univ_filter_exists
  结论: (f : α -> β) [Fintype β] [DecidablePred fun y => 存在 x, f x = y]
  证明: by
  ext
  simp
-/
theorem univ_filter_exists (f : α -> β) [Fintype β] [DecidablePred fun y => exists x, f x = y]
    [DecidableEq β] : (Finset.univ.filter fun y => exists x, f x = y) = Finset.univ.image f := by
  ext
  simp

/--
theorem `univ_filter_mem_range` / 定理 `univ_filter_mem_range`

English:
theorem univ_filter_mem_range
  statement: (f : α -> β) [Fintype β] [DecidablePred fun y => y in Set.range f]
  proof: by
  grind

中文:
定理 univ_filter_mem_range
  结论: (f : α -> β) [Fintype β] [DecidablePred fun y => y in Set.range f]
  证明: by
  grind
-/
theorem univ_filter_mem_range (f : α -> β) [Fintype β] [DecidablePred fun y => y in Set.range f]
    [DecidableEq β] : (Finset.univ.filter fun y => y in Set.range f) = Finset.univ.image f := by
  grind

/--
theorem `coe_filter_univ` / 定理 `coe_filter_univ`

English:
theorem coe_filter_univ
  given: (p : α -> Prop) [DecidablePred p]
  proof: by simp

中文:
定理 coe_filter_univ
  条件: (p : α -> 命题) [DecidablePred p]
  证明: by simp
-/
theorem coe_filter_univ (p : α -> Prop) [DecidablePred p] :
    (univ.filter p : Set α) = { x | p x } := by simp

end Fintypeα

/--
lemma `subtype_eq_univ` / 引理 `subtype_eq_univ`

English:
lemma subtype_eq_univ
  given: {p : α -> Prop} [DecidablePred p] [Fintype {a // p a}]
  proof: by simp [Finset.ext_iff]

中文:
引理 subtype_eq_univ
  条件: {p : α -> 命题} [DecidablePred p] [Fintype {a // p a}]
  证明: by simp [Finset.ext_iff]
-/
@[simp] lemma subtype_eq_univ {p : α -> Prop} [DecidablePred p] [Fintype {a // p a}] :
    s.subtype p = univ ↔ forall ⦃a⦄, p a -> a in s := by simp [Finset.ext_iff]

/--
lemma `subtype_univ` / 引理 `subtype_univ`

English:
lemma subtype_univ
  given: [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}]
  proof: by simp

中文:
引理 subtype_univ
  条件: [Fintype α] (p : α -> 命题) [DecidablePred p] [Fintype {a // p a}]
  证明: by simp
-/
@[simp] lemma subtype_univ [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.subtype p = univ := by simp

/--
lemma `univ_map_subtype` / 引理 `univ_map_subtype`

English:
lemma univ_map_subtype
  given: [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}]
  proof: by
  rw [← subtype_map]; rw [subtype_univ]

中文:
引理 univ_map_subtype
  条件: [Fintype α] (p : α -> 命题) [DecidablePred p] [Fintype {a // p a}]
  证明: by
  rw [← subtype_map]; rw [subtype_univ]

Depends on / 依赖: subtype_map, subtype_univ
-/
lemma univ_map_subtype [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.map (Function.Embedding.subtype p) = univ.filter p := by
  rw [← subtype_map]; rw [subtype_univ]

/--
lemma `univ_val_map_subtype_val` / 引理 `univ_val_map_subtype_val`

English:
lemma univ_val_map_subtype_val
  given: [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}]
  proof: by
  apply (map_val (Function.Embedding.subtype p) univ).symm.trans
  apply congr_arg
  apply univ_map_subtype

中文:
引理 univ_val_map_subtype_val
  条件: [Fintype α] (p : α -> 命题) [DecidablePred p] [Fintype {a // p a}]
  证明: by
  apply (map_val (Function.Embedding.subtype p) univ).symm.trans
  apply congr_arg
  apply univ_map_subtype

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, congr_arg, map_val, subtype, symm.trans, univ_map_subtype
-/
lemma univ_val_map_subtype_val [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map ((↑) : { a // p a } -> α) = (univ.filter p).val := by
  apply (map_val (Function.Embedding.subtype p) univ).symm.trans
  apply congr_arg
  apply univ_map_subtype

/--
lemma `univ_val_map_subtype_restrict` / 引理 `univ_val_map_subtype_restrict`

English:
lemma univ_val_map_subtype_restrict
  statement: [Fintype α] (f : α -> β)
  proof: by
  rw [← univ_val_map_subtype_val]; rw [Multiset.map_map]; rw [Subtype.restrict_def]

中文:
引理 univ_val_map_subtype_restrict
  结论: [Fintype α] (f : α -> β)
  证明: by
  rw [← univ_val_map_subtype_val]; rw [Multiset.map_map]; rw [Subtype.restrict_def]

Depends on / 依赖: Multiset, Multiset.map_map, Subtype, Subtype.restrict_def, map_map, restrict_def, univ_val_map_subtype_val
-/
lemma univ_val_map_subtype_restrict [Fintype α] (f : α -> β)
    (p : α -> Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map (Subtype.restrict p f) = (univ.filter p).val.map f := by
  rw [← univ_val_map_subtype_val]; rw [Multiset.map_map]; rw [Subtype.restrict_def]

section DecEq

variable [Fintype α] [DecidableEq α]

/--
lemma `filter_univ_mem` / 引理 `filter_univ_mem`

English:
lemma filter_univ_mem
  given: (s : Finset α)
  statement: univ.filter (· in s) = s
  proof: by simp

中文:
引理 filter_univ_mem
  条件: (s : Finset α)
  结论: univ.filter (· in s) = s
  证明: by simp
-/
lemma filter_univ_mem (s : Finset α) : univ.filter (· in s) = s := by simp

/--
Instance `decidableCodisjoint` / 实例 `decidableCodisjoint`

English:
instance decidableCodisjoint
  signature: : Decidable (Codisjoint s t)
  body: decidable_of_iff _ codisjoint_left.symm

中文:
实例 decidableCodisjoint
  签名: : Decidable (Codisjoint s t)
  定义体: decidable_of_iff _ codisjoint_left.symm

Depends on / 依赖: codisjoint_left, codisjoint_left.symm, decidable_of_iff
-/
instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm

/--
Instance `decidableIsCompl` / 实例 `decidableIsCompl`

English:
instance decidableIsCompl
  signature: : Decidable (IsCompl s t)
  body: decidable_of_iff' _ isCompl_iff

中文:
实例 decidableIsCompl
  签名: : Decidable (IsCompl s t)
  定义体: decidable_of_iff' _ isCompl_iff

Depends on / 依赖: decidable_of_iff, isCompl_iff
-/
instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff

end DecEq

end Finset
