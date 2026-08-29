/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.Grade
public import Mathlib.Order.Nat

/-!
# Finsets and multisets form a graded order

This file characterises atoms, coatoms and the covering relation in finsets and multisets. It also
proves that they form a `ℕ`-graded order.

## Main declarations

* `Multiset.instGradeMinOrder_nat`: Multisets are `ℕ`-graded
* `Finset.instGradeMinOrder_nat`: Finsets are `ℕ`-graded
-/

public section

open Order

variable {α : Type*}

namespace Multiset
variable {s t : Multiset α} {a : α}

/--
lemma `covBy_cons` / 引理 `covBy_cons`

English:
lemma covBy_cons
  given: (s : Multiset α) (a : α)
  statement: s ⋖ a ::ₘ s
  proof: ⟨lt_cons_self _ _, fun t hst hts => (covBy_succ _).2 (card_lt_card hst) by
    simpa using card_lt_card hts⟩

中文:
引理 covBy_cons
  条件: (s : Multiset α) (a : α)
  结论: s ⋖ a ::ₘ s
  证明: ⟨lt_cons_self _ _, fun t hst hts => (covBy_succ _).2 (card_lt_card hst) by
    simpa using card_lt_card hts⟩
-/
@[simp] lemma covBy_cons (s : Multiset α) (a : α) : s ⋖ a ::ₘ s :=
⟨lt_cons_self _ _, fun t hst hts => (covBy_succ _).2 (card_lt_card hst) by
    simpa using card_lt_card hts⟩

/--
lemma `_root_.CovBy.exists_multiset_cons` / 引理 `_root_.CovBy.exists_multiset_cons`

English:
lemma _root_.CovBy.exists_multiset_cons
  given: (h : s ⋖ t)
  statement: exists a, a ::ₘ s = t
  proof: (lt_iff_cons_le.1 h.lt).imp fun _a ha => ha.eq_of_not_lt h.2 lt_cons_self _ _

中文:
引理 _root_.CovBy.exists_multiset_cons
  条件: (h : s ⋖ t)
  结论: 存在 a, a ::ₘ s = t
  证明: (lt_iff_cons_le.1 h.lt).imp fun _a ha => ha.eq_of_not_lt h.2 lt_cons_self _ _

Depends on / 依赖: eq_of_not_lt, h.lt, ha.eq_of_not_lt, lt_cons_self, lt_iff_cons_le
-/
lemma _root_.CovBy.exists_multiset_cons (h : s ⋖ t) : exists a, a ::ₘ s = t :=
(lt_iff_cons_le.1 h.lt).imp fun _a ha => ha.eq_of_not_lt h.2 lt_cons_self _ _

/--
lemma `covBy_iff` / 引理 `covBy_iff`

English:
lemma covBy_iff
  statement: s ⋖ t ↔ exists a, a ::ₘ s = t
  proof: ⟨CovBy.exists_multiset_cons, by rintro ⟨a, rfl⟩; exact covBy_cons _ _⟩

中文:
引理 covBy_iff
  结论: s ⋖ t ↔ 存在 a, a ::ₘ s = t
  证明: ⟨CovBy.exists_multiset_cons, by rintro ⟨a, rfl⟩; exact covBy_cons _ _⟩

Depends on / 依赖: CovBy.exists_multiset_cons, covBy_cons, exists_multiset_cons
-/
lemma covBy_iff : s ⋖ t ↔ exists a, a ::ₘ s = t :=
  ⟨CovBy.exists_multiset_cons, by rintro ⟨a, rfl⟩; exact covBy_cons _ _⟩

/--
lemma `_root_.CovBy.card_multiset` / 引理 `_root_.CovBy.card_multiset`

English:
lemma _root_.CovBy.card_multiset
  given: (h : s ⋖ t)
  statement: card s ⋖ card t
  proof: by
  obtain ⟨a, rfl⟩ := h.exists_multiset_cons; rw [card_cons]; exact covBy_succ _

中文:
引理 _root_.CovBy.card_multiset
  条件: (h : s ⋖ t)
  结论: card s ⋖ card t
  证明: by
  obtain ⟨a, rfl⟩ := h.exists_multiset_cons; rw [card_cons]; exact covBy_succ _

Depends on / 依赖: card_cons, covBy_succ, exists_multiset_cons, h.exists_multiset_cons
-/
lemma _root_.CovBy.card_multiset (h : s ⋖ t) : card s ⋖ card t := by
  obtain ⟨a, rfl⟩ := h.exists_multiset_cons; rw [card_cons]; exact covBy_succ _

/--
lemma `isAtom_iff` / 引理 `isAtom_iff`

English:
lemma isAtom_iff
  statement: IsAtom s ↔ exists a, s = {a}
  proof: by simp [← bot_covBy_iff, covBy_iff, eq_comm]

中文:
引理 isAtom_iff
  结论: IsAtom s ↔ 存在 a, s = {a}
  证明: by simp [← bot_covBy_iff, covBy_iff, eq_comm]

Depends on / 依赖: bot_covBy_iff, covBy_iff, eq_comm
-/
lemma isAtom_iff : IsAtom s ↔ exists a, s = {a} := by simp [← bot_covBy_iff, covBy_iff, eq_comm]

/--
lemma `isAtom_singleton` / 引理 `isAtom_singleton`

English:
lemma isAtom_singleton
  given: (a : α)
  statement: IsAtom ({a} : Multiset α)
  proof: isAtom_iff.2 ⟨_, rfl⟩

中文:
引理 isAtom_singleton
  条件: (a : α)
  结论: IsAtom ({a} : Multiset α)
  证明: isAtom_iff.2 ⟨_, rfl⟩
-/
@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Multiset α) := isAtom_iff.2 ⟨_, rfl⟩

/--
Instance `instGradeMinOrder` / 实例 `instGradeMinOrder`

English:
instance instGradeMinOrder
  signature: : GradeMinOrder Nat (Multiset α) where
  body: card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_multiset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

中文:
实例 instGradeMinOrder
  签名: : GradeMinOrder 自然数 (Multiset α) where
  定义体: card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_multiset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
-/
instance instGradeMinOrder : GradeMinOrder Nat (Multiset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_multiset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

/--
lemma `grade_eq` / 引理 `grade_eq`

English:
lemma grade_eq
  given: (m : Multiset α)
  statement: grade Nat m = card m
  proof: rfl

中文:
引理 grade_eq
  条件: (m : Multiset α)
  结论: grade 自然数 m = card m
  证明: rfl
-/
@[simp] lemma grade_eq (m : Multiset α) : grade Nat m = card m := rfl

end Multiset

namespace Finset
variable {s t : Finset α} {a : α}

/--
lemma `ordConnected_range_val` / 引理 `ordConnected_range_val`

English:
lemma ordConnected_range_val
  statement: Set.OrdConnected (Set.range val : Set <| Multiset α)
  proof: ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨⟨t, Multiset.nodup_of_le ht.2 s.2⟩, rfl⟩⟩

中文:
引理 ordConnected_range_val
  结论: Set.OrdConnected (Set.range val : Set <| Multiset α)
  证明: ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨⟨t, Multiset.nodup_of_le ht.2 s.2⟩, rfl⟩⟩

Depends on / 依赖: Multiset, Multiset.nodup_of_le, nodup_of_le
-/
lemma ordConnected_range_val : Set.OrdConnected (Set.range val : Set <| Multiset α) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨⟨t, Multiset.nodup_of_le ht.2 s.2⟩, rfl⟩⟩

/--
lemma `ordConnected_range_coe` / 引理 `ordConnected_range_coe`

English:
lemma ordConnected_range_coe
  statement: Set.OrdConnected (Set.range ((↑) : Finset α -> Set α))
  proof: ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨_, (s.finite_toSet.subset ht.2).coe_toFinset⟩⟩

中文:
引理 ordConnected_range_coe
  结论: Set.OrdConnected (Set.range ((↑) : Finset α -> Set α))
  证明: ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨_, (s.finite_toSet.subset ht.2).coe_toFinset⟩⟩

Depends on / 依赖: coe_toFinset, finite_toSet, s.finite_toSet.subset, subset
-/
lemma ordConnected_range_coe : Set.OrdConnected (Set.range ((↑) : Finset α -> Set α)) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨_, (s.finite_toSet.subset ht.2).coe_toFinset⟩⟩

/--
lemma `val_wcovBy_val` / 引理 `val_wcovBy_val`

English:
lemma val_wcovBy_val
  statement: s.1 ⩿ t.1 ↔ s ⩿ t
  proof: ordConnected_range_val.apply_wcovBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

中文:
引理 val_wcovBy_val
  结论: s.1 ⩿ t.1 ↔ s ⩿ t
  证明: ordConnected_range_val.apply_wcovBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩
-/
@[simp] lemma val_wcovBy_val : s.1 ⩿ t.1 ↔ s ⩿ t :=
  ordConnected_range_val.apply_wcovBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

/--
lemma `val_covBy_val` / 引理 `val_covBy_val`

English:
lemma val_covBy_val
  statement: s.1 ⋖ t.1 ↔ s ⋖ t
  proof: ordConnected_range_val.apply_covBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

中文:
引理 val_covBy_val
  结论: s.1 ⋖ t.1 ↔ s ⋖ t
  证明: ordConnected_range_val.apply_covBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩
-/
@[simp] lemma val_covBy_val : s.1 ⋖ t.1 ↔ s ⋖ t :=
  ordConnected_range_val.apply_covBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

/--
lemma `coe_wcovBy_coe` / 引理 `coe_wcovBy_coe`

English:
lemma coe_wcovBy_coe
  statement: (s : Set α) ⩿ t ↔ s ⩿ t
  proof: ordConnected_range_coe.apply_wcovBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

中文:
引理 coe_wcovBy_coe
  结论: (s : Set α) ⩿ t ↔ s ⩿ t
  证明: ordConnected_range_coe.apply_wcovBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩
-/
@[simp] lemma coe_wcovBy_coe : (s : Set α) ⩿ t ↔ s ⩿ t :=
  ordConnected_range_coe.apply_wcovBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

/--
lemma `coe_covBy_coe` / 引理 `coe_covBy_coe`

English:
lemma coe_covBy_coe
  statement: (s : Set α) ⋖ t ↔ s ⋖ t
  proof: ordConnected_range_coe.apply_covBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

alias ⟨_, _root_.WCovBy.finset_val⟩ := val_wcovBy_val
alias ⟨_, _root_.CovBy.finset_val⟩ := val_covBy_val
alias ⟨_, _root_.WCovBy.finset_coe⟩ := coe_wcovBy_coe
alias ⟨_, _root_.CovBy.finset_coe⟩ := coe_covBy_coe

中文:
引理 coe_covBy_coe
  结论: (s : Set α) ⋖ t ↔ s ⋖ t
  证明: ordConnected_range_coe.apply_covBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

alias ⟨_, _root_.WCovBy.finset_val⟩ := val_wcovBy_val
alias ⟨_, _root_.CovBy.finset_val⟩ := val_covBy_val
alias ⟨_, _root_.WCovBy.finset_coe⟩ := coe_wcovBy_coe
alias ⟨_, _root_.CovBy.finset_coe⟩ := coe_covBy_coe
-/
@[simp] lemma coe_covBy_coe : (s : Set α) ⋖ t ↔ s ⋖ t :=
  ordConnected_range_coe.apply_covBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

alias ⟨_, _root_.WCovBy.finset_val⟩ := val_wcovBy_val
alias ⟨_, _root_.CovBy.finset_val⟩ := val_covBy_val
alias ⟨_, _root_.WCovBy.finset_coe⟩ := coe_wcovBy_coe
alias ⟨_, _root_.CovBy.finset_coe⟩ := coe_covBy_coe

/--
lemma `covBy_cons` / 引理 `covBy_cons`

English:
lemma covBy_cons
  given: (ha : a ∉ s)
  statement: s ⋖ s.cons a ha
  proof: by simp [← val_covBy_val]

中文:
引理 covBy_cons
  条件: (ha : a ∉ s)
  结论: s ⋖ s.cons a ha
  证明: by simp [← val_covBy_val]
-/
@[simp] lemma covBy_cons (ha : a ∉ s) : s ⋖ s.cons a ha := by simp [← val_covBy_val]

/--
lemma `_root_.CovBy.exists_finset_cons` / 引理 `_root_.CovBy.exists_finset_cons`

English:
lemma _root_.CovBy.exists_finset_cons
  given: (h : s ⋖ t)
  statement: exists a, exists ha : a ∉ s, s.cons a ha = t
  proof: let ⟨a, ha, hst⟩ := ssubset_iff_exists_cons_subset.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_cons _).symm⟩

中文:
引理 _root_.CovBy.exists_finset_cons
  条件: (h : s ⋖ t)
  结论: 存在 a, 存在 ha : a ∉ s, s.cons a ha = t
  证明: let ⟨a, ha, hst⟩ := ssubset_iff_exists_cons_subset.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_cons _).symm⟩

Depends on / 依赖: eq_of_not_ssuperset, h.lt, hst.eq_of_not_ssuperset, ssubset_cons, ssubset_iff_exists_cons_subset
-/
lemma _root_.CovBy.exists_finset_cons (h : s ⋖ t) : exists a, exists ha : a ∉ s, s.cons a ha = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_exists_cons_subset.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_cons _).symm⟩

/--
lemma `covBy_iff_exists_cons` / 引理 `covBy_iff_exists_cons`

English:
lemma covBy_iff_exists_cons
  statement: s ⋖ t ↔ exists a, exists ha : a ∉ s, s.cons a ha = t
  proof: ⟨CovBy.exists_finset_cons, by rintro ⟨a, ha, rfl⟩; exact covBy_cons _⟩

中文:
引理 covBy_iff_exists_cons
  结论: s ⋖ t ↔ 存在 a, 存在 ha : a ∉ s, s.cons a ha = t
  证明: ⟨CovBy.exists_finset_cons, by rintro ⟨a, ha, rfl⟩; exact covBy_cons _⟩

Depends on / 依赖: CovBy.exists_finset_cons, covBy_cons, exists_finset_cons
-/
lemma covBy_iff_exists_cons : s ⋖ t ↔ exists a, exists ha : a ∉ s, s.cons a ha = t :=
  ⟨CovBy.exists_finset_cons, by rintro ⟨a, ha, rfl⟩; exact covBy_cons _⟩

/--
lemma `_root_.CovBy.card_finset` / 引理 `_root_.CovBy.card_finset`

English:
lemma _root_.CovBy.card_finset
  given: (h : s ⋖ t)
  statement: s.card ⋖ t.card
  proof: (val_covBy_val.2 h).card_multiset

中文:
引理 _root_.CovBy.card_finset
  条件: (h : s ⋖ t)
  结论: s.card ⋖ t.card
  证明: (val_covBy_val.2 h).card_multiset

Depends on / 依赖: card_multiset, val_covBy_val
-/
lemma _root_.CovBy.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covBy_val.2 h).card_multiset

section DecidableEq
variable [DecidableEq α]

/--
lemma `wcovBy_insert` / 引理 `wcovBy_insert`

English:
lemma wcovBy_insert
  given: (s : Finset α) (a : α)
  statement: s ⩿ insert a s
  proof: by simp [← coe_wcovBy_coe]

中文:
引理 wcovBy_insert
  条件: (s : Finset α) (a : α)
  结论: s ⩿ insert a s
  证明: by simp [← coe_wcovBy_coe]
-/
@[simp] lemma wcovBy_insert (s : Finset α) (a : α) : s ⩿ insert a s := by simp [← coe_wcovBy_coe]
/--
lemma `erase_wcovBy` / 引理 `erase_wcovBy`

English:
lemma erase_wcovBy
  given: (s : Finset α) (a : α)
  statement: s.erase a ⩿ s
  proof: by simp [← coe_wcovBy_coe]

中文:
引理 erase_wcovBy
  条件: (s : Finset α) (a : α)
  结论: s.erase a ⩿ s
  证明: by simp [← coe_wcovBy_coe]
-/
@[simp] lemma erase_wcovBy (s : Finset α) (a : α) : s.erase a ⩿ s := by simp [← coe_wcovBy_coe]

/--
lemma `covBy_insert` / 引理 `covBy_insert`

English:
lemma covBy_insert
  given: (ha : a ∉ s)
  statement: s ⋖ insert a s
  proof: (wcovBy_insert _ _).covBy_of_lt ssubset_insert ha

omit [DecidableEq α] in

中文:
引理 covBy_insert
  条件: (ha : a ∉ s)
  结论: s ⋖ insert a s
  证明: (wcovBy_insert _ _).covBy_of_lt ssubset_insert ha

omit [DecidableEq α] in

Depends on / 依赖: covBy_of_lt, ssubset_insert, wcovBy_insert
-/
lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
(wcovBy_insert _ _).covBy_of_lt ssubset_insert ha

omit [DecidableEq α] in
/--
lemma `empty_covBy_singleton` / 引理 `empty_covBy_singleton`

English:
lemma empty_covBy_singleton
  given: (a : α)
  statement: ∅ ⋖ ({a} : Finset α)
  proof: by
classical exact insert_empty_eq (β := Finset α) a ▸ covBy_insert notMem_empty a

中文:
引理 empty_covBy_singleton
  条件: (a : α)
  结论: ∅ ⋖ ({a} : Finset α)
  证明: by
classical exact insert_empty_eq (β := Finset α) a ▸ covBy_insert notMem_empty a
-/
@[simp] lemma empty_covBy_singleton (a : α) : ∅ ⋖ ({a} : Finset α) := by
classical exact insert_empty_eq (β := Finset α) a ▸ covBy_insert notMem_empty a

/--
lemma `erase_covBy` / 引理 `erase_covBy`

English:
lemma erase_covBy
  given: (ha : a in s)
  statement: s.erase a ⋖ s
  proof: ⟨erase_ssubset ha, (erase_wcovBy _ _).2⟩

中文:
引理 erase_covBy
  条件: (ha : a in s)
  结论: s.erase a ⋖ s
  证明: ⟨erase_ssubset ha, (erase_wcovBy _ _).2⟩
-/
@[simp] lemma erase_covBy (ha : a in s) : s.erase a ⋖ s := ⟨erase_ssubset ha, (erase_wcovBy _ _).2⟩

/--
lemma `_root_.CovBy.exists_finset_insert` / 引理 `_root_.CovBy.exists_finset_insert`

English:
lemma _root_.CovBy.exists_finset_insert
  given: (h : s ⋖ t)
  statement: exists a ∉ s, insert a s = t
  proof: by
  simpa using h.exists_finset_cons

中文:
引理 _root_.CovBy.exists_finset_insert
  条件: (h : s ⋖ t)
  结论: 存在 a ∉ s, insert a s = t
  证明: by
  simpa using h.exists_finset_cons

Depends on / 依赖: exists_finset_cons, h.exists_finset_cons
-/
lemma _root_.CovBy.exists_finset_insert (h : s ⋖ t) : exists a ∉ s, insert a s = t := by
  simpa using h.exists_finset_cons

/--
lemma `_root_.CovBy.exists_finset_erase` / 引理 `_root_.CovBy.exists_finset_erase`

English:
lemma _root_.CovBy.exists_finset_erase
  given: (h : s ⋖ t)
  statement: exists a in t, t.erase a = s
  proof: by
  simpa only [← coe_inj, coe_erase] using! h.finset_coe.exists_set_sdiff_singleton

中文:
引理 _root_.CovBy.exists_finset_erase
  条件: (h : s ⋖ t)
  结论: 存在 a in t, t.erase a = s
  证明: by
  simpa only [← coe_inj, coe_erase] using! h.finset_coe.exists_set_sdiff_singleton

Depends on / 依赖: coe_erase, coe_inj, exists_set_sdiff_singleton, finset_coe, h.finset_coe.exists_set_sdiff_singleton
-/
lemma _root_.CovBy.exists_finset_erase (h : s ⋖ t) : exists a in t, t.erase a = s := by
  simpa only [← coe_inj, coe_erase] using! h.finset_coe.exists_set_sdiff_singleton

/--
lemma `covBy_iff_exists_insert` / 引理 `covBy_iff_exists_insert`

English:
lemma covBy_iff_exists_insert
  statement: s ⋖ t ↔ exists a ∉ s, insert a s = t
  proof: by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_insert, ← coe_inj, coe_insert, mem_coe]

中文:
引理 covBy_iff_exists_insert
  结论: s ⋖ t ↔ 存在 a ∉ s, insert a s = t
  证明: by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_insert, ← coe_inj, coe_insert, mem_coe]

Depends on / 依赖: Set.covBy_iff_exists_insert, coe_covBy_coe, coe_inj, coe_insert, covBy_iff_exists_insert, mem_coe
-/
lemma covBy_iff_exists_insert : s ⋖ t ↔ exists a ∉ s, insert a s = t := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_insert, ← coe_inj, coe_insert, mem_coe]

/--
lemma `covBy_iff_card_sdiff_eq_one` / 引理 `covBy_iff_card_sdiff_eq_one`

English:
lemma covBy_iff_card_sdiff_eq_one
  statement: t ⋖ s ↔ t subseteq s ∧ (s \ t).card = 1
  proof: by
  rw [covBy_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [card_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 <| superset_of_eq ha <| mem_singleton_self _).2, ?_⟩
    rw [insert_eq]; rw [← ha]; rw [sdiff_union_of_subset hts]

中文:
引理 covBy_iff_card_sdiff_eq_one
  结论: t ⋖ s ↔ t subseteq s ∧ (s \ t).card = 1
  证明: by
  rw [covBy_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [card_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 <| superset_of_eq ha <| mem_singleton_self _).2, ?_⟩
    rw [insert_eq]; rw [← ha]; rw [sdiff_union_of_subset hts]

Depends on / 依赖: card_eq_one, covBy_iff_exists_insert, insert_eq, mem_sdiff, mem_singleton_self, sdiff_union_of_subset, simp_rw, superset_of_eq
-/
lemma covBy_iff_card_sdiff_eq_one : t ⋖ s ↔ t subseteq s ∧ (s \ t).card = 1 := by
  rw [covBy_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [card_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 <| superset_of_eq ha <| mem_singleton_self _).2, ?_⟩
    rw [insert_eq]; rw [← ha]; rw [sdiff_union_of_subset hts]

/--
lemma `covBy_iff_exists_erase` / 引理 `covBy_iff_exists_erase`

English:
lemma covBy_iff_exists_erase
  statement: s ⋖ t ↔ exists a in t, t.erase a = s
  proof: by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_sdiff_singleton, ← coe_inj, coe_erase, mem_coe]

中文:
引理 covBy_iff_exists_erase
  结论: s ⋖ t ↔ 存在 a in t, t.erase a = s
  证明: by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_sdiff_singleton, ← coe_inj, coe_erase, mem_coe]

Depends on / 依赖: Set.covBy_iff_exists_sdiff_singleton, coe_covBy_coe, coe_erase, coe_inj, covBy_iff_exists_sdiff_singleton, mem_coe
-/
lemma covBy_iff_exists_erase : s ⋖ t ↔ exists a in t, t.erase a = s := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_sdiff_singleton, ← coe_inj, coe_erase, mem_coe]

end DecidableEq

/--
lemma `isAtom_singleton` / 引理 `isAtom_singleton`

English:
lemma isAtom_singleton
  given: (a : α)
  statement: IsAtom ({a} : Finset α)
  proof: ⟨singleton_ne_empty a, fun _ => eq_empty_of_ssubset_singleton⟩

中文:
引理 isAtom_singleton
  条件: (a : α)
  结论: IsAtom ({a} : Finset α)
  证明: ⟨singleton_ne_empty a, fun _ => eq_empty_of_ssubset_singleton⟩
-/
@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Finset α) :=
  ⟨singleton_ne_empty a, fun _ => eq_empty_of_ssubset_singleton⟩

/--
lemma `isAtom_iff` / 引理 `isAtom_iff`

English:
lemma isAtom_iff
  statement: IsAtom s ↔ exists a, s = {a}
  proof: by
  simp [← bot_covBy_iff, covBy_iff_exists_cons, eq_comm]

中文:
引理 isAtom_iff
  结论: IsAtom s ↔ 存在 a, s = {a}
  证明: by
  simp [← bot_covBy_iff, covBy_iff_exists_cons, eq_comm]
-/
protected lemma isAtom_iff : IsAtom s ↔ exists a, s = {a} := by
  simp [← bot_covBy_iff, covBy_iff_exists_cons, eq_comm]

section Fintype
variable [Fintype α] [DecidableEq α]

/--
lemma `isCoatom_compl_singleton` / 引理 `isCoatom_compl_singleton`

English:
lemma isCoatom_compl_singleton
  given: (a : α)
  statement: IsCoatom ({a}ᶜ : Finset α)
  proof: (isAtom_singleton a).compl

中文:
引理 isCoatom_compl_singleton
  条件: (a : α)
  结论: IsCoatom ({a}ᶜ : Finset α)
  证明: (isAtom_singleton a).compl

Depends on / 依赖: isAtom_singleton
-/
lemma isCoatom_compl_singleton (a : α) : IsCoatom ({a}ᶜ : Finset α) := (isAtom_singleton a).compl

/--
lemma `isCoatom_iff` / 引理 `isCoatom_iff`

English:
lemma isCoatom_iff
  statement: IsCoatom s ↔ exists a, s = {a}ᶜ
  proof: by
  simp_rw [← isAtom_compl, Finset.isAtom_iff, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

中文:
引理 isCoatom_iff
  结论: IsCoatom s ↔ 存在 a, s = {a}ᶜ
  证明: by
  simp_rw [← isAtom_compl, Finset.isAtom_iff, compl_eq_iff_isCompl, eq_compl_iff_isCompl]
-/
protected lemma isCoatom_iff : IsCoatom s ↔ exists a, s = {a}ᶜ := by
  simp_rw [← isAtom_compl, Finset.isAtom_iff, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

end Fintype

/--
Instance `instGradeMinOrder_multiset` / 实例 `instGradeMinOrder_multiset`

English:
instance instGradeMinOrder_multiset
  signature: : GradeMinOrder (Multiset α) (Finset α) where
  body: val
  grade_strictMono := val_strictMono
  covBy_grade _ _ := CovBy.finset_val
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

中文:
实例 instGradeMinOrder_multiset
  签名: : GradeMinOrder (Multiset α) (Finset α) where
  定义体: val
  grade_strictMono := val_strictMono
  covBy_grade _ _ := CovBy.finset_val
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
-/
instance instGradeMinOrder_multiset : GradeMinOrder (Multiset α) (Finset α) where
  grade := val
  grade_strictMono := val_strictMono
  covBy_grade _ _ := CovBy.finset_val
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

/--
lemma `grade_multiset_eq` / 引理 `grade_multiset_eq`

English:
lemma grade_multiset_eq
  given: (s : Finset α)
  statement: grade (Multiset α) s = s.1
  proof: rfl

中文:
引理 grade_multiset_eq
  条件: (s : Finset α)
  结论: grade (Multiset α) s = s.1
  证明: rfl
-/
@[simp] lemma grade_multiset_eq (s : Finset α) : grade (Multiset α) s = s.1 := rfl

/--
Instance `instGradeMinOrder_nat` / 实例 `instGradeMinOrder_nat`

English:
instance instGradeMinOrder_nat
  signature: : GradeMinOrder Nat (Finset α) where
  body: card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_finset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

中文:
实例 instGradeMinOrder_nat
  签名: : GradeMinOrder 自然数 (Finset α) where
  定义体: card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_finset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
-/
instance instGradeMinOrder_nat : GradeMinOrder Nat (Finset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_finset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

/--
lemma `grade_eq` / 引理 `grade_eq`

English:
lemma grade_eq
  given: (s : Finset α)
  statement: grade Nat s = s.card
  proof: rfl

中文:
引理 grade_eq
  条件: (s : Finset α)
  结论: grade 自然数 s = s.card
  证明: rfl
-/
@[simp] lemma grade_eq (s : Finset α) : grade Nat s = s.card := rfl

end Finset
