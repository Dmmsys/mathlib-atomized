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

/-
**Multiset.covBy_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (s : Multiset α) (a : α), s ⋖ a ::ₘ s
参数：s : Multiset α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Order.covBy_succ`：covBy_succ (a : α) : a ⋖ succ a
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
-/
@[simp] lemma covBy_cons (s : Multiset α) (a : α) : s ⋖ a ::ₘ s :=
  ⟨lt_cons_self _ _, fun t hst hts ↦ (covBy_succ _).2 (card_lt_card hst) <| by
    simpa using card_lt_card hts⟩
/-
**Multiset._root_.CovBy.exists_multiset_cons** 是 Mathlib 中的一个引理，位于命名空间 `Multiset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_multiset_cons (h : s ⋖ t) : ∃ a, a ::ₘ s = t :=
  (lt_iff_cons_le.1 h.lt).imp fun _a ha ↦ ha.eq_of_not_lt <| h.2 <| lt_cons_self _ _
/-
**Multiset.covBy_iff** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：covBy_iff : s ⋖ t ↔ exists a, a ::ₘ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.exists_multiset_cons`：∀ {α : Type u_1} {s t : Multiset α}, s ⋖ t →
 ∃ a, a ::ₘ s = t
· 使用定理 `Multiset.covBy_cons`：∀ {α : Type u_1} (s : Multiset α) (a : α), s ⋖ a ::
ₘ s
-/
lemma covBy_iff : s ⋖ t ↔ ∃ a, a ::ₘ s = t :=
  ⟨CovBy.exists_multiset_cons, by rintro ⟨a, rfl⟩; exact covBy_cons _ _⟩
/-
**Multiset._root_.CovBy.card_multiset** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.card_multiset (h : s ⋖ t) : card s ⋖ card t := by
  obtain ⟨a, rfl⟩ := h.exists_multiset_cons; rw [card_cons]; exact covBy_succ _
/-
**Multiset.isAtom_iff** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：isAtom_iff : IsAtom s ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isAtom_iff : IsAtom s ↔ ∃ a, s = {a} := by simp [← bot_covBy_iff, covBy_iff, eq_comm]
/-
**Multiset.isAtom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (a : α), IsAtom {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Multiset.isAtom_iff`：isAtom_iff : IsAtom s ↔ exists a, s = {a}
-/
@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Multiset α) := isAtom_iff.2 ⟨_, rfl⟩
/-
**Multiset.instGradeMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instGradeMinOrder : GradeMinOrder Nat (Multiset α) where grade
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.card_strictMono`：card_strictMono : StrictMono (@card α)
· 使用定理 `CovBy.card_multiset`：∀ {α : Type u_1} {s t : Multiset α}, s ⋖ t → s.card
 ⋖ t.card
-/
instance instGradeMinOrder : GradeMinOrder ℕ (Multiset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_multiset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
/-
**Multiset.grade_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (m : Multiset α), grade ℕ m = m.card
参数：m : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma grade_eq (m : Multiset α) : grade ℕ m = card m := rfl

end Multiset

namespace Finset
variable {s t : Finset α} {a : α}

/-- Finsets form an order-connected suborder of multisets. -/
/-
**Finset.ordConnected_range_val** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：ordConnected_range_val : Set.OrdConnected (Set.range val : Set <| Multiset
 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup

--- 原说明 ---
Finsets form an order-connected suborder of multisets.
-/
lemma ordConnected_range_val : Set.OrdConnected (Set.range val : Set <| Multiset α) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨⟨t, Multiset.nodup_of_le ht.2 s.2⟩, rfl⟩⟩

/-- Finsets form an order-connected suborder of sets. -/
/-
**Finset.ordConnected_range_coe** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：ordConnected_range_coe : Set.OrdConnected (Set.range ((↑) : Finset α -> Se
t α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
Finsets form an order-connected suborder of sets.
-/
lemma ordConnected_range_coe : Set.OrdConnected (Set.range ((↑) : Finset α → Set α)) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨_, (s.finite_toSet.subset ht.2).coe_toFinset⟩⟩
/-
**Finset.val_wcovBy_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, s.val ⩿ t.val ↔ s ⩿ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_wcovBy_apply_iff`：Set.OrdConnected.apply_wcovBy_a
pply_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⩿ f b ↔ a ⩿ b
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用引理 `Finset.ordConnected_range_val`：ordConnected_range_val : Set.OrdConnected
 (Set.range val : Set <| Multiset α)
-/
@[simp] lemma val_wcovBy_val : s.1 ⩿ t.1 ↔ s ⩿ t :=
  ordConnected_range_val.apply_wcovBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩
/-
**Finset.val_covBy_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, s.val ⋖ t.val ↔ s ⋖ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用引理 `Finset.ordConnected_range_val`：ordConnected_range_val : Set.OrdConnected
 (Set.range val : Set <| Multiset α)
-/
@[simp] lemma val_covBy_val : s.1 ⋖ t.1 ↔ s ⋖ t :=
  ordConnected_range_val.apply_covBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩
/-
**Finset.coe_wcovBy_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, ↑s ⩿ ↑t ↔ s ⩿ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_wcovBy_apply_iff`：Set.OrdConnected.apply_wcovBy_a
pply_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⩿ f b ↔ a ⩿ b
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用引理 `Finset.ordConnected_range_coe`：ordConnected_range_coe : Set.OrdConnected
 (Set.range ((↑) : Finset α -> Set α))
-/
@[simp] lemma coe_wcovBy_coe : (s : Set α) ⩿ t ↔ s ⩿ t :=
  ordConnected_range_coe.apply_wcovBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩
/-
**Finset.coe_covBy_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, ↑s ⋖ ↑t ↔ s ⋖ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用引理 `Finset.ordConnected_range_coe`：ordConnected_range_coe : Set.OrdConnected
 (Set.range ((↑) : Finset α -> Set α))
-/
@[simp] lemma coe_covBy_coe : (s : Set α) ⋖ t ↔ s ⋖ t :=
  ordConnected_range_coe.apply_covBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

alias ⟨_, _root_.WCovBy.finset_val⟩ := val_wcovBy_val
alias ⟨_, _root_.CovBy.finset_val⟩ := val_covBy_val
alias ⟨_, _root_.WCovBy.finset_coe⟩ := coe_wcovBy_coe
alias ⟨_, _root_.CovBy.finset_coe⟩ := coe_covBy_coe
/-
**Finset.covBy_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α} (ha : a ∉ s), s ⋖ Finset.cons a s 
ha
参数：ha : a ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma covBy_cons (ha : a ∉ s) : s ⋖ s.cons a ha := by simp [← val_covBy_val]
/-
**Finset._root_.CovBy.exists_finset_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_finset_cons (h : s ⋖ t) : ∃ a, ∃ ha : a ∉ s, s.cons a ha = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_exists_cons_subset.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_cons _).symm⟩
/-
**Finset.covBy_iff_exists_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：covBy_iff_exists_cons : s ⋖ t ↔ exists a, exists ha : a ∉ s, s.cons a ha =
 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.exists_finset_cons`：∀ {α : Type u_1} {s t : Finset α}, s ⋖ t → ∃ a
, ∃ (ha : a ∉ s), Finset.cons a s ha = t
· 使用定理 `Finset.covBy_cons`：∀ {α : Type u_1} {s : Finset α} {a : α} (ha : a ∉ s),
 s ⋖ Finset.cons a s ha
-/
lemma covBy_iff_exists_cons : s ⋖ t ↔ ∃ a, ∃ ha : a ∉ s, s.cons a ha = t :=
  ⟨CovBy.exists_finset_cons, by rintro ⟨a, ha, rfl⟩; exact covBy_cons _⟩
/-
**Finset._root_.CovBy.card_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covBy_val.2 h).card_multiset

section DecidableEq
variable [DecidableEq α]

/-
**Finset.wcovBy_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finset α) (a : α), s ⩿ insert
 a s
参数：s : Finset α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
-/
@[simp] lemma wcovBy_insert (s : Finset α) (a : α) : s ⩿ insert a s := by simp [← coe_wcovBy_coe]
/-
**Finset.erase_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finset α) (a : α), s.erase a 
⩿ s
参数：s : Finset α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
-/
@[simp] lemma erase_wcovBy (s : Finset α) (a : α) : s.erase a ⩿ s := by simp [← coe_wcovBy_coe]
/-
**Finset.covBy_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：covBy_insert (ha : a ∉ s) : s ⋖ insert a s
参数：ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.covBy_of_lt`：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
· 使用定理 `Finset.wcovBy_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finse
t α) (a : α), s ⩿ insert a s
· 使用定理 `Finset.ssubset_insert`：ssubset_insert (h : a ∉ s) : s ⊂ insert a s
-/
lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
  (wcovBy_insert _ _).covBy_of_lt <| ssubset_insert ha

omit [DecidableEq α] in
/-
**Finset.empty_covBy_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (a : α), ∅ ⋖ {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.covBy_insert`：covBy_insert (ha : a ∉ s) : s ⋖ insert a s
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
@[simp] lemma empty_covBy_singleton (a : α) : ∅ ⋖ ({a} : Finset α) := by
  classical exact insert_empty_eq (β := Finset α) a ▸ covBy_insert <| notMem_empty a
/-
**Finset.erase_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α} [inst : DecidableEq α], a ∈ s → s.
erase a ⋖ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.erase_ssubset`：erase_ssubset {a : α} {s : Finset α} (h : a in s) 
: s.erase a ⊂ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.erase_wcovBy`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finset
 α) (a : α), s.erase a ⩿ s
-/
@[simp] lemma erase_covBy (ha : a ∈ s) : s.erase a ⋖ s := ⟨erase_ssubset ha, (erase_wcovBy _ _).2⟩
/-
**Finset._root_.CovBy.exists_finset_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_finset_insert (h : s ⋖ t) : ∃ a ∉ s, insert a s = t := by
  simpa using h.exists_finset_cons
/-
**Finset._root_.CovBy.exists_finset_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CovBy.exists_finset_erase (h : s ⋖ t) : ∃ a ∈ t, t.erase a = s := by
  simpa only [← coe_inj, coe_erase] using! h.finset_coe.exists_set_sdiff_singleton
/-
**Finset.covBy_iff_exists_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：covBy_iff_exists_insert : s ⋖ t ↔ exists a ∉ s, insert a s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma covBy_iff_exists_insert : s ⋖ t ↔ ∃ a ∉ s, insert a s = t := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_insert, ← coe_inj, coe_insert, mem_coe]
/-
**Finset.covBy_iff_card_sdiff_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：covBy_iff_card_sdiff_eq_one : t ⋖ s ↔ t subseteq s ∧ (s \ t).card = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.covBy_iff_exists_insert`：covBy_iff_exists_insert : s ⋖ t ↔ exists
 a ∉ s, insert a s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_sdiff_cancel`：∀ {α : Type u_1} [inst : DecidableEq α] {s :
 Finset α} {a : α}, a ∉ s → insert a s \ s = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `superset_of_eq`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pre
order α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
-/
lemma covBy_iff_card_sdiff_eq_one : t ⋖ s ↔ t ⊆ s ∧ (s \ t).card = 1 := by
  rw [covBy_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [card_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 <| superset_of_eq ha <| mem_singleton_self _).2, ?_⟩
    rw [insert_eq, ← ha, sdiff_union_of_subset hts]
/-
**Finset.covBy_iff_exists_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：covBy_iff_exists_erase : s ⋖ t ↔ exists a in t, t.erase a = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma covBy_iff_exists_erase : s ⋖ t ↔ ∃ a ∈ t, t.erase a = s := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_sdiff_singleton, ← coe_inj, coe_erase, mem_coe]

end DecidableEq

/-
**Finset.isAtom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (a : α), IsAtom {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
· 使用定理 `Finset.eq_empty_of_ssubset_singleton`：eq_empty_of_ssubset_singleton {s :
 Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅
-/
@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Finset α) :=
  ⟨singleton_ne_empty a, fun _ ↦ eq_empty_of_ssubset_singleton⟩
/-
**Finset.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, IsAtom s ↔ ∃ a, s = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma isAtom_iff : IsAtom s ↔ ∃ a, s = {a} := by
  simp [← bot_covBy_iff, covBy_iff_exists_cons, eq_comm]

section Fintype
variable [Fintype α] [DecidableEq α]

/-
**Finset.isCoatom_compl_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：isCoatom_compl_singleton (a : α) : IsCoatom ({a}ᶜ : Finset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.compl`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α}, IsAtom
 a → IsCoatom aᶜ
· 使用定理 `Finset.isAtom_singleton`：∀ {α : Type u_1} (a : α), IsAtom {a}
-/
lemma isCoatom_compl_singleton (a : α) : IsCoatom ({a}ᶜ : Finset α) := (isAtom_singleton a).compl
/-
**Finset.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} [inst : Fintype α] [inst_1 : DecidableEq α
], IsCoatom s ↔ ∃ a, s = {a}ᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma isCoatom_iff : IsCoatom s ↔ ∃ a, s = {a}ᶜ := by
  simp_rw [← isAtom_compl, Finset.isAtom_iff, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

end Fintype

/-- Finsets are multiset-graded. This is not very meaningful mathematically but rather a handy way
to record that the inclusion `Finset α ↪ Multiset α` preserves the covering relation. -/
/-
**Finset.instGradeMinOrder_multiset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instGradeMinOrder_multiset : GradeMinOrder (Multiset α) (Finset α) where g
rade
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.val_strictMono`：val_strictMono : StrictMono (val : Finset α -> Mu
ltiset α)
· 使用定理 `CovBy.finset_val`：∀ {α : Type u_1} {s t : Finset α}, s ⋖ t → s.val ⋖ t.v
al

--- 原说明 ---
Finsets are multiset-graded. This is not very meaningful mathematically but rath
er a handy way
to record that the inclusion `Finset α ↪ Multiset α` preserves the covering rela
tion.
-/
instance instGradeMinOrder_multiset : GradeMinOrder (Multiset α) (Finset α) where
  grade := val
  grade_strictMono := val_strictMono
  covBy_grade _ _ := CovBy.finset_val
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
/-
**Finset.grade_multiset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), grade (Multiset α) s = s.val
参数：s : Finset α；Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma grade_multiset_eq (s : Finset α) : grade (Multiset α) s = s.1 := rfl
/-
**Finset.instGradeMinOrder_nat** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instGradeMinOrder_nat : GradeMinOrder Nat (Finset α) where grade
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_strictMono`：card_strictMono : StrictMono (card : Finset α ->
 Nat)
· 使用定理 `CovBy.card_finset`：∀ {α : Type u_1} {s t : Finset α}, s ⋖ t → s.card ⋖ t
.card
-/
instance instGradeMinOrder_nat : GradeMinOrder ℕ (Finset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_finset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot
/-
**Finset.grade_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), grade ℕ s = s.card
参数：s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma grade_eq (s : Finset α) : grade ℕ s = s.card := rfl

end Finset

