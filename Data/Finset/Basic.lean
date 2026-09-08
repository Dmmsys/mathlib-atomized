/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.SymmDiff

/-!
# Basic lemmas on finite sets

This file contains lemmas on the interaction of various definitions on the `Finset` type.

For an explanation of `Finset` design decisions, please see `Mathlib/Data/Finset/Defs.lean`.

## Main declarations

### Main definitions

* `Finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Equivalences between finsets

* The `Mathlib/Logic/Equiv/Defs.lean` file describes a general type of equivalence, so look in there
  for any lemmas. There is some API for rewriting sums and products from `s` to `t` given that
  `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-! #### union -/

@[simp]
/-
**Finset.disjUnion_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_eq_union (s t h) : @disjUnion α s t h = s union t
参数：s t h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### union
-/
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s ∪ t := by grind

@[simp]
/-
**Finset.disjoint_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_union_left : Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_union, or_imp, forall_and]

@[simp]
/-
**Finset.disjoint_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_union_right : Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s 
u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]

/-! #### inter -/

/-
**Finset.not_disjoint_iff_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s inter t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists a, a 
in s ∧ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
#### inter
-/
theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff.trans <| by simp [Finset.Nonempty]

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter
/-
**Finset.disjoint_or_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s inter t).N
onempty
参数：s t : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter 
: ¬Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s ∩ t).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _

omit [DecidableEq α] in
/-
**Finset.disjoint_of_subset_iff_left_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：disjoint_of_subset_iff_left_eq_empty (h : s subseteq t) : Disjoint s t ↔ s
 = ∅
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_of_le_iff_left_eq_bot`：disjoint_of_le_iff_left_eq_bot (h : a <=
 b) : Disjoint a b ↔ a = ⊥
-/
theorem disjoint_of_subset_iff_left_eq_empty (h : s ⊆ t) :
    Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h
/-
**Finset.pairwiseDisjoint_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_iff {ι : Type*} {s : Set ι} {f : ι -> Finset α} : s.Pairw
iseDisjoint f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f i inter f j).None
mpty -> i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pairwiseDisjoint_iff {ι : Type*} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Lattice

/-
**Finset.isDirected_le** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isDirected_le : IsDirectedOrder (Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
instance isDirected_le : IsDirectedOrder (Finset α) := by classical infer_instance
/-
**Finset.isDirected_subset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isDirected_subset : IsDirected (Finset α) (· subseteq ·)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isDirected_subset : IsDirected (Finset α) (· ⊆ ·) := isDirected_le

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

@[simp]
/-
**Finset.erase_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_empty (a : α) : erase ∅ a = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl
/-
**Finset.Nontrivial.erase_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`
。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, s.Nontrivi
al → (s.erase a).Nonempty
参数：s.erase a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.Nontrivial.exists_ne`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivi
al → ∀ (a : α), ∃ b ∈ s, b ≠ a
-/
protected lemma Nontrivial.erase_nonempty (hs : s.Nontrivial) : (s.erase a).Nonempty :=
  (hs.exists_ne a).imp <| by simp_all
/-
**Finset.erase_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∈ s → ((
s.erase a).Nonempty ↔ s.Nontrivial)
参数：(s.erase a).Nonempty ↔ s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Finset.Nontrivial.exists_ne`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivi
al → ∀ (a : α), ∃ b ∈ s, b ≠ a
-/
@[simp] lemma erase_nonempty (ha : a ∈ s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ ∈ _)]
  refine ⟨?_, fun hs ↦ hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
/-
**Finset.erase_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_singleton (a : α) : ({a} : Finset α).erase a = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by grind

@[simp]
/-
**Finset.erase_insert_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.er
ase a
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a := by grind
/-
**Finset.erase_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).erase a = s
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).erase a = s := by grind
/-
**Finset.erase_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_insert_of_ne {a b : α} {s : Finset α} (h : a != b) : (insert a s).er
ase b = insert a (s.erase b)
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    (insert a s).erase b = insert a (s.erase b) := by grind
/-
**Finset.erase_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a != b) : (s.
cons a ha).erase b = (s.erase b).cons a fun h => ha erase_subset _ _ h
参数：ha : a ∉ s；hb : a != b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    (s.cons a ha).erase b = (s.erase b).cons a fun h => ha <| erase_subset _ _ h := by grind
/-
**Finset.insert_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∈ s → in
sert a (s.erase a) = s
参数：s.erase a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem insert_erase (h : a ∈ s) : insert a (s.erase a) = s := by grind
/-
**Finset.erase_eq_iff_eq_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：erase_eq_iff_eq_insert (hs : a in s) (ht : a ∉ t) : s.erase a = t ↔ s = in
sert a t
参数：hs : a in s；ht : a ∉ t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma erase_eq_iff_eq_insert (hs : a ∈ s) (ht : a ∉ t) : s.erase a = t ↔ s = insert a t := by
  aesop
/-
**Finset.insert_erase_invOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_erase_invOn : Set.InvOn (insert a) (fun s => s.erase a) {s : Finset
 α | a in s} {s : Finset α | a ∉ s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
-/
lemma insert_erase_invOn :
    Set.InvOn (insert a) (fun s ↦ s.erase a) {s : Finset α | a ∈ s} {s : Finset α | a ∉ s} :=
  ⟨fun _s ↦ insert_erase, fun _s ↦ erase_insert⟩
/-
**Finset.erase_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_ssubset {a : α} {s : Finset α} (h : a in s) : s.erase a ⊂ s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s := by grind
/-
**Finset.erase_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_union_eq (a : α) (s : Finset α) (h : a in s) : (erase s a) union {a}
 = s
参数：a : α；s : Finset α；h : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_union_eq (a : α) (s : Finset α) (h : a ∈ s) : (erase s a) ∪ {a} = s := by grind
/-
**Finset.ssubset_iff_exists_subset_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ exists a in t, 
s subseteq t.erase a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  grind
/-
**Finset.erase_ssubset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s
参数：s : Finset α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.ssubset_iff_exists_subset_erase`：ssubset_iff_exists_subset_erase 
{s t : Finset α} : s ⊂ t ↔ exists a in t, s subseteq t.erase a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.erase_subset_erase`：erase_subset_erase (a : α) {s t : Finset α} (
h : s subseteq t) : erase s a subseteq erase t a
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
-/
theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, by grw [← subset_insert]⟩
/-
**Finset.erase_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by grind
/-
**Finset.subset_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_insert_iff {a : α} {s t : Finset α} : s subseteq insert a t ↔ s.era
se a subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ s.erase a ⊆ t := by grind
/-
**Finset.erase_insert_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_insert_subset (a : α) (s : Finset α) : (insert a s).erase a subseteq
 s
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem erase_insert_subset (a : α) (s : Finset α) : (insert a s).erase a ⊆ s :=
  subset_insert_iff.1 Subset.rfl
/-
**Finset.insert_erase_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_erase_subset (a : α) (s : Finset α) : s subseteq insert a (s.erase 
a)
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (s.erase a) :=
  subset_insert_iff.2 Subset.rfl
/-
**Finset.subset_insert_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_insert_iff_of_notMem (h : a ∉ s) : s subseteq insert a t ↔ s subset
eq t
参数：h : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_insert_iff_of_notMem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_notMem h]
/-
**Finset.erase_subset_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_subset_iff_of_mem (h : a in t) : s.erase a subseteq t ↔ s subseteq t
参数：h : a in t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]
/-
**Finset.erase_injOn'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_injOn' (a : α) : { s : Finset α | a in s }.InjOn fun s => s.erase a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
-/
theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => s.erase a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

end Erase

/-
**Finset.Nontrivial.exists_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`
。
形式化陈述：∀ {α : Type u_1} {s : Finset α},   s.Nontrivial → ∃ t a, ∃ (ha : a ∉ t), ∃
 b, ∃ (hb : b ∉ t) (hab : ¬a = b), Finset.cons a (Finset.cons b t hb) ⋯ = s
参数：ha : a ∉ t；hb : b ∉ t；hab : ¬a = b；Finset.cons b t hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
-/
lemma Nontrivial.exists_cons_eq {s : Finset α} (hs : s.Nontrivial) :
    ∃ t a ha b hb hab, (cons b t hb).cons a (mem_cons.not.2 <| not_or_intro hab ha) = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;> simp [insert_erase ha, *]

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-
**Finset.erase_sdiff_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：erase_sdiff_erase (hab : a != b) (hb : b in s) : s.erase a \ s.erase b = {
b}
参数：hab : a != b；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
lemma erase_sdiff_erase (hab : a ≠ b) (hb : b ∈ s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

-- TODO: Do we want to delete this lemma and `Finset.disjUnion_singleton`,
-- or instead add `Finset.union_singleton`/`Finset.singleton_union`?
/-
**Finset.sdiff_singleton_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ {a} = s.erase a
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ {a} = s.erase a := by grind

-- This lemma matches `Finset.insert_eq` in functionality.
/-
**Finset.erase_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a}
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
-/
theorem erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm
/-
**Finset.disjoint_erase_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_eq`：erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]
/-
**Finset.disjoint_insert_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ D
isjoint s t
参数：ha : a ∉ t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_erase_comm`：disjoint_erase_comm : Disjoint (s.erase a) t
 ↔ Disjoint s (t.erase a)
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]
/-
**Finset.disjoint_erase_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ D
isjoint s t
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjoint_erase_comm`：disjoint_erase_comm : Disjoint (s.erase a) t
 ↔ Disjoint s (t.erase a)
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]
/-
**Finset.disjoint_of_erase_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjo
int s t
参数：ha : a ∉ t；hst : Disjoint (s.erase a) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.disjoint_erase_comm`：disjoint_erase_comm : Disjoint (s.erase a) t
 ↔ Disjoint s (t.erase a)
· 使用定理 `Finset.disjoint_insert_right`：disjoint_insert_right : Disjoint s (insert
 a t) ↔ a ∉ s ∧ Disjoint s t
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjoint s t := by
  rw [← erase_insert ha, ← disjoint_erase_comm, disjoint_insert_right]
  exact ⟨notMem_erase _ _, hst⟩
/-
**Finset.disjoint_of_erase_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disj
oint s t
参数：ha : a ∉ s；hst : Disjoint s (t.erase a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.disjoint_erase_comm`：disjoint_erase_comm : Disjoint (s.erase a) t
 ↔ Disjoint s (t.erase a)
· 使用定理 `Finset.disjoint_insert_left`：disjoint_insert_left : Disjoint (insert a s
) t ↔ a ∉ t ∧ Disjoint s t
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disjoint s t := by
  rw [← erase_insert ha, disjoint_erase_comm, disjoint_insert_left]
  exact ⟨notMem_erase _ _, hst⟩
/-
**Finset.inter_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_erase (a : α) (s t : Finset α) : s inter t.erase a = (s inter t).era
se a
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.erase a = (s ∩ t).erase a := by grind

@[simp]
/-
**Finset.erase_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_inter (a : α) (s t : Finset α) : s.erase a inter t = (s inter t).era
se a
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_inter (a : α) (s t : Finset α) : s.erase a ∩ t = (s ∩ t).erase a := by grind
/-
**Finset.erase_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase 
a
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by grind
/-
**Finset.erase_inter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_inter_comm (s t : Finset α) (a : α) : s.erase a inter t = s inter t.
erase a
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a := by grind
/-
**Finset.erase_union_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_union_distrib (s t : Finset α) (a : α) : (s union t).erase a = s.era
se a union t.erase a
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a := by
  grind
/-
**Finset.insert_inter_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inter_distrib (s t : Finset α) (a : α) : insert a (s inter t) = ins
ert a s inter insert a t
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by grind
/-
**Finset.erase_sdiff_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a
 \ t.erase a
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a := by
  grind
/-
**Finset.erase_union_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_union_of_mem (ha : a in t) (s : Finset α) : s.erase a union t = s un
ion t
参数：ha : a in t；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.erase a ∪ t = s ∪ t := by
  grind
/-
**Finset.union_erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_erase_of_mem (ha : a in s) (t : Finset α) : s union t.erase a = s un
ion t
参数：ha : a in s；t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.erase a = s ∪ t := by
  grind
/-
**Finset.sdiff_union_erase_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_erase_cancel (hts : t subseteq s) (ha : a in t) : s \ t union 
t.erase a = s.erase a
参数：hts : t subseteq s；ha : a in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a := by
  grind
/-
**Finset.sdiff_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x
参数：s t : Finset α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  grind
/-
**Finset.sdiff_insert_insert_of_mem_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：sdiff_insert_insert_of_mem_of_notMem {s t : Finset α} {x : α} (hxs : x in 
s) (hxt : x ∉ t) : insert x (s \ insert x t) = s \ t
参数：hxs : x in s；hxt : x ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_insert_insert_of_mem_of_notMem {s t : Finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  grind
/-
**Finset.sdiff_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_erase (h : a in s) : s \ t.erase a = insert a (s \ t)
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) := by
  grind
/-
**Finset.sdiff_erase_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_erase_self (ha : a in s) : s \ s.erase a = {a}
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} := by
  grind
/-
**Finset.erase_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a
}
参数：s : Finset α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.sdiff_eq_empty_iff_subset`：sdiff_eq_empty_iff_subset : s \ t = ∅ 
↔ s subseteq t
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]

--TODO@Yaël: Kill lemmas duplicate with `BooleanAlgebra`
/-
**Finset.sdiff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_disjoint : Disjoint (t \ s) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
-/
theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2
/-
**Finset.disjoint_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_sdiff : Disjoint s (t \ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
-/
theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm
/-
**Finset.disjoint_sdiff_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s inter t)
参数：s t : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subsete
q u) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
-/
theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right inter_subset_right sdiff_disjoint

end Sdiff

/-! ### attach -/

@[simp]
/-
**Finset.attach_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_empty : (∅ : Finset α).attach = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### attach
-/
theorem attach_empty : (∅ : Finset α).attach = ∅ :=
  rfl

@[simp]
/-
**Finset.attach_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_nonempty_iff {s : Finset α} : s.attach.Nonempty ↔ s.Nonempty
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
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attach_nonempty_iff {s : Finset α} : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]
/-
**Finset.attach_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_eq_empty_iff {s : Finset α} : s.attach = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem attach_eq_empty_iff {s : Finset α} : s.attach = ∅ ↔ s = ∅ := by
  simp [eq_empty_iff_forall_notMem]

/-! ### filter -/

section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

/-
**Finset.filter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅ := by grind
/-
**Finset.filter_cons_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) : (s.con
s a ha).filter p = (s.filter p).cons a ((mem_of_mem_filter _).mt ha)
参数：a : α；s : Finset α；ha : a ∉ s；hp : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用定理 `Multiset.filter_cons_of_pos`：filter_cons_of_pos {a : α} (s) : p a -> fil
ter p (a ::ₘ s) = a ::ₘ filter p s
-/
theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    (s.cons a ha).filter p = (s.filter p).cons a ((mem_of_mem_filter _).mt ha) :=
  eq_of_veq <| s.val.filter_cons_of_pos hp
/-
**Finset.filter_cons_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) : (s.co
ns a ha).filter p = s.filter p
参数：a : α；s : Finset α；ha : a ∉ s；hp : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.filter_cons_of_neg`：filter_cons_of_neg {a : α} (s) : ¬p a -> fi
lter p (a ::ₘ s) = filter p s
-/
theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    (s.cons a ha).filter p = s.filter p :=
  eq_of_veq <| s.val.filter_cons_of_neg hp
/-
**Finset.disjoint_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_filter {s : Finset α} {p q : α -> Prop} [DecidablePred p] [Decida
blePred q] : Disjoint (s.filter p) (s.filter q) ↔ forall x in s, p x -> ¬q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem disjoint_filter {s : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filter p) (s.filter q) ↔ ∀ x ∈ s, p x → ¬q x := by
  constructor <;> simp +contextual [disjoint_left]
/-
**Finset.disjoint_filter_filter'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_filter_filter' (s t : Finset α) {p q : α -> Prop} [DecidablePred 
p] [DecidablePred q] (h : Disjoint p q) : Disjoint (s.filter p) (t.filter q)
参数：s t : Finset α；h : Disjoint p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Pi.disjoint_iff`：disjoint_iff [forall i, OrderBot (α' i)] {f g : forall 
i, α' i} : Disjoint f g ↔ forall i, Disjoint (f i) (g i)
-/
theorem disjoint_filter_filter' (s t : Finset α)
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) :
    Disjoint (s.filter p) (t.filter q) := by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a
/-
**Finset.disjoint_filter_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_filter_filter_not (s t : Finset α) (p : α -> Prop) [DecidablePred
 p] [forall x, Decidable (¬p x)] : Disjoint (s.filter p) (t.filter fun a => ¬p a
)
参数：s t : Finset α；p : α -> Prop；¬p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_filter_filter'`：disjoint_filter_filter' (s t : Finset α)
 {p q : α -> Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) : Disj
oint (s.filter p) (t…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem disjoint_filter_filter_not (s t : Finset α) (p : α → Prop)
    [DecidablePred p] [∀ x, Decidable (¬p x)] :
    Disjoint (s.filter p) (t.filter fun a => ¬p a) :=
  s.disjoint_filter_filter' t disjoint_compl_right
/-
**Finset.filter_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_disjUnion (s : Finset α) (t : Finset α) (h : Disjoint s t) : (s.dis
jUnion t h).filter p = (s.filter p).disjUnion (t.filter p) (disjoint_filter_filt
er h)
参数：s : Finset α；t : Finset α；h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.disjoint_filter_filter`：∀ {α : Type u_1} {s t : Finset α} {p q : 
α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred q],   Disjoint s t → 
Disjoint (Finset.fi…
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
-/
theorem filter_disjUnion (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    (s.disjUnion t h).filter p = (s.filter p).disjUnion (t.filter p) (disjoint_filter_filter h) :=
  eq_of_veq <| Multiset.filter_add _ _ _
/-
**Finset.filter_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_cons {a : α} (s : Finset α) (ha : a ∉ s) : (s.cons a ha).filter p =
 if p a then (s.filter p).cons a ((mem_of_mem_filter _).mt ha) else s.filter p
参数：s : Finset α；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).filter p =
      if p a then (s.filter p).cons a ((mem_of_mem_filter _).mt ha) else s.filter p := by grind

@[simp]
/-
**Finset.disjoint_disjUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_disjUnion_left {s t u : Finset α} (h : Disjoint s t) : Disjoint (
s.disjUnion t h) u ↔ Disjoint s u ∧ Disjoint t u
参数：h : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_disjUnion_left {s t u : Finset α} (h : Disjoint s t) :
    Disjoint (s.disjUnion t h) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_disjUnion, or_imp, forall_and]

@[simp]
/-
**Finset.disjoint_disjUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_disjUnion_right {s t u : Finset α} (h : Disjoint t u) : Disjoint 
s (t.disjUnion u h) ↔ Disjoint s t ∧ Disjoint s u
参数：h : Disjoint t u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_disjUnion_right {s t u : Finset α} (h : Disjoint t u) :
    Disjoint s (t.disjUnion u h) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_disjUnion, or_imp, forall_and]

section
variable [DecidableEq α]

/-
**Finset.filter_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).filter p = s₁.filter p uni
on s₂.filter p
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p := by
  grind
/-
**Finset.filter_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_union_right (s : Finset α) : s.filter p union s.filter q = s.filter
 fun x => p x ∨ q x
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_union_right (s : Finset α) :
    s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x := by grind
/-
**Finset.filter_mem_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_mem_eq_inter {s t : Finset α} [forall i, Decidable (i in t)] : (s.f
ilter fun i => i in t) = s inter t
参数：i in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filter fun i => i ∈ t) = s ∩ t := by grind
/-
**Finset.filter_notMem_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_notMem_eq_sdiff {s t : Finset α} [forall i, Decidable (i ∉ t)] : (s
.filter fun i => i ∉ t) = s \ t
参数：i ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_notMem_eq_sdiff {s t : Finset α} [∀ i, Decidable (i ∉ t)] :
    (s.filter fun i => i ∉ t) = s \ t := by grind
/-
**Finset.filter_inter_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_inter_distrib (s t : Finset α) : (s inter t).filter p = s.filter p 
inter t.filter p
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  grind
/-
**Finset.filter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_inter (s t : Finset α) : s.filter p inter t = (s inter t).filter p
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_inter (s t : Finset α) : s.filter p ∩ t = (s ∩ t).filter p := by grind
/-
**Finset.inter_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_filter (s t : Finset α) : s inter t.filter p = (s inter t).filter p
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_filter (s t : Finset α) : s ∩ t.filter p = (s ∩ t).filter p := by grind
/-
**Finset.filter_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_insert (a : α) (s : Finset α) : (insert a s).filter p = if p a then
 insert a (s.filter p) else s.filter p
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_insert (a : α) (s : Finset α) :
    (insert a s).filter p = if p a then insert a (s.filter p) else s.filter p := by grind
/-
**Finset.filter_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_erase (a : α) (s : Finset α) : (s.erase a).filter p = (s.filter p).
erase a
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_erase (a : α) (s : Finset α) : (s.erase a).filter p = (s.filter p).erase a := by
  grind
/-
**Finset.filter_or** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p unio
n s.filter q
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q := by
  grind
/-
**Finset.filter_and** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p int
er s.filter q
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q := by
  grind
/-
**Finset.filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p := by
  grind
/-
**Finset.filter_and_not** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_and_not (s : Finset α) (p q : α -> Prop) [DecidablePred p] [Decidab
lePred q] : s.filter (fun a => p a ∧ ¬ q a) = s.filter p \ s.filter q
参数：s : Finset α；p q : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filter_and_not (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    s.filter (fun a ↦ p a ∧ ¬ q a) = s.filter p \ s.filter q := by grind
/-
**Finset.sdiff_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁.filter (· ∉ s₂)
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁.filter (· ∉ s₂) := by grind
/-
**Finset.subset_union_elim** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s subseteq t₁ union
 t₂) : exists s₁ s₂ : Finset α, s₁ union s₂ = s ∧ ↑s₁ subseteq t₁ ∧ ↑s₂ subseteq
 t₂ \ t₁
参数：h : ↑s subseteq t₁ union t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · grind
    · grind
    · intro x
      simp only [coe_filter, Set.mem_ofPred_eq, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

-- This is not a good simp lemma, as it would prevent `Finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter (Eq b)`.
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
/-
**Finset.filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_eq [DecidableEq β] (s : Finset β) (b : β) : s.filter (Eq b) = ite (
b in s) {b} ∅
参数：s : Finset β；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
After filtering out everything that does not equal a given value, at most that v
alue remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) :
    s.filter (Eq b) = ite (b ∈ s) {b} ∅ := by grind

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
/-
**Finset.filter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a =
 b) = ite (b in s) {b} ∅
参数：s : Finset β；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
After filtering out everything that does not equal a given value, at most that v
alue remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ := by grind
/-
**Finset.filter_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_ne [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => b !=
 a) = s.erase b
参数：s : Finset β；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b ≠ a) = s.erase b := by grind
/-
**Finset.filter_ne'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a !
= b) = s.erase b
参数：s : Finset β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.filter_ne`：filter_ne [DecidableEq β] (s : Finset β) (b : β) : (s.
filter fun a => b != a) = s.erase b
-/
theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]).trans (s.filter_ne b)
/-
**Finset.filter_union_filter_of_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) : s.
filter p union s.filter q = s
参数：s : Finset α；h : Codisjoint p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b
· 使用定理 `trivial`：True
-/
theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filter p ∪ s.filter q = s :=
  (filter_or _ _ _).symm.trans <| filter_true_of_mem fun x _ => h.top_le x trivial
/-
**Finset.filter_union_filter_not_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_union_filter_not_eq [forall x, Decidable (¬p x)] (s : Finset α) : (
s.filter p union s.filter fun a => ¬p a) = s
参数：¬p x；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_union_filter_of_codisjoint`：filter_union_filter_of_codisjo
int (s : Finset α) (h : Codisjoint p q) : s.filter p union s.filter q = s
· 使用定理 `codisjoint_hnot_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a :
 α}, Codisjoint a (￢a)
-/
theorem filter_union_filter_not_eq [∀ x, Decidable (¬p x)] (s : Finset α) :
    (s.filter p ∪ s.filter fun a => ¬p a) = s :=
  filter_union_filter_of_codisjoint _ _ _ <| @codisjoint_hnot_right _ _ p

end

end Filter

/-! ### range -/


section Range

open Nat

variable {n m l : ℕ}

@[simp]
/-
**Finset.range_filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_filter_eq {n m : Nat} : (range n).filter (· = m) = if m < n then {m}
 else ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by grind

@[simp]
/-
**Finset.range_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_inter_range (m n : Nat) : range m inter range n = range (min m n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_inter_range (m n : ℕ) : range m ∩ range n = range (min m n) := by ext; simp

@[simp]
/-
**Finset.range_union_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_union_range (m n : Nat) : range m union range n = range (max m n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_union_range (m n : ℕ) : range m ∪ range n = range (max m n) := by ext; simp

end Range

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

@[simp]
/-
**Multiset.toFinset_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_add (s t : Multiset α) : (s + t).toFinset = s.toFinset union t.to
Finset
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toFinset_add (s t : Multiset α) : (s + t).toFinset = s.toFinset ∪ t.toFinset :=
  Finset.ext <| by simp

@[simp]
/-
**Multiset.toFinset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_inter (s t : Multiset α) : (s inter t).toFinset = s.toFinset inte
r t.toFinset
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toFinset_inter (s t : Multiset α) : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset :=
  Finset.ext <| by simp

@[simp]
/-
**Multiset.toFinset_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_union (s t : Multiset α) : (s union t).toFinset = s.toFinset unio
n t.toFinset
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext; simp

@[simp]
/-
**Multiset.toFinset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Multiset.dedup_eq_zero`：dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s
 = 0
-/
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]
/-
**Multiset.toFinset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_nonempty : s.toFinset.Nonempty ↔ s != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_nonempty : s.toFinset.Nonempty ↔ s ≠ 0 := by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty

@[simp]
/-
**Multiset.toFinset_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_filter (s : Multiset α) (p : α -> Prop) [DecidablePred p] : (s.fi
lter p).toFinset = s.toFinset.filter p
参数：s : Multiset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_filter (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).toFinset = s.toFinset.filter p := by
  ext; simp

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α} {f : α → β}
  {s : Finset α} {t : Set β} {t' : Finset β}

@[simp]
/-
**List.toFinset_union** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_union (l l' : List α) : (l union l').toFinset = l.toFinset union 
l'.toFinset
参数：l l' : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset := by
  ext
  simp

@[simp]
/-
**List.toFinset_inter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_inter (l l' : List α) : (l inter l').toFinset = l.toFinset inter 
l'.toFinset
参数：l l' : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset := by
  ext
  simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty_iff

@[simp]
/-
**List.toFinset_filter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_filter (s : List α) (p : α -> Bool) : (s.filter p).toFinset = s.t
oFinset.filter (p ·)
参数：s : List α；p : α -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_filter (s : List α) (p : α → Bool) :
    (s.filter p).toFinset = s.toFinset.filter (p ·) := by
  ext; simp [List.mem_filter]
/-
**List.filter_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_toFinset (s : List α) (p : α -> Prop) [DecidablePred p] : s.toFinse
t.filter p = (s.filter p).toFinset
参数：s : List α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toFinset_filter`：toFinset_filter (s : List α) (p : α -> Bool) : (s.
filter p).toFinset = s.toFinset.filter (p ·)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_toFinset (s : List α) (p : α → Prop) [DecidablePred p] :
    s.toFinset.filter p = (s.filter p).toFinset := by simp

end List

namespace Finset

section ToList

@[simp]
/-
**Finset.toList_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.toList_eq_nil`：toList_eq_nil {s : Multiset α} : s.toList = [] ↔
 s = 0
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
-/
theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  Multiset.toList_eq_nil.trans val_eq_zero
/-
**Finset.empty_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_toList {s : Finset α} : s.toList.isEmpty ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_toList {s : Finset α} : s.toList.isEmpty ↔ s = ∅ := by simp

@[simp]
/-
**Finset.toList_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_empty : (∅ : Finset α).toList = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.toList_eq_nil`：toList_eq_nil {s : Finset α} : s.toList = [] ↔ s =
 ∅
-/
theorem toList_empty : (∅ : Finset α).toList = [] :=
  toList_eq_nil.mpr rfl
/-
**Finset.Nonempty.toList_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → s.toList ≠ []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.toList_eq_nil`：toList_eq_nil {s : Finset α} : s.toList = [] ↔ s =
 ∅
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
-/
theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=
  mt toList_eq_nil.mp hs.ne_empty
/-
**Finset.Nonempty.not_empty_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → ¬s.toList.isEmpty = true
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.empty_toList`：empty_toList {s : Finset α} : s.toList.isEmpty ↔ s 
= ∅
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
-/
theorem Nonempty.not_empty_toList {s : Finset α} (hs : s.Nonempty) : ¬s.toList.isEmpty :=
  mt empty_toList.mp hs.ne_empty

end ToList

/-! ### choose -/


section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
/-
**Finset.chooseX** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：chooseX (hp : exists! a, a in l ∧ p a) : { a // a in l ∧ p a }
参数：hp : exists! a, a in l ∧ p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `l` and a predicate `p`, associate to a proof that there is a uni
que element of
`l` satisfying `p` this unique element, as an element of the corresponding subty
pe.
-/
def chooseX (hp : ∃! a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  l.val.chooseX p hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
/-
**Finset.choose** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：choose (hp : exists! a, a in l ∧ p a) : α
参数：hp : exists! a, a in l ∧ p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `l` and a predicate `p`, associate to a proof that there is a uni
que element of
`l` satisfying `p` this unique element, as an element of the ambient type.
-/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  l.chooseX p hp
/-
**Finset.choose_spec** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：choose_spec (hp : exists! a, a in l ∧ p a) : l.choose p hp in l ∧ p (l.cho
ose p hp)
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : l.choose p hp ∈ l ∧ p (l.choose p hp) :=
  (l.chooseX p hp).property
/-
**Finset.choose_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：choose_mem (hp : exists! a, a in l ∧ p a) : l.choose p hp in l
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : l.choos
e p hp in l ∧ p (l.choose p hp)
-/
theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : l.choose p hp ∈ l :=
  (choose_spec _ _ _).1

grind_pattern choose_mem => l.choose p hp
/-
**Finset.choose_property** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：choose_property (hp : exists! a, a in l ∧ p a) : p (l.choose p hp)
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : l.choos
e p hp in l ∧ p (l.choose p hp)
-/
theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (l.choose p hp) :=
  (choose_spec _ _ _).2

grind_pattern choose_property => l.choose p hp
/-
**Finset.choose_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：choose_eq_iff (hp : exists! a, a in l ∧ p a) {a : α} : choose p l hp = a ↔
 a in l ∧ p a
参数：hp : exists! a, a in l ∧ p a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.choose_eq_iff`：choose_eq_iff (hp : exists! a, a in l ∧ p a) {a 
: α} : choose p l hp = a ↔ a in l ∧ p a
-/
theorem choose_eq_iff (hp : ∃! a, a ∈ l ∧ p a) {a : α} : choose p l hp = a ↔ a ∈ l ∧ p a :=
  l.val.choose_eq_iff _ hp

end Choose

end Finset

namespace Equiv
variable [DecidableEq α] {s t : Finset α}

open Finset

/-- The disjoint union of finsets is a sum -/
/-
**Equiv.Finset.union** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Finset`。
形式化陈述：{α : Type u_1} → [inst : DecidableEq α] → (s t : Finset α) → Disjoint s t 
→ ↥s ⊕ ↥t ≃ ↥(s ∪ t)
参数：s t : Finset α；s ∪ t。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)

--- 原说明 ---
The disjoint union of finsets is a sum
-/
def Finset.union (s t : Finset α) (h : Disjoint s t) :
    s ⊕ t ≃ (s ∪ t : Finset α) :=
  Equiv.setCongr (coe_union _ _) |>.trans (Equiv.Set.union (disjoint_coe.mpr h)) |>.symm

@[simp]
/-
**Equiv.Finset.union_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) (x : ↥s),   (Equiv.Finset.union s t h) (Sum.inl x) = ⟨↑x, ⋯⟩
参数：h : Disjoint s t；x : ↥s；Equiv.Finset.union s t h；Sum.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.union_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Finset.union_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) (y : ↥t),   (Equiv.Finset.union s t h) (Sum.inr y) = ⟨↑y, ⋯⟩
参数：h : Disjoint s t；y : ↥t；Equiv.Finset.union s t h；Sum.inr y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.union_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Finset.union_symm_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) {i : α} (hi : i ∈ s) (hi' : i ∈ s ∪ t),   (Equiv.Finset.union s t h).symm ⟨i, 
hi'⟩ = Sum.inl ⟨i, hi⟩
参数：h : Disjoint s t；hi : i ∈ s；hi' : i ∈ s ∪ t；Equiv.Finset.union s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.union_symm_left (h : Disjoint s t) {i : α} (hi : i ∈ s)
    (hi' : i ∈ s ∪ t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
/-
**Equiv.Finset.union_symm_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) {i : α} (hi : i ∈ t) (hi' : i ∈ s ∪ t),   (Equiv.Finset.union s t h).symm ⟨i, 
hi'⟩ = Sum.inr ⟨i, hi⟩
参数：h : Disjoint s t；hi : i ∈ t；hi' : i ∈ s ∪ t；Equiv.Finset.union s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.union_symm_right (h : Disjoint s t) {i : α} (hi : i ∈ t)
    (hi' : i ∈ s ∪ t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/-- The disjoint union of finsets is a sum -/
/-
**Equiv.Finset.disjUnionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Finset`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (s t : Finset α) → (h : Disjoint s t) →
 ↥s ⊕ ↥t ≃ ↥(s.disjUnion t h)
参数：s t : Finset α；h : Disjoint s t；s.disjUnion t h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finset.coe_disjUnion`：coe_disjUnion {s t : Finset α} (h : Disjoint s t) 
: (disjUnion s t h : Set α) = (s : Set α) union t

--- 原说明 ---
The disjoint union of finsets is a sum
-/
def Finset.disjUnionEquiv (s t : Finset α) (h : Disjoint s t) :
    s ⊕ t ≃ s.disjUnion t h :=
  Equiv.setCongr (coe_disjUnion h) |>.trans (Equiv.Set.union (disjoint_coe.mpr h)) |>.symm

@[simp]
/-
**Equiv.Finset.disjUnionEquiv_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) (x : ↥s),   (Equiv.Finset.disjUnionEquiv s t h) (Sum.inl x) = ⟨↑x, ⋯⟩
参数：h : Disjoint s t；x : ↥s；Equiv.Finset.disjUnionEquiv s t h；Sum.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.disjUnionEquiv_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.disjUnionEquiv s t h (Sum.inl x) = ⟨x, Finset.mem_disjUnion.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Finset.disjUnionEquiv_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) (y : ↥t),   (Equiv.Finset.disjUnionEquiv s t h) (Sum.inr y) = ⟨↑y, ⋯⟩
参数：h : Disjoint s t；y : ↥t；Equiv.Finset.disjUnionEquiv s t h；Sum.inr y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.disjUnionEquiv_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.disjUnionEquiv s t h (Sum.inr y) = ⟨y, Finset.mem_disjUnion.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Finset.disjUnionEquiv_symm_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset`
。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) {i : α} (hi : i ∈ s)   (hi' : i ∈ s.disjUnion t h), (Equiv.Finset.disjUnionEqu
iv s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩
参数：h : Disjoint s t；hi : i ∈ s；hi' : i ∈ s.disjUnion t h；Equiv.Finset.disjUnionE
quiv s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.disjUnionEquiv_symm_left (h : Disjoint s t) {i : α} (hi : i ∈ s)
    (hi' : i ∈ s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
/-
**Equiv.Finset.disjUnionEquiv_symm_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Finset
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t
) {i : α} (hi : i ∈ t)   (hi' : i ∈ s.disjUnion t h), (Equiv.Finset.disjUnionEqu
iv s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩
参数：h : Disjoint s t；hi : i ∈ t；hi' : i ∈ s.disjUnion t h；Equiv.Finset.disjUnionE
quiv s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.disjUnionEquiv_symm_right (h : Disjoint s t) {i : α} (hi : i ∈ t)
    (hi' : i ∈ s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
  type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
/-
**Equiv.piFinsetUnion** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piFinsetUnion {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι} (h : D
isjoint s t) : ((forall i : s, α i) × forall i : t, α i) ≃ forall i : (s union t
 : Finset ι), α i
参数：α : ι -> Type*；h : Disjoint s t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The type of dependent functions on the disjoint union of finsets `s ∪ t` is equi
valent to the
  type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiE
quivProdPi`.
-/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.piFinsetUnion_left** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piFinsetUnion_left {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι} (
h : Disjoint s t) {f g} {i : ι} (hi : i in s) (hi' : i in s union t) : piFinsetU
nion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩
参数：α : ι -> Type*；h : Disjoint s t；hi : i in s；hi' : i in s union t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.Finset.union_symm_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s
 t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ s) (hi' : i ∈ s ∪ t),   (Equ
iv.Finset.union s …
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
-/
lemma piFinsetUnion_left {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
    piFinsetUnion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_left h hi hi']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.piFinsetUnion_right** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piFinsetUnion_right {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι} 
(h : Disjoint s t) {f g} {i : ι} (hi : i in t) (hi' : i in s union t) : Equiv.pi
FinsetUnion α h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩
参数：α : ι -> Type*；h : Disjoint s t；hi : i in t；hi' : i in s union t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.Finset.union_symm_right`：∀ {α : Type u_1} [inst : DecidableEq α] {
s t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ t) (hi' : i ∈ s ∪ t),   (Eq
uiv.Finset.union s …
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
-/
lemma piFinsetUnion_right {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ t) (hi' : i ∈ s ∪ t) :
    Equiv.piFinsetUnion α h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_right h hi hi']
  rfl

/-- A finset is equivalent to its coercion as a set. -/
/-
**Equiv._root_.Finset.equivToSet** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finset is equivalent to its coercion as a set.
-/
def _root_.Finset.equivToSet (s : Finset α) : s ≃ (s : Set α) where
  toFun a := ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

end Equiv

namespace Multiset

variable [DecidableEq α]

@[simp]
/-
**Multiset.toFinset_replicate** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：toFinset_replicate (n : Nat) (a : α) : (replicate n a).toFinset = if n = 0
 then ∅ else {a}
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma toFinset_replicate (n : ℕ) (a : α) :
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by
  ext x
  simp only [mem_toFinset, mem_replicate]
  split_ifs with hn <;> simp [hn]

end Multiset

namespace Finset

variable {α : Type*}

/-
**Finset.mem_union_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t) 
{x : α} : x in s union t ↔ Xor (x in s) (x in t)
参数：h : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Xor.eq_1`：∀ (a b : Prop), Xor a b = (a ∧ ¬b ∨ b ∧ ¬a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem mem_union_of_disjoint [DecidableEq α]
    {s t : Finset α} (h : Disjoint s t) {x : α} :
    x ∈ s ∪ t ↔ Xor (x ∈ s) (x ∈ t) := by
  rw [Finset.mem_union, Xor]
  have := disjoint_left.1 h
  tauto

@[simp]
/-
**Finset.univ_finset_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_finset_of_isEmpty [h : IsEmpty α] : (Set.univ : Set (Finset α)) = {∅}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_empty_of_isEmpty`：eq_empty_of_isEmpty [IsEmpty α] (s : Finset 
α) : s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_finset_of_isEmpty [h : IsEmpty α] : (Set.univ : Set (Finset α)) = {∅} :=
  subset_antisymm (fun S hS ↦ by simp [Finset.eq_empty_of_isEmpty S]) (by simp)
/-
**Finset.isEmpty_of_forall_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isEmpty_of_forall_eq_empty (H : forall s : Finset α, s = ∅) : IsEmpty α
参数：H : forall s : Finset α, s = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isEmpty_iff`：isEmpty_iff : IsEmpty α ↔ α -> False
-/
theorem isEmpty_of_forall_eq_empty (H : ∀ s : Finset α, s = ∅) : IsEmpty α :=
  isEmpty_iff.mpr fun a ↦ by specialize H {a}; aesop

@[simp]
/-
**Finset.univ_finset_eq_singleton_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_finset_eq_singleton_empty_iff : @Set.univ (Finset α) = {∅} ↔ IsEmpty 
α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.isEmpty_of_forall_eq_empty`：isEmpty_of_forall_eq_empty (H : foral
l s : Finset α, s = ∅) : IsEmpty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_finset_of_isEmpty`：univ_finset_of_isEmpty [h : IsEmpty α] : 
(Set.univ : Set (Finset α)) = {∅}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_finset_eq_singleton_empty_iff : @Set.univ (Finset α) = {∅} ↔ IsEmpty α :=
  ⟨fun h ↦ isEmpty_of_forall_eq_empty fun s ↦ Set.mem_singleton_iff.mp
    (Set.ext_iff.mp h s |>.mp (Set.mem_univ s)), fun _ ↦ by simp⟩

end Finset

