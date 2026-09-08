/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.UpperLower.Basic

/-!
# Intersecting families

This file defines intersecting families and proves their basic properties.

## Main declarations

* `Set.Intersecting`: Predicate for a set of elements in a generalized Boolean algebra to be an
  intersecting family.
* `Set.Intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `Set.Intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.
* `Set.IsIntersectingOf`: Predicate stating that a family `𝒜` of finsets is `L`-intersecting, i.e.,
  meaning the intersection size of every pair of distinct members of `𝒜` belongs to `L ⊆ ℕ`.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

@[expose] public section

assert_not_exists Monoid

open Finset

namespace Set

section SemilatticeInf

variable {α : Type*}

variable [SemilatticeInf α] [OrderBot α] {s t : Set α} {a b c : α}

/-- A set family is intersecting if every pair of elements is non-disjoint. -/
/-
**Set.Intersecting** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Intersecting (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set family is intersecting if every pair of elements is non-disjoint.
-/
def Intersecting (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬Disjoint a b

@[gcongr, mono]
/-
**Set.Intersecting.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s t : Se
t α}, t ⊆ s → s.Intersecting → t.Intersecting
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Intersecting.mono (h : t ⊆ s) (hs : s.Intersecting) : t.Intersecting := fun _a ha _b hb =>
  hs (h ha) (h hb)
/-
**Set.Intersecting.bot_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set 
α}, s.Intersecting → ⊥ ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
theorem Intersecting.bot_notMem (hs : s.Intersecting) : ⊥ ∉ s := fun h => hs h h disjoint_bot_left
/-
**Set.Intersecting.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set 
α} {a : α}, s.Intersecting → a ∈ s → a ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Set.Intersecting.bot_notMem`：∀ {α : Type u_1} [inst : SemilatticeInf α] 
[inst_1 : OrderBot α] {s : Set α}, s.Intersecting → ⊥ ∉ s
-/
theorem Intersecting.ne_bot (hs : s.Intersecting) (ha : a ∈ s) : a ≠ ⊥ :=
  ne_of_mem_of_not_mem ha hs.bot_notMem
/-
**Set.intersecting_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intersecting_empty : (∅ : Set α).Intersecting
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intersecting_empty : (∅ : Set α).Intersecting := fun _ => False.elim

@[simp]
/-
**Set.intersecting_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intersecting_singleton : ({a} : Set α).Intersecting ↔ a != ⊥
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intersecting_singleton : ({a} : Set α).Intersecting ↔ a ≠ ⊥ := by simp [Intersecting]
/-
**Set.Intersecting.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set 
α} {a : α},   s.Intersecting → a ≠ ⊥ → (∀ b ∈ s, ¬Disjoint a b) → (insert a s).I
ntersecting
参数：∀ b ∈ s, ¬Disjoint a b；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
protected theorem Intersecting.insert (hs : s.Intersecting) (ha : a ≠ ⊥)
    (h : ∀ b ∈ s, ¬Disjoint a b) : (insert a s).Intersecting := by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
  · exact h _ hc
  · exact fun H => h _ hb H.symm
  · exact hs hb hc
/-
**Set.intersecting_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intersecting_insert : (insert a s).Intersecting ↔ s.Intersecting ∧ a != ⊥ 
∧ forall b in s, ¬Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Intersecting.mono`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_
1 : OrderBot α] {s t : Set α}, t ⊆ s → s.Intersecting → t.Intersecting
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.Intersecting.ne_bot`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α}, s.Intersecting → a ∈ s → a ≠ ⊥
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.Intersecting.insert`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α},   s.Intersecting → a ≠ ⊥ → (∀ b ∈ s, ¬Dis
joint a b) → …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem intersecting_insert :
    (insert a s).Intersecting ↔ s.Intersecting ∧ a ≠ ⊥ ∧ ∀ b ∈ s, ¬Disjoint a b :=
  ⟨fun h =>
    ⟨h.mono <| subset_insert _ _, h.ne_bot <| mem_insert _ _, fun _b hb =>
      h (mem_insert _ _) <| mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩
/-
**Set.intersecting_iff_pairwise_not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intersecting_iff_pairwise_not_disjoint : s.Intersecting ↔ (s.Pairwise fun 
a b => ¬Disjoint a b) ∧ s != {⊥}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.intersecting_singleton`：intersecting_singleton : ({a} : Set α).Inter
secting ↔ a != ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
theorem intersecting_iff_pairwise_not_disjoint :
    s.Intersecting ↔ (s.Pairwise fun a b => ¬Disjoint a b) ∧ s ≠ {⊥} := by
  refine ⟨fun h => ⟨fun a ha b hb _ => h ha hb, ?_⟩, fun h a ha b hb hab => ?_⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
  have := h.1.eq ha hb (Classical.not_not.2 hab)
  rw [this, disjoint_self] at hab
  rw [hab] at hb
  exact
    h.2
      (eq_singleton_iff_unique_mem.2
        ⟨hb, fun c hc => not_ne_iff.1 fun H => h.1 hb hc H.symm disjoint_bot_left⟩)
/-
**Set.Subsingleton.intersecting** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set 
α},   s.Subsingleton → (s.Intersecting ↔ s ≠ {⊥})
参数：s.Intersecting ↔ s ≠ {⊥}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.intersecting_iff_pairwise_not_disjoint`：intersecting_iff_pairwise_no
t_disjoint : s.Intersecting ↔ (s.Pairwise fun a b => ¬Disjoint a b) ∧ s != {⊥}
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
protected theorem Subsingleton.intersecting (hs : s.Subsingleton) : s.Intersecting ↔ s ≠ {⊥} :=
  intersecting_iff_pairwise_not_disjoint.trans <| and_iff_right <| hs.pairwise _
/-
**Set.intersecting_iff_eq_empty_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intersecting_iff_eq_empty_of_subsingleton [Subsingleton α] (s : Set α) : s
.Intersecting ↔ s = ∅
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.Subsingleton.intersecting`：∀ {α : Type u_1} [inst : SemilatticeInf α
] [inst_1 : OrderBot α] {s : Set α},   s.Subsingleton → (s.Intersecting ↔ s ≠ {⊥
})
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem intersecting_iff_eq_empty_of_subsingleton [Subsingleton α] (s : Set α) :
    s.Intersecting ↔ s = ∅ := by
  refine
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
    rwa [Subsingleton.elim ⊥ a]
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm

/-- Maximal intersecting families are upper sets. -/
/-
**Set.Intersecting.isUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set 
α},   s.Intersecting → (∀ (t : Set α), t.Intersecting → s ⊆ t → s = t) → IsUpper
Set s
参数：∀ (t : Set α), t.Intersecting → s ⊆ t → s = t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Intersecting.insert`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α},   s.Intersecting → a ≠ ⊥ → (∀ b ∈ s, ¬Dis
joint a b) → …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `Set.Intersecting.ne_bot`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α}, s.Intersecting → a ∈ s → a ≠ ⊥
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
Maximal intersecting families are upper sets.
-/
protected theorem Intersecting.isUpperSet (hs : s.Intersecting)
    (h : ∀ t : Set α, t.Intersecting → s ⊆ t → s = t) : IsUpperSet s := by
  rintro a b hab ha
  rw [h (Insert.insert b s) _ (subset_insert _ _)]
  · exact mem_insert _ _
  exact
    hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab

/-- Maximal intersecting families are upper sets. Finset version. -/
/-
**Set.Intersecting.isUpperSet'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Fins
et α},   (↑s).Intersecting → (∀ (t : Finset α), (↑t).Intersecting → s ⊆ t → s = 
t) → IsUpperSet ↑s
参数：↑s；∀ (t : Finset α), (↑t).Intersecting → s ⊆ t → s = t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.Intersecting.insert`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α},   s.Intersecting → a ≠ ⊥ → (∀ b ∈ s, ¬Dis
joint a b) → …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `Set.Intersecting.ne_bot`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α}, s.Intersecting → a ∈ s → a ≠ ⊥
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s

--- 原说明 ---
Maximal intersecting families are upper sets. Finset version.
-/
theorem Intersecting.isUpperSet' {s : Finset α} (hs : (s : Set α).Intersecting)
    (h : ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) : IsUpperSet (s : Set α) := by
  classical
    rintro a b hab ha
    rw [h (Insert.insert b s) _ (Finset.subset_insert _ _)]
    · exact mem_insert_self _ _
    rw [coe_insert]
    exact
      hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab

end SemilatticeInf

section

variable {α : Type*}

/-
**Set.Intersecting.exists_mem_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} {𝒜 : Set (Set α)}, 𝒜.Intersecting → ∀ {s t : Set α}, s ∈ 
𝒜 → t ∈ 𝒜 → ∃ a ∈ s, a ∈ t
参数：Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
-/
theorem Intersecting.exists_mem_set {𝒜 : Set (Set α)} (h𝒜 : 𝒜.Intersecting) {s t : Set α}
    (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| h𝒜 hs ht
/-
**Set.Intersecting.exists_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Set (Finset α)},   𝒜.Intersec
ting → ∀ {s t : Finset α}, s ∈ 𝒜 → t ∈ 𝒜 → ∃ a ∈ s, a ∈ t
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
-/
theorem Intersecting.exists_mem_finset [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.Intersecting)
    {s t : Finset α} (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| disjoint_coe.not.2 <| h𝒜 hs ht

variable [BooleanAlgebra α]
/-
**Set.Intersecting.compl_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] {s : Set α}, s.Intersecting → ∀
 {a : α}, a ∈ s → aᶜ ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem Intersecting.compl_notMem {s : Set α} (hs : s.Intersecting) {a : α} (ha : a ∈ s) :
    aᶜ ∉ s := fun h => hs ha h disjoint_compl_right
/-
**Set.Intersecting.notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] {s : Set α}, s.Intersecting → ∀
 {a : α}, aᶜ ∈ s → a ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem Intersecting.notMem {s : Set α} (hs : s.Intersecting) {a : α} (ha : aᶜ ∈ s) : a ∉ s :=
  fun h => hs ha h disjoint_compl_left
/-
**Set.Intersecting.disjoint_map_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersectin
g`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] {s : Finset α},   (↑s).Intersec
ting → Disjoint s (Finset.map { toFun := compl, inj' := ⋯ } s)
参数：↑s；Finset.map { toFun := compl, inj' := ⋯ } s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Set.Intersecting.compl_notMem`：∀ {α : Type u_1} [inst : BooleanAlgebra α
] {s : Set α}, s.Intersecting → ∀ {a : α}, a ∈ s → aᶜ ∉ s
-/
theorem Intersecting.disjoint_map_compl {s : Finset α} (hs : (s : Set α).Intersecting) :
    Disjoint s (s.map ⟨compl, compl_injective⟩) := by
  rw [Finset.disjoint_left]
  rintro x hx hxc
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc
  exact hs.compl_notMem hx' hx
/-
**Set.Intersecting.card_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] [inst_1 : Fintype α] {s : Finse
t α},   (↑s).Intersecting → 2 * s.card ≤ Fintype.card α
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Set.Intersecting.disjoint_map_compl`：∀ {α : Type u_1} [inst : BooleanAlg
ebra α] {s : Finset α},   (↑s).Intersecting → Disjoint s (Finset.map { toFun := 
compl, inj' := ⋯ } s)
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Finset.card_disjUnion`：card_disjUnion (s t : Finset α) (h) : #(s.disjUni
on t h) = #s + #t
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem Intersecting.card_le [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting) :
    2 * #s ≤ Fintype.card α := by
  refine (s.disjUnion _ hs.disjoint_map_compl).card_le_univ.trans_eq' ?_
  rw [Nat.two_mul, card_disjUnion, card_map]

variable [Nontrivial α] [Fintype α] {s : Finset α}

-- Note, this lemma is false when `α` has exactly one element and boring when `α` is empty.
/-
**Set.Intersecting.is_max_iff_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersectin
g`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] [Nontrivial α] [inst_2 : Fintyp
e α] {s : Finset α},   (↑s).Intersecting → ((∀ (t : Finset α), (↑t).Intersecting
 → s ⊆ t → s = t) ↔ 2 * s.card = Fintype.card α)
参数：↑s；(∀ (t : Finset α), (↑t).Intersecting → s ⊆ t → s = t) ↔ 2 * s.card = Finty
pe.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Set.Intersecting.disjoint_map_compl`：∀ {α : Type u_1} [inst : BooleanAlg
ebra α] {s : Finset α},   (↑s).Intersecting → Disjoint s (Finset.map { toFun := 
compl, inj' := ⋯ } s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_univ`：coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.ne_insert_of_notMem`：ne_insert_of_notMem (s t : Finset α) {a : α}
 (h : a ∉ s) : s != insert a t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.Intersecting.insert`：∀ {α : Type u_1} [inst : SemilatticeInf α] [ins
t_1 : OrderBot α] {s : Set α} {a : α},   s.Intersecting → a ≠ ⊥ → (∀ b ∈ s, ¬Dis
joint a b) → …
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.intersecting_singleton`：intersecting_singleton : ({a} : Set α).Inter
secting ↔ a != ⊥
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `IsUpperSet.top_notMem`：IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s
 ↔ s = ∅
· 使用定理 `Set.Intersecting.isUpperSet'`：∀ {α : Type u_1} [inst : SemilatticeInf α]
 [inst_1 : OrderBot α] {s : Finset α},   (↑s).Intersecting → (∀ (t : Finset α), 
(↑t).Intersecting …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `Disjoint.le_compl_left`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b 
: α}, Disjoint b a → a ≤ bᶜ
（共 40 条，此处仅展示前 30 条）
-/
theorem Intersecting.is_max_iff_card_eq (hs : (s : Set α).Intersecting) :
    (∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) ↔ 2 * #s = Fintype.card α := by
  classical
    refine ⟨fun h ↦ ?_, fun h t ht hst ↦ Finset.eq_of_subset_of_card_le hst <|
      Nat.le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) Nat.two_pos⟩
    suffices s.disjUnion (s.map ⟨compl, compl_injective⟩) hs.disjoint_map_compl = Finset.univ by
      rw [Fintype.card, ← this, Nat.two_mul, card_disjUnion, card_map]
    rw [← coe_eq_univ, disjUnion_eq_union, coe_union, coe_map, Function.Embedding.coeFn_mk,
      image_eq_preimage_of_inverse compl_compl compl_compl]
    refine eq_univ_of_forall fun a => ?_
    simp_rw [mem_union, mem_preimage]
    by_contra! ha
    refine s.ne_insert_of_notMem _ ha.1 (h _ ?_ <| s.subset_insert _)
    rw [coe_insert]
    refine hs.insert ?_ fun b hb hab => ha.2 <| (hs.isUpperSet' h) hab.le_compl_left hb
    rintro rfl
    have := h {⊤} (by rw [coe_singleton]; exact intersecting_singleton.2 top_ne_bot)
    rw [compl_bot] at ha
    rw [coe_eq_empty.1 ((hs.isUpperSet' h).top_notMem.1 ha.2)] at this
    exact Finset.singleton_ne_empty _ (this <| Finset.empty_subset _).symm
/-
**Set.Intersecting.exists_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Intersecting`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] [Nontrivial α] [inst_2 : Fintyp
e α] {s : Finset α},   (↑s).Intersecting → ∃ t, s ⊆ t ∧ 2 * t.card = Fintype.car
d α ∧ (↑t).Intersecting
参数：↑s；↑t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Intersecting.card_le`：∀ {α : Type u_1} [inst : BooleanAlgebra α] [in
st_1 : Fintype α] {s : Finset α},   (↑s).Intersecting → 2 * s.card ≤ Fintype.car
d α
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Intersecting.is_max_iff_card_eq`：∀ {α : Type u_1} [inst : BooleanAlg
ebra α] [Nontrivial α] [inst_2 : Fintype α] {s : Finset α},   (↑s).Intersecting 
→ ((∀ (t : Finset α), (↑t…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `Nat.two_pos`：0 < 2
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Intersecting.exists_card_eq (hs : (s : Set α).Intersecting) :
    ∃ t, s ⊆ t ∧ 2 * #t = Fintype.card α ∧ (t : Set α).Intersecting := by
  have := hs.card_le
  rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le Nat.two_pos] at this
  revert hs
  refine s.strongDownwardInductionOn ?_ this
  rintro s ih _hcard hs
  by_cases! h : ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t
  · exact ⟨s, Subset.rfl, hs.is_max_iff_card_eq.1 h, hs⟩
  obtain ⟨t, ht, hst⟩ := h
  refine (ih ?_ (_root_.ssubset_iff_subset_ne.2 hst) ht).imp fun u => And.imp_left hst.1.trans
  rw [Nat.le_div_iff_mul_le Nat.two_pos, Nat.mul_comm]
  exact ht.card_le

end

/-!
### `L`-intersecting families

This section defines `L`-intersecting families and establishes their basic properties.
-/

variable {L L' : Set ℕ}
variable {α : Type*} [DecidableEq α]
variable {𝒜 ℬ : Set (Finset α)}

/--
A family `𝒜` of finite subsets of `α` is `L`-intersecting if the intersection size of every pair of
distinct members of `𝒜` belongs to `L ⊆ ℕ`.

That is, for all `s, t ∈ 𝒜` with `s ≠ t`, we have `|(s ∩ t)| ∈ L`.
-/
/-
**Set.IsIntersectingOf** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IsIntersectingOf (L : Set Nat) (𝒜 : Set (Finset α)) : Prop
参数：L : Set Nat；𝒜 : Set (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `𝒜` of finite subsets of `α` is `L`-intersecting if the intersection si
ze of every pair of
distinct members of `𝒜` belongs to `L ⊆ ℕ`.

That is, for all `s, t ∈ 𝒜` with `s ≠ t`, we have `|(s ∩ t)| ∈ L`.
-/
def IsIntersectingOf (L : Set ℕ) (𝒜 : Set (Finset α)) : Prop := 𝒜.Pairwise fun s t ↦ #(s ∩ t) ∈ L

namespace IsIntersectingOf

/--
An `L`-intersecting family is also `L'`-intersecting whenever `L ⊆ L'`.
-/
@[gcongr]
/-
**Set.IsIntersectingOf.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsIntersectingOf`。
形式化陈述：mono (h : L subseteq L') (hL : IsIntersectingOf L 𝒜) : IsIntersectingOf L'
 𝒜
参数：h : L subseteq L'；hL : IsIntersectingOf L 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `L`-intersecting family is also `L'`-intersecting whenever `L ⊆ L'`.
-/
theorem mono (h : L ⊆ L') (hL : IsIntersectingOf L 𝒜) : IsIntersectingOf L' 𝒜 := by tauto

/--
An `L`-intersecting family remains `L`-intersecting under restriction to any subfamily.
-/
@[gcongr]
/-
**Set.IsIntersectingOf.anti** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsIntersectingOf`。
形式化陈述：anti (h : ℬ subseteq 𝒜) (h𝒜 : IsIntersectingOf L 𝒜) : IsIntersectingOf L ℬ
参数：h : ℬ subseteq 𝒜；h𝒜 : IsIntersectingOf L 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r

--- 原说明 ---
An `L`-intersecting family remains `L`-intersecting under restriction to any sub
family.
-/
theorem anti (h : ℬ ⊆ 𝒜) (h𝒜 : IsIntersectingOf L 𝒜) : IsIntersectingOf L ℬ := Pairwise.mono h h𝒜

/--
The empty family of finite sets is `L`-intersecting, vacuously, because it contains no pairs of
sets.
-/
@[simp]
/-
**Set.IsIntersectingOf.empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsIntersectingOf`。
形式化陈述：∀ {L : Set ℕ} {α : Type u_1} [inst : DecidableEq α], L.IsIntersectingOf ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty family of finite sets is `L`-intersecting, vacuously, because it conta
ins no pairs of
sets.
-/
protected theorem empty : IsIntersectingOf L (∅ : Set (Finset α)) := by tauto

/--
Every family of finite sets is `univ`-intersecting.
-/
@[simp]
/-
**Set.IsIntersectingOf.univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsIntersectingOf`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Set (Finset α)}, Set.univ.IsI
ntersectingOf 𝒜
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_of_forall`：pairwise_of_forall (s : Set α) (r : α -> α -> Pr
op) (h : forall a b, r a b) : s.Pairwise r
· 使用定理 `trivial`：True

--- 原说明 ---
Every family of finite sets is `univ`-intersecting.
-/
protected theorem univ : IsIntersectingOf univ 𝒜 := 𝒜.pairwise_of_forall _ fun _ _ ↦ trivial

end IsIntersectingOf

end Set

