/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Equitable functions

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the codomain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `SuccOrder` + `ConditionallyCompleteMonoid`, but we don't have the
latter yet.
-/

@[expose] public section


variable {α β : Type*}

namespace Set

/-- A set is equitable if no element value is more than one bigger than another. -/
/-
**Set.EquitableOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α -> β) : Prop
参数：s : Set α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is equitable if no element value is more than one bigger than another.
-/
def EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1

@[simp]
/-
**Set.equitableOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：equitableOn_empty [LE β] [Add β] [One β] (f : α -> β) : EquitableOn ∅ f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem equitableOn_empty [LE β] [Add β] [One β] (f : α → β) : EquitableOn ∅ f := fun a _ ha =>
  (Set.notMem_empty a ha).elim
/-
**Set.equitableOn_iff_exists_le_le_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：equitableOn_iff_exists_le_le_add_one {s : Set α} {f : α -> Nat} : s.Equita
bleOn f ↔ exists b, forall a in s, b <= f a ∧ f a <= b + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem equitableOn_iff_exists_le_le_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, b ≤ f a ∧ f a ≤ b + 1 := by
  refine ⟨?_, fun ⟨b, hb⟩ x y hx hy => by grw [(hb x hx).2, (hb y hy).1]⟩
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  intro hs
  by_cases! h : ∀ y ∈ s, f x ≤ f y
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
  obtain ⟨w, hw, hwx⟩ := h
  refine ⟨f w, fun y hy => ⟨Nat.le_of_succ_le_succ ?_, hs hy hw⟩⟩
  rw [(Nat.succ_le_of_lt hwx).antisymm (hs hx hw)]
  exact hs hx hy
/-
**Set.equitableOn_iff_exists_image_subset_icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：equitableOn_iff_exists_image_subset_icc {s : Set α} {f : α -> Nat} : s.Equ
itableOn f ↔ exists b, f '' s subseteq Icc b (b + 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.equitableOn_iff_exists_le_le_add_one`：equitableOn_iff_exists_le_le_a
dd_one {s : Set α} {f : α -> Nat} : s.EquitableOn f ↔ exists b, forall a in s, b
 <= f a ∧ f a <= b + 1
-/
theorem equitableOn_iff_exists_image_subset_icc {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, f '' s ⊆ Icc b (b + 1) := by
  simpa only [image_subset_iff] using! equitableOn_iff_exists_le_le_add_one
/-
**Set.equitableOn_iff_exists_eq_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：equitableOn_iff_exists_eq_eq_add_one {s : Set α} {f : α -> Nat} : s.Equita
bleOn f ↔ exists b, forall a in s, f a = b ∨ f a = b + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equitableOn_iff_exists_eq_eq_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 := by
  simp_rw [equitableOn_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]

section LinearOrder
variable [LinearOrder β] [Add β] [One β] {s : Set α} {f : α → β}

@[simp]
/-
**Set.not_equitableOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_equitableOn : ¬s.EquitableOn f ↔ exists a in s, exists b in s, f b + 1
 < f a
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
lemma not_equitableOn : ¬s.EquitableOn f ↔ ∃ a ∈ s, ∃ b ∈ s, f b + 1 < f a := by
  simp [EquitableOn]

end LinearOrder

section OrderedSemiring

variable [Semiring β] [PartialOrder β] [IsOrderedRing β]

/-
**Set.Subsingleton.equitableOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Semiring β] [inst_1 : PartialOrder
 β] [IsOrderedRing β] {s : Set α},   s.Subsingleton → ∀ (f : α → β), s.Equitable
On f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
theorem Subsingleton.equitableOn {s : Set α} (hs : s.Subsingleton) (f : α → β) : s.EquitableOn f :=
  fun i j hi hj => by
  rw [hs hi hj]
  exact le_add_of_nonneg_right zero_le_one
/-
**Set.equitableOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：equitableOn_singleton (a : α) (f : α -> β) : Set.EquitableOn {a} f
参数：a : α；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.equitableOn`：∀ {α : Type u_1} {β : Type u_2} [inst : Se
miring β] [inst_1 : PartialOrder β] [IsOrderedRing β] {s : Set α},   s.Subsingle
ton → ∀ (f : α → β…
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem equitableOn_singleton (a : α) (f : α → β) : Set.EquitableOn {a} f :=
  Set.subsingleton_singleton.equitableOn f

end OrderedSemiring

end Set

open Set

namespace Finset

variable {s : Finset α} {f : α → ℕ} {a : α}

/-
**Finset.equitableOn_iff_le_le_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：equitableOn_iff_le_le_add_one : EquitableOn (s : Set α) f ↔ forall a in s,
 (∑ i in s, f i) / s.card <= f a ∧ f a <= (∑ i in s, f i) / s.card + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.equitableOn_iff_exists_le_le_add_one`：equitableOn_iff_exists_le_le_a
dd_one {s : Set α} {f : α -> Nat} : s.EquitableOn f ↔ exists b, forall a in s, b
 <= f a ∧ f a <= b + 1
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_eq_of_lt_le`：∀ {k n m : ℕ}, k * n ≤ m → m < (k + 1) * n → m / n 
= k
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.sum_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → M} {s : Fins
et ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 32 条，此处仅展示前 30 条）
-/
theorem equitableOn_iff_le_le_add_one :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, (∑ i ∈ s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i ∈ s, f i) / s.card + 1 := by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨b, hb⟩
  by_cases! h : ∀ a ∈ s, f a = b + 1
  · intro a ha
    rw [h _ ha, sum_const_nat h, Nat.mul_div_cancel_left _ (card_pos.2 ⟨a, ha⟩)]
    exact ⟨le_rfl, Nat.le_succ _⟩
  obtain ⟨x, hx₁, hx₂⟩ := h
  suffices h : b = (∑ i ∈ s, f i) / s.card by
    simp_rw [← h]
    apply hb
  symm
  refine
    Nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum fun a ha => (hb a ha).1))
      ((sum_lt_sum (fun a ha => (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le ?_)
  rw [mul_comm, sum_const_nat]
  exact fun _ _ => rfl
/-
**Finset.EquitableOn.le** 是 Mathlib 中的一个定理，位于命名空间 `Finset.EquitableOn`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ} {a : α}, (↑s).EquitableOn f → 
a ∈ s → (∑ i ∈ s, f i) / s.card ≤ f a
参数：↑s；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.equitableOn_iff_le_le_add_one`：equitableOn_iff_le_le_add_one : Eq
uitableOn (s : Set α) f ↔ forall a in s, (∑ i in s, f i) / s.card <= f a ∧ f a <
= (∑ i in s, f i) / s.card…
-/
theorem EquitableOn.le (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    (∑ i ∈ s, f i) / s.card ≤ f a :=
  (equitableOn_iff_le_le_add_one.1 h a ha).1
/-
**Finset.EquitableOn.le_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset.EquitableOn`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ} {a : α}, (↑s).EquitableOn f → 
a ∈ s → f a ≤ (∑ i ∈ s, f i) / s.card + 1
参数：↑s；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.equitableOn_iff_le_le_add_one`：equitableOn_iff_le_le_add_one : Eq
uitableOn (s : Set α) f ↔ forall a in s, (∑ i in s, f i) / s.card <= f a ∧ f a <
= (∑ i in s, f i) / s.card…
-/
theorem EquitableOn.le_add_one (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    f a ≤ (∑ i ∈ s, f i) / s.card + 1 :=
  (equitableOn_iff_le_le_add_one.1 h a ha).2
/-
**Finset.equitableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：equitableOn_iff : EquitableOn (s : Set α) f ↔ forall a in s, f a = (∑ i in
 s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equitableOn_iff :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, f a = (∑ i ∈ s, f i) / s.card ∨ f a = (∑ i ∈ s, f i) / s.card + 1 := by
  simp_rw [equitableOn_iff_le_le_add_one, Nat.le_and_le_add_one_iff]

end Finset

