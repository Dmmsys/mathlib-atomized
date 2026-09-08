/-
Copyright (c) 2025 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Powerset

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

public section

open scoped Pointwise

namespace Finset
variable {M : Type*} [DecidableEq M] [AddCommMonoid M] {A : Finset M} {a : M}

/-- The subset-sum of a finite set `A` in a commutative monoid is the set of all sums
of subsets of `A`. -/
/-
**Finset.subsetSum** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：subsetSum (A : Finset M) : Finset M
参数：A : Finset M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subset-sum of a finite set `A` in a commutative monoid is the set of all sum
s
of subsets of `A`.
-/
def subsetSum (A : Finset M) : Finset M := A.powerset.image fun B ↦ B.sum id
/-
**Finset.mem_subsetSum_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_subsetSum_iff : a in A.subsetSum ↔ exists B subseteq A, ∑ b in B, b = 
a
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_subsetSum_iff : a ∈ A.subsetSum ↔ ∃ B ⊆ A, ∑ b ∈ B, b = a := by simp [subsetSum]

@[simp]
/-
**Finset.zero_mem_subsetSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_mem_subsetSum : 0 in A.subsetSum
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_subsetSum_iff`：mem_subsetSum_iff : a in A.subsetSum ↔ exists 
B subseteq A, ∑ b in B, b = a
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
-/
lemma zero_mem_subsetSum : 0 ∈ A.subsetSum := mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩
/-
**Finset.subsetSum_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {M : Type u_1} [inst : DecidableEq M] [inst_1 : AddCommMonoid M] {A : Fi
nset M}, A.subsetSum.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma subsetSum_nonempty : A.subsetSum.Nonempty := ⟨0, by simp⟩
/-
**Finset.subset_subsetSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_subsetSum : A subseteq A.subsetSum
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_subsetSum_iff`：mem_subsetSum_iff : a in A.subsetSum ↔ exists 
B subseteq A, ∑ b in B, b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma subset_subsetSum : A ⊆ A.subsetSum :=
  fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]
/-
**Finset.subsetSum_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subsetSum_mono {B : Finset M} (hAB : A subseteq B) : A.subsetSum subseteq 
B.subsetSum
参数：hAB : A subseteq B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_mono`：image_mono (f : α -> β) : Monotone (Finset.image f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.powerset_mono`：powerset_mono {s t : Finset α} : powerset s subset
eq powerset t ↔ s subseteq t
-/
lemma subsetSum_mono {B : Finset M} (hAB : A ⊆ B) : A.subsetSum ⊆ B.subsetSum :=
  image_mono _ <| powerset_mono.mpr hAB
/-
**Finset.subsetSum_erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {M : Type u_1} [inst : DecidableEq M] [inst_1 : AddCommMonoid M] {A : Fi
nset M}, (A.erase 0).subsetSum = A.subsetSum
参数：A.erase 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.subsetSum_mono`：subsetSum_mono {B : Finset M} (hAB : A subseteq B
) : A.subsetSum subseteq B.subsetSum
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.mem_subsetSum_iff`：mem_subsetSum_iff : a in A.subsetSum ↔ exists 
B subseteq A, ∑ b in B, b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `Finset.sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid 
M] [inst_1 : DecidableEq ι] (s : Finset ι) {f : ι → M} {a : ι},   f a = 0 → ∑ x 
∈ s.er…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma subsetSum_erase_zero : (A.erase 0).subsetSum = A.subsetSum := by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨B.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hB (mem_of_mem_erase hi)⟩
/-
**Finset.vadd_finset_subsetSum_subset_subsetSum_insert** 是 Mathlib 中的一个引理，位于命名空间
 `Finset`。
形式化陈述：vadd_finset_subsetSum_subset_subsetSum_insert (a_notin_A : a ∉ A) : a +ᵥ A
.subsetSum subseteq (insert a A).subsetSum
参数：a_notin_A : a ∉ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vadd_finset_subsetSum_subset_subsetSum_insert (a_notin_A : a ∉ A) :
    a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum := by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact ⟨insert a B, by aesop, by rw [sum_insert (fun h => a_notin_A (hB h))]; simp⟩

variable [LinearOrder M] [IsOrderedCancelAddMonoid M]
/-
**Finset.nonneg_of_mem_subsetSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nonneg_of_mem_subsetSum (A_nonneg : forall x in A, 0 <= x) : forall x in A
.subsetSum, 0 <= x
参数：A_nonneg : forall x in A, 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
-/
lemma nonneg_of_mem_subsetSum (A_nonneg : ∀ x ∈ A, 0 ≤ x) : ∀ x ∈ A.subsetSum, 0 ≤ x := by
  simpa [mem_subsetSum_iff] using fun B hB ↦ Finset.sum_nonneg fun x hx ↦ A_nonneg _ <| hB hx
/-
**Finset.card_add_card_subsetSum_lt_card_subsetSum_insert_max** 是 Mathlib 中的一个引理
，位于命名空间 `Finset`。
形式化陈述：card_add_card_subsetSum_lt_card_subsetSum_insert_max (hA : forall x in A, 
0 < x) (hAa : forall x in A, x < a) (ha : 0 < a) : #A + #A.subsetSum < #(insert 
a A).subsetSum
参数：hA : forall x in A, 0 < x；hAa : forall x in A, x < a；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.nonneg_of_mem_subsetSum`：nonneg_of_mem_subsetSum (A_nonneg : fora
ll x in A, 0 <= x) : forall x in A.subsetSum, 0 <= x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `lt_add_of_lt_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddLeftMono α] {a b c : α}, b < c → 0 ≤ a → b < c + a
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `mem_of_le_of_mem`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [
inst_1 : LE A] [IsConcreteLE A B] {S T : A},   S ≤ T → ∀ ⦃x : B⦄, x ∈ S → x ∈ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Finset.subsetSum_mono`：subsetSum_mono {B : Finset M} (hAB : A subseteq B
) : A.subsetSum subseteq B.subsetSum
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Finset.zero_mem_subsetSum`：zero_mem_subsetSum : 0 in A.subsetSum
· 使用引理 `Finset.subset_subsetSum`：subset_subsetSum : A subseteq A.subsetSum
· 使用引理 `Finset.vadd_finset_subsetSum_subset_subsetSum_insert`：vadd_finset_subset
Sum_subset_subsetSum_insert (a_notin_A : a ∉ A) : a +ᵥ A.subsetSum subseteq (ins
ert a A).subsetSum
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 43 条，此处仅展示前 30 条）
-/
lemma card_add_card_subsetSum_lt_card_subsetSum_insert_max (hA : ∀ x ∈ A, 0 < x)
    (hAa : ∀ x ∈ A, x < a) (ha : 0 < a) :
    #A + #A.subsetSum < #(insert a A).subsetSum := by
  -- We show that `insert 0 A` and `a +ᵥ A.subsetSum` are disjoint subsets of
  -- `(insert a A).subsetSum`, and their combined cardinality gives the result.
  -- The sets are disjoint.
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    have := nonneg_of_mem_subsetSum (fun y hy ↦ (hA y hy).le)
    simpa [disjoint_left, mem_insert, mem_vadd_finset] using
      ⟨fun x hx => (add_pos_of_pos_of_nonneg ha <| this _ hx).ne',
        fun x hx y hy ↦ (lt_add_of_lt_of_nonneg (hAa x hx) <| this _ hy).ne'⟩
  -- Both sets are subsets of `(insert a A).subsetSum`.
  have insert_subset : insert 0 A ⊆ (insert a A).subsetSum := by
    grw [insert_subset_iff, ← subset_insert]; exact ⟨zero_mem_subsetSum, subset_subsetSum⟩
  have vadd_subset : a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (hAa a ha).false
  -- Count the sizes.
  calc #A + #A.subsetSum
    _ < #A + 1 + #A.subsetSum := by gcongr; exact Nat.lt_add_one _
    _ = #(insert 0 A) + #A.subsetSum := by rw [card_insert_of_notMem fun h => (hA 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by simp [vadd_finset_def, card_image_of_injOn]
    _ = #((insert 0 A) ∪ (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ ≤ #(insert a A).subsetSum := by grw [union_subset insert_subset vadd_subset]

-- The proof follows Theorem 3 in [Nathanson1995].
/-
**Finset.card_succ_choose_two_lt_card_subsetSum_of_pos** 是 Mathlib 中的一个定理，位于命名空间
 `Finset`。
形式化陈述：card_succ_choose_two_lt_card_subsetSum_of_pos (A_pos : forall x in A, 0 < 
x) : (#A + 1).choose 2 < #A.subsetSum
参数：A_pos : forall x in A, 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max`：induction_on_max [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, x < a) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Nat.choose_succ_left`：choose_succ_left (n k : Nat) (hk : 0 < k) : choose
 (n + 1) k = choose n (k - 1) + choose n k
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用引理 `Finset.card_add_card_subsetSum_lt_card_subsetSum_insert_max`：card_add_ca
rd_subsetSum_lt_card_subsetSum_insert_max (hA : forall x in A, 0 < x) (hAa : for
all x in A, x < a) (ha : 0 < a) : #A + #A.subsetS…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem card_succ_choose_two_lt_card_subsetSum_of_pos (A_pos : ∀ x ∈ A, 0 < x) :
    (#A + 1).choose 2 < #A.subsetSum := by
  induction A using induction_on_max with
  | empty => simp
  | insert a A A_lt_a ih =>
    have A_pos' : ∀ x ∈ A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    grw [card_insert_of_notMem fun ha => (A_lt_a a ha).false, Nat.choose_succ_left _ _ (by lia),
      Nat.choose_one_right, add_right_comm, add_assoc, Nat.add_one_le_iff.2 (ih A_pos')]
    exact card_add_card_subsetSum_lt_card_subsetSum_insert_max A_pos' A_lt_a <| A_pos a <|
      mem_insert_self a A
/-
**Finset.card_choose_two_lt_card_subsetSum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：card_choose_two_lt_card_subsetSum_of_nonneg (A_pos : forall x in A, 0 <= x
) : (#A).choose 2 < #A.subsetSum
参数：A_pos : forall x in A, 0 <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Nat.choose_le_choose`：choose_le_choose {a b : Nat} (c : Nat) (h : a <= b
) : choose a c <= choose b c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Finset.pred_card_le_card_erase`：pred_card_le_card_erase : #s - 1 <= #(s.
erase a)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_succ_choose_two_lt_card_subsetSum_of_pos`：card_succ_choose_t
wo_lt_card_subsetSum_of_pos (A_pos : forall x in A, 0 < x) : (#A + 1).choose 2 <
 #A.subsetSum
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subsetSum_erase_zero`：∀ {M : Type u_1} [inst : DecidableEq M] [in
st_1 : AddCommMonoid M] {A : Finset M}, (A.erase 0).subsetSum = A.subsetSum
-/
theorem card_choose_two_lt_card_subsetSum_of_nonneg (A_pos : ∀ x ∈ A, 0 ≤ x) :
    (#A).choose 2 < #A.subsetSum := by
  calc (#A).choose 2
    _ ≤ (#(A.erase 0) + 1).choose 2 := by grw [tsub_le_iff_right.1 <| pred_card_le_card_erase]
    _ < #(A.erase 0).subsetSum :=
        card_succ_choose_two_lt_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

end Finset

