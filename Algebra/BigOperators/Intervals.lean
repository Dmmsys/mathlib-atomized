/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Results about big operators over intervals

We prove results about big operators over intervals.
-/

public section

open Nat Finset

variable {α G M : Type*}

namespace Finset

section Generic
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

@[to_additive]
/-
**Finset.prod_Ico_add'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid
 α] [ExistsAddOfLE α] [LocallyFiniteOrder α] (f : α -> M) (a b c : α) : (∏ x in 
Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x
参数：f : α -> M；a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_right_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
-/
theorem prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (x + c)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl

@[to_additive]
/-
**Finset.prod_Ico_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_add [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid 
α] [ExistsAddOfLE α] [LocallyFiniteOrder α] (f : α -> M) (a b c : α) : (∏ x in I
co a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x
参数：f : α -> M；a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.prod_Ico_add'`：prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [
IsOrderedCancelAddMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α] (f : α -> M
) (a b c :…
-/
theorem prod_Ico_add [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (c + x)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  convert! prod_Ico_add' f a b c using 2
  rw [add_comm]

@[to_additive (attr := simp)]
/-
**Finset.prod_Ico_add_right_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_add_right_sub_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCan
celAddMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α] [Sub α] [OrderedSub α] 
(a b c : α) : ∏ x in Ico (a + c) (b + c), f (x - c) = ∏ x in Ico a b, f x
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_add_right_sub_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α] [Sub α] [OrderedSub α] (a b c : α) :
    ∏ x ∈ Ico (a + c) (b + c), f (x - c) = ∏ x ∈ Ico a b, f x := by
  simp only [← map_add_right_Ico, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

@[to_additive]
/-
**Finset.prod_Ico_succ_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_succ_top {a b : Nat} (hab : a <= b) (f : Nat -> M) : (∏ k in Ico 
a (b + 1), f k) = (∏ k in Ico a b, f k) * f b
参数：hab : a <= b；f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ico_right_eq_Ico_add_one`：insert_Ico_right_eq_Ico_add_one 
(h : a <= b) : insert b (Ico a b) = Ico a (b + 1)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ico a (b + 1), f k) = (∏ k ∈ Ico a b, f k) * f b := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, prod_insert right_notMem_Ico, mul_comm]

@[to_additive]
/-
**Finset.prod_Ico_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_consecutive (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n 
<= k) : ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i
参数：f : Nat -> M；hmn : m <= n；hnk : n <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.Ico_disjoint_Ico_consecutive`：Ico_disjoint_Ico_consecutive (a b c
 : α) : Disjoint (Ico a b) (Ico b c)
· 使用定理 `Finset.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <
= b) (hbc : b <= c) : Ico a b union Ico b c = Ico a c
-/
theorem prod_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ico m n, f i) * ∏ i ∈ Ico n k, f i) = ∏ i ∈ Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

@[to_additive]
/-
**Finset.prod_Ioc_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ioc_consecutive (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n 
<= k) : ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i
参数：f : Nat -> M；hmn : m <= n；hnk : n <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Ioc_union_Ioc_eq_Ioc`：Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a <=
 b) (h₂ : b <= c) : Ioc a b union Ioc b c = Ioc a c
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_Ioc_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ioc m n, f i) * ∏ i ∈ Ioc n k, f i) = ∏ i ∈ Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

@[to_additive]
/-
**Finset.prod_Ioc_succ_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ioc_succ_top {a b : Nat} (hab : a <= b) (f : Nat -> M) : (∏ k in Ioc 
a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1)
参数：hab : a <= b；f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_Ioc_consecutive`：prod_Ioc_consecutive (f : Nat -> M) {m n k 
: Nat} (hmn : m <= n) (hnk : n <= k) : ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, 
f i) = ∏ i in Ioc…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.Ioc_succ_singleton`：Ioc_succ_singleton : Ioc b (b + 1) = {b + 1}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ioc a (b + 1), f k) = (∏ k ∈ Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]

@[to_additive]
/-
**Finset.prod_Icc_succ_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Icc_succ_top {a b : Nat} (hab : a <= b + 1) (f : Nat -> M) : (∏ k in 
Icc a (b + 1), f k) = (∏ k in Icc a b, f k) * f (b + 1)
参数：hab : a <= b + 1；f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.Ico_add_one_right_eq_Icc`：Ico_add_one_right_eq_Icc (a b : α) : Ic
o a (b + 1) = Icc a b
· 使用定理 `Finset.prod_Ico_succ_top`：prod_Ico_succ_top {a b : Nat} (hab : a <= b) (
f : Nat -> M) : (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b
-/
theorem prod_Icc_succ_top {a b : ℕ} (hab : a ≤ b + 1) (f : ℕ → M) :
    (∏ k ∈ Icc a (b + 1), f k) = (∏ k ∈ Icc a b, f k) * f (b + 1) := by
  rw [← Ico_add_one_right_eq_Icc, prod_Ico_succ_top hab, Ico_add_one_right_eq_Icc]

@[to_additive]
/-
**Finset.prod_range_mul_prod_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_mul_prod_Ico (f : Nat -> M) {m n : Nat} (h : m <= n) : ((∏ k in
 range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k
参数：f : Nat -> M；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_Ico_consecutive`：prod_Ico_consecutive (f : Nat -> M) {m n k 
: Nat} (hmn : m <= n) (hnk : n <= k) : ((∏ i in Ico m n, f i) * ∏ i in Ico n k, 
f i) = ∏ i in Ico…
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
-/
theorem prod_range_mul_prod_Ico (f : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ((∏ k ∈ range m, f k) * ∏ k ∈ Ico m n, f k) = ∏ k ∈ range n, f k :=
  Nat.Ico_zero_eq_range m ▸ Nat.Ico_zero_eq_range n ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]
/-
**Finset.prod_range_eq_mul_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_eq_mul_Ico (f : Nat -> M) {n : Nat} (hn : 0 < n) : ∏ x in Finse
t.range n, f x = f 0 * ∏ x in Ico 1 n, f x
参数：f : Nat -> M；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_prod_Ico_succ_bot`：prod_eq_prod_Ico_succ_bot {a b : Nat} 
(hab : a < b) (f : Nat -> M) : ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b,
 f k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
-/
theorem prod_range_eq_mul_Ico (f : ℕ → M) {n : ℕ} (hn : 0 < n) :
    ∏ x ∈ Finset.range n, f x = f 0 * ∏ x ∈ Ico 1 n, f x :=
  Finset.range_eq_Ico n ▸ Finset.prod_eq_prod_Ico_succ_bot hn f

@[to_additive]
/-
**Finset.prod_Ico_eq_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (
h : m <= n) : ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k
)⁻¹
参数：f : Nat -> δ；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_range_mul_prod_Ico`：prod_range_mul_prod_Ico (f : Nat -> M) {
m n : Nat} (h : m <= n) : ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in
 range n, f k
-/
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) * (∏ k ∈ range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

@[to_additive]
/-
**Finset.prod_Ico_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (h : 
m <= n) : ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k
参数：f : Nat -> δ；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.prod_Ico_eq_mul_inv`：prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ
] (f : Nat -> δ) {m n : Nat} (h : m <= n) : ∏ k in Ico m n, f k = (∏ k in range 
n, f k) * (∏ k i…
-/
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) / ∏ k ∈ range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

@[to_additive]
/-
**Finset.prod_range_div_prod_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_div_prod_range {G : Type*} [CommGroup G] {f : Nat -> G} {n m : 
Nat} (hnm : n <= m) : ((∏ k in range m, f k) / ∏ k in range n, f k) = ∏ k in ran
ge m with n <= k, f k
参数：hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_Ico_eq_div`：prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : N
at -> δ) {m n : Nat} (h : m <= n) : ∏ k in Ico m n, f k = (∏ k in range n, f k) 
/ ∏ k in ran…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem prod_range_div_prod_range {G : Type*} [CommGroup G] {f : ℕ → G} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k ∈ range m, f k) / ∏ k ∈ range n, f k) = ∏ k ∈ range m with n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto

/-- The two ways of summing over `(i, j)` in the range `a ≤ i ≤ j < b` are equal. -/
/-
**Finset.sum_Ico_Ico_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Nat
 -> M) : (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) = ∑ j in Finset.I
co a b, ∑ i in Finset.Ico a (j + 1), f i j
参数：a b : Nat；f : Nat -> Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The two ways of summing over `(i, j)` in the range `a ≤ i ≤ j < b` are equal.
-/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico i b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

/-- The two ways of summing over `(i, j)` in the range `a ≤ i < j < b` are equal. -/
/-
**Finset.sum_Ico_Ico_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Na
t -> M) : (∑ i in Finset.Ico a b, ∑ j in Finset.Ico (i + 1) b, f i j) = ∑ j in F
inset.Ico a b, ∑ i in Finset.Ico a j, f i j
参数：a b : Nat；f : Nat -> Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The two ways of summing over `(i, j)` in the range `a ≤ i < j < b` are equal.
-/
theorem sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico (i + 1) b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a j, f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

@[to_additive]
/-
**Finset.prod_Ico_eq_prod_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_eq_prod_range (f : Nat -> M) (m n : Nat) : ∏ k in Ico m n, f k = 
∏ k in range (n - m), f (m + k)
参数：f : Nat -> M；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `Finset.prod_Ico_add`：prod_Ico_add [AddCommMonoid α] [PartialOrder α] [Is
OrderedCancelAddMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α] (f : α -> M) 
(a b c : …
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
-/
theorem prod_Ico_eq_prod_range (f : ℕ → M) (m n : ℕ) :
    ∏ k ∈ Ico m n, f k = ∏ k ∈ range (n - m), f (m + k) := by
  by_cases! h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h := h.le
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
/-
**Finset.prod_Ico_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_reflect (f : Nat -> M) (k : Nat) {m n : Nat} (h : m <= n + 1) : (
∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j
参数：f : Nat -> M；k : Nat；h : m <= n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_image_const_sub_eq_Ico`：Ico_image_const_sub_eq_Ico (hac : a <= c
) : ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a)
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `tsub_le_tsub_iff_left`：tsub_le_tsub_iff_left (h : c <= a) : a - b <= a -
 c ↔ c <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_reflect (f : ℕ → M) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j ∈ Ico k m, f (n - j)) = ∏ j ∈ Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k ≤ n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]
/-
**Finset.sum_Ico_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (k : Nat) {m 
n : Nat} (h : m <= n + 1) : (∑ j in Ico k m, f (n - j)) = ∑ j in Ico (n + 1 - m)
 (n + 1 - k), f j
参数：f : Nat -> δ；k : Nat；h : m <= n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_Ico_reflect`：prod_Ico_reflect (f : Nat -> M) (k : Nat) {m n 
: Nat} (h : m <= n + 1) : (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (
n + 1 - k), f…
-/
theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
/-
**Finset.prod_range_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_reflect (f : Nat -> M) (n : Nat) : (∏ j in range n, f (n - 1 - 
j)) = ∏ j in range n, f j
参数：f : Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Finset.prod_Ico_reflect`：prod_Ico_reflect (f : Nat -> M) (k : Nat) {m n 
: Nat} (h : m <= n + 1) : (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (
n + 1 - k), f…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
-/
theorem prod_range_reflect (f : ℕ → M) (n : ℕ) :
    (∏ j ∈ range n, f (n - 1 - j)) = ∏ j ∈ range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
/-
**Finset.sum_range_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (n : Nat) :
 (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j
参数：f : Nat -> δ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_range_reflect`：prod_range_reflect (f : Nat -> M) (n : Nat) :
 (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j
-/
theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j ∈ range n, f (n - 1 - j)) = ∑ j ∈ range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n

@[simp]
/-
**Finset.prod_Ico_id_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ (n : ℕ), ∏ x ∈ Finset.Ico 1 (n + 1), x = n.factorial
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x ∈ Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]

section GaussSum

/-- Gauss' summation formula -/
/-
**Finset.sum_range_id_mul_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_range_id_mul_two (n : Nat) : (∑ i in range n, i) * 2 = n * (n - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_reflect`：sum_range_reflect {δ : Type*} [AddCommMonoid δ
] (f : Nat -> δ) (n : Nat) : (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f
 j
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n

--- 原说明 ---
Gauss' summation formula
-/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i ∈ range n, i) * 2 = (∑ i ∈ range n, i) + ∑ i ∈ range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i ∈ range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ ∈ range n, (n - 1) :=
      sum_congr rfl fun _ hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
/-
**Finset.sum_range_id** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_range_id (n : Nat) : ∑ i in range n, i = n * (n - 1) / 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_id_mul_two`：sum_range_id_mul_two (n : Nat) : (∑ i in ra
nge n, i) * 2 = n * (n - 1)
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Nat.zero_lt_two`：0 < 2

--- 原说明 ---
Gauss' summation formula
-/
theorem sum_range_id (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ Nat.zero_lt_two]

end GaussSum

@[to_additive]
/-
**Finset.prod_range_diag_flip** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_range_diag_flip (n : Nat) (f : Nat -> Nat -> M) : (∏ m in range n, ∏ 
k in range (m + 1), f k (m - k)) = ∏ m in range n, ∏ k in range (n - m), f m k
参数：n : Nat；f : Nat -> Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用引理 `Finset.prod_nbij'`：prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a i
n s, i a in t) (hj : forall a in t, j a in s) (left_inv : forall a in s, j (i a)
 = a) (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma prod_range_diag_flip (n : ℕ) (f : ℕ → ℕ → M) :
    (∏ m ∈ range n, ∏ k ∈ range (m + 1), f k (m - k)) =
      ∏ m ∈ range n, ∏ k ∈ range (n - m), f m k := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun a ↦ ⟨a.2, a.1 - a.2⟩) (fun a ↦ ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, implies_true,
      Sigma.forall, add_tsub_cancel_of_le, add_tsub_cancel_left]
  exact fun a b han hba ↦ lt_of_le_of_lt hba han

end Generic

section Nat

variable {M : Type*}
variable (f g : ℕ → M) {m n : ℕ}

section Group

variable [CommGroup M]

@[to_additive]
/-
**Finset.prod_range_succ_div_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, 
f i) = f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
-/
theorem prod_range_succ_div_prod : ((∏ i ∈ range (n + 1), f i) / ∏ i ∈ range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n

@[to_additive]
/-
**Finset.prod_range_succ_div_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range
 n, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
-/
theorem prod_range_succ_div_top : (∏ i ∈ range (n + 1), f i) / f n = ∏ i ∈ range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n

@[to_additive]
/-
**Finset.prod_Ico_div_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico 
(m + 1) n, f i
参数：hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `Finset.prod_eq_prod_Ico_succ_bot`：prod_eq_prod_Ico_succ_bot {a b : Nat} 
(hab : a < b) (f : Nat -> M) : ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b,
 f k
-/
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i ∈ Ico m n, f i) / f m = ∏ i ∈ Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]
/-
**Finset.prod_Ico_succ_div_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_succ_div_top (hmn : m <= n) : (∏ i in Ico m (n + 1), f i) / f n =
 ∏ i in Ico m n, f i
参数：hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `Finset.prod_Ico_succ_top`：prod_Ico_succ_top {a b : Nat} (hab : a <= b) (
f : Nat -> M) : (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b
-/
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i ∈ Ico m (n + 1), f i) / f n = ∏ i ∈ Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _

@[to_additive]
/-
**Finset.prod_Ico_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_div (hmn : m <= n) : ∏ i in Ico m n, f (i + 1) / f i = f n / f m
参数：hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_Ico_eq_div`：prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : N
at -> δ) {m n : Nat} (h : m <= n) : ∏ k in Ico m n, f k = (∏ k in range n, f k) 
/ ∏ k in ran…
· 使用引理 `Finset.prod_range_div`：prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in
 range n, f (i + 1) / f i) = f n / f 0
· 使用定理 `div_div_div_cancel_right`：div_div_div_cancel_right (a b c : G) : a / c /
 (b / c) = a / b
-/
theorem prod_Ico_div (hmn : m ≤ n) : ∏ i ∈ Ico m n, f (i + 1) / f i = f n / f m := by
  rw [prod_Ico_eq_div _ hmn, prod_range_div, prod_range_div, div_div_div_cancel_right]

@[to_additive]
/-
**Finset.prod_Icc_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_Icc_div (hmn : m <= n) (f : Nat -> M) : ∏ i in Icc m n, f (i + 1) / f
 i = f (n + 1) / f m
参数：hmn : m <= n；f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.Ico_add_one_right_eq_Icc`：Ico_add_one_right_eq_Icc (a b : α) : Ic
o a (b + 1) = Icc a b
· 使用定理 `Finset.prod_Ico_div`：prod_Ico_div (hmn : m <= n) : ∏ i in Ico m n, f (i 
+ 1) / f i = f n / f m
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem prod_Icc_div (hmn : m ≤ n) (f : ℕ → M) :
    ∏ i ∈ Icc m n, f (i + 1) / f i = f (n + 1) / f m := by
  rw [← Finset.Ico_add_one_right_eq_Icc, prod_Ico_div]
  omega

end Group

end Nat
end Finset

section Fin

@[to_additive]
/-
**Finset.prod_fin_Icc_eq_prod_nat_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.prod_fin_Icc_eq_prod_nat_Icc [CommMonoid α] {n : Nat} (a b : Fin n)
 (f : Fin n -> α) : ∏ i in Icc a b, f i = ∏ i in Icc (a : Nat) b, if h : i < n t
hen f ⟨i, h⟩ else 1
参数：a b : Fin n；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_ite_mem_eq`：prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : 
ι -> M) [DecidablePred (· in s)] : (∏ i, if i in s then f i else 1) = ∏ i in s, 
f i
· 使用定理 `Finset.prod_fin_eq_prod_range`：Finset.prod_fin_eq_prod_range [CommMonoid
 β] {n : Nat} (c : Fin n -> β) : ∏ i, c i = ∏ i in Finset.range n, if h : i < n 
then c ⟨i, h⟩ else …
· 使用引理 `Finset.prod_congr_of_eq_on_inter`：prod_congr_of_eq_on_inter {ι M : Type*
} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M] (h₁ : forall a in s₁, a ∉ s₂ 
-> f a = 1) (h₂ : fora…
-/
lemma Finset.prod_fin_Icc_eq_prod_nat_Icc [CommMonoid α] {n : ℕ} (a b : Fin n) (f : Fin n → α) :
    ∏ i ∈ Icc a b, f i = ∏ i ∈ Icc (a : ℕ) b, if h : i < n then f ⟨i, h⟩ else 1 := by
  rw [← prod_ite_mem_eq, prod_fin_eq_prod_range]
  apply prod_congr_of_eq_on_inter <;> grind

/-- Telescopic product over `Fin`. -/
@[to_additive /-- Telescopic sum over `Fin`. -/]
/-
**Fin.prod_Iic_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.prod_Iic_div [CommGroup M] {n : Nat} (a : Fin n) (f : Fin (n + 1) -> M
) : ∏ i in Iic a, (f i.succ / f i.castSucc) = f a.succ / f 0
参数：a : Fin n；f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_ite_mem_eq`：prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : 
ι -> M) [DecidablePred (· in s)] : (∏ i, if i in s then f i else 1) = ∏ i in s, 
f i
· 使用定理 `Finset.prod_fin_eq_prod_range`：Finset.prod_fin_eq_prod_range [CommMonoid
 β] {n : Nat} (c : Fin n -> β) : ∏ i, c i = ∏ i in Finset.range n, if h : i < n 
then c ⟨i, h⟩ else …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Finset.prod_congr_of_eq_on_inter`：prod_congr_of_eq_on_inter {ι M : Type*
} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M] (h₁ : forall a in s₁, a ∉ s₂ 
-> f a = 1) (h₂ : fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用引理 `Finset.prod_range_div`：prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in
 range n, f (i + 1) / f i) = f n / f 0

--- 原说明 ---
Telescopic product over `Fin`.
-/
lemma Fin.prod_Iic_div [CommGroup M] {n : ℕ} (a : Fin n) (f : Fin (n + 1) → M) :
    ∏ i ∈ Iic a, (f i.succ / f i.castSucc) = f a.succ / f 0 := by
  rw [← prod_ite_mem_eq, prod_fin_eq_prod_range]
  convert! prod_range_div (fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else 1) (a + 1) using 1 with k
    hk
  · exact prod_congr_of_eq_on_inter (by grind) (by grind) (by simp_all; grind)
  · grind

/-- Telescopic product over `Fin`. -/
@[to_additive /-- Telescopic sum over `Fin`. -/]
/-
**Fin.prod_Icc_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.prod_Icc_div [CommGroup M] {n : Nat} {a b : Fin n} (hab : a <= b) (f :
 Fin (n + 1) -> M) : ∏ i in Icc a b, (f i.succ / f i.castSucc) = f b.succ / f a.
castSucc
参数：hab : a <= b；f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_fin_Icc_eq_prod_nat_Icc`：Finset.prod_fin_Icc_eq_prod_nat_Icc
 [CommMonoid α] {n : Nat} (a b : Fin n) (f : Fin n -> α) : ∏ i in Icc a b, f i =
 ∏ i in Icc (a : Nat) b, …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.prod_Icc_div`：prod_Icc_div (hmn : m <= n) (f : Nat -> M) : ∏ i in
 Icc m n, f (i + 1) / f i = f (n + 1) / f m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b

--- 原说明 ---
Telescopic product over `Fin`.
-/
lemma Fin.prod_Icc_div [CommGroup M] {n : ℕ} {a b : Fin n} (hab : a ≤ b)
    (f : Fin (n + 1) → M) :
    ∏ i ∈ Icc a b, (f i.succ / f i.castSucc) = f b.succ / f a.castSucc := by
  rw [prod_fin_Icc_eq_prod_nat_Icc]
  convert! Finset.prod_Icc_div (Fin.le_def.1 hab) (fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else 1)
  · simp_all
    grind
  · grind
  · simp only [Order.lt_add_one_iff, is_le', ↓reduceDIte]
    rfl

end Fin

