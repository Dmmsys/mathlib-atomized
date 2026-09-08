/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Row- and Column-stochastic matrices

A square matrix `M` is *row-stochastic* if all its entries are non-negative and `M *ᵥ 1 = 1`.
Likewise, `M` is *column-stochastic* if all its entries are non-negative and `1 ᵥ* M = 1`. This
file defines these concepts and provides basic API for them.

Note that *doubly stochastic* matrices (i.e. matrices that are both row- and column-stochastic)
are defined in `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`.

## Main definitions

* `rowStochastic`: row-stochastic matrices indexed by `n` with entries in `R`, as a submonoid
  of `Matrix n n R`.
* `colStochastic R n`: column-stochastic matrices indexed by `n` with entries in `R`, as a
  submonoid of `Matrix n n R`.

-/

@[expose] public section

open Finset

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}
variable {x : n → R}

/- ## Row-stochastic matrices -/

/-- A square matrix is row stochastic iff all entries are nonnegative, and right
multiplication by the vector of all 1s gives the vector of all 1s. -/
/-
**Matrix.rowStochastic** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [Part
ialOrder R] [IsOrderedRing R] : Submonoid (Matrix n n R) where carrier
参数：R n : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix is row stochastic iff all entries are nonnegative, and right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1  }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    rw [← mulVec_mulVec, hN.2, hM.2]
  one_mem' := by
    simp [zero_le_one_elem]
/-
**Matrix.mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mem_rowStochastic : M in rowStochastic R n ↔ (forall i j, 0 <= M i j) ∧ M 
*ᵥ 1 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_rowStochastic :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 :=
  Iff.rfl

/-- A square matrix is row stochastic if each element is non-negative and row sums to one. -/
/-
**Matrix.mem_rowStochastic_iff_sum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mem_rowStochastic_iff_sum : M in rowStochastic R n ↔ (forall i j, 0 <= M i
 j) ∧ (forall i, ∑ j, M i j = 1)
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A square matrix is row stochastic if each element is non-negative and row sums t
o one.
-/
lemma mem_rowStochastic_iff_sum :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) := by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

/-- Every entry of a row stochastic matrix is nonnegative. -/
/-
**Matrix.nonneg_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_of_mem_rowStochastic (hM : M in rowStochastic R n) {i j : n} : 0 <=
 M i j
参数：hM : M in rowStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Every entry of a row stochastic matrix is nonnegative.
-/
lemma nonneg_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each row sum of a row stochastic matrix is 1. -/
/-
**Matrix.sum_row_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_row_of_mem_rowStochastic (hM : M in rowStochastic R n) (i : n) : ∑ j, 
M i j = 1
参数：hM : M in rowStochastic R n；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.mem_rowStochastic_iff_sum`：mem_rowStochastic_iff_sum : M in rowSt
ochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1)

--- 原说明 ---
Each row sum of a row stochastic matrix is 1.
-/
lemma sum_row_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_rowStochastic_iff_sum.1 hM).2 _

/-- The all-ones column vector multiplied with a row stochastic matrix is 1. -/
/-
**Matrix.one_vecMul_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：one_vecMul_of_mem_rowStochastic (hM : M in rowStochastic R n) : M *ᵥ 1 = 1
参数：hM : M in rowStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.mem_rowStochastic`：mem_rowStochastic : M in rowStochastic R n ↔ (
forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1

--- 原说明 ---
The all-ones column vector multiplied with a row stochastic matrix is 1.
-/
lemma one_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_rowStochastic.1 hM).2

/-- Every entry of a row stochastic matrix is less than or equal to 1. -/
/-
**Matrix.le_one_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：le_one_of_mem_rowStochastic (hM : M in rowStochastic R n) {i j : n} : M i 
j <= 1
参数：hM : M in rowStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.sum_row_of_mem_rowStochastic`：sum_row_of_mem_rowStochastic (hM : 
M in rowStochastic R n) (i : n) : ∑ j, M i j = 1
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Every entry of a row stochastic matrix is less than or equal to 1.
-/
lemma le_one_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/-- Left multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector -/
/-
**Matrix.nonneg_vecMul_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_vecMul_of_mem_rowStochastic (hM : M in rowStochastic R n) (hx : for
all i : n, 0 <= x i) : forall j : n, 0 <= (x ᵥ* M) j
参数：hM : M in rowStochastic R n；hx : forall i : n, 0 <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Matrix.nonneg_of_mem_rowStochastic`：nonneg_of_mem_rowStochastic (hM : M 
in rowStochastic R n) {i j : n} : 0 <= M i j

--- 原说明 ---
Left multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector
-/
lemma nonneg_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Right multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector -/
/-
**Matrix.nonneg_mulVec_of_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_mulVec_of_mem_rowStochastic (hM : M in rowStochastic R n) (hx : for
all i : n, 0 <= x i) : forall j : n, 0 <= (M *ᵥ x) j
参数：hM : M in rowStochastic R n；hx : forall i : n, 0 <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Left.mul_nonneg`：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <=
 b) : 0 <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Matrix.nonneg_of_mem_rowStochastic`：nonneg_of_mem_rowStochastic (hM : M 
in rowStochastic R n) {i j : n} : 0 <= M i j

--- 原说明 ---
Right multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector
-/
lemma nonneg_mulVec_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Left left-multiplication by row stochastic preserves `ℓ₁ norm` -/
/-
**Matrix.vecMul_dotProduct_one_eq_one_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix`。
形式化陈述：vecMul_dotProduct_one_eq_one_rowStochastic (hM : M in rowStochastic R n) (
hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1
参数：hM : M in rowStochastic R n；hx : x ⬝ᵥ 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Left left-multiplication by row stochastic preserves `ℓ₁ norm`
-/
lemma vecMul_dotProduct_one_eq_one_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1 := by
  rw [← dotProduct_mulVec, hM.2, hx]

/-- The set of row stochastic matrices is convex. -/
/-
**Matrix.convex_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：convex_rowStochastic : Convex R (rowStochastic R n : Set (Matrix n n R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The set of row stochastic matrices is convex.
-/
lemma convex_rowStochastic : Convex R (rowStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is row stochastic. -/
@[simp, grind ←]
/-
**Matrix.permMatrix_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_mem_rowStochastic {σ : Equiv.Perm n} : σ.permMatrix R in rowSto
chastic R n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.mem_rowStochastic_iff_sum`：mem_rowStochastic_iff_sum : M in rowSt
ochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1)
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Any permutation matrix is row stochastic.
-/
lemma permMatrix_mem_rowStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ rowStochastic R n := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]


/- ## Column-stochastic matrices -/

/-- A square matrix is column stochastic iff all entries are nonnegative, and left
multiplication by the vector of all 1s gives the vector of all 1s. -/
/-
**Matrix.colStochastic** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：colStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [Part
ialOrder R] [IsOrderedRing R] : Submonoid (Matrix n n R) where carrier
参数：R n : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix is column stochastic iff all entries are nonnegative, and left
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def colStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ 1 ᵥ* M = 1  }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      grind [mul_nonneg]
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]
/-
**Matrix.mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mem_colStochastic : M in colStochastic R n ↔ (forall i j, 0 <= M i j) ∧ 1 
ᵥ* M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_colStochastic :
    M ∈ colStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ 1 ᵥ* M = 1 :=
  Iff.rfl

/-- A matrix is column stochastic if each column sums to one. -/
/-
**Matrix.mem_colStochastic_iff_sum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mem_colStochastic_iff_sum : M in colStochastic R n ↔ (forall i j, 0 <= M i
 j) ∧ (forall j, ∑ i, M i j = 1)
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A matrix is column stochastic if each column sums to one.
-/
lemma mem_colStochastic_iff_sum :
    M ∈ colStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ j, ∑ i, M i j = 1) := by
  simp [funext_iff, colStochastic, vecMul, dotProduct]

/-- Every entry of a column stochastic matrix is nonnegative. -/
/-
**Matrix.nonneg_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_of_mem_colStochastic (hM : M in colStochastic R n) {i j : n} : 0 <=
 M i j
参数：hM : M in colStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Every entry of a column stochastic matrix is nonnegative.
-/
lemma nonneg_of_mem_colStochastic (hM : M ∈ colStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each column sum of a column stochastic matrix is 1. -/
/-
**Matrix.sum_col_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_col_of_mem_colStochastic (hM : M in colStochastic R n) (i : n) : ∑ j, 
M j i = 1
参数：hM : M in colStochastic R n；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.mem_colStochastic_iff_sum`：mem_colStochastic_iff_sum : M in colSt
ochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall j, ∑ i, M i j = 1)

--- 原说明 ---
Each column sum of a column stochastic matrix is 1.
-/
lemma sum_col_of_mem_colStochastic (hM : M ∈ colStochastic R n) (i : n) : ∑ j, M j i = 1 :=
  (mem_colStochastic_iff_sum.1 hM).2 _

/-- The all-ones column vector multiplied with a column stochastic matrix is 1. -/
/-
**Matrix.one_vecMul_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：one_vecMul_of_mem_colStochastic (hM : M in colStochastic R n) : 1 ᵥ* M = 1
参数：hM : M in colStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.mem_colStochastic`：mem_colStochastic : M in colStochastic R n ↔ (
forall i j, 0 <= M i j) ∧ 1 ᵥ* M = 1

--- 原说明 ---
The all-ones column vector multiplied with a column stochastic matrix is 1.
-/
lemma one_vecMul_of_mem_colStochastic (hM : M ∈ colStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_colStochastic.1 hM).2

/-- Every entry of a column stochastic matrix is less than or equal to 1. -/
/-
**Matrix.le_one_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：le_one_of_mem_colStochastic (hM : M in colStochastic R n) {i j : n} : M j 
i <= 1
参数：hM : M in colStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.sum_col_of_mem_colStochastic`：sum_col_of_mem_colStochastic (hM : 
M in colStochastic R n) (i : n) : ∑ j, M j i = 1
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Every entry of a column stochastic matrix is less than or equal to 1.
-/
lemma le_one_of_mem_colStochastic (hM : M ∈ colStochastic R n) {i j : n} :
    M j i ≤ 1 := by
  rw [← sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

/-- Right multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector. -/
/-
**Matrix.nonneg_mulVec_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_mulVec_of_mem_colStochastic (hM : M in colStochastic R n) (hx : for
all i : n, 0 <= x i) : forall j : n, 0 <= (M *ᵥ x) j
参数：hM : M in colStochastic R n；hx : forall i : n, 0 <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Left.mul_nonneg`：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <=
 b) : 0 <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Matrix.nonneg_of_mem_colStochastic`：nonneg_of_mem_colStochastic (hM : M 
in colStochastic R n) {i j : n} : 0 <= M i j

--- 原说明 ---
Right multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector.
-/
lemma nonneg_mulVec_of_mem_colStochastic (hM : M ∈ colStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_colStochastic hM

/-- Left multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector. -/
/-
**Matrix.nonneg_vecMul_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_vecMul_of_mem_colStochastic (hM : M in colStochastic R n) (hx : for
all i : n, 0 <= x i) : forall j : n, 0 <= (x ᵥ* M) j
参数：hM : M in colStochastic R n；hx : forall i : n, 0 <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Left.mul_nonneg`：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <=
 b) : 0 <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Matrix.nonneg_of_mem_colStochastic`：nonneg_of_mem_colStochastic (hM : M 
in colStochastic R n) {i j : n} : 0 <= M i j

--- 原说明 ---
Left multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector.
-/
lemma nonneg_vecMul_of_mem_colStochastic (hM : M ∈ colStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg (hx k) ?_
  exact nonneg_of_mem_colStochastic hM

/-- Left left-multiplication by column stochastic preserves `ℓ₁ norm` -/
/-
**Matrix.mulVec_dotProduct_one_eq_one_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix`。
形式化陈述：mulVec_dotProduct_one_eq_one_colStochastic (hM : M in colStochastic R n) (
hx : 1 ⬝ᵥ x = 1) : 1 ⬝ᵥ (M *ᵥ x) = 1
参数：hM : M in colStochastic R n；hx : 1 ⬝ᵥ x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Left left-multiplication by column stochastic preserves `ℓ₁ norm`
-/
lemma mulVec_dotProduct_one_eq_one_colStochastic (hM : M ∈ colStochastic R n)
    (hx : 1 ⬝ᵥ x = 1) : 1 ⬝ᵥ (M *ᵥ x) = 1 := by
  rw [dotProduct_mulVec, hM.2, hx]

/-- Applying a column-stochastic matrix to a vector preserves its sum. -/
/-
**Matrix.sum_mulVec_of_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_mulVec_of_mem_colStochastic {M : Matrix n n R} {x : n -> R} (hA : M in
 colStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i
参数：hA : M in colStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.sum_col_of_mem_colStochastic`：sum_col_of_mem_colStochastic (hM : 
M in colStochastic R n) (i : n) : ∑ j, M j i = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Applying a column-stochastic matrix to a vector preserves its sum.
-/
lemma sum_mulVec_of_mem_colStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ colStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

/-- The set of column stochastic matrices is convex. -/
/-
**Matrix.convex_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：convex_colStochastic : Convex R (colStochastic R n : Set (Matrix n n R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The set of column stochastic matrices is convex.
-/
lemma convex_colStochastic : Convex R (colStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_colStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is column stochastic. -/
@[simp, grind ←]
/-
**Matrix.permMatrix_mem_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：permMatrix_mem_colStochastic {σ : Equiv.Perm n} : σ.permMatrix R in colSto
chastic R n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.mem_colStochastic_iff_sum`：mem_colStochastic_iff_sum : M in colSt
ochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall j, ∑ i, M i j = 1)
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Any permutation matrix is column stochastic.
-/
lemma permMatrix_mem_colStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ colStochastic R n := by
  rw [mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply σ]

/-- The transpose of a matrix is row stochastic matrix if it is column stochastic. -/
@[grind =]
/-
**Matrix.transpose_mem_rowStochastic_iff_mem_colStochastic** 是 Mathlib 中的一个引理，位于
命名空间 `Matrix`。
形式化陈述：transpose_mem_rowStochastic_iff_mem_colStochastic : Mᵀ in rowStochastic R 
n ↔ M in colStochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b

--- 原说明 ---
The transpose of a matrix is row stochastic matrix if it is column stochastic.
-/
lemma transpose_mem_rowStochastic_iff_mem_colStochastic :
    Mᵀ ∈ rowStochastic R n ↔ M ∈ colStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_comm

/-- The transpose of a matrix is column stochastic matrix if it is row stochastic. -/
@[grind =]
/-
**Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic** 是 Mathlib 中的一个引理，位于
命名空间 `Matrix`。
形式化陈述：transpose_mem_colStochastic_iff_mem_rowStochastic : Mᵀ in colStochastic R 
n ↔ M in rowStochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b

--- 原说明 ---
The transpose of a matrix is column stochastic matrix if it is row stochastic.
-/
lemma transpose_mem_colStochastic_iff_mem_rowStochastic :
    Mᵀ ∈ colStochastic R n ↔ M ∈ rowStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_comm

/-- Reindexing a matrix preserves row-stochasticity. -/
@[aesop safe apply]
/-
**Matrix.reindex_mem_rowStochastic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：reindex_mem_rowStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Mat
rix n n R} {e₁ e₂ : n ≃ m} (hM : M in rowStochastic R n) : M.reindex e₁ e₂ in ro
wStochastic R m
参数：hM : M in rowStochastic R n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.nonneg_of_mem_rowStochastic`：nonneg_of_mem_rowStochastic (hM : M 
in rowStochastic R n) {i j : n} : 0 <= M i j
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_mulVec_equiv`：submatrix_mulVec_equiv [Fintype n] [Finty
pe o] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : o -> α) (e₁ : l -> m
) (e₂ : o ≃ n) : M.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reindexing a matrix preserves row-stochasticity.
-/
lemma reindex_mem_rowStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M ∈ rowStochastic R n) : M.reindex e₁ e₂ ∈ rowStochastic R m :=
  ⟨fun _ _ ↦ by simpa using nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

/-- Reindexing a matrix preserves row-stochasticity. -/
@[grind =]
/-
**Matrix.reindex_mem_rowStochastic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：reindex_mem_rowStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M :
 Matrix n n R} {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in rowStochastic R m ↔ M in row
Stochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.reindex_mem_rowStochastic`：reindex_mem_rowStochastic {m : Type*} 
[Fintype m] [DecidableEq m] {M : Matrix n n R} {e₁ e₂ : n ≃ m} (hM : M in rowSto
chastic R n) : M.reind…

--- 原说明 ---
Reindexing a matrix preserves row-stochasticity.
-/
lemma reindex_mem_rowStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ rowStochastic R m ↔ M ∈ rowStochastic R n := by
  refine ⟨fun h => ?_, reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact reindex_mem_rowStochastic h

/-- Reindexing a matrix preserves column-stochasticity. -/
@[grind =]
/-
**Matrix.reindex_mem_colStochastic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：reindex_mem_colStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M :
 Matrix n n R} {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in colStochastic R m ↔ M in col
Stochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.transpose_reindex`：transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M
 : Matrix m n α) : (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ
· 使用引理 `Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic`：transpose_mem_
colStochastic_iff_mem_rowStochastic : Mᵀ in colStochastic R n ↔ M in rowStochast
ic R n
· 使用引理 `Matrix.reindex_mem_rowStochastic_iff`：reindex_mem_rowStochastic_iff {m :
 Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R} {e₁ e₂ : n ≃ m} : M.reind
ex e₁ e₂ in rowStochastic …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Reindexing a matrix preserves column-stochasticity.
-/
lemma reindex_mem_colStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ colStochastic R m ↔ M ∈ colStochastic R n := by
  rw [← transpose_transpose (reindex e₁ e₂ M), transpose_reindex,
    transpose_mem_colStochastic_iff_mem_rowStochastic, reindex_mem_rowStochastic_iff,
    ← transpose_mem_colStochastic_iff_mem_rowStochastic, transpose_transpose]

/-- Reindexing a matrix preserves column-stochasticity. -/
@[aesop safe apply]
alias ⟨_, reindex_mem_colStochastic⟩ := reindex_mem_colStochastic_iff

end Matrix

