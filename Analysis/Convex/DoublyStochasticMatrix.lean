/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Doubly stochastic matrices

## Main definitions

* `doublyStochastic`: a square matrix is doubly stochastic if all entries are nonnegative, and left
  or right multiplication by the vector of all 1s gives the vector of all 1s. Equivalently, all
  row and column sums are equal to 1.

## Main statements

* `convex_doublyStochastic`: The set of doubly stochastic matrices is convex.
* `permMatrix_mem_doublyStochastic`: Any permutation matrix is doubly stochastic.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

@[expose] public section

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

/--
A square matrix is doubly stochastic iff all entries are nonnegative, and left or right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
/-
**doublyStochastic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [P
artialOrder R] [IsOrderedRing R] : Submonoid (Matrix n n R) where carrier
参数：R n : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix is doubly stochastic iff all entries are nonnegative, and left o
r right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]
/-
**mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_doublyStochastic : M in doublyStochastic R n ↔ (forall i j, 0 <= M i j
) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_doublyStochastic :
    M ∈ doublyStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 :=
  Iff.rfl
/-
**mem_doublyStochastic_iff_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_doublyStochastic_iff_sum : M in doublyStochastic R n ↔ (forall i j, 0 
<= M i j) ∧ (forall i, ∑ j, M i j = 1) ∧ forall j, ∑ i, M i j = 1
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_doublyStochastic_iff_sum :
    M ∈ doublyStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

/-- A matrix is doubly stochastic if and only if it is both row and
column stochastic. -/
@[local grind =]
/-
**doublyStochastic_eq_rowStochastic_inf_colStochastic** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：doublyStochastic_eq_rowStochastic_inf_colStochastic : doublyStochastic R n
 = rowStochastic R n ⊓ colStochastic R n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
A matrix is doubly stochastic if and only if it is both row and
column stochastic.
-/
lemma doublyStochastic_eq_rowStochastic_inf_colStochastic :
    doublyStochastic R n = rowStochastic R n ⊓ colStochastic R n := by
  ext M
  simp only [rowStochastic, colStochastic, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, doublyStochastic]
  grind
/-
**mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic** 是 Mathlib 中
的一个引理，位于命名空间 ``。
形式化陈述：mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic {M : Matr
ix n n R} : M in doublyStochastic R n ↔ M in rowStochastic R n ∧ M in colStochas
tic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `doublyStochastic_eq_rowStochastic_inf_colStochastic`：doublyStochastic_eq
_rowStochastic_inf_colStochastic : doublyStochastic R n = rowStochastic R n ⊓ co
lStochastic R n
· 使用定理 `Submonoid.mem_inf`：mem_inf {p p' : Submonoid M} {x : M} : x in p ⊓ p' ↔ 
x in p ∧ x in p'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic {M : Matrix n n R} :
    M ∈ doublyStochastic R n ↔ M ∈ rowStochastic R n ∧ M ∈ colStochastic R n := by
  rw [doublyStochastic_eq_rowStochastic_inf_colStochastic, Submonoid.mem_inf]

/-- Every entry of a doubly stochastic matrix is nonnegative. -/
/-
**nonneg_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonneg_of_mem_doublyStochastic (hM : M in doublyStochastic R n) {i j : n} 
: 0 <= M i j
参数：hM : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Every entry of a doubly stochastic matrix is nonnegative.
-/
lemma nonneg_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each row sum of a doubly stochastic matrix is 1. -/
/-
**sum_row_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_row_of_mem_doublyStochastic (hM : M in doublyStochastic R n) (i : n) :
 ∑ j, M i j = 1
参数：hM : M in doublyStochastic R n；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_doublyStochastic_iff_sum`：mem_doublyStochastic_iff_sum : M in doubly
Stochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1) ∧ forall 
j, ∑ i, M i j = 1

--- 原说明 ---
Each row sum of a doubly stochastic matrix is 1.
-/
lemma sum_row_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.1 _

/-- Each column sum of a doubly stochastic matrix is 1. -/
/-
**sum_col_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_col_of_mem_doublyStochastic (hM : M in doublyStochastic R n) (j : n) :
 ∑ i, M i j = 1
参数：hM : M in doublyStochastic R n；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_doublyStochastic_iff_sum`：mem_doublyStochastic_iff_sum : M in doubly
Stochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1) ∧ forall 
j, ∑ i, M i j = 1

--- 原说明 ---
Each column sum of a doubly stochastic matrix is 1.
-/
lemma sum_col_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.2 _

/-- A doubly stochastic matrix multiplied with the all-ones column vector is 1. -/
/-
**mulVec_one_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulVec_one_of_mem_doublyStochastic (hM : M in doublyStochastic R n) : M *ᵥ
 1 = 1
参数：hM : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_doublyStochastic`：mem_doublyStochastic : M in doublyStochastic R n ↔
 (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1

--- 原说明 ---
A doubly stochastic matrix multiplied with the all-ones column vector is 1.
-/
lemma mulVec_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_doublyStochastic.1 hM).2.1

/-- The all-ones row vector multiplied with a doubly stochastic matrix is 1. -/
/-
**one_vecMul_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_vecMul_of_mem_doublyStochastic (hM : M in doublyStochastic R n) : 1 ᵥ*
 M = 1
参数：hM : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_doublyStochastic`：mem_doublyStochastic : M in doublyStochastic R n ↔
 (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1

--- 原说明 ---
The all-ones row vector multiplied with a doubly stochastic matrix is 1.
-/
lemma one_vecMul_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_doublyStochastic.1 hM).2.2

/-- Every entry of a doubly stochastic matrix is less than or equal to 1. -/
/-
**le_one_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_one_of_mem_doublyStochastic (hM : M in doublyStochastic R n) {i j : n} 
: M i j <= 1
参数：hM : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sum_row_of_mem_doublyStochastic`：sum_row_of_mem_doublyStochastic (hM : M
 in doublyStochastic R n) (i : n) : ∑ j, M i j = 1
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
Every entry of a doubly stochastic matrix is less than or equal to 1.
-/
lemma le_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/-- The set of doubly stochastic matrices is convex. -/
/-
**convex_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n
 R))
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
The set of doubly stochastic matrices is convex.
-/
lemma convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is doubly stochastic. -/
@[simp, grind ←]
/-
**permMatrix_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} : σ.permMatrix R in dou
blyStochastic R n
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any permutation matrix is doubly stochastic.
-/
lemma permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ doublyStochastic R n := by grind

/-- A matrix is doubly stochastic iff its transpose is doubly stochastic -/
@[grind =]
/-
**transpose_mem_doublyStochastic_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transpose_mem_doublyStochastic_iff : Mᵀ in doublyStochastic R n ↔ M in dou
blyStochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix is doubly stochastic iff its transpose is doubly stochastic
-/
lemma transpose_mem_doublyStochastic_iff :
    Mᵀ ∈ doublyStochastic R n ↔ M ∈ doublyStochastic R n := by grind

/-- Reindexing a matrix preserves double stochasticity. -/
@[aesop safe apply]
/-
**reindex_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：reindex_mem_doublyStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : 
Matrix n n R} {e₁ e₂ : n ≃ m} (hM : M in doublyStochastic R n) : M.reindex e₁ e₂
 in doublyStochastic R m
参数：hM : M in doublyStochastic R n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindexing a matrix preserves double stochasticity.
-/
lemma reindex_mem_doublyStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M ∈ doublyStochastic R n) : M.reindex e₁ e₂ ∈ doublyStochastic R m := by
  grind

/-- Reindexing a matrix preserves double stochasticity. -/
@[grind =]
/-
**reindex_mem_doublyStochastic_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：reindex_mem_doublyStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {
M : Matrix n n R} {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in doublyStochastic R m ↔ M 
in doublyStochastic R n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindexing a matrix preserves double stochasticity.
-/
lemma reindex_mem_doublyStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ doublyStochastic R m ↔ M ∈ doublyStochastic R n := by
  grind

/-- Applying a doubly stochastic matrix to a vector preserves its sum. -/
/-
**sum_mulVec_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_mulVec_of_mem_doublyStochastic {M : Matrix n n R} {x : n -> R} (hA : M
 in doublyStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i
参数：hA : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.sum_mulVec_of_mem_colStochastic`：sum_mulVec_of_mem_colStochastic 
{M : Matrix n n R} {x : n -> R} (hA : M in colStochastic R n) : ∑ i, (M *ᵥ x) i 
= ∑ i, x i

--- 原说明 ---
Applying a doubly stochastic matrix to a vector preserves its sum.
-/
lemma sum_mulVec_of_mem_doublyStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ doublyStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  apply sum_mulVec_of_mem_colStochastic
  grind

end OrderedSemiring

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]

/--
A matrix is `s` times a doubly stochastic matrix iff all entries are nonnegative, and all row and
column sums are equal to `s`.

This lemma is useful for the proof of Birkhoff's theorem - in particular because it allows scaling
by nonnegative factors rather than positive ones only.
-/
/-
**exists_mem_doublyStochastic_eq_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0
 <= s) : (exists M' in doublyStochastic R n, M = s • M') ↔ (forall i j, 0 <= M i
 j) ∧ (forall i, ∑ j, M i j = s) ∧ (forall j, ∑ i, M i j = s)
参数：hs : 0 <= s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `mem_doublyStochastic_iff_sum`：mem_doublyStochastic_iff_sum : M in doubly
Stochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1) ∧ forall 
j, ∑ i, M i j = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
A matrix is `s` times a doubly stochastic matrix iff all entries are nonnegative
, and all row and
column sums are equal to `s`.

This lemma is useful for the proof of Birkhoff's theorem - in particular because
 it allows scaling
by nonnegative factors rather than positive ones only.
-/
lemma exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0 ≤ s) :
    (∃ M' ∈ doublyStochastic R n, M = s • M') ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) := by
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

end LinearOrderedSemifield

