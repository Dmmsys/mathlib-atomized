/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Relation of covering by cosets

This file defines a predicate for a set to be covered by at most `K` cosets of another set.

This is a fundamental relation to study in additive combinatorics.
-/

@[expose] public section

open scoped Finset Pointwise

variable {M N X : Type*} [Monoid M] [Monoid N] [MulAction M X] [MulAction N X] {K L : ℝ}
  {A A₁ A₂ B B₁ B₂ C : Set X}

variable (M) in
/-- Predicate for a set `A` to be covered by at most `K` cosets of another set `B` under the action
by the monoid `M`. -/
@[to_additive /-- Predicate for a set `A` to be covered by at most `K` cosets of another set `B`
under the action by the monoid `M`. -/]
/-
**CovBySMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CovBySMul (K : Real) (A B : Set X) : Prop
参数：K : Real；A B : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CovBySMul (K : ℝ) (A B : Set X) : Prop := ∃ F : Finset M, #F ≤ K ∧ A ⊆ (F : Set M) • B

@[to_additive (attr := simp, refl)]
/-
**CovBySMul.rfl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.rfl : CovBySMul M 1 A A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_one`：card_one : #(1 : Finset α) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.coe_one`：coe_one : ↑(1 : Finset α) = (1 : Set α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma CovBySMul.rfl : CovBySMul M 1 A A := ⟨1, by simp⟩

@[to_additive (attr := simp)]
/-
**CovBySMul.of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.of_subset (hAB : A subseteq B) : CovBySMul M 1 A B
参数：hAB : A subseteq B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_one`：card_one : #(1 : Finset α) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.coe_one`：coe_one : ↑(1 : Finset α) = (1 : Set α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma CovBySMul.of_subset (hAB : A ⊆ B) : CovBySMul M 1 A B := ⟨1, by simpa⟩
/-
**CovBySMul.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `CovBySMul`。
形式化陈述：∀ {M : Type u_1} {X : Type u_3} [inst : Monoid M] [inst_1 : MulAction M X]
 {K : ℝ} {A B : Set X},   CovBySMul M K A B → 0 ≤ K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
@[to_additive] lemma CovBySMul.nonneg : CovBySMul M K A B → 0 ≤ K := by
  rintro ⟨F, hF, -⟩; exact (#F).cast_nonneg.trans hF

@[to_additive (attr := simp)]
/-
**covBySMul_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：covBySMul_zero : CovBySMul M 0 A B ↔ A = ∅
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.empty_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β}, ∅ • t = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma covBySMul_zero : CovBySMul M 0 A B ↔ A = ∅ := by simp [CovBySMul]

@[to_additive]
/-
**CovBySMul.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.mono (hKL : K <= L) : CovBySMul M K A B -> CovBySMul M L A B
参数：hKL : K <= L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma CovBySMul.mono (hKL : K ≤ L) : CovBySMul M K A B → CovBySMul M L A B := by
  rintro ⟨F, hF, hFAB⟩; exact ⟨F, hF.trans hKL, hFAB⟩
/-
**CovBySMul.trans** 是 Mathlib 中的一个定理，位于命名空间 `CovBySMul`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {X : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : MulAction M X]   [inst_3 : MulAction N X] {K L : ℝ} {A B C 
: Set X} [inst_4 : SMul M N] [IsScalarTower M N X],   CovBySMul M K A B → CovByS
Mul N L B C → CovBySMul N (K * L) A C
参数：K * L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBySMul.nonneg`：∀ {M : Type u_1} {X : Type u_3} [inst : Monoid M] [ins
t_1 : MulAction M X] {K : ℝ} {A B : Set X},   CovBySMul M K A B → 0 ≤ K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_smul_le`：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq
 β] [inst_1 : SMul α β] {s : Finset α} {t : Finset β},   (s • t).card ≤ s.card *
 t.card
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Set.smul_subset_smul`：smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t
₂ -> s₁ • t₁ subseteq s₂ • t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma CovBySMul.trans [SMul M N] [IsScalarTower M N X]
    (hAB : CovBySMul M K A B) (hBC : CovBySMul N L B C) : CovBySMul N (K * L) A C := by
  classical
  have := hAB.nonneg
  obtain ⟨F₁, hF₁, hFAB⟩ := hAB
  obtain ⟨F₂, hF₂, hFBC⟩ := hBC
  refine ⟨F₁ • F₂, ?_, ?_⟩
  · calc
      (#(F₁ • F₂) : ℝ) ≤ #F₁ * #F₂ := mod_cast Finset.card_smul_le
      _ ≤ K * L := by gcongr
  · calc
      A ⊆ (F₁ : Set M) • B := hFAB
      _ ⊆ (F₁ : Set M) • (F₂ : Set N) • C := by gcongr
      _ = (↑(F₁ • F₂) : Set N) • C := by simp

@[to_additive]
/-
**CovBySMul.subset_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.subset_left (hA : A₁ subseteq A₂) (hAB : CovBySMul M K A₂ B) : C
ovBySMul M K A₁ B
参数：hA : A₁ subseteq A₂；hAB : CovBySMul M K A₂ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `CovBySMul.trans`：∀ {M : Type u_1} {N : Type u_2} {X : Type u_3} [inst : 
Monoid M] [inst_1 : Monoid N] [inst_2 : MulAction M X]   [inst_3 : MulAction N X
] {K …
· 使用引理 `CovBySMul.of_subset`：CovBySMul.of_subset (hAB : A subseteq B) : CovBySMu
l M 1 A B
-/
lemma CovBySMul.subset_left (hA : A₁ ⊆ A₂) (hAB : CovBySMul M K A₂ B) :
    CovBySMul M K A₁ B := by simpa using (CovBySMul.of_subset (M := M) hA).trans hAB

@[to_additive]
/-
**CovBySMul.subset_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.subset_right (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A B₁) : 
CovBySMul M K A B₂
参数：hB : B₁ subseteq B₂；hAB : CovBySMul M K A B₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `CovBySMul.trans`：∀ {M : Type u_1} {N : Type u_2} {X : Type u_3} [inst : 
Monoid M] [inst_1 : Monoid N] [inst_2 : MulAction M X]   [inst_3 : MulAction N X
] {K …
· 使用引理 `CovBySMul.of_subset`：CovBySMul.of_subset (hAB : A subseteq B) : CovBySMu
l M 1 A B
-/
lemma CovBySMul.subset_right (hB : B₁ ⊆ B₂) (hAB : CovBySMul M K A B₁) :
    CovBySMul M K A B₂ := by simpa using hAB.trans (.of_subset (M := M) hB)

@[to_additive]
/-
**CovBySMul.subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CovBySMul.subset (hA : A₁ subseteq A₂) (hB : B₁ subseteq B₂) (hAB : CovByS
Mul M K A₂ B₁) : CovBySMul M K A₁ B₂
参数：hA : A₁ subseteq A₂；hB : B₁ subseteq B₂；hAB : CovBySMul M K A₂ B₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CovBySMul.subset_right`：CovBySMul.subset_right (hB : B₁ subseteq B₂) (hA
B : CovBySMul M K A B₁) : CovBySMul M K A B₂
· 使用引理 `CovBySMul.subset_left`：CovBySMul.subset_left (hA : A₁ subseteq A₂) (hAB 
: CovBySMul M K A₂ B) : CovBySMul M K A₁ B
-/
lemma CovBySMul.subset (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) (hAB : CovBySMul M K A₂ B₁) :
    CovBySMul M K A₁ B₂ := (hAB.subset_left hA).subset_right hB
