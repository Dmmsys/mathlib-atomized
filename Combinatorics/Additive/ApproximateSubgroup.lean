/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Combinatorics.Additive.RuzsaCovering
public import Mathlib.Combinatorics.Additive.SmallTripling

/-!
# Approximate subgroups

This file defines approximate subgroups of a group, namely symmetric sets `A` such that `A * A` can
be covered by a small number of translates of `A`.

## Main results

Approximate subgroups are a central concept in additive combinatorics, as a natural weakening and
flexible substitute of genuine subgroups. As such, they share numerous properties with subgroups:
* `IsApproximateSubgroup.image`: Group homomorphisms send approximate subgroups to approximate
  subgroups
* `IsApproximateSubgroup.pow_inter_pow`: The intersection of (non-trivial powers of) two approximate
  subgroups is an approximate subgroup. Warning: The intersection of two approximate subgroups isn't
  an approximate subgroup in general.

Approximate subgroups are close qualitatively and quantitatively to other concepts in additive
combinatorics:
* `IsApproximateSubgroup.card_pow_le`: An approximate subgroup has small powers.
* `IsApproximateSubgroup.of_small_tripling`: A set of small tripling can be made an approximate
  subgroup by squaring.

It can be readily confirmed that approximate subgroups are a weakening of subgroups:
* `isApproximateSubgroup_one`: A 1-approximate subgroup is the same thing as a subgroup.
-/

public section

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A + A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
/-
**IsApproximateAddSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{G : Type u_2} → [AddGroup G] → ℝ → Set G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An approximate subgroup in a group is a symmetric set `A` containing the identit
y and such that
`A + A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  zero_mem : 0 ∈ A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
@[to_additive]
/-
**IsApproximateSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{G : Type u_1} → [Group G] → ℝ → Set G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An approximate subgroup in a group is a symmetric set `A` containing the identit
y and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  one_mem : 1 ∈ A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

/-
**IsApproximateSubgroup.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `IsApproximateSubgrou
p`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {A : Set G} {K : ℝ}, IsApproximateSubgro
up K A → A.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] {K : ℝ}
 {A : Set G}, IsApproximateSubgroup K A → 1 ∈ A
-/
@[to_additive] lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
/-
**IsApproximateSubgroup.one_le** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSubgroup`
。
形式化陈述：one_le (hA : IsApproximateSubgroup K A) : 1 <= K
参数：hA : IsApproximateSubgroup K A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `IsApproximateSubgroup.nonempty`：∀ {G : Type u_1} [inst : Group G] {A : S
et G} {K : ℝ}, IsApproximateSubgroup K A → A.Nonempty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  grw [← hF]
  have : F.Nonempty := by by_contra! rfl; simp [hA.nonempty.ne_empty] at hSF
  simpa

@[to_additive]
/-
**IsApproximateSubgroup.mono** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSubgroup`。
形式化陈述：mono (hKL : K <= L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgro
up L A where one_mem
参数：hKL : K <= L；hA : IsApproximateSubgroup K A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] {K : ℝ}
 {A : Set G}, IsApproximateSubgroup K A → 1 ∈ A
· 使用定理 `IsApproximateSubgroup.inv_eq_self`：∀ {G : Type u_1} [inst : Group G] {K 
: ℝ} {A : Set G}, IsApproximateSubgroup K A → A⁻¹ = A
· 使用引理 `CovBySMul.mono`：CovBySMul.mono (hKL : K <= L) : CovBySMul M K A B -> Cov
BySMul M L A B
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
-/
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
/-
**IsApproximateSubgroup.card_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSubg
roup`。
形式化陈述：card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (
A : Set G)) : forall {n}, #(A ^ n) <= K ^ (n - 1) * #A | 0 => by simpa using hA.
nonempty | 1 => by simp | n + 2 => by obtain ⟨F, hF, hSF⟩
参数：hA : IsApproximateSubgroup K (A : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.card_one`：card_one : #(1 : Finset α) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsApproximateSubgroup.nonempty`：∀ {G : Type u_1} [inst : Group G] {A : S
et G} {K : ℝ}, IsApproximateSubgroup K A → A.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Set.pow_subset_pow_mul_of_sq_subset_mul`：pow_subset_pow_mul_of_sq_subset
_mul (hst : s ^ 2 subseteq t * s) (hn : n != 0) : s ^ n subseteq t ^ (n - 1) * s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_mul_le`：card_mul_le : #(s * t) <= #s * #t
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.card_pow_le`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mo
noid α] {s : Finset α} {n : ℕ}, (s ^ n).card ≤ s.card ^ n
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by lia)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

@[to_additive]
/-
**IsApproximateSubgroup.card_mul_self_le** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximat
eSubgroup`。
形式化陈述：card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgrou
p K (A : Set G)) : #(A * A) <= K * #A
参数：hA : IsApproximateSubgroup K (A : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `IsApproximateSubgroup.card_pow_le`：card_pow_le [DecidableEq G] {A : Fins
et G} (hA : IsApproximateSubgroup K (A : Set G)) : forall {n}, #(A ^ n) <= K ^ (
n - 1) * #A | 0 => by s…
-/
lemma card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) ≤ K * #A := by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]
/-
**IsApproximateSubgroup.image** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSubgroup`。
形式化陈述：image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : 
F) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where one
_mem
参数：f : F；hA : IsApproximateSubgroup K A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] {K : ℝ}
 {A : Set G}, IsApproximateSubgroup K A → 1 ∈ A
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsApproximateSubgroup.inv_eq_self`：∀ {G : Type u_1} [inst : Group G] {K 
: ℝ} {A : Set G}, IsApproximateSubgroup K A → A⁻¹ = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  one_mem := ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : ℝ) ≤ #F := mod_cast F.card_image_le
        _ ≤ K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul, smul_eq_mul] at hAF ⊢
      gcongr

@[to_additive]
/-
**IsApproximateSubgroup.subgroup** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSubgrou
p`。
形式化陈述：subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} : IsApproxi
mateSubgroup 1 (H : Set G) where one_mem
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `inv_coe_set`：inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S 
G] {H : S} : (H : Set G)⁻¹ = H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `coe_set_pow`：∀ {M : Type u_3} {S : Type u_6} [inst : Monoid M] [inst_1 :
 SetLike S M] [SubmonoidClass S M] {n : ℕ},   n ≠ 0 → ∀ (H : S), ↑H ^ n = ↑H
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  one_mem := OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
/-
**IsApproximateSubgroup.of_small_tripling** 是 Mathlib 中的一个引理，位于命名空间 `IsApproxima
teSubgroup`。
形式化陈述：of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 in A) (hAsymm : 
A⁻¹ = A) (hA : #(A ^ 3) <= K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set 
G) where one_mem
参数：hA₁ : 1 in A；hAsymm : A⁻¹ = A；hA : #(A ^ 3) <= K * #A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `Finset.small_pow_of_small_tripling`：small_pow_of_small_tripling (hm : 3 
<= m) (hA : #(A ^ 3) <= K * #A) (hAsymm : A⁻¹ = A) : #(A ^ m) <= K ^ (m - 2) * #
A
· 使用定理 `Finset.ruzsa_covering_mul`：ruzsa_covering_mul (hB : B.Nonempty) (hK : #(
A * B) <= K * #B) : exists F subseteq A, #F <= K ∧ A subseteq F * (B / B)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 ∈ A) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  one_mem := by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling (by lia) hA hAsymm
    have hA₀ : A.Nonempty := ⟨1, hA₁⟩
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
/-
**IsApproximateSubgroup.pow_inter_pow_covBySMul_sq_inter_sq** 是 Mathlib 中的一个引理，位
于命名空间 `IsApproximateSubgroup`。
形式化陈述：pow_inter_pow_covBySMul_sq_inter_sq (hA : IsApproximateSubgroup K A) (hB :
 IsApproximateSubgroup L B) (hm : 2 <= m) (hn : 2 <= n) : CovBySMul G (K ^ (m - 
1) * L ^ (n - 1)) (A ^ m inter B ^ n) (A ^ 2 inter B ^ 2)
参数：hA : IsApproximateSubgroup K A；hB : IsApproximateSubgroup L B；hm : 2 <= m；hn 
: 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
· 使用引理 `IsApproximateSubgroup.one_le`：one_le (hA : IsApproximateSubgroup K A) : 
1 <= K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.card_pow_le`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mo
noid α] {s : Finset α} {n : ℕ}, (s ^ n).card ≤ s.card ^ n
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用引理 `Set.pow_subset_pow_mul_of_sq_subset_mul`：pow_subset_pow_mul_of_sq_subset
_mul (hst : s ^ 2 subseteq t * s) (hn : n != 0) : s ^ n subseteq t ^ (n - 1) * s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.iUnion₂_inter_iUnion₂`：iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι
₁ -> Sort*} {k₂ : κ₁ -> Sort*} (f : forall i₁, ι₂ i₁ -> Set α) (g : forall j₁, k
₂ j₁ -> Set α) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 42 条，此处仅展示前 30 条）
-/
lemma pow_inter_pow_covBySMul_sq_inter_sq
    (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    CovBySMul G (K ^ (m - 1) * L ^ (n - 1)) (A ^ m ∩ B ^ n) (A ^ 2 ∩ B ^ 2) := by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) : ℝ)
      _ ≤ #(F₁ ^ (m - 1)) * #(F₂ ^ (n - 1)) := mod_cast Finset.card_image₂_le ..
      _ ≤ #F₁ ^ (m - 1) * #F₂ ^ (n - 1) := by gcongr <;> exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (m - 1) * L ^ (n - 1) := by gcongr
  · calc
      A ^ m ∩ B ^ n ⊆ (F₁ ^ (m - 1) * A) ∩ (F₂ ^ (n - 1) * B) := by
        gcongr <;> apply pow_subset_pow_mul_of_sq_subset_mul <;> norm_cast <;> lia
      _ = ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), a • A ∩ b • B := by
        simp_rw [← smul_eq_mul, ← iUnion_smul_set, iUnion₂_inter_iUnion₂]; norm_cast
      _ ⊆ ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), f a b • (A⁻¹ * A ∩ (B⁻¹ * B)) := by
        gcongr; exact hf ..
      _ = (Finset.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) * (A ^ 2 ∩ B ^ 2) := by
        simp_rw [hA.inv_eq_self, hB.inv_eq_self, ← sq]
        rw [Finset.coe_image₂, ← smul_eq_mul, ← iUnion_smul_set, biUnion_image2]
        simp_rw [Finset.mem_coe]

open Set in
@[to_additive]
/-
**IsApproximateSubgroup.pow_inter_pow** 是 Mathlib 中的一个引理，位于命名空间 `IsApproximateSu
bgroup`。
形式化陈述：pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup
 L B) (hm : 2 <= m) (hn : 2 <= n) : IsApproximateSubgroup (K ^ (2 * m - 1) * L ^
 (2 * n - 1)) (A ^ m inter B ^ n) where one_mem
参数：hA : IsApproximateSubgroup K A；hB : IsApproximateSubgroup L B；hm : 2 <= m；hn 
: 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.one_mem_pow`：∀ {α : Type u_2} [inst : Monoid α] {s : Set α} {n : ℕ},
 1 ∈ s → 1 ∈ s ^ n
· 使用定理 `IsApproximateSubgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] {K : ℝ}
 {A : Set G}, IsApproximateSubgroup K A → 1 ∈ A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsApproximateSubgroup.inv_eq_self`：∀ {G : Type u_1} [inst : Group G] {K 
: ℝ} {A : Set G}, IsApproximateSubgroup K A → A⁻¹ = A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CovBySMul.subset`：CovBySMul.subset (hA : A₁ subseteq A₂) (hB : B₁ subset
eq B₂) (hAB : CovBySMul M K A₂ B₁) : CovBySMul M K A₁ B₂
· 使用引理 `Set.inter_pow_subset`：inter_pow_subset : (s inter t) ^ n subseteq s ^ n 
inter t ^ n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用引理 `Set.pow_subset_pow`：pow_subset_pow (hst : s subseteq t) (ht : 1 in t) (h
mn : m <= n) : s ^ m subseteq t ^ n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `IsApproximateSubgroup.pow_inter_pow_covBySMul_sq_inter_sq`：pow_inter_pow
_covBySMul_sq_inter_sq (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgr
oup L B) (hm : 2 <= m) (hn : 2 <= n) : CovBySMu…
-/
lemma pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m ∩ B ^ n) where
  one_mem := ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by lia) (by lia)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    calc
      (A ^ m ∩ B ^ n) ^ 2 ⊆ (A ^ m) ^ 2 ∩ (B ^ n) ^ 2 := Set.inter_pow_subset
      _ = A ^ (2 * m) ∩ B ^ (2 * n) := by simp [pow_mul']

end IsApproximateSubgroup

open Set in
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/
@[to_additive (attr := simp)
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/]
/-
**isApproximateSubgroup_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isApproximateSubgroup_one {A : Set G} : IsApproximateSubgroup 1 (A : Set G
) ↔ exists H : Subgroup G, H = A where mp hA
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsApproximateSubgroup.sq_covBySMul`：∀ {G : Type u_1} [inst : Group G] {K
 : ℝ} {A : Set G}, IsApproximateSubgroup K A → CovBySMul G K (A ^ 2) A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `IsApproximateSubgroup.nonempty`：∀ {G : Type u_1} [inst : Group G] {A : S
et G} {K : ℝ}, IsApproximateSubgroup K A → A.Nonempty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Set.singleton_smul`：singleton_smul : ({a} : Set α) • t = a • t
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `IsApproximateSubgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] {K : ℝ}
 {A : Set G}, IsApproximateSubgroup K A → 1 ∈ A
· 使用定理 `IsApproximateSubgroup.inv_eq_self`：∀ {G : Type u_1} [inst : Group G] {K 
: ℝ} {A : Set G}, IsApproximateSubgroup K A → A⁻¹ = A
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 38 条，此处仅展示前 30 条）
-/
lemma isApproximateSubgroup_one {A : Set G} :
    IsApproximateSubgroup 1 (A : Set G) ↔ ∃ H : Subgroup G, H = A where
  mp hA := by
    suffices A * A ⊆ A from
      let H : Subgroup G :=
        { carrier := A
          one_mem' := hA.one_mem
          inv_mem' hx := by rwa [← hA.inv_eq_self, inv_mem_inv]
          mul_mem' hx hy := this (mul_mem_mul hx hy) }
      ⟨H, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : G, A * A ⊆ x • A := by
      obtain ⟨K, hK, hKA⟩ := hA.sq_covBySMul
      simp only [Nat.cast_le_one, Finset.card_le_one_iff_subset_singleton,
        Finset.subset_singleton_iff] at hK
      obtain ⟨x, rfl | rfl⟩ := hK
      · simp [hA.nonempty.ne_empty] at hKA
      · rw [Finset.coe_singleton, singleton_smul, sq] at hKA
        use x
    have hx' : x⁻¹ • (A * A) ⊆ A := by rwa [← subset_smul_set_iff]
    have hx_inv : x⁻¹ ∈ A := by
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hA.one_mem hA.one_mem))
    have hx_sq : x * x ∈ A := by
      rw [← hA.inv_eq_self]
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hx_inv hA.one_mem))
    calc A * A ⊆ x • A := by assumption
      _ = x⁻¹ • (x * x) • A := by simp [smul_smul]
      _ ⊆ x⁻¹ • (A • A) := smul_set_mono (smul_set_subset_smul hx_sq)
      _ ⊆ A := hx'
  mpr := by rintro ⟨H, rfl⟩; exact .subgroup
