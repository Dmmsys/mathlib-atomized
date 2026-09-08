/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Group.TypeTags.Pointwise

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require classifying these exponents according to their total sum
`∑ i, f i`, or variants, and this file provides some API for that.

## Weight

We fix a type `σ`, a semiring `R`, an `R`-module `M`,
as well as a function `w : σ → M`. (The important case is `R = ℕ`.)

- `Finsupp.weight` of a finitely supported function `f : σ →₀ R`
  with respect to `w`: it is the sum `∑ (f i) • (w i)`.
  It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight` says that `f s ≤ f.weight w` when `M = ℕ`

- `Finsupp.le_weight_of_ne_zero` says that `w s ≤ f.weight w`
  for `IsOrderedAddMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight_of_ne_zero'` is the same statement for `CanonicallyOrderedAdd M`.

- `NonTorsionWeight`: all values `w s` are nontorsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
  `f = 0` for `NonTorsionWeight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree f` is the sum of all `f s`, for `s ∈ f.support`.
  The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1` when `R` is a semiring.
  This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded degree.


## TODO

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
  both `AddMonoidHom` or both functions.

-/

@[expose] public section

open Module

variable {σ M R : Type*} [Semiring R] (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]
/-- The `weight` of the finitely supported function `f : σ →₀ R`
with respect to `w : σ → M` is the sum `∑ i, f i • w i`. -/
/-
**Finsupp.weight** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：weight : (σ ->₀ R) ->+ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `weight` of the finitely supported function `f : σ →₀ R`
with respect to `w : σ → M` is the sum `∑ i, f i • w i`.
-/
noncomputable def weight : (σ →₀ R) →+ M :=
  (Finsupp.linearCombination R w).toAddMonoidHom
/-
**Finsupp.weight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_apply (f : σ ->₀ R) : weight w f = Finsupp.sum f (fun i c => c • w 
i)
参数：f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weight_apply (f : σ →₀ R) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl
/-
**Finsupp.weight_single_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_single_index [DecidableEq σ] (s : σ) (c : M) (f : σ ->₀ R) : weight
 (Pi.single s c) f = f s • c
参数：s : σ；c : M；f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.linearCombination_single_index`：linearCombination_single_index (
c : M) (a : α) (f : α ->₀ R) [DecidableEq α] : linearCombination R (Pi.single a 
c) f = f a • c
-/
theorem weight_single_index [DecidableEq σ] (s : σ) (c : M) (f : σ →₀ R) :
    weight (Pi.single s c) f = f s • c :=
  linearCombination_single_index σ M R c s f
/-
**Finsupp.weight_single_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_single_one_apply [DecidableEq σ] (s : σ) (f : σ ->₀ R) : weight (Pi
.single s 1) f = f s
参数：s : σ；f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.weight_single_index`：weight_single_index [DecidableEq σ] (s : σ)
 (c : M) (f : σ ->₀ R) : weight (Pi.single s c) f = f s • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem weight_single_one_apply [DecidableEq σ] (s : σ) (f : σ →₀ R) :
    weight (Pi.single s 1) f = f s := by
  rw [weight_single_index, smul_eq_mul, mul_one]
/-
**Finsupp.weight_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_single (s : σ) (r : R) : weight w (Finsupp.single s r) = r • w s
参数：s : σ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
-/
theorem weight_single (s : σ) (r : R) :
    weight w (Finsupp.single s r) = r • w s :=
  Finsupp.linearCombination_single _ _ _
/-
**Finsupp.weight_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_eq_sum [Fintype σ] (f : σ ->₀ R) : weight w f = ∑ i, f i • w i
参数：f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.weight_apply`：weight_apply (f : σ ->₀ R) : weight w f = Finsupp.
sum f (fun i c => c • w i)
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem weight_eq_sum [Fintype σ] (f : σ →₀ R) : weight w f = ∑ i, f i • w i := by
  rw [weight_apply, f.sum_fintype (fun i c ↦ c • w i) fun _ ↦ zero_smul _ _]

variable (R) in
/-- A weight function is nontorsion if its values are not torsion. -/
/-
**Finsupp.NonTorsionWeight** 是 Mathlib 中的一个归纳类型，位于命名空间 `Finsupp`。
形式化陈述：{σ : Type u_1} →   {M : Type u_2} →     (R : Type u_3) → [inst : Semiring 
R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → (σ → M) → Prop
参数：R : Type u_3；σ → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weight function is nontorsion if its values are not torsion.
-/
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {r : R} {s : σ} (h : r • w s = 0) : r = 0

variable (R) in
/-- Without zero divisors, nonzero weight is a `NonTorsionWeight` -/
/-
**Finsupp.nonTorsionWeight_of** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：nonTorsionWeight_of [IsDomain R] [IsTorsionFree R M] (hw : forall i : σ, w
 i != 0) : NonTorsionWeight R w where eq_zero_of_smul_eq_zero {n s} h
参数：hw : forall i : σ, w i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α

--- 原说明 ---
Without zero divisors, nonzero weight is a `NonTorsionWeight`
-/
theorem nonTorsionWeight_of [IsDomain R] [IsTorsionFree R M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight R w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)

variable (R) in
/-
**Finsupp.NonTorsionWeight.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.NonTorsion
Weight`。
形式化陈述：∀ {σ : Type u_1} {M : Type u_2} (R : Type u_3) [inst : Semiring R] (w : σ 
→ M) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Nontrivial R] [F
insupp.NonTorsionWeight R w] (s : σ), w s ≠ 0
参数：R : Type u_3；w : σ → M；s : σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero`：∀ {σ : Type u_1} {M : 
Type u_2} {R : Type u_3} {inst : Semiring R} {inst_1 : AddCommMonoid M}   {inst_
2 : _root_.Module R M} {w : σ → M} [se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem NonTorsionWeight.ne_zero [Nontrivial R] [NonTorsionWeight R w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul R (w s)] at h
  apply zero_ne_one.symm (α := R)
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

variable {w} in
/-
**Finsupp.weight_sub_single_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：weight_sub_single_add {f : σ ->₀ Nat} {i : σ} (hi : f i != 0) : (f - singl
e i 1).weight w + w i = f.weight w
参数：hi : f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.sub_add_single_one_cancel`：sub_add_single_one_cancel {u : ι ->₀ 
Nat} {i : ι} (h : u i != 0) : u - single i 1 + single i 1 = u
· 使用定理 `Finsupp.weight_apply`：weight_apply (f : σ ->₀ R) : weight w f = Finsupp.
sum f (fun i c => c • w i)
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma weight_sub_single_add {f : σ →₀ ℕ} {i : σ} (hi : f i ≠ 0) :
    (f - single i 1).weight w + w i = f.weight w := by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index', sum_single_index, one_smul, weight_apply]
  exacts [zero_smul .., fun _ ↦ zero_smul .., fun _ _ _ ↦ add_smul ..]

end AddCommMonoid

section OrderedAddCommMonoid

/-
**Finsupp.le_weight** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_weight (w : σ -> Nat) {s : σ} (hs : w s != 0) (f : σ ->₀ Nat) : f s <= 
weight w f
参数：w : σ -> Nat；hs : w s != 0；f : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton_of_mem`：∀ {ι : Type u_1} {M : Type
 u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι}, 
  i ∈ s → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem le_weight (w : σ → ℕ) {s : σ} (hs : w s ≠ 0) (f : σ →₀ ℕ) :
    f s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s ∈ f.support
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [notMem_support_iff] at h
    rw [h]
    apply zero_le

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] (w : σ → M)
  {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Module R M]

variable {w} in
/-
**Finsupp.le_weight_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_weight_of_ne_zero (hw : forall s, 0 <= w s) {s : σ} {f : σ ->₀ Nat} (hs
 : f s != 0) : w s <= weight w f
参数：hw : forall s, 0 <= w s；hs : f s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `le_smul_of_one_le_left`：le_smul_of_one_le_left [SMulPosMono α β] (hb : 0
 <= b) (h : 1 <= a) : b <= a • b
· 使用定理 `instSMulPosMonoNatOfIsOrderedAddMonoid`：∀ {M : Type u_3} [inst : Partial
Order M] [inst_1 : AddCommMonoid M] [IsOrderedAddMonoid M], SMulPosMono ℕ M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton_of_mem`：∀ {ι : Type u_1} {M : Type
 u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι}, 
  i ∈ s → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `nsmul_nonneg`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorder M
] [AddLeftMono M] {a : M}, 0 ≤ a → ∀ (n : ℕ), 0 ≤ n • a
-/
theorem le_weight_of_ne_zero (hw : ∀ s, 0 ≤ w s) {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hs]
    exact le_add_of_nonneg_right <| Finset.sum_nonneg <|
      fun i _ ↦ nsmul_nonneg (hw i) (f i)

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [CanonicallyOrderedAdd M] (w : σ → M)

/-
**Finsupp.le_weight_of_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_weight_of_ne_zero' {s : σ} {f : σ ->₀ Nat} (hs : f s != 0) : w s <= wei
ght w f
参数：hs : f s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.le_weight_of_ne_zero`：le_weight_of_ne_zero (hw : forall s, 0 <= 
w s) {s : σ} {f : σ ->₀ Nat} (hs : f s != 0) : w s <= weight w f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem le_weight_of_ne_zero' {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) : w s ≤ weight w f :=
  le_weight_of_ne_zero (fun _ ↦ zero_le) hs

/-- If `M` is a `CanonicallyOrderedAddCommMonoid`, then `weight f` is zero iff `f = 0`. -/
/-
**Finsupp.weight_eq_zero_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：weight_eq_zero_iff_eq_zero (w : σ -> M) [NonTorsionWeight Nat w] {f : σ ->
₀ Nat} : weight w f = 0 ↔ f = 0
参数：w : σ -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finsupp.NonTorsionWeight.ne_zero`：∀ {σ : Type u_1} {M : Type u_2} (R : T
ype u_3) [inst : Semiring R] (w : σ → M) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] [No…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Finsupp.le_weight_of_ne_zero'`：le_weight_of_ne_zero' {s : σ} {f : σ ->₀ 
Nat} (hs : f s != 0) : w s <= weight w f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `M` is a `CanonicallyOrderedAddCommMonoid`, then `weight f` is zero iff `f = 
0`.
-/
theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight ℕ w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero ℕ w s
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]
/-
**Finsupp.finite_of_nat_weight_le** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_nat_weight_le [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0
) (n : Nat) : {d : σ ->₀ Nat | weight w d <= n}.Finite
参数：w : σ -> Nat；hw : forall x, w x != 0；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finsupp.le_weight`：le_weight (w : σ -> Nat) {s : σ} (hs : w s != 0) (f :
 σ ->₀ Nat) : f s <= weight w f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem finite_of_nat_weight_le [Finite σ] (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d ≤ n}.Finite := by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ →₀ ℕ | weight w d ≤ n} ⊆ ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_antidiagonal, Prod.exists, exists_and_right, exists_eq_right]
  use Finsupp.equivFunOnFinite.symm (Function.const σ n) - d
  ext x
  dsimp at hd
  grw [← le_weight _ (hw x)] at hd
  simp [*]
/-
**Finsupp.finite_of_nat_weight_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_nat_weight_lt [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0
) (n : Nat) : {d : σ ->₀ Nat | weight w d < n}.Finite
参数：w : σ -> Nat；hw : forall x, w x != 0；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finsupp.finite_of_nat_weight_le`：finite_of_nat_weight_le [Finite σ] (w :
 σ -> Nat) (hw : forall x, w x != 0) (n : Nat) : {d : σ ->₀ Nat | weight w d <= 
n}.Finite
-/
theorem finite_of_nat_weight_lt [Finite σ] (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d < n}.Finite :=
  Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)
/-
**Finsupp.finite_of_nat_weight_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_nat_weight_eq [Finite σ] (w : σ -> Nat) (hw : forall x, w x != 0
) (n : Nat) : {d : σ ->₀ Nat | weight w d = n}.Finite
参数：w : σ -> Nat；hw : forall x, w x != 0；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finsupp.finite_of_nat_weight_le`：finite_of_nat_weight_le [Finite σ] (w :
 σ -> Nat) (hw : forall x, w x != 0) (n : Nat) : {d : σ ->₀ Nat | weight w d <= 
n}.Finite
-/
theorem finite_of_nat_weight_eq [Finite σ] (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d = n}.Finite :=
  Set.Finite.subset (finite_of_nat_weight_le w hw n) (by grind)

end CanonicallyOrderedAddCommMonoid

variable {R : Type*} [AddCommMonoid R]

/-- The degree of a finsupp function. -/
/-
**Finsupp.degree** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：degree : (σ ->₀ R) ->+ R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of a finsupp function.
-/
def degree : (σ →₀ R) →+ R where
  toFun := fun d => ∑ i ∈ d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl
/-
**Finsupp.degree_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degree_apply (d : σ ->₀ R) : degree d = ∑ i in d.support, d i
参数：d : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_apply (d : σ →₀ R) : degree d = ∑ i ∈ d.support, d i := rfl
/-
**Finsupp.degree_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degree_eq_sum [Fintype σ] (f : σ ->₀ R) : f.degree = ∑ i, f i
参数：f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_apply`：degree_apply (d : σ ->₀ R) : degree d = ∑ i in d.s
upport, d i
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem degree_eq_sum [Fintype σ] (f : σ →₀ R) : f.degree = ∑ i, f i := by
  rw [degree_apply, Finset.sum_subset] <;> simp

@[simp]
/-
**Finsupp.degree_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degree_single (a : σ) (r : R) : (Finsupp.single a r).degree = r
参数：a : σ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem degree_single (a : σ) (r : R) : (Finsupp.single a r).degree = r :=
  Finsupp.sum_single_index (h := fun _ => id) rfl
/-
**Finsupp.degree_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：degree_eq_zero_iff {R : Type*} [AddCommMonoid R] [PartialOrder R] [Canonic
allyOrderedAdd R] (d : σ ->₀ R) : degree d = 0 ↔ d = 0
参数：d : σ ->₀ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma degree_eq_zero_iff {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (d : σ →₀ R) :
    degree d = 0 ↔ d = 0 := by
  simp only [degree_apply, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]
/-
**Finsupp.le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_degree {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrder
edAdd R] (s : σ) (f : σ ->₀ R) : f s <= degree f
参数：s : σ；f : σ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.single_le_sum_of_canonicallyOrdered`：∀ {ι : Type u_1} {M : Type u
_4} [inst : AddCommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f 
: ι → M}   {s : Finset ι} {i : ι…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem le_degree {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (s : σ) (f : σ →₀ R) :
    f s ≤ degree f := by
  by_cases h : s ∈ f.support
  · exact Finset.single_le_sum_of_canonicallyOrdered h
  · simp only [notMem_support_iff] at h
    simp only [h, zero_le]
/-
**Finsupp.degree_eq_weight_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degree_eq_weight_one {R : Type*} [Semiring R] : degree (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.addHom_ext'`：addHom_ext' [AddZeroClass N] ⦃f g : (α ->₀ M) ->+ N
⦄ (H : forall x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.singleAddHom_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZ
eroClass M] (a : ι) (b : M), (Finsupp.singleAddHom a) b = fun₀ | a => b
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_eq_weight_one {R : Type*} [Semiring R] :
    degree (R := R) (σ := σ) = weight (fun _ ↦ 1) := by
  ext d
  simp [weight_apply, smul_eq_mul, mul_one]
/-
**Finsupp.finite_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_degree_le [Finite σ] (n : Nat) : {f : σ ->₀ Nat | degree f <= n}
.Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `Finsupp.finite_of_nat_weight_le`：finite_of_nat_weight_le [Finite σ] (w :
 σ -> Nat) (hw : forall x, w x != 0) (n : Nat) : {d : σ ->₀ Nat | weight w d <= 
n}.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]
/-
**Finsupp.finite_of_degree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_degree_lt [Finite σ] (n : Nat) : {f : σ ->₀ Nat | degree f < n}.
Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finsupp.finite_of_degree_le`：finite_of_degree_le [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f <= n}.Finite
-/
lemma finite_of_degree_lt [Finite σ] (n : ℕ) : {f : σ →₀ ℕ | degree f < n}.Finite :=
  Set.Finite.subset (finite_of_degree_le n) (by grind)
/-
**Finsupp.finite_of_degree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：finite_of_degree_eq [Finite σ] (n : Nat) : {f : σ ->₀ Nat | f.degree = n}.
Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finsupp.finite_of_degree_le`：finite_of_degree_le [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f <= n}.Finite
-/
lemma finite_of_degree_eq [Finite σ] (n : ℕ) : {f : σ →₀ ℕ | f.degree = n}.Finite :=
  Set.Finite.subset (finite_of_degree_le n) (by grind)
/-
**Finsupp.range_single_one** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：range_single_one : Set.range (fun a : σ => Finsupp.single a 1) = { d | d.d
egree = 1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.sum_eq_one_iff`：sum_eq_one_iff (d : α ->₀ Nat) : sum d (fun _ n 
=> n) = 1 ↔ exists a, d = single a 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma range_single_one :
    Set.range (fun a : σ ↦ Finsupp.single a 1) = { d | d.degree = 1 } := by
  refine subset_antisymm ?_ ?_
  · simp [Set.range_subset_iff]
  · intro p (hp : p.sum (fun a k ↦ k) = 1)
    obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hp
    use a

@[simp]
/-
**Finsupp.degree_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degree_mapDomain {τ : Type*} (f : σ -> τ) [AddCommMonoid M] (x : σ ->₀ M) 
: degree (x.mapDomain f) = degree x
参数：f : σ -> τ；x : σ ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
-/
theorem degree_mapDomain {τ : Type*} (f : σ → τ) [AddCommMonoid M] (x : σ →₀ M) :
    degree (x.mapDomain f) = degree x := by
  simp [mapDomain, sum]
  dsimp [degree_apply]

@[deprecated (since := "2026-04-27")]
alias degree_mapDomain_eq_of_subsingletonAddUnits := degree_mapDomain

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd** 是 Mathlib 中的一个定理，位于命名
空间 `Finsupp`。
形式化陈述：degree_comapDomain_le_of_canonicallyOrderedAdd {τ : Type*} {f : σ -> τ} [A
ddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M] {x : τ ->₀ M} (hf : S
et.InjOn f (f ⁻¹' x.support)) : degree (x.comapDomain f hf) <= degree x
参数：hf : Set.InjOn f (f ⁻¹' x.support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_preimage'`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_3} [in
st : AddCommMonoid β] (f : ι → κ)   [inst_1 : DecidablePred fun x => x ∈ Set.ran
ge f] (s :…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
theorem degree_comapDomain_le_of_canonicallyOrderedAdd {τ : Type*} {f : σ → τ} [AddCommMonoid M]
    [PartialOrder M] [CanonicallyOrderedAdd M] {x : τ →₀ M} (hf : Set.InjOn f (f ⁻¹' x.support)) :
      degree (x.comapDomain f hf) ≤ degree x := by
  classical
  simpa [degree, comapDomain, Finset.sum_preimage' f x.support hf x] using
    Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
/-
**Finsupp.degree_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：degree_mono {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrd
eredAdd R] : Monotone (Finsupp.degree (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
-/
lemma degree_mono {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R] :
    Monotone (Finsupp.degree (σ := σ) (R := R)) :=
  fun _ _ e ↦
    (Finset.sum_le_sum_of_subset (support_mono e)).trans (Finset.sum_le_sum fun _ _ ↦ e _)
/-
**Finsupp.exists_le_degree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：exists_le_degree_eq {σ : Type*} (f : σ ->₀ Nat) (n : Nat) (hn : n <= f.deg
ree) : exists g <= f, g.degree = n
参数：f : σ ->₀ Nat；n : Nat；hn : n <= f.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_le_degree_eq {σ : Type*} (f : σ →₀ ℕ) (n : ℕ) (hn : n ≤ f.degree) :
    ∃ g ≤ f, g.degree = n := by
  induction n with
  | zero => simp [degree_eq_zero_iff]
  | succ n IH =>
    obtain ⟨g, hgf, rfl⟩ := IH (by lia)
    obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    exact ⟨g + .single i 1, add_le_add_right (by simp; grind) _, by simp⟩

open scoped Pointwise in
/-
**Finsupp.degree_preimage_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：degree_preimage_add {σ : Type*} (s t : Set Nat) : degree (σ
参数：s t : Set Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.preimage_add_preimage_subset`：∀ {F : Type u_1} {α : Type u_2} {β : T
ype u_3} [inst : Add α] [inst_1 : Add β] [inst_2 : FunLike F α β]   [AddHomClass
 F α β] (m : F) {s t :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `Finsupp.exists_le_degree_eq`：exists_le_degree_eq {σ : Type*} (f : σ ->₀ 
Nat) (n : Nat) (hn : n <= f.degree) : exists g <= f, g.degree = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma degree_preimage_add {σ : Type*} (s t : Set ℕ) :
    degree (σ := σ) ⁻¹' (s + t) = degree (σ := σ) ⁻¹' s + degree (σ := σ) ⁻¹' t := by
  refine (Set.preimage_add_preimage_subset ..).antisymm' ?_
  rintro f ⟨m, hm, n, hn, e : m + n = _⟩
  obtain ⟨g, hgf, rfl⟩ := exists_le_degree_eq f m (by grind)
  obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
  exact Set.add_mem_add hm (by simp_all)

open scoped Pointwise in
/-
**Finsupp.degree_preimage_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：degree_preimage_nsmul {σ : Type*} (s : Set Nat) (n : Nat) (hn : n != 0) : 
degree (σ
参数：s : Set Nat；n : Nat；hn : n != 0。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用引理 `Finsupp.degree_preimage_add`：degree_preimage_add {σ : Type*} (s t : Set 
Nat) : degree (σ
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma degree_preimage_nsmul {σ : Type*} (s : Set ℕ) (n : ℕ) (hn : n ≠ 0) :
    degree (σ := σ) ⁻¹' (n • s) = n • degree (σ := σ) ⁻¹' s := by
  obtain (_ | n) := n; · contradiction
  induction n <;> simp_all [succ_nsmul, degree_preimage_add]

open scoped Pointwise in
/-
**Finsupp.nsmul_single_one_image** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：nsmul_single_one_image {α : Type*} {n : Nat} {s : Set α} : n • (single · 1
) '' s = {x : α ->₀ Nat | x.degree = n ∧ ↑x.support subseteq s}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add'`：∀ {α : Type u} [inst : AddCommMagma α] [inst_1 : Pre
order α] [CanonicallyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = c + a
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 40 条，此处仅展示前 30 条）
-/
lemma nsmul_single_one_image {α : Type*} {n : ℕ} {s : Set α} :
    n • (single · 1) '' s = {x : α →₀ ℕ | x.degree = n ∧ ↑x.support ⊆ s} := by
  classical
  induction n with
  | zero => aesop (add simp degree_eq_zero_iff)
  | succ n ih =>
    rw [succ_nsmul, ih]
    refine subset_antisymm ?_ fun f ⟨f_deg, f_supp⟩ ↦ ?_
    · simp [Set.subset_def, Set.mem_add, @forall_comm (α →₀ ℕ)]; grind
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    obtain ⟨x, hx⟩ := le_iff_exists_add'.mp
      (show single i 1 ≤ f by simpa [Nat.one_le_iff_ne_zero] using hi)
    exact ⟨x, by aesop (add simp Set.subset_def), _, ⟨_, f_supp (by simp_all), rfl⟩, hx.symm⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Pointwise in
/-
**Finsupp.image_pow_eq_finsuppProd_image** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：image_pow_eq_finsuppProd_image {α β : Type*} [CommMonoid β] {f : α -> β} {
n} {s : Set α} : (f '' s) ^ n = (·.prod (f · ^ ·)) '' {x : α ->₀ Nat | x.degree 
= n ∧ ↑x.support subseteq s}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_add_index`：prod_add_index [DecidableEq α] [AddZeroClass M] 
[CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a in f.support
 union g.sup…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_pow`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Mo
noid α] [inst_1 : Monoid β] [inst_2 : FunLike F α β]   [MonoidHomClass F α β] (f
 : …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Multiplicative.toAdd_image_nsmul`：toAdd_image_nsmul (n : Nat) (s : Set (
Multiplicative M)) : toAdd '' (s ^ n) = n • (toAdd '' s)
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem image_pow_eq_finsuppProd_image {α β : Type*} [CommMonoid β] {f : α → β} {n} {s : Set α} :
    (f '' s) ^ n = (·.prod (f · ^ ·)) '' {x : α →₀ ℕ | x.degree = n ∧ ↑x.support ⊆ s} := by
  classical
  suffices ∀ (s : Set (α →₀ ℕ)), ((·.prod (f · ^ ·)) '' s) ^ n = (·.prod (f · ^ ·)) '' (n • s) by
    simp [← nsmul_single_one_image, ← this, Set.image_image]
  intro s
  refine (Set.image_pow (⟨⟨(·.prod (f · ^ ·)) ∘ Multiplicative.toAdd, by simp⟩,
    by simp [Finsupp.prod_add_index, pow_add]⟩ : Multiplicative (α →₀ ℕ) →* β) _ _).symm.trans ?_
  simp [-Function.comp_apply, Set.image_comp, show Multiplicative.toAdd '' s = s from
    Set.image_id _]

end Finsupp

