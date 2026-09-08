/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree and support of univariate polynomials

## Main results
* `Polynomial.as_sum_support`: write `p : R[X]` as a sum over its support
* `Polynomial.as_sum_range`: write `p : R[X]` as a sum over `{0, ..., natDegree p}`
* `Polynomial.natDegree_mem_support_of_nonzero`: `natDegree p ∈ support p` if `p ≠ 0`
-/

public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-
**Polynomial.supDegree_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：supDegree_eq_natDegree (p : R[X]) : p.toFinsupp.supDegree id = p.natDegree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.supDegree_zero`：supDegree_zero : (0 : R[A]).supDegree D
 = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
· 使用定理 `AddMonoidAlgebra.supDegree_withBot_some_comp`：supDegree_withBot_some_com
p {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty) : supDegree (WithBo
t.some ∘ D) s = supDegree D s
· 使用定理 `Polynomial.support_toFinsupp`：support_toFinsupp (p : R[X]) : p.toFinsupp
.coeff.support = p.support
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.support_eq_empty`：support_eq_empty : p.support = ∅ ↔ p = 0
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Polynomial.supDegree_eq_degree`：supDegree_eq_degree (p : R[X]) : p.toFin
supp.supDegree WithBot.some = p.degree
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
-/
theorem supDegree_eq_natDegree (p : R[X]) : p.toFinsupp.supDegree id = p.natDegree := by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp, Function.comp_id, supDegree_eq_degree,
    degree_eq_natDegree h, Nat.cast_withBot]
  rwa [support_toFinsupp, nonempty_iff_ne_empty, Ne, support_eq_empty]
/-
**Polynomial.le_natDegree_of_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_natDegree_of_mem_supp (a : Nat) : a in p.support -> a <= natDegree p
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem le_natDegree_of_mem_supp (a : ℕ) : a ∈ p.support → a ≤ natDegree p :=
  le_natDegree_of_ne_zero ∘ mem_support_iff.mp
/-
**Polynomial.supp_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：supp_subset_range (h : natDegree p < m) : p.support subseteq Finset.range 
m
参数：h : natDegree p < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
-/
theorem supp_subset_range (h : natDegree p < m) : p.support ⊆ Finset.range m := fun _n hn =>
  mem_range.2 <| (le_natDegree_of_mem_supp _ hn).trans_lt h
/-
**Polynomial.supp_subset_range_natDegree_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：supp_subset_range_natDegree_succ : p.support subseteq Finset.range (natDeg
ree p + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.supp_subset_range`：supp_subset_range (h : natDegree p < m) : 
p.support subseteq Finset.range m
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) :=
  supp_subset_range (Nat.lt_succ_self _)
/-
**Polynomial.as_sum_support** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_support (p : R[X]) : p = ∑ i in p.support, monomial i (p.coeff i)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
-/
theorem as_sum_support (p : R[X]) : p = ∑ i ∈ p.support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm
/-
**Polynomial.as_sum_support_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i in p.support, C (p.coeff i
) * X ^ i
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Polynomial.as_sum_support`：as_sum_support (p : R[X]) : p = ∑ i in p.supp
ort, monomial i (p.coeff i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i ∈ p.support, C (p.coeff i) * X ^ i :=
  _root_.trans p.as_sum_support <| by simp only [C_mul_X_pow_eq_monomial]

/-- We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.natDegree < n`.
-/
/-
**Polynomial.sum_over_range'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_over_range' [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : fora
ll n, f n 0 = 0) (n : Nat) (hn : p.natDegree < n) : p.sum f = ∑ a in range n, f 
a (coeff p a)
参数：p : R[X]；h : forall n, f n 0 = 0；n : Nat；hn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.supp_subset_range`：supp_subset_range (h : natDegree p < m) : 
p.support subseteq Finset.range m
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …

--- 原说明 ---
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.natDegree < n`.
-/
theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (hn : p.natDegree < n) : p.sum f = ∑ a ∈ range n, f a (coeff p a) := by
  have := supp_subset_range hn
  simp only [Polynomial.sum, support, coeff] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

/-- We can reexpress a sum over `p.support` as a sum over `range (p.natDegree + 1)`.
-/
/-
**Polynomial.sum_over_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_over_range [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : foral
l n, f n 0 = 0) : p.sum f = ∑ a in range (p.natDegree + 1), f a (coeff p a)
参数：p : R[X]；h : forall n, f n 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.sum_over_range'`：sum_over_range' [AddCommMonoid S] (p : R[X])
 {f : Nat -> R -> S} (h : forall n, f n 0 = 0) (n : Nat) (hn : p.natDegree < n) 
: p.sum f = ∑ a …
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
We can reexpress a sum over `p.support` as a sum over `range (p.natDegree + 1)`.
-/
theorem sum_over_range [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
    p.sum f = ∑ a ∈ range (p.natDegree + 1), f a (coeff p a) :=
  sum_over_range' p h (p.natDegree + 1) (lt_add_one _)

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
/-
**Polynomial.sum_fin** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_fin [AddCommMonoid S] (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {
n : Nat} {p : R[X]} (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum
 f
参数：f : Nat -> R -> S；hf : forall i, f i 0 = 0；hn : p.degree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sum_zero_index`：sum_zero_index {S : Type*} [AddCommMonoid S] 
(f : Nat -> R -> S) : (0 : R[X]).sum f = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Polynomial.sum_over_range'`：sum_over_range' [AddCommMonoid S] (p : R[X])
 {f : Nat -> R -> S} (h : forall n, f n 0 = 0) (n : Nat) (hn : p.natDegree < n) 
: p.sum f = ∑ a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_lt_iff_degree_lt`：natDegree_lt_iff_degree_lt (hp : 
p != 0) : p.natDegree < n ↔ p.degree < ↑n
· 使用定理 `Fin.sum_univ_eq_sum_range`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f 
: ℕ → α) (n : ℕ), ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i
-/
theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum f := by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn),
    Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]
/-
**Polynomial.as_sum_range'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_range' (p : R[X]) (n : Nat) (hn : p.natDegree < n) : p = ∑ i in ran
ge n, monomial i (coeff p i)
参数：p : R[X]；n : Nat；hn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum_over_range'`：sum_over_range' [AddCommMonoid S] (p : R[X])
 {f : Nat -> R -> S} (h : forall n, f n 0 = 0) (n : Nat) (hn : p.natDegree < n) 
: p.sum f = ∑ a …
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
-/
theorem as_sum_range' (p : R[X]) (n : ℕ) (hn : p.natDegree < n) :
    p = ∑ i ∈ range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range' monomial_zero_right _ hn
/-
**Polynomial.as_sum_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_range (p : R[X]) : p = ∑ i in range (p.natDegree + 1), monomial i (
coeff p i)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.as_sum_range'`：as_sum_range' (p : R[X]) (n : Nat) (hn : p.nat
Degree < n) : p = ∑ i in range n, monomial i (coeff p i)
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem as_sum_range (p : R[X]) : p = ∑ i ∈ range (p.natDegree + 1), monomial i (coeff p i) :=
  p.as_sum_range' _ (lt_add_one _)
/-
**Polynomial.as_sum_range_C_mul_X_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_range_C_mul_X_pow' (p : R[X]) {n : Nat} (hn : p.natDegree < n) : p 
= ∑ i in range n, C (coeff p i) * X ^ i
参数：p : R[X]；hn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.as_sum_range'`：as_sum_range' (p : R[X]) (n : Nat) (hn : p.nat
Degree < n) : p = ∑ i in range n, monomial i (coeff p i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem as_sum_range_C_mul_X_pow' (p : R[X]) {n : ℕ} (hn : p.natDegree < n) :
    p = ∑ i ∈ range n, C (coeff p i) * X ^ i :=
  (p.as_sum_range' _ hn).trans <| by simp only [C_mul_X_pow_eq_monomial]
/-
**Polynomial.as_sum_range_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：as_sum_range_C_mul_X_pow (p : R[X]) : p = ∑ i in range (p.natDegree + 1), 
C (coeff p i) * X ^ i
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow'`：as_sum_range_C_mul_X_pow' (p : R[X
]) {n : Nat} (hn : p.natDegree < n) : p = ∑ i in range n, C (coeff p i) * X ^ i
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i ∈ range (p.natDegree + 1), C (coeff p i) * X ^ i :=
  p.as_sum_range_C_mul_X_pow' (lt_add_one _)
/-
**Polynomial.mem_support_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_support_C_mul_X_pow {n a : Nat} {c : R} (h : a in support (C c * X ^ n
)) : a = n
参数：h : a in support (C c * X ^ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Polynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset (n : N
at) (c : R) : Polynomial.support (C c * X ^ n) subseteq singleton n
-/
theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ support (C c * X ^ n)) : a = n :=
  mem_singleton.1 <| support_C_mul_X_pow_subset n c h
/-
**Polynomial.card_support_C_mul_X_pow_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：card_support_C_mul_X_pow_le_one {c : R} {n : Nat} : #(support (C c * X ^ n
)) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Polynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset (n : N
at) (c : R) : Polynomial.support (C c * X ^ n) subseteq singleton n
-/
theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : #(support (C c * X ^ n)) ≤ 1 := by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow_subset n c)
/-
**Polynomial.card_supp_le_succ_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_supp_le_succ_natDegree (p : R[X]) : #p.support <= p.natDegree + 1
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Polynomial.supp_subset_range_natDegree_succ`：supp_subset_range_natDegree
_succ : p.support subseteq Finset.range (natDegree p + 1)
-/
theorem card_supp_le_succ_natDegree (p : R[X]) : #p.support ≤ p.natDegree + 1 := by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card supp_subset_range_natDegree_succ
/-
**Polynomial.le_degree_of_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_degree_of_mem_supp (a : Nat) : a in p.support -> ↑a <= degree p
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp
/-
**Polynomial.nonempty_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nonempty_support_iff : p.support.Nonempty ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.support_eq_empty`：support_eq_empty : p.support = ∅ ↔ p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_support_iff : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Ne, nonempty_iff_ne_empty, Ne, ← support_eq_empty]

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/-
**Polynomial.natDegree_mem_support_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_mem_support_of_nonzero (H : p != 0) : p.natDegree in p.support
参数：H : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem natDegree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.support := by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H
/-
**Polynomial.natDegree_eq_support_max'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_support_max' (h : p != 0) : p.natDegree = p.support.max' (non
empty_support_iff.mpr h)
参数：h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Polynomial.natDegree_mem_support_of_nonzero`：natDegree_mem_support_of_no
nzero (H : p != 0) : p.natDegree in p.support
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.max'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
H : s.Nonempty) (x : α), (∀ y ∈ s, y ≤ x) → s.max' H ≤ x
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
-/
theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm <|
    max'_le _ _ _ le_natDegree_of_mem_supp

end Semiring

end Polynomial

