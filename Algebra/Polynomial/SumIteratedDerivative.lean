/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Sum of iterated derivatives

This file introduces `Polynomial.sumIDeriv`, the sum of the iterated derivatives of a polynomial,
as a linear map. This is used in particular in the proof of the Lindemann-Weierstrass theorem
(see https://github.com/leanprover-community/mathlib4/pull/6718).

## Main results

* `Polynomial.sumIDeriv`: Sum of iterated derivatives of a polynomial, as a linear map
* `Polynomial.sumIDeriv_apply`, `Polynomial.sumIDeriv_apply_of_lt`,
  `Polynomial.sumIDeriv_apply_of_le`: `Polynomial.sumIDeriv` expressed as a sum
* `Polynomial.sumIDeriv_C`, `Polynomial.sumIDeriv_X`: `Polynomial.sumIDeriv` applied to simple
  polynomials
* `Polynomial.sumIDeriv_map`: `Polynomial.sumIDeriv` commutes with `Polynomial.map`
* `Polynomial.sumIDeriv_derivative`: `Polynomial.sumIDeriv` commutes with `Polynomial.derivative`
* `Polynomial.sumIDeriv_eq_self_add`: `sumIDeriv p = p + derivative (sumIDeriv p)`
* `Polynomial.exists_iterate_derivative_eq_factorial_smul`: the `k`-th iterated derivative of a
  polynomial has a common factor `k!`
* `Polynomial.aeval_iterate_derivative_of_lt`, `Polynomial.aeval_iterate_derivative_self`,
  `Polynomial.aeval_iterate_derivative_of_ge`: applying `Polynomial.aeval` to iterated derivatives
* `Polynomial.aeval_sumIDeriv`, `Polynomial.aeval_sumIDeriv_of_pos`: applying `Polynomial.aeval` to
  `Polynomial.sumIDeriv`

-/

@[expose] public section

open Finset
open scoped Nat

namespace Polynomial

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S]

/--
Sum of iterated derivatives of a polynomial, as a linear map

This definition does not allow different weights for the derivatives. It is likely that it could be
extended to allow them, but this was not needed for the initial use case (the integration by parts
of the integral $I_i$ in the
[Lindemann-Weierstrass](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstrass_theorem)
theorem).
-/
/-
**Polynomial.sumIDeriv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv : R[X] ->ₗ[R] R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum of iterated derivatives of a polynomial, as a linear map

This definition does not allow different weights for the derivatives. It is like
ly that it could be
extended to allow them, but this was not needed for the initial use case (the in
tegration by parts
of the integral $I_i$ in the
[Lindemann-Weierstrass](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstr
ass_theorem)
theorem).
-/
noncomputable def sumIDeriv : R[X] →ₗ[R] R[X] :=
  Finsupp.lsum ℕ (fun _ ↦ LinearMap.id) ∘ₗ derivativeFinsupp
/-
**Polynomial.sumIDeriv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑ i in range (p.natDegree + 1),
 derivative^[i] p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sumIDeriv_apply (p : R[X]) :
    sumIDeriv p = ∑ i ∈ range (p.natDegree + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)
/-
**Polynomial.sumIDeriv_apply_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_apply_of_lt {p : R[X]} {n : Nat} (hn : p.natDegree < n) : sumIDe
riv p = ∑ i in range n, derivative^[i] p
参数：hn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sumIDeriv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    sumIDeriv p = ∑ i ∈ range n, derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)
/-
**Polynomial.sumIDeriv_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_apply_of_le {p : R[X]} {n : Nat} (hn : p.natDegree <= n) : sumID
eriv p = ∑ i in range (n + 1), derivative^[i] p
参数：hn : p.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sumIDeriv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    sumIDeriv p = ∑ i ∈ range (n + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

@[simp]
/-
**Polynomial.sumIDeriv_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_C (a : R) : sumIDeriv (C a) = C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_apply`：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑
 i in range (p.natDegree + 1), derivative^[i] p
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
-/
theorem sumIDeriv_C (a : R) : sumIDeriv (C a) = C a := by
  rw [sumIDeriv_apply, natDegree_C, zero_add, sum_range_one, Function.iterate_zero_apply]

@[simp]
/-
**Polynomial.sumIDeriv_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_X : sumIDeriv X = X + C 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_apply`：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑
 i in range (p.natDegree + 1), derivative^[i] p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem sumIDeriv_X : sumIDeriv X = X + C 1 := by
  rw [sumIDeriv_apply, natDegree_X, sum_range_succ, sum_range_one, Function.iterate_zero_apply,
    Function.iterate_one, derivative_X, eq_natCast, Nat.cast_one]

@[simp]
/-
**Polynomial.sumIDeriv_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_map (p : R[X]) (f : R ->+* S) : sumIDeriv (p.map f) = (sumIDeriv
 p).map f
参数：p : R[X]；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_apply_of_le`：sumIDeriv_apply_of_le {p : R[X]} {n : 
Nat} (hn : p.natDegree <= n) : sumIDeriv p = ∑ i in range (n + 1), derivative^[i
] p
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.iterate_derivative_map`：iterate_derivative_map [Semiring S] (
p : R[X]) (f : R ->+* S) (k : Nat) : Polynomial.derivative^[k] (p.map f) = (Poly
nomial.derivative^[k] p…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumIDeriv_map (p : R[X]) (f : R →+* S) :
    sumIDeriv (p.map f) = (sumIDeriv p).map f := by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIDeriv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [sumIDeriv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]
/-
**Polynomial.sumIDeriv_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_derivative (p : R[X]) : sumIDeriv (derivative p) = derivative (s
umIDeriv p)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_apply_of_le`：sumIDeriv_apply_of_le {p : R[X]} {n : 
Nat} (hn : p.natDegree <= n) : sumIDeriv p = ∑ i in range (n + 1), derivative^[i
] p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_derivative_le`：natDegree_derivative_le (p : R[X]) :
 p.derivative.natDegree <= p.natDegree - 1
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `Polynomial.sumIDeriv_apply`：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑
 i in range (p.natDegree + 1), derivative^[i] p
· 使用定理 `Polynomial.derivative_sum`：derivative_sum {s : Finset ι} {f : ι -> R[X]}
 : derivative (∑ b in s, f b) = ∑ b in s, derivative (f b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumIDeriv_derivative (p : R[X]) : sumIDeriv (derivative p) = derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self), sumIDeriv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
/-
**Polynomial.sumIDeriv_eq_self_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sumIDeriv_eq_self_add (p : R[X]) : sumIDeriv p = p + derivative (sumIDeriv
 p)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_apply`：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑
 i in range (p.natDegree + 1), derivative^[i] p
· 使用定理 `Polynomial.derivative_sum`：derivative_sum {s : Finset ι} {f : ι -> R[X]}
 : derivative (∑ b in s, f b) = ∑ b in s, derivative (f b)
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.iterate_derivative_eq_zero`：iterate_derivative_eq_zero {p : R
[X]} {x : Nat} (hx : p.natDegree < x) : Polynomial.derivative^[x] p = 0
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumIDeriv_eq_self_add (p : R[X]) : sumIDeriv p = p + derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]
/-
**Polynomial.exists_iterate_derivative_eq_factorial_smul** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：exists_iterate_derivative_eq_factorial_smul (p : R[X]) (k : Nat) : exists 
gp : R[X], gp.natDegree <= p.natDegree - k ∧ derivative^[k] p = k ! • gp
参数：p : R[X]；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `Polynomial.natDegree_sum_le`：natDegree_sum_le (f : ι -> S[X]) : natDegre
e (∑ i in s, f i) <= s.fold max 0 (natDegree ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `Finset.fold_max_le`：fold_max_le : s.fold max b f <= c ↔ b <= c ∧ forall 
x in s, f x <= c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `Polynomial.natDegree_X_pow_le`：natDegree_X_pow_le {R : Type*} [Semiring 
R] (n : Nat) : (X ^ n : R[X]).natDegree <= n
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `Polynomial.natDegree_iterate_derivative`：natDegree_iterate_derivative (p
 : R[X]) (k : Nat) : (derivative^[k] p).natDegree <= p.natDegree - k
· 使用定理 `Polynomial.iterate_derivative_eq_factorial_smul_sum`：iterate_derivative_
eq_factorial_smul_sum (p : R[X]) (k : Nat) : derivative^[k] p = k ! • ∑ x in (de
rivative^[k] p).support, C ((x + k).choos…
-/
theorem exists_iterate_derivative_eq_factorial_smul (p : R[X]) (k : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧ derivative^[k] p = k ! • gp := by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
  exact (natDegree_C_mul_le _ _).trans <| (natDegree_X_pow_le _).trans <|
    (le_natDegree_of_mem_supp _ hi).trans <| natDegree_iterate_derivative _ _

end Semiring

section CommSemiring

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

/-
**Polynomial.aeval_iterate_derivative_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：aeval_iterate_derivative_of_lt (p : R[X]) (q : Nat) (r : A) {p' : A[X]} (h
p : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : Nat} (hk : k < q) : aeval 
r (derivative^[k] p) = 0
参数：p : R[X]；q : Nat；r : A；hp : p.map (algebraMap R A) = (X - C r) ^ q * p'；hk : 
k < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.iterate_derivative_map`：iterate_derivative_map [Semiring S] (
p : R[X]) (f : R ->+* S) (k : Nat) : Polynomial.derivative^[k] (p.map f) = (Poly
nomial.derivative^[k] p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.iterate_derivative_mul`：iterate_derivative_mul {n} (p q : R[X
]) : derivative^[n] (p * q) = ∑ k in range n.succ, (n.choose k • (derivative^[n 
- k] p * derivative^[k]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.iterate_derivative_X_sub_pow`：iterate_derivative_X_sub_pow (n
 k : Nat) (c : R) : derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C 
c) ^ (n - k)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
（共 35 条，此处仅展示前 30 条）
-/
theorem aeval_iterate_derivative_of_lt (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : ℕ} (hk : k < q) :
    aeval r (derivative^[k] p) = 0 := by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _)
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul,
    h, ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul]
/-
**Polynomial.aeval_iterate_derivative_self** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：aeval_iterate_derivative_self (p : R[X]) (q : Nat) (r : A) {p' : A[X]} (hp
 : p.map (algebraMap R A) = (X - C r) ^ q * p') : aeval r (derivative^[q] p) = q
 ! • p'.eval r
参数：p : R[X]；q : Nat；r : A；hp : p.map (algebraMap R A) = (X - C r) ^ q * p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.iterate_derivative_map`：iterate_derivative_map [Semiring S] (
p : R[X]) (f : R ->+* S) (k : Nat) : Polynomial.derivative^[k] (p.map f) = (Poly
nomial.derivative^[k] p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.iterate_derivative_mul`：iterate_derivative_mul {n} (p q : R[X
]) : derivative^[n] (p * q) = ∑ k in range n.succ, (n.choose k • (derivative^[n 
- k] p * derivative^[k]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.iterate_derivative_X_sub_pow`：iterate_derivative_X_sub_pow (n
 k : Nat) (c : R) : derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C 
c) ^ (n - k)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.descFactorial_self`：∀ (n : ℕ), n.descFactorial n = n.factorial
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 46 条，此处仅展示前 30 条）
-/
theorem aeval_iterate_derivative_self (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') :
    aeval r (derivative^[q] p) = q ! • p'.eval r := by
  have h (x) (h : 1 ≤ x) (h' : x ≤ q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ', Nat.choose_zero_right, one_mul, tsub_zero, Nat.descFactorial_self, tsub_self,
    pow_zero, smul_mul_assoc, one_mul, Function.iterate_zero_apply, eval_add, eval_smul]
  convert! zero_add _
  rw [eval_finsetSum]
  apply sum_eq_zero
  intro x hx
  rw [h (x + 1) le_add_self (Nat.add_one_le_iff.mpr (mem_range.mp hx)), pow_one,
    eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    smul_zero, zero_mul]

variable (A)
/-
**Polynomial.aeval_iterate_derivative_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：aeval_iterate_derivative_of_ge (p : R[X]) (q : Nat) {k : Nat} (hk : q <= k
) : exists gp : R[X], gp.natDegree <= p.natDegree - k ∧ forall r : A, aeval r (d
erivative^[k] p) = q ! • aeval r gp
参数：p : R[X]；q : Nat；hk : q <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_iterate_derivative_eq_factorial_smul`：exists_iterate_d
erivative_eq_factorial_smul (p : R[X]) (k : Nat) : exists gp : R[X], gp.natDegre
e <= p.natDegree - k ∧ derivative^[k] p = k …
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Nat.add_descFactorial_eq_ascFactorial`：∀ (n k : ℕ), (n + k).descFactoria
l k = (n + 1).ascFactorial k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem aeval_iterate_derivative_of_ge (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧
      ∀ r : A, aeval r (derivative^[k] p) = q ! • aeval r gp := by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.cast_mul,
    Nat.add_descFactorial_eq_ascFactorial, Nat.factorial_mul_ascFactorial]
/-
**Polynomial.aeval_sumIDeriv_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_sumIDeriv_eq_eval (p : R[X]) (r : A) : aeval r (sumIDeriv p) = eval 
r (sumIDeriv (map (algebraMap R A) p))
参数：p : R[X]；r : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用定理 `Polynomial.sumIDeriv_map`：sumIDeriv_map (p : R[X]) (f : R ->+* S) : sumI
Deriv (p.map f) = (sumIDeriv p).map f
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
-/
theorem aeval_sumIDeriv_eq_eval (p : R[X]) (r : A) :
    aeval r (sumIDeriv p) = eval r (sumIDeriv (map (algebraMap R A) p)) := by
  rw [aeval_def, eval, sumIDeriv_map, eval₂_map, RingHom.id_comp]
/-
**Polynomial.aeval_sumIDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_sumIDeriv (p : R[X]) (q : Nat) : exists gp : R[X], gp.natDegree <= p
.natDegree - q ∧ forall (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) -> aeval
 r (sumIDeriv p) = q ! • aeval r gp
参数：p : R[X]；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Polynomial.aeval_iterate_derivative_of_lt`：aeval_iterate_derivative_of_l
t (p : R[X]) (q : Nat) (r : A) {p' : A[X]} (hp : p.map (algebraMap R A) = (X - C
 r) ^ q * p') {k : Nat} (hk : k…
· 使用定理 `Polynomial.aeval_iterate_derivative_of_ge`：aeval_iterate_derivative_of_g
e (p : R[X]) (q : Nat) {k : Nat} (hk : q <= k) : exists gp : R[X], gp.natDegree 
<= p.natDegree - k ∧ forall r :…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `Polynomial.natDegree_sum_le`：natDegree_sum_le (f : ι -> S[X]) : natDegre
e (∑ i in s, f i) <= s.fold max 0 (natDegree ∘ f)
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `Finset.fold_max_le`：fold_max_le : s.fold max b f <= c ↔ b <= c ∧ forall 
x in s, f x <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.sumIDeriv_apply`：sumIDeriv_apply (p : R[X]) : sumIDeriv p = ∑
 i in range (p.natDegree + 1), derivative^[i] p
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）
-/
theorem aeval_sumIDeriv (p : R[X]) (q : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
        aeval r (sumIDeriv p) = q ! • aeval r gp := by
  have h (k) :
      ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
        ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.zero_le _
      intro r ⟨p', hp⟩
      rw [map_zero, smul_zero, aeval_iterate_derivative_of_lt p q r hp hk]
    | inr hk =>
      obtain ⟨gp, gp_le, h⟩ := aeval_iterate_derivative_of_ge A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r _ => h r⟩
  choose c h using h
  choose c_le hc using h
  refine ⟨(range (p.natDegree + 1)).sum c, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r ⟨p', hp⟩
  rw [sumIDeriv_apply, map_sum]; simp_rw [hc _ r ⟨_, hp⟩, map_sum, smul_sum]
/-
**Polynomial.aeval_sumIDeriv_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_sumIDeriv_of_pos [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : N
at} (hq : 0 < q) (inj_amap : Function.Injective (algebraMap R A)) : exists gp : 
R[X], gp.natDegree <= p.natDegree - q ∧ forall (r : A) {p' : A[X]}, p.map (algeb
raMap R A) = (X - C r) ^ (q - 1) * p' -> aeval r (sumIDeriv p) = (q - 1)! • p'.e
val r + q ! • aeval r gp
参数：p : R[X]；hq : 0 < q；inj_amap : Function.Injective (algebraMap R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Polynomial.aeval_iterate_derivative_of_ge`：aeval_iterate_derivative_of_g
e (p : R[X]) (q : Nat) {k : Nat} (hk : q <= k) : exists gp : R[X], gp.natDegree 
<= p.natDegree - k ∧ forall r :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 75 条，此处仅展示前 30 条）
-/
theorem aeval_sumIDeriv_of_pos [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : ℕ} (hq : 0 < q)
    (inj_amap : Function.Injective (algebraMap R A)) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' →
        aeval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • aeval r gp := by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (eq_zero_of_pow_eq_zero h)
  let c k := if hk : q ≤ k then (aeval_iterate_derivative_of_ge A p q hk).choose else 0
  have c_le (k) : (c k).natDegree ≤ p.natDegree - k := by
    dsimp only [c]
    split_ifs with h
    · exact (aeval_iterate_derivative_of_ge A p q h).choose_spec.1
    · rw [natDegree_zero]; exact Nat.zero_le _
  have hc (k) (hk : q ≤ k) : ∀ (r : A), aeval r (derivative^[k] p) = q ! • aeval r (c k) := by
    simp_rw [c, dif_pos hk]
    exact (aeval_iterate_derivative_of_ge A p q hk).choose_spec.2
  refine ⟨∑ x ∈ Ico q (p.natDegree + 1), c x, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro r p' hp
  have : range (p.natDegree + 1) = range q ∪ Ico q (p.natDegree + 1) := by
    rw [range_eq_Ico, range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    rw [← tsub_le_iff_right]
    calc
      q - 1 ≤ q - 1 + p'.natDegree := le_self_add
      _ = (p.map <| algebraMap R A).natDegree := by
        rw [hp, natDegree_mul, natDegree_pow, natDegree_X_sub_C, mul_one,
          ← Nat.sub_add_comm (Nat.one_le_of_lt hq)]
        · exact pow_ne_zero _ (X_sub_C_ne_zero r)
        · rintro rfl
          rw [mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp
          exact p0 hp
      _ ≤ p.natDegree := natDegree_map_le
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sumIDeriv_apply, map_sum, map_sum, this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union, this, sum_range_succ]
  · congr 2
    · apply sum_eq_zero
      exact fun x hx => aeval_iterate_derivative_of_lt p _ r hp (mem_range.mp hx)
    · rw [← aeval_iterate_derivative_self _ _ _ hp]
    · rw [smul_sum, sum_congr rfl]
      intro k hk
      exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_inter, mem_Ico, mem_Ico] at hx
    exact hx.1.2.not_ge hx.2.1

end CommSemiring

/-
**Polynomial.eval_sumIDeriv_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_sumIDeriv_of_pos [CommRing R] [Nontrivial R] [NoZeroDivisors R] (p : 
R[X]) {q : Nat} (hq : 0 < q) : exists gp : R[X], gp.natDegree <= p.natDegree - q
 ∧ forall (r : R) {p' : R[X]}, p = ((X : R[X]) - C r) ^ (q - 1) * p' -> eval r (
sumIDeriv p) = (q - 1)! • p'.eval r + q ! • eval r gp
参数：p : R[X]；hq : 0 < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `Polynomial.aeval_sumIDeriv_of_pos`：aeval_sumIDeriv_of_pos [Nontrivial A]
 [NoZeroDivisors A] (p : R[X]) {q : Nat} (hq : 0 < q) (inj_amap : Function.Injec
tive (algebraMap R A)) …
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem eval_sumIDeriv_of_pos
    [CommRing R] [Nontrivial R] [NoZeroDivisors R] (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : R) {p' : R[X]},
        p = ((X : R[X]) - C r) ^ (q - 1) * p' →
        eval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • eval r gp := by
  simpa using aeval_sumIDeriv_of_pos R p hq Function.injective_id

end Polynomial

