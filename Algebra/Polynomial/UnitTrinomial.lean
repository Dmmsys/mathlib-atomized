/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.Data.Int.Order.Units
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Unit Trinomials

This file defines irreducible trinomials and proves an irreducibility criterion.

## Main definitions

- `Polynomial.IsUnitTrinomial`

## Main results

- `Polynomial.IsUnitTrinomial.irreducible_of_coprime`: An irreducibility criterion for unit
  trinomials.

-/

@[expose] public section

assert_not_exists TopologicalSpace

namespace Polynomial

open scoped Polynomial

open Finset

section Semiring

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

/-- Shorthand for a trinomial -/
/-
**Polynomial.trinomial** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：trinomial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shorthand for a trinomial
-/
noncomputable def trinomial :=
  C u * X ^ k + C v * X ^ m + C w * X ^ n
/-
**Polynomial.trinomial_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * 
X ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n :=
  rfl

variable {k m n u v w}
/-
**Polynomial.trinomial_leading_coeff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) : (trinomial k m n u 
v w).coeff n = w
参数：hkm : k < m；hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trinomial_def`：trinomial_def : trinomial k m n u v w = C u * 
X ^ k + C v * X ^ m + C w * X ^ n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff n = w := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add]
/-
**Polynomial.trinomial_middle_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_middle_coeff (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 
w).coeff m = v
参数：hkm : k < m；hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trinomial_def`：trinomial_def : trinomial k m n u v w = C u * 
X ^ k + C v * X ^ m + C w * X ^ n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff m = v := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_neg hkm.ne', if_pos rfl, if_neg hmn.ne, zero_add, add_zero]
/-
**Polynomial.trinomial_trailing_coeff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) : (trinomial k m n u
 v w).coeff k = u
参数：hkm : k < m；hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trinomial_def`：trinomial_def : trinomial k m n u v w = C u * 
X ^ k + C v * X ^ m + C w * X ^ n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff k = u := by
  rw [trinomial_def, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    if_pos rfl, if_neg hkm.ne, if_neg (hkm.trans hmn).ne, add_zero, add_zero]
/-
**Polynomial.trinomial_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w != 0) : (trinomial
 k m n u v w).natDegree = n
参数：hkm : k < m；hmn : m < n；hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Polynomial.support_trinomial_subset`：support_trinomial_subset (k m n : N
at) (x y z : R) : Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) s
ubseteq {k, m, n}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `Polynomial.trinomial_leading_coeff'`：trinomial_leading_coeff' (hkm : k <
 m) (hmn : m < n) : (trinomial k m n u v w).coeff n = w
-/
theorem trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).natDegree = n := by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
        le_degree_of_ne_zero <| by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact WithBot.coe_le_coe.mpr (hkm.trans hmn).le
  · exact WithBot.coe_le_coe.mpr hmn.le
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.trinomial_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u != 0) : (t
rinomial k m n u v w).natTrailingDegree = k
参数：hkm : k < m；hmn : m < n；hu : u != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some`：natTrailingDe
gree_eq_of_trailingDegree_eq_some {p : R[X]} {n : Nat} (h : trailingDegree p = n
) : natTrailingDegree p = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.le_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, a ≤ f b) 
→ a…
· 使用定理 `Polynomial.support_trinomial_subset`：support_trinomial_subset (k m n : N
at) (x y z : R) : Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) s
ubseteq {k, m, n}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Polynomial.trailingDegree_le_of_ne_zero`：trailingDegree_le_of_ne_zero (h
 : coeff p n != 0) : trailingDegree p <= n
· 使用定理 `Polynomial.trinomial_trailing_coeff'`：trinomial_trailing_coeff' (hkm : k
 < m) (hmn : m < n) : (trinomial k m n u v w).coeff k = u
-/
theorem trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).natTrailingDegree = k := by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
          trailingDegree_le_of_ne_zero <| by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact le_rfl
  · exact WithTop.coe_le_coe.mpr hkm.le
  · exact WithTop.coe_le_coe.mpr (hkm.trans hmn).le
/-
**Polynomial.trinomial_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w != 0) : (trinom
ial k m n u v w).leadingCoeff = w
参数：hkm : k < m；hmn : m < n；hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.trinomial_natDegree`：trinomial_natDegree (hkm : k < m) (hmn :
 m < n) (hw : w != 0) : (trinomial k m n u v w).natDegree = n
· 使用定理 `Polynomial.trinomial_leading_coeff'`：trinomial_leading_coeff' (hkm : k <
 m) (hmn : m < n) : (trinomial k m n u v w).coeff n = w
-/
theorem trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (trinomial k m n u v w).leadingCoeff = w := by
  rw [leadingCoeff, trinomial_natDegree hkm hmn hw, trinomial_leading_coeff' hkm hmn]
/-
**Polynomial.trinomial_trailingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u != 0) : (trino
mial k m n u v w).trailingCoeff = u
参数：hkm : k < m；hmn : m < n；hu : u != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Polynomial.trinomial_natTrailingDegree`：trinomial_natTrailingDegree (hkm
 : k < m) (hmn : m < n) (hu : u != 0) : (trinomial k m n u v w).natTrailingDegre
e = k
· 使用定理 `Polynomial.trinomial_trailing_coeff'`：trinomial_trailing_coeff' (hkm : k
 < m) (hmn : m < n) : (trinomial k m n u v w).coeff k = u
-/
theorem trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (trinomial k m n u v w).trailingCoeff = u := by
  rw [trailingCoeff, trinomial_natTrailingDegree hkm hmn hu, trinomial_trailing_coeff' hkm hmn]
/-
**Polynomial.trinomial_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).Moni
c
参数：hkm : k < m；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.trinomial_leadingCoeff`：trinomial_leadingCoeff (hkm : k < m) 
(hmn : m < n) (hw : w != 0) : (trinomial k m n u v w).leadingCoeff = w
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).Monic := by
  nontriviality R
  exact trinomial_leadingCoeff hkm hmn one_ne_zero
/-
**Polynomial.trinomial_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u != 0) (hw : w != 0) :
 (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u
参数：hkm : k < m；hmn : m < n；hu : u != 0；hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.trinomial_natTrailingDegree`：trinomial_natTrailingDegree (hkm
 : k < m) (hmn : m < n) (hu : u != 0) : (trinomial k m n u v w).natTrailingDegre
e = k
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用定理 `Polynomial.trinomial_natDegree`：trinomial_natDegree (hkm : k < m) (hmn :
 m < n) (hw : w != 0) : (trinomial k m n u v w).natDegree = n
· 使用定理 `Polynomial.trinomial_def`：trinomial_def : trinomial k m n u v w = C u * 
X ^ k + C v * X ^ m + C w * X ^ n
· 使用定理 `Polynomial.reflect_add`：reflect_add (f g : R[X]) (N : Nat) : reflect N (
f + g) = reflect N f + reflect N g
· 使用定理 `Polynomial.reflect_C_mul_X_pow`：reflect_C_mul_X_pow (N n : Nat) {c : R} 
: reflect N (C c * X ^ n) = C c * X ^ revAt N n
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u := by
  rw [mirror, trinomial_natTrailingDegree hkm hmn hu, reverse, trinomial_natDegree hkm hmn hw,
    trinomial_def, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, revAt_le (hkm.trans hmn).le, revAt_le hmn.le, revAt_le le_rfl, add_mul,
    add_mul, mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
    Nat.sub_add_cancel (hkm.trans hmn).le, Nat.sub_self, zero_add, add_comm, add_comm (C u * X ^ n),
    ← add_assoc, ← trinomial_def]
/-
**Polynomial.trinomial_support** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trinomial_support (hkm : k < m) (hmn : m < n) (hu : u != 0) (hv : v != 0) 
(hw : w != 0) : (trinomial k m n u v w).support = {k, m, n}
参数：hkm : k < m；hmn : m < n；hu : u != 0；hv : v != 0；hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.support_trinomial`：support_trinomial {k m n : Nat} (hkm : k <
 m) (hmn : m < n) {x y z : R} (hx : x != 0) (hy : y != 0) (hz : z != 0) : suppor
t (C x * X ^ k + C…
-/
theorem trinomial_support (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (trinomial k m n u v w).support = {k, m, n} :=
  support_trinomial hkm hmn hu hv hw

end Semiring

variable (p q : ℤ[X])

/-- A unit trinomial is a trinomial with unit coefficients. -/
/-
**Polynomial.IsUnitTrinomial** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：IsUnitTrinomial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unit trinomial is a trinomial with unit coefficients.
-/
def IsUnitTrinomial :=
  ∃ (k m n : ℕ) (_ : k < m) (_ : m < n) (u v w : Units ℤ), p = trinomial k m n (u : ℤ) v w

variable {p q}

namespace IsUnitTrinomial

/-
**Polynomial.IsUnitTrinomial.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
UnitTrinomial`。
形式化陈述：not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p
参数：hp : p.IsUnitTrinomial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.trinomial_natDegree`：trinomial_natDegree (hkm : k < m) (hmn :
 m < n) (hw : w != 0) : (trinomial k m n u v w).natDegree = n
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))
/-
**Polynomial.IsUnitTrinomial.card_support_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.IsUnitTrinomial`。
形式化陈述：card_support_eq_three (hp : p.IsUnitTrinomial) : #p.support = 3
参数：hp : p.IsUnitTrinomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.card_support_trinomial`：card_support_trinomial {k m n : Nat} 
(hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0) (hy : y != 0) (hz : z != 0
) : #(support (C x * X …
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_support_eq_three (hp : p.IsUnitTrinomial) : #p.support = 3 := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero
/-
**Polynomial.IsUnitTrinomial.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsUni
tTrinomial`。
形式化陈述：ne_zero (hp : p.IsUnitTrinomial) : p != 0
参数：hp : p.IsUnitTrinomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.IsUnitTrinomial.card_support_eq_three`：card_support_eq_three 
(hp : p.IsUnitTrinomial) : #p.support = 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero (hp : p.IsUnitTrinomial) : p ≠ 0 := by
  rintro rfl
  simpa using hp.card_support_eq_three
/-
**Polynomial.IsUnitTrinomial.coeff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
IsUnitTrinomial`。
形式化陈述：coeff_isUnit (hp : p.IsUnitTrinomial) {k : Nat} (hk : k in p.support) : Is
Unit (p.coeff k)
参数：hp : p.IsUnitTrinomial；hk : k in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.support_trinomial_subset`：support_trinomial_subset (k m n : N
at) (x y z : R) : Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) s
ubseteq {k, m, n}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Polynomial.trinomial_trailing_coeff'`：trinomial_trailing_coeff' (hkm : k
 < m) (hmn : m < n) : (trinomial k m n u v w).coeff k = u
· 使用定理 `Polynomial.trinomial_middle_coeff`：trinomial_middle_coeff (hkm : k < m) 
(hmn : m < n) : (trinomial k m n u v w).coeff m = v
· 使用定理 `Polynomial.trinomial_leading_coeff'`：trinomial_leading_coeff' (hkm : k <
 m) (hmn : m < n) : (trinomial k m n u v w).coeff n = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_isUnit (hp : p.IsUnitTrinomial) {k : ℕ} (hk : k ∈ p.support) :
    IsUnit (p.coeff k) := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial_subset k m n (u : ℤ) v w hk
  rw [mem_insert, mem_insert, mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [trinomial_middle_coeff hkm hmn]⟩
  · refine ⟨w, by rw [trinomial_leading_coeff' hkm hmn]⟩
/-
**Polynomial.IsUnitTrinomial.leadingCoeff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.IsUnitTrinomial`。
形式化陈述：leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff
参数：hp : p.IsUnitTrinomial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsUnitTrinomial.coeff_isUnit`：coeff_isUnit (hp : p.IsUnitTrin
omial) {k : Nat} (hk : k in p.support) : IsUnit (p.coeff k)
· 使用定理 `Polynomial.natDegree_mem_support_of_nonzero`：natDegree_mem_support_of_no
nzero (H : p != 0) : p.natDegree in p.support
· 使用定理 `Polynomial.IsUnitTrinomial.ne_zero`：ne_zero (hp : p.IsUnitTrinomial) : p
 != 0
-/
theorem leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff :=
  hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)
/-
**Polynomial.IsUnitTrinomial.trailingCoeff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.IsUnitTrinomial`。
形式化陈述：trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff
参数：hp : p.IsUnitTrinomial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsUnitTrinomial.coeff_isUnit`：coeff_isUnit (hp : p.IsUnitTrin
omial) {k : Nat} (hk : k in p.support) : IsUnit (p.coeff k)
· 使用定理 `Polynomial.natTrailingDegree_mem_support_of_nonzero`：natTrailingDegree_m
em_support_of_nonzero : p != 0 -> natTrailingDegree p in p.support
· 使用定理 `Polynomial.IsUnitTrinomial.ne_zero`：ne_zero (hp : p.IsUnitTrinomial) : p
 != 0
-/
theorem trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff :=
  hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)

end IsUnitTrinomial

/-
**Polynomial.isUnitTrinomial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnitTrinomial_iff : p.IsUnitTrinomial ↔ #p.support = 3 ∧ forall k in p.s
upport, IsUnit (p.coeff k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsUnitTrinomial.card_support_eq_three`：card_support_eq_three 
(hp : p.IsUnitTrinomial) : #p.support = 3
· 使用定理 `Polynomial.IsUnitTrinomial.coeff_isUnit`：coeff_isUnit (hp : p.IsUnitTrin
omial) {k : Nat} (hk : k in p.support) : IsUnit (p.coeff k)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq_three`：card_support_eq_three : #f.support = 3
 ↔ exists (k m n : Nat) (_ : k < m) (_ : m < n) (x y z : R) (_ : x != 0) (_ : y 
!= 0) (_ : z != 0), f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_trinomial`：support_trinomial {k m n : Nat} (hkm : k <
 m) (hmn : m < n) {x y z : R} (hx : x != 0) (hy : y != 0) (hz : z != 0) : suppor
t (C x * X ^ k + C…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_X_pow_self`：coeff_X_pow_self (n : Nat) : coeff (X ^ n :
 R[X]) n = 1
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isUnitTrinomial_iff :
    p.IsUnitTrinomial ↔ #p.support = 3 ∧ ∀ k ∈ p.support, IsUnit (p.coeff k) := by
  refine ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n}))
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n)))
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz
  rw [if_neg hkm.ne, if_neg (hkm.trans hmn).ne] at hx
  rw [if_neg hkm.ne', if_neg hmn.ne] at hy
  rw [if_neg (hkm.trans hmn).ne', if_neg hmn.ne'] at hz
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz
  exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩
/-
**Polynomial.isUnitTrinomial_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnitTrinomial_iff' : p.IsUnitTrinomial ↔ (p * p.mirror).coeff (((p * p.m
irror).natDegree + (p * p.mirror).natTrailingDegree) / 2) = 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_mul_mirror`：natDegree_mul_mirror : (p * p.mirror).n
atDegree = 2 * p.natDegree
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Polynomial.natTrailingDegree_mul_mirror`：natTrailingDegree_mul_mirror : 
(p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_right`：∀ (n : ℕ) {m : ℕ}, 0 < m → m * n / m = n
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.coeff_mul_mirror`：coeff_mul_mirror : (p * p.mirror).coeff (p.
natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2)
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Polynomial.trinomial_support`：trinomial_support (hkm : k < m) (hmn : m <
 n) (hu : u != 0) (hv : v != 0) (hw : w != 0) : (trinomial k m n u v w).support 
= {k, m, n}
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Polynomial.trinomial_leading_coeff'`：trinomial_leading_coeff' (hkm : k <
 m) (hmn : m < n) : (trinomial k m n u v w).coeff n = w
· 使用定理 `Polynomial.trinomial_middle_coeff`：trinomial_middle_coeff (hkm : k < m) 
(hmn : m < n) : (trinomial k m n u v w).coeff m = v
· 使用定理 `Polynomial.trinomial_trailing_coeff'`：trinomial_trailing_coeff' (hkm : k
 < m) (hmn : m < n) : (trinomial k m n u v w).coeff k = u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 49 条，此处仅展示前 30 条）
-/
theorem isUnitTrinomial_iff' :
    p.IsUnitTrinomial ↔
      (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailingDegree) / 2) =
        3 := by
  rw [natDegree_mul_mirror, natTrailingDegree_mul_mirror, ← mul_add,
    Nat.mul_div_right _ zero_lt_two, coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def, trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero,
      sum_insert (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton, trinomial_leading_coeff' hkm hmn,
      trinomial_middle_coeff hkm hmn, trinomial_trailing_coeff' hkm hmn]
    simp_rw [← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one]
    decide
  · have key : ∀ k ∈ p.support, p.coeff k ^ 2 = 1 := fun k hk =>
      Int.sq_eq_one_of_sq_le_three
        ((single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk)
    refine isUnitTrinomial_iff.mpr ⟨?_, fun k hk => .of_pow_eq_one (key k hk) two_ne_zero⟩
    rw [sum_def, sum_congr rfl key, sum_const, Nat.smul_one_eq_cast] at hp
    exact Nat.cast_injective hp
/-
**Polynomial.isUnitTrinomial_iff''** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) : p.IsUnitTrinomia
l ↔ q.IsUnitTrinomial
参数：h : p * p.mirror = q * q.mirror。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isUnitTrinomial_iff'`：isUnitTrinomial_iff' : p.IsUnitTrinomia
l ↔ (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailing
Degree) / 2) = 3
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) :
    p.IsUnitTrinomial ↔ q.IsUnitTrinomial := by
  rw [isUnitTrinomial_iff', isUnitTrinomial_iff', h]

namespace IsUnitTrinomial

/-
**Polynomial.IsUnitTrinomial.irreducible_aux1** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsUnitTrinomial`。
形式化陈述：irreducible_aux1 {k m n : Nat} (hkm : k < m) (hmn : m < n) (u v w : Units 
Int) (hp : p = trinomial k m n (u : Int) v w) : C (v : Int) * (C (u : Int) * X ^
 (m + n) + C (w : Int) * X ^ (n - m + k + n)) = ⟨.ofCoeff (p * p.mirror).toFinsu
pp.coeff.filter (· in Set.Ioo (k + n) (n + n))⟩
参数：hkm : k < m；hmn : m < n；u v w : Units Int；hp : p = trinomial k m n (u : Int) 
v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `tsub_lt_tsub_iff_left_of_le`：tsub_lt_tsub_iff_left_of_le (h : b <= a) : 
a - b < a - c ↔ c < b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.trinomial_mirror`：trinomial_mirror (hkm : k < m) (hmn : m < n
) (hu : u != 0) (hw : w != 0) : (trinomial k m n u v w).mirror = trinomial k (n 
- m + k) n w v u
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Finsupp.filter.congr_simp`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (p p_1 : α → Prop),   p = p_1 →     ∀ {inst_1 : DecidablePred p} [inst_2 : De
cidablePred p_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `Finsupp.filter_add`：filter_add [DecidablePred p] {v v' : α ->₀ M} : (v +
 v').filter p = v.filter p + v'.filter p
· 使用定理 `Finsupp.filter_single_of_neg`：filter_single_of_neg {a : α} {b : M} (h : 
¬p a) : (single a b).filter p = 0
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 57 条，此处仅展示前 30 条）
-/
theorem irreducible_aux1 {k m n : ℕ} (hkm : k < m) (hmn : m < n) (u v w : Units ℤ)
    (hp : p = trinomial k m n (u : ℤ) v w) :
    C (v : ℤ) * (C (u : ℤ) * X ^ (m + n) + C (w : ℤ) * X ^ (n - m + k + n)) =
      ⟨.ofCoeff <| (p * p.mirror).toFinsupp.coeff.filter (· ∈ Set.Ioo (k + n) (n + n))⟩ := by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp, trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidAlgebra.coeff_add, Finsupp.filter_add,
    AddMonoidAlgebra.coeff_single]
  rw [Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]
  · simp only [add_zero, zero_add, AddMonoidAlgebra.ofCoeff_add, ofFinsupp_add,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single, C_mul_monomial, C_mul_monomial,
      mul_comm (v : ℤ) w, add_comm (n - m + k) n]
  · simp
  · refine ⟨?_, by gcongr⟩
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt]
  · exact fun h => h.1.ne (add_comm k n)
  · constructor <;> gcongr
  · rw [← add_assoc, add_tsub_cancel_of_le hmn.le, add_comm]
    exact fun h => h.1.ne rfl
  · grind
  · exact fun h => h.1.ne rfl
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) key
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn)
/-
**Polynomial.IsUnitTrinomial.irreducible_aux2** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsUnitTrinomial`。
形式化陈述：irreducible_aux2 {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < 
m') (hmn' : m' < n) (u v w : Units Int) (hp : p = trinomial k m n (u : Int) v w)
 (hq : q = trinomial k m' n (u : Int) v w) (h : p * p.mirror = q * q.mirror) : q
 = p ∨ q = p.mirror
参数：hkm : k < m；hmn : m < n；hkm' : k < m'；hmn' : m' < n；u v w : Units Int；hp : p 
= trinomial k m n (u : Int) v w；hq : q = trinomial k m' n (u : Int) v w；h : p * 
p.mirror = q * q.mirror。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.IsUnitTrinomial.irreducible_aux1`：irreducible_aux1 {k m n : N
at} (hkm : k < m) (hmn : m < n) (u v w : Units Int) (hp : p = trinomial k m n (u
 : Int) v w) : C (v : Int) * (C (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.binomial_eq_binomial`：binomial_eq_binomial {k l m n : Nat} {u
 v : R} (hu : u != 0) (hv : v != 0) : C u * X ^ k + C v * X ^ l = C u * X ^ m + 
C v * X ^ n ↔ k = m ∧…
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Polynomial.mirror_eq_iff`：mirror_eq_iff : p.mirror = q ↔ p = q.mirror
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.trinomial_mirror`：trinomial_mirror (hkm : k < m) (hmn : m < n
) (hu : u != 0) (hw : w != 0) : (trinomial k m n u v w).mirror = trinomial k (n 
- m + k) n w v u
-/
theorem irreducible_aux2 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w) (hq : q = trinomial k m' n (u : ℤ) v w)
    (h : p * p.mirror = q * q.mirror) : q = p ∨ q = p.mirror := by
  let f (p : ℤ[X]) : ℤ[X] := ⟨.ofCoeff <| .filter (· ∈ Set.Ioo (k + n) (n + n)) p.toFinsupp.coeff⟩
  replace h := congr_arg f h
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj] at h
  rw [binomial_eq_binomial u.ne_zero w.ne_zero] at h
  simp only [add_left_inj, Units.val_inj] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩)
  · exact Or.inl (hq.trans hp.symm)
  · refine Or.inr ?_
    rw [← trinomial_mirror hkm' hmn' u.ne_zero u.ne_zero, eq_comm, mirror_eq_iff] at hp
    exact hq.trans hp
  · grind
/-
**Polynomial.IsUnitTrinomial.irreducible_aux3** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsUnitTrinomial`。
形式化陈述：irreducible_aux3 {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < 
m') (hmn' : m' < n) (u v w x z : Units Int) (hp : p = trinomial k m n (u : Int) 
v w) (hq : q = trinomial k m' n (x : Int) v z) (h : p * p.mirror = q * q.mirror)
 : q = p ∨ q = p.mirror
参数：hkm : k < m；hmn : m < n；hkm' : k < m'；hmn' : m' < n；u v w x z : Units Int；hp 
: p = trinomial k m n (u : Int) v w；hq : q = trinomial k m' n (x : Int) v z；h : 
p * p.mirror = q * q.mirror。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.isUnit_add_isUnit_eq_isUnit_add_isUnit`：isUnit_add_isUnit_eq_isUnit_
add_isUnit {a b c d : Int} (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (hd :
 IsUnit d) : a + b = c + d ↔ a =…
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.trinomial_trailingCoeff`：trinomial_trailingCoeff (hkm : k < m
) (hmn : m < n) (hu : u != 0) : (trinomial k m n u v w).trailingCoeff = u
· 使用定理 `Polynomial.trinomial_leadingCoeff`：trinomial_leadingCoeff (hkm : k < m) 
(hmn : m < n) (hw : w != 0) : (trinomial k m n u v w).leadingCoeff = w
· 使用定理 `Polynomial.mirror_leadingCoeff`：mirror_leadingCoeff : p.mirror.leadingCo
eff = p.trailingCoeff
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `add_sq'`：add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.units_sq`：units_sq (u : Intˣ) : u ^ 2 = 1
（共 61 条，此处仅展示前 30 条）
-/
theorem irreducible_aux3 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w x z : Units ℤ) (hp : p = trinomial k m n (u : ℤ) v w)
    (hq : q = trinomial k m' n (x : ℤ) v z) (h : p * p.mirror = q * q.mirror) :
    q = p ∨ q = p.mirror := by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_mul, mirror_leadingCoeff, mirror_leadingCoeff, hp, hq,
    trinomial_leadingCoeff hkm hmn w.ne_zero, trinomial_leadingCoeff hkm' hmn' z.ne_zero,
    trinomial_trailingCoeff hkm hmn u.ne_zero, trinomial_trailingCoeff hkm' hmn' x.ne_zero]
    at hmul
  have hadd := congr_arg (eval 1) h
  rw [eval_mul, eval_mul, mirror_eval_one, mirror_eval_one, ← sq, ← sq, hp, hq] at hadd
  simp only [eval_add, eval_C_mul, eval_X_pow, one_pow, mul_one, trinomial_def] at hadd
  rw [add_assoc, add_assoc, add_comm (u : ℤ), add_comm (x : ℤ), add_assoc, add_assoc] at hadd
  simp only [add_sq', add_assoc, add_right_inj, ← Units.val_pow_eq_pow_val, Int.units_sq] at hadd
  rw [mul_assoc, hmul, ← mul_assoc, add_right_inj,
    mul_right_inj' (show 2 * (v : ℤ) ≠ 0 from mul_ne_zero two_ne_zero v.ne_zero)] at hadd
  replace hadd :=
    (Int.isUnit_add_isUnit_eq_isUnit_add_isUnit w.isUnit u.isUnit z.isUnit x.isUnit).mp hadd
  simp only [Units.val_inj] at hadd
  rcases hadd with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h
  · rw [← mirror_inj, trinomial_mirror hkm' hmn' w.ne_zero u.ne_zero] at hq
    rw [mul_comm q, ← q.mirror_mirror, q.mirror.mirror_mirror] at h
    rw [← mirror_inj, or_comm, ← mirror_eq_iff]
    exact
      irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
        (lt_tsub_iff_right.mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h
/-
**Polynomial.IsUnitTrinomial.irreducible_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.IsUnitTrinomial`。
形式化陈述：irreducible_of_coprime (hp : p.IsUnitTrinomial) (h : IsRelPrime p p.mirror
) : Irreducible p
参数：hp : p.IsUnitTrinomial；h : IsRelPrime p p.mirror。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.irreducible_of_mirror`：irreducible_of_mirror (h1 : ¬IsUnit f)
 (h2 : forall k, f * f.mirror = k * k.mirror -> k = f ∨ k = -f ∨ k = f.mirror ∨ 
k = -f.mirror) (h3 : I…
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Polynomial.IsUnitTrinomial.not_isUnit`：not_isUnit (hp : p.IsUnitTrinomia
l) : ¬IsUnit p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isUnitTrinomial_iff''`：isUnitTrinomial_iff'' (h : p * p.mirro
r = q * q.mirror) : p.IsUnitTrinomial ↔ q.IsUnitTrinomial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.trinomial_natTrailingDegree`：trinomial_natTrailingDegree (hkm
 : k < m) (hmn : m < n) (hu : u != 0) : (trinomial k m n u v w).natTrailingDegre
e = k
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `Polynomial.natTrailingDegree_mul_mirror`：natTrailingDegree_mul_mirror : 
(p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree
· 使用定理 `Polynomial.trinomial_natDegree`：trinomial_natDegree (hkm : k < m) (hmn :
 m < n) (hw : w != 0) : (trinomial k m n u v w).natDegree = n
· 使用定理 `Polynomial.natDegree_mul_mirror`：natDegree_mul_mirror : (p * p.mirror).n
atDegree = 2 * p.natDegree
· 使用引理 `eq_or_eq_neg_of_sq_eq_sq`：eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b
 ^ 2 -> a = b ∨ a = -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.isUnit_sq`：isUnit_sq {a : Int} (ha : IsUnit a) : a ^ 2 = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Polynomial.IsUnitTrinomial.irreducible_aux3`：irreducible_aux3 {k m m' n 
: Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n) (u v w x z : 
Units Int) (hp : p = trinomial k …
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Polynomial.trinomial_def`：trinomial_def : trinomial k m n u v w = C u * 
X ^ k + C v * X ^ m + C w * X ^ n
· 使用定理 `Polynomial.mirror_neg`：mirror_neg : (-p).mirror = -p.mirror
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
-/
theorem irreducible_of_coprime (hp : p.IsUnitTrinomial)
    (h : IsRelPrime p p.mirror) : Irreducible p := by
  refine irreducible_of_mirror hp.not_isUnit (fun q hpq => ?_) h
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ←
      trinomial_natTrailingDegree hkm hmn u.ne_zero, ← hp, ← natTrailingDegree_mul_mirror, hpq,
      natTrailingDegree_mul_mirror, hq, trinomial_natTrailingDegree hkm' hmn' x.ne_zero]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ← trinomial_natDegree hkm hmn w.ne_zero, ←
      hp, ← natDegree_mul_mirror, hpq, natDegree_mul_mirror, hq,
      trinomial_natDegree hkm' hmn' z.ne_zero]
  subst hk
  subst hn
  rcases eq_or_eq_neg_of_sq_eq_sq (y : ℤ) (v : ℤ)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · rw [h1] at hq
    rcases irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rw [h1] at hq
    rw [trinomial_def] at hp
    rw [← neg_inj, neg_add, neg_add, ← neg_mul, ← neg_mul, ← neg_mul, ← C_neg, ← C_neg, ← C_neg]
      at hp
    rw [← neg_mul_neg, ← mirror_neg] at hpq
    rcases irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))

/-- A unit trinomial is irreducible if it is coprime with its mirror -/
/-
**Polynomial.IsUnitTrinomial.irreducible_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.IsUnitTrinomial`。
形式化陈述：irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirro
r) : Irreducible p
参数：hp : p.IsUnitTrinomial；h : IsCoprime p p.mirror。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsUnitTrinomial.irreducible_of_coprime`：irreducible_of_coprim
e (hp : p.IsUnitTrinomial) (h : IsRelPrime p p.mirror) : Irreducible p
· 使用定理 `IsCoprime.isUnit_of_dvd'`：IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCo
prime a b) (ha : x ∣ a) (hb : x ∣ b) : IsUnit x

--- 原说明 ---
A unit trinomial is irreducible if it is coprime with its mirror
-/
theorem irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror) :
    Irreducible p :=
  irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

end IsUnitTrinomial

end Polynomial

