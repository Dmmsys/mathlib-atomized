/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Nat.WithBot

/-!
# Results on polynomials of specific small degrees
-/

public section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-
**Polynomial.eq_X_add_C_of_degree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_X_add_C_of_degree_le_one (h : degree p <= 1) : p = C (p.coeff 1) * X + 
C (p.coeff 0)
参数：h : degree p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.one_lt_ofNat`：one_lt_ofNat : 1 < (ofNat(n) : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
-/
theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = C (p.coeff 1) * X + C (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp) fun m => by
        have : degree p < m.succ.succ := lt_of_le_of_lt h Nat.one_lt_ofNat
        simp [coeff_eq_zero_of_degree_lt this]
/-
**Polynomial.eq_X_add_C_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_X_add_C_of_degree_eq_one (h : degree p = 1) : p = C p.leadingCoeff * X 
+ C (p.coeff 0)
参数：h : degree p = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eq_X_add_C_of_degree_le_one`：eq_X_add_C_of_degree_le_one (h :
 degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = C p.leadingCoeff * X + C (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])
/-
**Polynomial.eq_X_add_C_of_natDegree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：eq_X_add_C_of_natDegree_le_one (h : natDegree p <= 1) : p = C (p.coeff 1) 
* X + C (p.coeff 0)
参数：h : natDegree p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_X_add_C_of_degree_le_one`：eq_X_add_C_of_degree_le_one (h :
 degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
-/
theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one <| degree_le_of_natDegree_le h
/-
**Polynomial.Monic.eq_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R},   p.Monic → p.natDe
gree = 1 → p = Polynomial.X + Polynomial.C (p.coeff 0)
参数：p.coeff 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `Polynomial.eq_X_add_C_of_natDegree_le_one`：eq_X_add_C_of_natDegree_le_on
e (h : natDegree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = X + C (p.coeff 0) := by
  rw [← one_mul X, ← C_1, ← hm.coeff_natDegree, hnd, ← eq_X_add_C_of_natDegree_le_one hnd.le]
/-
**Polynomial.exists_eq_X_add_C_of_natDegree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p <= 1) : exists a b,
 p = C a * X + C b
参数：h : natDegree p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_X_add_C_of_natDegree_le_one`：eq_X_add_C_of_natDegree_le_on
e (h : natDegree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
-/
theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = C a * X + C b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/-
**Polynomial.zero_le_degree_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_le_degree_iff : 0 <= degree p ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.WithBot.lt_zero_iff`：lt_zero_iff {n : WithBot Nat} : n < 0 ↔ n = ⊥
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_le_degree_iff : 0 ≤ degree p ↔ p ≠ 0 := by
  rw [← not_lt, Nat.WithBot.lt_zero_iff, degree_eq_bot]
/-
**Polynomial.ne_zero_of_coe_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_coe_le_degree (hdeg : ↑n <= p.degree) : p != 0
参数：hdeg : ↑n <= p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.zero_le_degree_iff`：zero_le_degree_iff : 0 <= degree p ↔ p !=
 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 :=
  zero_le_degree_iff.mp <| (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg
/-
**Polynomial.le_natDegree_of_coe_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：le_natDegree_of_coe_le_degree (hdeg : ↑n <= p.degree) : n <= p.natDegree
参数：hdeg : ↑n <= p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.ne_zero_of_coe_le_degree`：ne_zero_of_coe_le_degree (hdeg : ↑n
 <= p.degree) : p != 0
-/
theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  WithBot.coe_le_coe.mp <| by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg
/-
**Polynomial.degree_linear_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_linear_le : degree (C a * X + C b) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_add_le_of_degree_le`：degree_add_le_of_degree_le {p q :
 R[X]} {n : Nat} (hp : degree p <= n) (hq : degree q <= n) : degree (p + q) <= n
· 使用定理 `Polynomial.degree_C_mul_X_le`：degree_C_mul_X_le (a : R) : degree (C a * 
X) <= 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Nat.WithBot.coe_nonneg`：coe_nonneg {n : Nat} : 0 <= (n : WithBot Nat)
-/
theorem degree_linear_le : degree (C a * X + C b) ≤ 1 :=
  degree_add_le_of_degree_le (degree_C_mul_X_le _) <| le_trans degree_C_le Nat.WithBot.coe_nonneg
/-
**Polynomial.degree_linear_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_linear_lt : degree (C a * X + C b) < 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.degree_linear_le`：degree_linear_le : degree (C a * X + C b) <
= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
theorem degree_linear_lt : degree (C a * X + C b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two

@[simp]
/-
**Polynomial.degree_linear** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_linear (ha : a != 0) : degree (C a * X + C b) = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用定理 `Polynomial.degree_C_lt_degree_C_mul_X`：degree_C_lt_degree_C_mul_X (ha : 
a != 0) : degree (C b) < degree (C a * X)
· 使用定理 `Polynomial.degree_C_mul_X`：degree_C_mul_X (ha : a != 0) : degree (C a * 
X) = 1
-/
theorem degree_linear (ha : a ≠ 0) : degree (C a * X + C b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]
/-
**Polynomial.natDegree_linear_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_linear_le : natDegree (C a * X + C b) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用定理 `Polynomial.degree_linear_le`：degree_linear_le : degree (C a * X + C b) <
= 1
-/
theorem natDegree_linear_le : natDegree (C a * X + C b) ≤ 1 :=
  natDegree_le_of_degree_le degree_linear_le
/-
**Polynomial.natDegree_linear** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_linear (ha : a != 0) : natDegree (C a * X + C b) = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_C_mul_X`：natDegree_C_mul_X (a : R) (ha : a != 0) : 
natDegree (C a * X) = 1
-/
theorem natDegree_linear (ha : a ≠ 0) : natDegree (C a * X + C b) = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X a ha]

@[simp]
/-
**Polynomial.leadingCoeff_linear** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_linear (ha : a != 0) : leadingCoeff (C a * X + C b) = a
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Polynomial.degree_C_lt_degree_C_mul_X`：degree_C_lt_degree_C_mul_X (ha : 
a != 0) : degree (C b) < degree (C a * X)
· 使用定理 `Polynomial.leadingCoeff_C_mul_X`：leadingCoeff_C_mul_X (a : R) : leadingC
oeff (C a * X) = a
-/
theorem leadingCoeff_linear (ha : a ≠ 0) : leadingCoeff (C a * X + C b) = a := by
  rw [add_comm, leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha),
    leadingCoeff_C_mul_X]
/-
**Polynomial.degree_quadratic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.degree_add_le_of_degree_le`：degree_add_le_of_degree_le {p q :
 R[X]} {n : Nat} (hp : degree p <= n) (hq : degree q <= n) : degree (p + q) <= n
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_linear_le`：degree_linear_le : degree (C a * X + C b) <
= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) ≤ 2 := by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)
/-
**Polynomial.degree_quadratic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.degree_quadratic_le`：degree_quadratic_le : degree (C a * X ^ 
2 + C b * X + C c) <= 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
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
theorem degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3 :=
  degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2
/-
**Polynomial.degree_linear_lt_degree_C_mul_X_sq** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：degree_linear_lt_degree_C_mul_X_sq (ha : a != 0) : degree (C b * X + C c) 
< degree (C a * X ^ 2)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
· 使用定理 `Polynomial.degree_linear_lt`：degree_linear_lt : degree (C a * X + C b) <
 2
-/
theorem degree_linear_lt_degree_C_mul_X_sq (ha : a ≠ 0) :
    degree (C b * X + C c) < degree (C a * X ^ 2) := by
  simpa only [degree_C_mul_X_pow 2 ha] using! degree_linear_lt

@[simp]
/-
**Polynomial.degree_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_quadratic (ha : a != 0) : degree (C a * X ^ 2 + C b * X + C c) = 2
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用定理 `Polynomial.degree_linear_lt_degree_C_mul_X_sq`：degree_linear_lt_degree_C
_mul_X_sq (ha : a != 0) : degree (C b * X + C c) < degree (C a * X ^ 2)
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
-/
theorem degree_quadratic (ha : a ≠ 0) : degree (C a * X ^ 2 + C b * X + C c) = 2 := by
  rw [add_assoc, degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    degree_C_mul_X_pow 2 ha]
  rfl
/-
**Polynomial.natDegree_quadratic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用定理 `Polynomial.degree_quadratic_le`：degree_quadratic_le : degree (C a * X ^ 
2 + C b * X + C c) <= 2
-/
theorem natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) ≤ 2 :=
  natDegree_le_of_degree_le degree_quadratic_le
/-
**Polynomial.natDegree_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_quadratic (ha : a != 0) : natDegree (C a * X ^ 2 + C b * X + C c
) = 2
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_quadratic`：degree_quadratic (ha : a != 0) : degree (C 
a * X ^ 2 + C b * X + C c) = 2
-/
theorem natDegree_quadratic (ha : a ≠ 0) : natDegree (C a * X ^ 2 + C b * X + C c) = 2 :=
  natDegree_eq_of_degree_eq_some <| degree_quadratic ha

@[simp]
/-
**Polynomial.leadingCoeff_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_quadratic (ha : a != 0) : leadingCoeff (C a * X ^ 2 + C b * X
 + C c) = a
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Polynomial.degree_linear_lt_degree_C_mul_X_sq`：degree_linear_lt_degree_C
_mul_X_sq (ha : a != 0) : degree (C b * X + C c) < degree (C a * X ^ 2)
· 使用定理 `Polynomial.leadingCoeff_C_mul_X_pow`：leadingCoeff_C_mul_X_pow (a : R) (n
 : Nat) : leadingCoeff (C a * X ^ n) = a
-/
theorem leadingCoeff_quadratic (ha : a ≠ 0) : leadingCoeff (C a * X ^ 2 + C b * X + C c) = a := by
  rw [add_assoc, add_comm, leadingCoeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    leadingCoeff_C_mul_X_pow]
/-
**Polynomial.degree_cubic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.degree_add_le_of_degree_le`：degree_add_le_of_degree_le {p q :
 R[X]} {n : Nat} (hp : degree p <= n) (hq : degree q <= n) : degree (p + q) <= n
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_quadratic_le`：degree_quadratic_le : degree (C a * X ^ 
2 + C b * X + C c) <= 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 := by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)
/-
**Polynomial.degree_cubic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.degree_cubic_le`：degree_cubic_le : degree (C a * X ^ 3 + C b 
* X ^ 2 + C c * X + C d) <= 3
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
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
theorem degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4 :=
  degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3
/-
**Polynomial.degree_quadratic_lt_degree_C_mul_X_cb** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：degree_quadratic_lt_degree_C_mul_X_cb (ha : a != 0) : degree (C b * X ^ 2 
+ C c * X + C d) < degree (C a * X ^ 3)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
· 使用定理 `Polynomial.degree_quadratic_lt`：degree_quadratic_lt : degree (C a * X ^ 
2 + C b * X + C c) < 3
-/
theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
    degree (C b * X ^ 2 + C c * X + C d) < degree (C a * X ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using! degree_quadratic_lt

@[simp]
/-
**Polynomial.degree_cubic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cubic (ha : a != 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X +
 C d) = 3
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用定理 `Polynomial.degree_quadratic_lt_degree_C_mul_X_cb`：degree_quadratic_lt_de
gree_C_mul_X_cb (ha : a != 0) : degree (C b * X ^ 2 + C c * X + C d) < degree (C
 a * X ^ 3)
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
-/
theorem degree_cubic (ha : a ≠ 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2),
    degree_add_eq_left_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    degree_C_mul_X_pow 3 ha]
  rfl
/-
**Polynomial.natDegree_cubic_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
 <= 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用定理 `Polynomial.degree_cubic_le`：degree_cubic_le : degree (C a * X ^ 3 + C b 
* X ^ 2 + C c * X + C d) <= 3
-/
theorem natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
  natDegree_le_of_degree_le degree_cubic_le
/-
**Polynomial.natDegree_cubic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cubic (ha : a != 0) : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c
 * X + C d) = 3
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_cubic`：degree_cubic (ha : a != 0) : degree (C a * X ^ 
3 + C b * X ^ 2 + C c * X + C d) = 3
-/
theorem natDegree_cubic (ha : a ≠ 0) : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
  natDegree_eq_of_degree_eq_some <| degree_cubic ha

@[simp]
/-
**Polynomial.leadingCoeff_cubic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_cubic (ha : a != 0) : leadingCoeff (C a * X ^ 3 + C b * X ^ 2
 + C c * X + C d) = a
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Polynomial.degree_quadratic_lt_degree_C_mul_X_cb`：degree_quadratic_lt_de
gree_C_mul_X_cb (ha : a != 0) : degree (C b * X ^ 2 + C c * X + C d) < degree (C
 a * X ^ 3)
· 使用定理 `Polynomial.leadingCoeff_C_mul_X_pow`：leadingCoeff_C_mul_X_pow (a : R) (n
 : Nat) : leadingCoeff (C a * X ^ n) = a
-/
theorem leadingCoeff_cubic (ha : a ≠ 0) :
    leadingCoeff (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = a := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2), add_comm,
    leadingCoeff_add_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    leadingCoeff_C_mul_X_pow]

end Semiring

end Polynomial

