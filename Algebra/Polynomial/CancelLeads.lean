/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic.ComputeDegree

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancelLeads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancelLeads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/

@[expose] public section


namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type*}

section Ring

variable [Ring R] (p q : R[X])

/-- `cancelLeads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
/-
**Polynomial.cancelLeads** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cancelLeads : R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cancelLeads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.
-/
def cancelLeads : R[X] :=
  C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

variable {p q}

@[simp]
/-
**Polynomial.neg_cancelLeads** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _
/-
**Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm** 是 Math
lib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (comm : p.leadi
ngCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff) (h : p.natDegree <= 
q.natDegree) (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree
参数：comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff；h : 
p.natDegree <= q.natDegree；hq : 0 < q.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.cancelLeads.eq_1`：∀ {R : Type u_1} [inst : Ring R] (p q : Pol
ynomial R),   p.cancelLeads q =     Polynomial.C p.leadingCoeff * Polynomial.X ^
 (p.natDegree - q…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.natDegree_add_le_of_le`：natDegree_add_le_of_le (hp : natDegre
e p <= m) (hq : natDegree q <= n) : natDegree (p + q) <= max m n
· 使用定理 `Polynomial.natDegree_mul_le_of_le`：natDegree_mul_le_of_le (hp : natDegre
e p <= m) (hg : natDegree q <= n) : natDegree (p * q) <= m + n
· 使用定理 `Mathlib.Tactic.ComputeDegree.natDegree_C_le`：natDegree_C_le (a : R) : na
tDegree (C a) <= 0
· 使用引理 `le_rfl`：le_rfl : a <= a
（共 55 条，此处仅展示前 30 条）
-/
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree := by
  by_cases hp : p = 0
  · convert! hq
    simp [hp, cancelLeads]
  rw [cancelLeads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zero, mul_one]
  by_cases h0 :
    C p.leadingCoeff * q + -(C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by simp only [h0, natDegree_zero])).trans_lt hq
  apply lt_of_le_of_ne
  · compute_degree!
    rwa [Nat.sub_add_cancel]
  · contrapose h0
    rw [← leadingCoeff_eq_zero, leadingCoeff, h0, mul_assoc, X_pow_mul, ← tsub_add_cancel_of_le h,
      add_comm _ p.natDegree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_comm p.natDegree, tsub_add_cancel_of_le h, ← leadingCoeff, ← leadingCoeff, comm,
      add_neg_cancel]

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

/-
**Polynomial.dvd_cancelLeads_of_dvd_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q
.cancelLeads r
参数：pq : p ∣ q；pr : p ∣ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
-/
theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))
/-
**Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree <= q.n
atDegree) (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree
参数：h : p.natDegree <= q.natDegree；hq : 0 < q.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm`：n
atDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (comm : p.leadingCoeff
 * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff) (h : p…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree :=
  natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq

end CommRing

end

end Polynomial

