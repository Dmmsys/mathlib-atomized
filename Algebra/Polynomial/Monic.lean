/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Regular.SMul

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`Monic.mul`, `Monic.map`, `Monic.pow`.
-/

@[expose] public section


noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-
**Polynomial.monic_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_iff_zero_eq_one`：subsingleton_iff_zero_eq_one : (0 : M₀) = 
1 ↔ Subsingleton M₀
-/
theorem monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R :=
  subsingleton_iff_zero_eq_one
/-
**Polynomial.not_monic_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.monic_zero_iff_subsingleton`：monic_zero_iff_subsingleton : Mo
nic (0 : R[X]) ↔ Subsingleton R
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `subsingleton_iff_zero_eq_one`：subsingleton_iff_zero_eq_one : (0 : M₀) = 
1 ↔ Subsingleton M₀
-/
theorem not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) ≠ 1 :=
  (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not
/-
**Polynomial.monic_zero_iff_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：monic_zero_iff_subsingleton' : Monic (0 : R[X]) ↔ (forall f g : R[X], f = 
g) ∧ forall a b : R, a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.monic_zero_iff_subsingleton`：monic_zero_iff_subsingleton : Mo
nic (0 : R[X]) ↔ Subsingleton R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem monic_zero_iff_subsingleton' :
    Monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ ∀ a b : R, a = b :=
  Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩
/-
**Polynomial.Monic.as_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R},   p.Monic → p = Pol
ynomial.X ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, Polynomial.C (p.coeff 
i) * Polynomial.X ^ i
参数：p.coeff i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow`：as_sum_range_C_mul_X_pow (p : R[X])
 : p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i
· 使用定理 `Finset.sum_range_succ_comm`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f
 : ℕ → M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = f n + ∑ x ∈ Finset.range 
n, f x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Monic.as_sum (hp : p.Monic) :
    p = X ^ p.natDegree + ∑ i ∈ range p.natDegree, C (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp
/-
**Polynomial.Monic.map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p : Polynomial R} [inst_1
 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.map f p).Monic
参数：f : R →+* S；Polynomial.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff`：leadingCoeff_map_
eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp : IsUnit p.leadingCo
eff) : (p.map f).leadingCoeff = f p.leading…
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem Monic.map [Semiring S] (f : R →+* S) (hp : Monic p) : Monic (p.map f) :=
  subsingleton_or_nontrivial S |>.elim (·.elim ..) fun _ ↦
    f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ <| isUnit_one
/-
**Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 
1) : Monic (C b * p)
参数：hp : b * p.leadingCoeff = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Monic (C b * p) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]
/-
**Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 
1) : Monic (p * C b)
参数：hp : p.leadingCoeff * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Monic (p * C b) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]
/-
**Polynomial.monic_X_pow_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_pow_add {n : Nat} (H : degree p < n) : Monic (X ^ n + p)
参数：H : degree p < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_of_degree_le`：monic_of_degree_le (n : Nat) (pn : p.degr
ee <= n) (p1 : p.coeff n = 1) : Monic p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem monic_X_pow_add {n : ℕ} (H : degree p < n) : Monic (X ^ n + p) :=
  monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

variable (a) in
/-
**Polynomial.monic_X_pow_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_pow_add_C {n : Nat} (h : n != 0) : (X ^ n + C a).Monic
参数：h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X_pow_add`：monic_X_pow_add {n : Nat} (H : degree p < n)
 : Monic (X ^ n + p)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem monic_X_pow_add_C {n : ℕ} (h : n ≠ 0) : (X ^ n + C a).Monic :=
  monic_X_pow_add <| (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))
/-
**Polynomial.monic_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_add_C (x : R) : Monic (X + C x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X_pow_add_C`：monic_X_pow_add_C {n : Nat} (h : n != 0) :
 (X ^ n + C a).Monic
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem monic_X_add_C (x : R) : Monic (X + C x) :=
  pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero
/-
**Polynomial.Monic.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, p.Monic → q.Monic
 → (p * q).Monic
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `subsingleton_of_zero_eq_one`：∀ {M₀ : Type u_1} [inst : MulZeroOneClass M
₀], 0 = 1 → Subsingleton M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def, leadingCoeff_mul' this, Monic.def.1 hp, Monic.def.1 hq, one_mul]
/-
**Polynomial.Monic.pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ (n : ℕ)
, (p ^ n).Monic
参数：n : ℕ；p ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succ]
    exact (Monic.pow hp n).mul hp
/-
**Polynomial.Monic.add_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, p.Monic → q.degre
e < p.degree → (p + q).Monic
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
-/
theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]
/-
**Polynomial.Monic.add_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, q.Monic → p.degre
e < q.degree → (p + q).Monic
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
-/
theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]
/-
**Polynomial.Monic.of_mul_monic_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic
`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, p.Monic → (p * q)
.Monic → q.Monic
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff_monic_mul`：leadingCoeff_monic_mul {p q : R[X]} (
hp : Monic p) : leadingCoeff (p * q) = leadingCoeff q
-/
theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]
/-
**Polynomial.Monic.of_mul_monic_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Moni
c`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, q.Monic → (p * q)
.Monic → p.Monic
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
-/
theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

namespace Monic

/-
**Polynomial.Monic.comp** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Monic`。
形式化陈述：comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree != 0) : (p.comp q).Mon
ic
参数：hp : p.Monic；hq : q.Monic；h : q.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.natDegree_comp_eq_of_mul_ne_zero`：natDegree_comp_eq_of_mul_ne
_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0) : natDegree (p.co
mp q) = natDegree p * natDegree q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
-/
lemma comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
    natDegree_comp_eq_of_mul_ne_zero <| by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Monic.def, Polynomial.leadingCoeff, this, coeff_comp_degree_mul_degree h, hp.leadingCoeff,
    hq.leadingCoeff, one_pow, mul_one]
/-
**Polynomial.Monic.comp_X_add_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Monic`。
形式化陈述：comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic
参数：hp : p.Monic；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Polynomial.Monic.comp`：comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegr
ee != 0) : (p.comp q).Monic
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_X_add_C`：natDegree_X_add_C (x : R) : (X + C x).natD
egree = 1
-/
lemma comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha ↦ ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

@[simp]
/-
**Polynomial.Monic.degree_le_zero_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Monic`。
形式化陈述：degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree <= 0 ↔ p = 1
参数：hp : p.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree ≤ 0 ↔ p = 1 := by
  rw [← hp.natDegree_eq_zero, natDegree_eq_zero_iff_degree_le_zero]
/-
**Polynomial.Monic.natDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：natDegree_mul (hp : p.Monic) (hq : q.Monic) : (p * q).natDegree = p.natDeg
ree + q.natDegree
参数：hp : p.Monic；hq : q.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem natDegree_mul (hp : p.Monic) (hq : q.Monic) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]
/-
**Polynomial.Monic.degree_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degre
e
参数：hp : p.Monic；q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree := by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul', hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]
/-
**Polynomial.Monic.natDegree_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Moni
c`。
形式化陈述：natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p)
.natDegree
参数：hp : p.Monic；q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree := by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h, Polynomial.natDegree_mul', add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]
/-
**Polynomial.Monic._root_.Polynomial.not_isUnit_X_add_C** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Monic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.not_isUnit_X_add_C [Nontrivial R] (a : R) : ¬ IsUnit (X + C a) := by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg, natDegree_one, natDegree_X_add_C] at h
  grind
/-
**Polynomial.Monic.not_dvd_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Monic`。
形式化陈述：not_dvd_of_natDegree_lt (hp : Monic p) (h0 : q != 0) (hl : natDegree q < n
atDegree p) : ¬p ∣ q
参数：hp : Monic p；h0 : q != 0；hl : natDegree q < natDegree p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem not_dvd_of_natDegree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : natDegree q < natDegree p) :
    ¬p ∣ q := by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)
/-
**Polynomial.Monic.not_dvd_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mo
nic`。
形式化陈述：not_dvd_of_degree_lt (hp : Monic p) (h0 : q != 0) (hl : degree q < degree 
p) : ¬p ∣ q
参数：hp : Monic p；h0 : q != 0；hl : degree q < degree p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.not_dvd_of_natDegree_lt`：not_dvd_of_natDegree_lt (hp : 
Monic p) (h0 : q != 0) (hl : natDegree q < natDegree p) : ¬p ∣ q
· 使用定理 `Polynomial.natDegree_lt_natDegree`：natDegree_lt_natDegree {q : S[X]} (hp
 : p != 0) (hpq : p.degree < q.degree) : p.natDegree < q.natDegree
-/
theorem not_dvd_of_degree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : degree q < degree p) : ¬p ∣ q :=
  Monic.not_dvd_of_natDegree_lt hp h0 <| natDegree_lt_natDegree h0 hl
/-
**Polynomial.Monic.nextCoeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：nextCoeff_mul (hp : Monic p) (hq : Monic q) : nextCoeff (p * q) = nextCoef
f p + nextCoeff q
参数：hp : Monic p；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.reverse_mul`：reverse_mul {f g : R[X]} (fg : f.leadingCoeff * 
g.leadingCoeff != 0) : reverse (f * g) = reverse f * reverse g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.mul_coeff_one`：mul_coeff_one (p q : R[X]) : coeff (p * q) 1 =
 coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0
· 使用定理 `Polynomial.coeff_zero_reverse`：coeff_zero_reverse (f : R[X]) : coeff (re
verse f) 0 = leadingCoeff f
· 使用定理 `Polynomial.coeff_one_reverse`：coeff_one_reverse (f : R[X]) : coeff (reve
rse f) 1 = nextCoeff f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nextCoeff_mul (hp : Monic p) (hq : Monic q) :
    nextCoeff (p * q) = nextCoeff p + nextCoeff q := by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]
/-
**Polynomial.Monic.nextCoeff_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：nextCoeff_pow (hp : p.Monic) (n : Nat) : (p ^ n).nextCoeff = n • p.nextCoe
ff
参数：hp : p.Monic；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.nextCoeff_C_eq_zero`：nextCoeff_C_eq_zero (c : R) : nextCoeff 
(C c) = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.Monic.nextCoeff_mul`：nextCoeff_mul (hp : Monic p) (hq : Monic
 q) : nextCoeff (p * q) = nextCoeff p + nextCoeff q
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
-/
theorem nextCoeff_pow (hp : p.Monic) (n : ℕ) : (p ^ n).nextCoeff = n • p.nextCoeff := by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, (hp.pow n).nextCoeff_mul hp, ih, succ_nsmul]
/-
**Polynomial.Monic.eq_one_of_map_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mo
nic`。
形式化陈述：eq_one_of_map_eq_one {S : Type*} [Semiring S] [Nontrivial S] (f : R ->+* S
) (hp : p.Monic) (map_eq : p.map f = 1) : p = 1
参数：f : R ->+* S；hp : p.Monic；map_eq : p.map f = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
-/
theorem eq_one_of_map_eq_one {S : Type*} [Semiring S] [Nontrivial S] (f : R →+* S) (hp : p.Monic)
    (map_eq : p.map f = 1) : p = 1 := by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leadingCoeff_ne_zero f _, map_eq, degree_one]
    · rw [hp.leadingCoeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.natDegree = 0 :=
    WithBot.coe_eq_coe.mp ((degree_eq_natDegree hp.ne_zero).symm.trans hdeg)
  convert! eq_C_of_degree_eq_zero hdeg
  rw [← hndeg, ← Polynomial.leadingCoeff, hp.leadingCoeff, C.map_one]
/-
**Polynomial.Monic.natDegree_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：natDegree_pow (hp : p.Monic) (n : Nat) : (p ^ n).natDegree = n * p.natDegr
ee
参数：hp : p.Monic；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.Monic.natDegree_mul`：natDegree_mul (hp : p.Monic) (hq : q.Mon
ic) : (p * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem natDegree_pow (hp : p.Monic) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, (hp.pow n).natDegree_mul hp, hn, Nat.succ_mul, add_comm]

end Monic

@[simp]
/-
**Polynomial.natDegree_pow_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pow_X_add_C [Nontrivial R] (n : Nat) (r : R) : ((X + C r) ^ n).n
atDegree = n
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.natDegree_pow`：natDegree_pow (hp : p.Monic) (n : Nat) :
 (p ^ n).natDegree = n * p.natDegree
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
· 使用定理 `Polynomial.natDegree_X_add_C`：natDegree_X_add_C (x : R) : (X + C x).natD
egree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem natDegree_pow_X_add_C [Nontrivial R] (n : ℕ) (r : R) : ((X + C r) ^ n).natDegree = n := by
  rw [(monic_X_add_C r).natDegree_pow, natDegree_X_add_C, mul_one]
/-
**Polynomial.Monic.eq_one_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`
。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → IsUnit p 
→ p = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `right_ne_zero_of_mul_eq_one`：right_ne_zero_of_mul_eq_one (h : a * b = 1)
 : b != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
-/
theorem Monic.eq_one_of_isUnit (hm : Monic p) (hpu : IsUnit p) : p = 1 := by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h, natDegree_one, eq_comm, add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1
/-
**Polynomial.Monic.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → (IsUnit p
 ↔ p = 1)
参数：IsUnit p ↔ p = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.eq_one_of_isUnit`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → IsUnit p → p = 1
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.isUnit_iff (hm : p.Monic) : IsUnit p ↔ p = 1 :=
  ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩
/-
**Polynomial.eq_of_monic_of_associated** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated 
p q) : p = q
参数：hp : p.Monic；hq : q.Monic；hpq : Associated p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_one_of_isUnit`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → IsUnit p → p = 1
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, rfl⟩ := hpq
  rw [(hp.of_mul_monic_left hq).eq_one_of_isUnit u.isUnit, mul_one]

section MonicDegreeEq

variable [Semiring S]

variable (R n) in
/--
The type of monic polynomials of degree `n`.

The implementation is slightly different because it is useful to still contain `X ^ n` when
`R` is trivial. See `MonicDegreeEq.mk` for the usual constructor.
-/
/-
**Polynomial.MonicDegreeEq** 是 Mathlib 中的一个缩写定义，位于命名空间 `Polynomial`。
形式化陈述：MonicDegreeEq : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of monic polynomials of degree `n`.

The implementation is slightly different because it is useful to still contain `
X ^ n` when
`R` is trivial. See `MonicDegreeEq.mk` for the usual constructor.
-/
abbrev MonicDegreeEq : Type _ := { p : R[X] // p.coeff n = 1 ∧ ∀ i > n, p.coeff i = 0 }

@[simp]
/-
**Polynomial.MonicDegreeEq.natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic
DegreeEq`。
形式化陈述：∀ {R : Type u} {n : ℕ} [inst : Semiring R] [Nontrivial R] (p : Polynomial.
MonicDegreeEq R n), (↑p).natDegree = n
参数：p : Polynomial.MonicDegreeEq R n；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_le_iff_coeff_eq_zero`：natDegree_le_iff_coeff_eq_zer
o : p.natDegree <= n ↔ forall N : Nat, n < N -> p.coeff N = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma MonicDegreeEq.natDegree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr p.2.2) (by simp [p.2.1])

@[simp]
/-
**Polynomial.MonicDegreeEq.degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.MonicDeg
reeEq`。
形式化陈述：∀ {R : Type u} {n : ℕ} [inst : Semiring R] [Nontrivial R] (p : Polynomial.
MonicDegreeEq R n), (↑p).degree = ↑n
参数：p : Polynomial.MonicDegreeEq R n；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_eq_of_le_of_coeff_ne_zero`：degree_eq_of_le_of_coeff_ne
_zero (pn : p.degree <= n) (p1 : p.coeff n != 0) : p.degree = n
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.MonicDegreeEq.natDegree`：∀ {R : Type u} {n : ℕ} [inst : Semir
ing R] [Nontrivial R] (p : Polynomial.MonicDegreeEq R n), (↑p).natDegree = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma MonicDegreeEq.degree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le p.natDegree.le) (by simp [p.2.1])
/-
**Polynomial.MonicDegreeEq.monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.MonicDegr
eeEq`。
形式化陈述：∀ {R : Type u} {n : ℕ} [inst : Semiring R] (p : Polynomial.MonicDegreeEq R
 n), (↑p).Monic
参数：p : Polynomial.MonicDegreeEq R n；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.MonicDegreeEq.natDegree`：∀ {R : Type u} {n : ℕ} [inst : Semir
ing R] [Nontrivial R] (p : Polynomial.MonicDegreeEq R n), (↑p).natDegree = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma MonicDegreeEq.monic (p : MonicDegreeEq R n) :
    p.1.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff, p.natDegree, p.2.1]
/-
**Polynomial.MonicDegreeEq.coeff_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mon
icDegreeEq`。
形式化陈述：∀ {R : Type u} {n : ℕ} [inst : Semiring R] (p : Polynomial.MonicDegreeEq R
 n) (i : ℕ),   n ≤ i → (↑p).coeff i = if i = n then 1 else 0
参数：p : Polynomial.MonicDegreeEq R n；i : ℕ；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma MonicDegreeEq.coeff_of_ge (p : MonicDegreeEq R n) (i : ℕ) (hi : n ≤ i) :
    p.1.coeff i = if i = n then 1 else 0 := by
  split_ifs <;> simp_all [p.2.1, p.2.2 _ (hi.lt_of_ne (.symm _))]

/-- The constructor for `MonicDegreeEq` given a monic polynomial of degree `n`. -/
@[simps]
/-
**Polynomial.MonicDegreeEq.mk** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.MonicDegreeE
q`。
形式化陈述：{R : Type u} →   {n : ℕ} → [inst : Semiring R] → (p : Polynomial R) → p.Mo
nic → p.natDegree = n → Polynomial.MonicDegreeEq R n
参数：p : Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructor for `MonicDegreeEq` given a monic polynomial of degree `n`.
-/
def MonicDegreeEq.mk (p : R[X]) (hp : p.Monic) (hp' : p.natDegree = n) :
    MonicDegreeEq R n :=
  ⟨p, by rw [← hp', ← leadingCoeff, hp], fun i hi ↦ coeff_eq_zero_of_natDegree_lt (hp'.trans_lt hi)⟩

/-- The image of a monic polynomial of degree `n` under a ring homomorphism. -/
@[simps] noncomputable
/-
**Polynomial.MonicDegreeEq.map** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.MonicDegree
Eq`。
形式化陈述：{R : Type u} →   {S : Type v} →     {n : ℕ} →       [inst : Semiring R] → 
        [inst_1 : Semiring S] → Polynomial.MonicDegreeEq R n → (R →+* S) → Polyn
omial.MonicDegreeEq S n
参数：R →+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a monic polynomial of degree `n` under a ring homomorphism.
-/
def MonicDegreeEq.map (p : MonicDegreeEq R n) (f : R →+* S) :
    MonicDegreeEq S n :=
  ⟨p.1.map f, by simp +contextual [coeff_map, p.2]⟩

end MonicDegreeEq

end Semiring

section CommSemiring

variable [CommSemiring R] {p : R[X]}

/-
**Polynomial.monic_multiset_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：monic_multiset_prod_of_monic (t : Multiset ι) (f : ι -> R[X]) (ht : forall
 i in t, Monic (f i)) : Monic (t.map f).prod
参数：t : Multiset ι；f : ι -> R[X]；ht : forall i in t, Monic (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι → R[X]) (ht : ∀ i ∈ t, Monic (f i)) :
    Monic (t.map f).prod := by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons, Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))
/-
**Polynomial.monic_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_prod_of_monic (s : Finset ι) (f : ι -> R[X]) (hs : forall i in s, Mo
nic (f i)) : Monic (∏ i in s, f i)
参数：s : Finset ι；f : ι -> R[X]；hs : forall i in s, Monic (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
-/
theorem monic_prod_of_monic (s : Finset ι) (f : ι → R[X]) (hs : ∀ i ∈ s, Monic (f i)) :
    Monic (∏ i ∈ s, f i) :=
  monic_multiset_prod_of_monic s.1 f hs
/-
**Polynomial.monic_finprod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_finprod_of_monic (α : Type*) (f : α -> R[X]) (hf : forall i in Funct
ion.mulSupport f, Monic (f i)) : Monic (finprod f)
参数：α : Type*；f : α -> R[X]；hf : forall i in Function.mulSupport f, Monic (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.monic_one`：monic_one : Monic (1 : R[X])
-/
theorem monic_finprod_of_monic (α : Type*) (f : α → R[X])
    (hf : ∀ i ∈ Function.mulSupport f, Monic (f i)) :
    Monic (finprod f) := by
  classical
  rw [finprod_def]
  split_ifs
  · exact monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact monic_one
/-
**Polynomial.Monic.nextCoeff_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Monic`。
形式化陈述：∀ {R : Type u} {ι : Type y} [inst : CommSemiring R] (t : Multiset ι) (f : 
ι → Polynomial R),   (∀ i ∈ t, (f i).Monic) → (Multiset.map f t).prod.nextCoeff 
= (Multiset.map (fun i => (f i).nextCoeff) t).sum
参数：t : Multiset ι；f : ι → Polynomial R；∀ i ∈ t, (f i).Monic；Multiset.map f t；Mul
tiset.map (fun i => (f i).nextCoeff) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.nextCoeff_C_eq_zero`：nextCoeff_C_eq_zero (c : R) : nextCoeff 
(C c) = 0
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Polynomial.Monic.nextCoeff_mul`：nextCoeff_mul (hp : Monic p) (hq : Monic
 q) : nextCoeff (p * q) = nextCoeff p + nextCoeff q
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem Monic.nextCoeff_multiset_prod (t : Multiset ι) (f : ι → R[X]) (h : ∀ i ∈ t, Monic (f i)) :
    nextCoeff (t.map f).prod = (t.map fun i => nextCoeff (f i)).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]
/-
**Polynomial.Monic.nextCoeff_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} {ι : Type y} [inst : CommSemiring R] (s : Finset ι) (f : ι 
→ Polynomial R),   (∀ i ∈ s, (f i).Monic) → (∏ i ∈ s, f i).nextCoeff = ∑ i ∈ s, 
(f i).nextCoeff
参数：s : Finset ι；f : ι → Polynomial R；∀ i ∈ s, (f i).Monic；∏ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.nextCoeff_multiset_prod`：∀ {R : Type u} {ι : Type y} [i
nst : CommSemiring R] (t : Multiset ι) (f : ι → Polynomial R),   (∀ i ∈ t, (f i)
.Monic) → (Multiset.map f t).p…
-/
theorem Monic.nextCoeff_prod (s : Finset ι) (f : ι → R[X]) (h : ∀ i ∈ s, Monic (f i)) :
    nextCoeff (∏ i ∈ s, f i) = ∑ i ∈ s, nextCoeff (f i) :=
  Monic.nextCoeff_multiset_prod s.1 f h

variable [NoZeroDivisors R] {p q : R[X]}
/-
**Polynomial.irreducible_of_monic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_of_monic (hp : p.Monic) (hp1 : p != 1) : Irreducible p ↔ foral
l f g : R[X], f.Monic -> g.Monic -> f * g = p -> f = 1 ∨ g = 1
参数：hp : p.Monic；hp1 : p != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Polynomial.Monic.eq_one_of_isUnit`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → IsUnit p → p = 1
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 := by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (.of_mul_eq_one _)
          (.of_mul_eq_one _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]
/-
**Polynomial.Monic.irreducible_iff_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [NoZeroDivisors R] {p : Polynomial 
R},   p.Monic →     (Irreducible p ↔ p ≠ 1 ∧ ∀ (f g : Polynomial R), f.Monic → g
.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0)
参数：Irreducible p ↔ p ≠ 1 ∧ ∀ (f g : Polynomial R), f.Monic → g.Monic → f * g = p
 → f.natDegree = 0 ∨ g.natDegree = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Polynomial.irreducible_of_monic`：irreducible_of_monic (hp : p.Monic) (hp
1 : p != 1) : Irreducible p ↔ forall f g : R[X], f.Monic -> g.Monic -> f * g = p
 -> f = 1 ∨ g = 1
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1, and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero, hb.natDegree_eq_zero]
/-
**Polynomial.Monic.irreducible_iff_natDegree'** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [NoZeroDivisors R] {p : Polynomial 
R},   p.Monic →     (Irreducible p ↔       p ≠ 1 ∧ ∀ (f g : Polynomial R), f.Mon
ic → g.Monic → f * g = p → g.natDegree ∉ Finset.Ioc 0 (p.natDegree / 2))
参数：Irreducible p ↔       p ≠ 1 ∧ ∀ (f g : Polynomial R), f.Monic → g.Monic → f *
 g = p → g.natDegree ∉ Finset.Ioc 0 (p.natDegree / 2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.irreducible_iff_natDegree`：∀ {R : Type u} [inst : CommS
emiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     (Irreducible p
 ↔ p ≠ 1 ∧ ∀ (f g : Polynomial R…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Polynomial.Monic.natDegree_mul`：natDegree_mul (hp : p.Monic) (hq : q.Mon
ic) : (p * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 35 条，此处仅展示前 30 条）
-/
lemma Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p ≠ 1 ∧
    ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

/-- Alternate phrasing of `Polynomial.Monic.irreducible_iff_natDegree'` where we only have to check
one divisor at a time. -/
/-
**Polynomial.Monic.irreducible_iff_lt_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [NoZeroDivisors R] {p : Polynomial 
R},   p.Monic →     p ≠ 1 → (Irreducible p ↔ ∀ (q : Polynomial R), q.Monic → q.n
atDegree ∈ Finset.Ioc 0 (p.natDegree / 2) → ¬q ∣ p)
参数：Irreducible p ↔ ∀ (q : Polynomial R), q.Monic → q.natDegree ∈ Finset.Ioc 0 (p
.natDegree / 2) → ¬q ∣ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.irreducible_iff_natDegree'`：∀ {R : Type u} [inst : Comm
Semiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     (Irreducible 
p ↔       p ≠ 1 ∧ ∀ (f g : Polyno…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a

--- 原说明 ---
Alternate phrasing of `Polynomial.Monic.irreducible_iff_natDegree'` where we onl
y have to check
one divisor at a time.
-/
lemma Monic.irreducible_iff_lt_natDegree_lt {p : R[X]} (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree', and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)
/-
**Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [NoZeroDivisors R] {p : Polynomial 
R},   p.Monic → p.natDegree = 2 → (¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂
 ∧ p.coeff 1 = c₁ + c₂)
参数：¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Monic.irreducible_iff_natDegree'`：∀ {R : Type u} [inst : Comm
Semiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     (Irreducible 
p ↔       p ≠ 1 ∧ ∀ (f g : Polyno…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
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
· 使用定理 `Nat.Ioc_succ_singleton`：Ioc_succ_singleton : Ioc b (b + 1) = {b + 1}
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.Monic.natDegree_mul`：natDegree_mul (hp : p.Monic) (hq : q.Mon
ic) : (p * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `Polynomial.Monic.nextCoeff_mul`：nextCoeff_mul (hp : Monic p) (hq : Monic
 q) : nextCoeff (p * q) = nextCoeff p + nextCoeff q
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow`：as_sum_range_C_mul_X_pow (p : R[X])
 : p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
（共 70 条，此处仅展示前 30 条）
-/
lemma Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree', and_iff_right, hnd]
  · push Not
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb, hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using! ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

end CommSemiring

section Semiring

variable [Semiring R]

@[simp]
/-
**Polynomial.Monic.natDegree_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] [inst_1 : Semiring S] [Non
trivial S] {P : Polynomial R},   P.Monic → ∀ (f : R →+* S), (Polynomial.map f P)
.natDegree = P.natDegree
参数：f : R →+* S；Polynomial.map f P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).natDegree = P.natDegree := by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map, Monic.coeff_natDegree hmo, map_one]
  exact one_ne_zero

@[simp]
/-
**Polynomial.Monic.degree_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] [inst_1 : Semiring S] [Non
trivial S] {P : Polynomial R},   P.Monic → ∀ (f : R →+* S), (Polynomial.map f P)
.degree = P.degree
参数：f : R →+* S；Polynomial.map f P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem Monic.degree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).degree = P.degree := by
  simp_all

section Injective

open Function

variable [Semiring S] {f : R →+* S}

/-
**Polynomial.monic_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_of_injective (hf : Injective f) {p : R[X]} (hp : (p.map f).Monic) : 
p.Monic
参数：hf : Injective f；hp : (p.map f).Monic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem monic_of_injective (hf : Injective f) {p : R[X]} (hp : (p.map f).Monic) : p.Monic := by
  apply hf
  rw [← leadingCoeff_map_of_injective hf, hp.leadingCoeff, f.map_one]
/-
**Polynomial._root_.Function.Injective.monic_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.monic_map_iff (hf : Injective f) {p : R[X]} :
    p.Monic ↔ (p.map f).Monic :=
  ⟨Monic.map _, Polynomial.monic_of_injective hf⟩

end Injective

end Semiring

section Ring

variable [Ring R] {p : R[X]}

/-
**Polynomial.monic_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_sub_C (x : R) : Monic (X - C x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
-/
theorem monic_X_sub_C (x : R) : Monic (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)
/-
**Polynomial.monic_X_pow_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_pow_sub {n : Nat} (H : degree p < n) : Monic (X ^ n - p)
参数：H : degree p < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.monic_X_pow_add`：monic_X_pow_add {n : Nat} (H : degree p < n)
 : Monic (X ^ n + p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem monic_X_pow_sub {n : ℕ} (H : degree p < n) : Monic (X ^ n - p) := by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) < n by rwa [← degree_neg p] at H)

/-- `X ^ n - a` is monic. -/
/-
**Polynomial.monic_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : Nat} (h : n != 0) : (
X ^ n - C a).Monic
参数：a : R；h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.monic_X_pow_add_C`：monic_X_pow_add_C {n : Nat} (h : n != 0) :
 (X ^ n + C a).Monic

--- 原说明 ---
`X ^ n - a` is monic.
-/
theorem monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : ℕ} (h : n ≠ 0) :
    (X ^ n - C a).Monic := by
  simpa only [map_neg, ← sub_eq_add_neg] using monic_X_pow_add_C (-a) h
/-
**Polynomial.not_isUnit_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_isUnit_X_pow_sub_one (R : Type*) [Ring R] [Nontrivial R] (n : Nat) : ¬
IsUnit (X ^ n - 1 : R[X])
参数：R : Type*；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.Monic.eq_one_of_isUnit`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → IsUnit p → p = 1
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Polynomial.natDegree_X_pow_sub_C`：natDegree_X_pow_sub_C {n : Nat} {r : R
} : (X ^ n - C r).natDegree = n
-/
theorem not_isUnit_X_pow_sub_one (R : Type*) [Ring R] [Nontrivial R] (n : ℕ) :
    ¬IsUnit (X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R, ← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h, natDegree_X_pow_sub_C]
/-
**Polynomial.Monic.comp_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {p : Polynomial R}, p.Monic → ∀ (r : R), (p
.comp (Polynomial.X - Polynomial.C r)).Monic
参数：r : R；p.comp (Polynomial.X - Polynomial.C r)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `Polynomial.Monic.comp_X_add_C`：comp_X_add_C (hp : p.Monic) (r : R) : (p.
comp (X + C r)).Monic
-/
lemma Monic.comp_X_sub_C {p : R[X]} (hp : p.Monic) (r : R) : (p.comp (X - C r)).Monic := by
  simpa using! hp.comp_X_add_C (-r)
/-
**Polynomial.Monic.sub_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R}, p.Monic → q.degree < 
p.degree → (p - q).Monic
参数：p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.Monic.add_of_left`：∀ {R : Type u} [inst : Semiring R] {p q : 
Polynomial R}, p.Monic → q.degree < p.degree → (p + q).Monic
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem Monic.sub_of_left {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p) :
    Monic (p - q) := by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]
/-
**Polynomial.Monic.sub_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R}, q.leadingCoeff = -1 →
 p.degree < q.degree → (p - q).Monic
参数：p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.Monic.add_of_right`：∀ {R : Type u} [inst : Semiring R] {p q :
 Polynomial R}, q.Monic → p.degree < q.degree → (p + q).Monic
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) :
    Monic (p - q) := by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg, coeff_neg, show q.coeff q.natDegree = -1 from hq, neg_neg]
  rw [sub_eq_add_neg]
  apply Monic.add_of_right this
  rwa [degree_neg]

end Ring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/-
**Polynomial.not_monic_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_monic_zero : ¬Monic (0 : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.not_monic_zero_iff`：not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ 
(0 : R) != 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
theorem not_monic_zero : ¬Monic (0 : R[X]) :=
  not_monic_zero_iff.mp zero_ne_one

end NonzeroSemiring

section NotZeroDivisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring
variable [Semiring R] {p : R[X]}

/-
**Polynomial.Monic.mul_left_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`
。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ {q : Po
lynomial R}, q ≠ 0 → q * p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `WithBot.add_eq_bot`：∀ {α : Type u} [inst : Add α] {x y : WithBot α}, x +
 y = ⊥ ↔ x = ⊥ ∨ y = ⊥
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Polynomial.Monic.degree_le_zero_iff_eq_one`：degree_le_zero_iff_eq_one (h
p : p.Monic) : p.degree <= 0 ↔ p = 1
-/
theorem Monic.mul_left_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : q * p ≠ 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne, ← degree_eq_bot, hp.degree_mul, WithBot.add_eq_bot, not_or, degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine (lt_trans ?_ h).ne'
  simp
/-
**Polynomial.Monic.mul_right_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic
`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ {q : Po
lynomial R}, q ≠ 0 → p * q ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.Monic.degree_mul_comm`：degree_mul_comm (hp : p.Monic) (q : R[
X]) : (p * q).degree = (q * p).degree
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `WithBot.add_eq_bot`：∀ {α : Type u} [inst : Add α] {x y : WithBot α}, x +
 y = ⊥ ↔ x = ⊥ ∨ y = ⊥
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Polynomial.Monic.degree_le_zero_iff_eq_one`：degree_le_zero_iff_eq_one (h
p : p.Monic) : p.degree <= 0 ↔ p = 1
-/
theorem Monic.mul_right_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : p * q ≠ 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne, ← degree_eq_bot, hp.degree_mul_comm, hp.degree_mul, WithBot.add_eq_bot, not_or,
    degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine (lt_trans ?_ h).ne'
  simp
/-
**Polynomial.Monic.mul_natDegree_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mo
nic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R},   p.Monic → ∀ {q : 
Polynomial R}, (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_comm_eq`：iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Monic.mul_natDegree_lt_iff (h : Monic p) {q : R[X]} :
    (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0 := by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree ≠ 0 by simp [hq, ← h.natDegree_eq_zero, iffComm]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]
/-
**Polynomial.Monic.mul_right_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.M
onic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ {q : Po
lynomial R}, p * q = 0 ↔ q = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.Monic.mul_right_ne_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, q ≠ 0 → p * q ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Monic.mul_right_eq_zero_iff (h : Monic p) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]
/-
**Polynomial.Monic.mul_left_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mo
nic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ {q : Po
lynomial R}, q * p = 0 ↔ q = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.Monic.mul_left_ne_zero`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, q ≠ 0 → q * p ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Monic.mul_left_eq_zero_iff (h : Monic p) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]
/-
**Polynomial.Monic.isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {p : Polynomial R}, p.Monic → IsRegular p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.Monic.mul_right_eq_zero_iff`：∀ {R : Type u} [inst : Semiring 
R] {p : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, p * q = 0 ↔ q = 0
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.Monic.mul_left_eq_zero_iff`：∀ {R : Type u} [inst : Semiring R
] {p : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, q * p = 0 ↔ q = 0
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
-/
theorem Monic.isRegular {R : Type*} [Ring R] {p : R[X]} (hp : Monic p) : IsRegular p := by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero, ← hp.mul_right_eq_zero_iff, mul_sub, h, sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero, ← hp.mul_left_eq_zero_iff, sub_mul, h, sub_self]
/-
**Polynomial.degree_smul_of_smul_regular** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S} (p : R
[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree
参数：p : R[X]；h : IsSMulRegular R k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.degree_lt_iff_coeff_zero`：degree_lt_iff_coeff_zero (f : R[X])
 (n : Nat) : degree f < n ↔ forall m : Nat, n <= m -> coeff f m = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree := by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl
/-
**Polynomial.natDegree_smul_of_smul_regular** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S} (p 
: R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree
参数：p : R[X]；h : IsSMulRegular R k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `IsSMulRegular.polynomial`：∀ {R : Type u} [inst : Semiring R] {S : Type u
_1} [inst_1 : SMulZeroClass S R] {a : S},   IsSMulRegular R a → IsSMulRegular (P
olynomial R) a
· 使用定理 `Polynomial.degree_smul_of_smul_regular`：degree_smul_of_smul_regular {S :
 Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R k) : (k • p)
.degree = p.degree
-/
theorem natDegree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree hp, ← degree_eq_natDegree,
    degree_smul_of_smul_regular p h]
  contrapose hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp
/-
**Polynomial.leadingCoeff_smul_of_smul_regular** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：leadingCoeff_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S} 
(p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff
参数：p : R[X]；h : IsSMulRegular R k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.natDegree_smul_of_smul_regular`：natDegree_smul_of_smul_regula
r {S : Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R k) : (
k • p).natDegree = p.natDegree
-/
theorem leadingCoeff_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, coeff_smul,
    natDegree_smul_of_smul_regular p h]
/-
**Polynomial.monic_of_isUnit_leadingCoeff_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) : Monic 
(h.unit⁻¹ • p)
参数：h : IsUnit p.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff_smul_of_smul_regular`：leadingCoeff_smul_of_smul_
regular {S : Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R 
k) : (k • p).leadingCoeff = k • p.…
· 使用定理 `isSMulRegular_of_group`：isSMulRegular_of_group [MulAction G R] (g : G) :
 IsSMulRegular R g
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) :
    Monic (h.unit⁻¹ • p) := by
  rw [Monic.def, leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _), Units.smul_def]
  simp
/-
**Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：isUnit_leadingCoeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q :
 R[X]} : p * q = 0 ↔ q = 0
参数：h : IsUnit p.leadingCoeff。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.Monic.mul_right_eq_zero_iff`：∀ {R : Type u} [inst : Semiring 
R] {p : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, p * q = 0 ↔ q = 0
· 使用定理 `Polynomial.monic_of_isUnit_leadingCoeff_inv_smul`：monic_of_isUnit_leadin
gCoeff_inv_smul (h : IsUnit p.leadingCoeff) : Monic (h.unit⁻¹ • p)
· 使用引理 `smul_eq_zero_iff_eq`：smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x
 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isUnit_leadingCoeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    p * q = 0 ↔ q = 0 := by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc]
    rwa [this, Monic.mul_right_eq_zero_iff] at hp
    exact monic_of_isUnit_leadingCoeff_inv_smul _
  · rintro rfl
    simp
/-
**Polynomial.isUnit_leadingCoeff_mul_left_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : 
R[X]} : q * p = 0 ↔ q = 0
参数：h : IsUnit p.leadingCoeff。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.mul_left_eq_zero_iff`：∀ {R : Type u} [inst : Semiring R
] {p : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, q * p = 0 ↔ q = 0
· 使用定理 `Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one`：monic_mul_C_of_leadin
gCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) : Monic (p * C b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Monic.mul_left_eq_zero_iff] at hp
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

end NotZeroDivisor

end Polynomial

