/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Uthaiwat, Oliver Nash
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotency in polynomial rings.

This file is a place for results related to nilpotency in (single-variable) polynomial rings.

## Main results:
* `Polynomial.isNilpotent_iff`
* `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`

-/

public section

namespace Polynomial

variable {R : Type*} {r : R}

section Semiring

variable [Semiring R] {P : R[X]}

/-
**Polynomial.isNilpotent_C_mul_pow_X_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：isNilpotent_C_mul_pow_X_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) : 
IsNilpotent ((C r) * X ^ n)
参数：n : Nat；hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isNilpotent_mul_right`：isNilpotent_mul_right (h_comm : Commute x
 y) (h : IsNilpotent x) : IsNilpotent (x * y)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Polynomial.commute_X_pow`：commute_X_pow (p : R[X]) (n : Nat) : Commute (
X ^ n) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_pow`：C_pow : C (a ^ n) = C a ^ n
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
-/
lemma isNilpotent_C_mul_pow_X_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow, hm, C_0]
/-
**Polynomial.isNilpotent_pow_X_mul_C_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：isNilpotent_pow_X_mul_C_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) : 
IsNilpotent (X ^ n * (C r))
参数：n : Nat；hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.commute_X_pow`：commute_X_pow (p : R[X]) (n : Nat) : Commute (
X ^ n) p
· 使用引理 `Polynomial.isNilpotent_C_mul_pow_X_of_isNilpotent`：isNilpotent_C_mul_pow
_X_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) : IsNilpotent ((C r) * X ^ n)
-/
lemma isNilpotent_pow_X_mul_C_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent (X ^ n * (C r)) := by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil
/-
**Polynomial.isNilpotent_monomial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {r : R} [inst : Semiring R] {n : ℕ}, IsNilpotent ((Polyno
mial.monomial n) r) ↔ IsNilpotent r
参数：(Polynomial.monomial n) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_pow`：monomial_pow (n : Nat) (r : R) (k : Nat) : mono
mial n r ^ k = monomial (n * k) (r ^ k)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isNilpotent_monomial_iff {n : ℕ} :
    IsNilpotent (monomial (R := R) n r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simp
/-
**Polynomial.isNilpotent_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {r : R} [inst : Semiring R], IsNilpotent (Polynomial.C r)
 ↔ IsNilpotent r
参数：Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
-/
@[simp] lemma isNilpotent_C_iff :
    IsNilpotent (C r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simpa only [← C_pow] using C_eq_zero
/-
**Polynomial.isNilpotent_X_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Polynomial R}, IsNilpotent (Poly
nomial.X * P) ↔ IsNilpotent P
参数：Polynomial.X * P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.isNilpotent_mul_left_iff`：∀ {R : Type u_1} {x y : R} [inst : Sem
iring R],   Commute x y → x ∈ nonZeroDivisorsLeft R → (IsNilpotent (x * y) ↔ IsN
ilpotent y)
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma isNilpotent_X_mul_iff :
    IsNilpotent (X * P) ↔ IsNilpotent P := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rwa [Commute.isNilpotent_mul_left_iff (commute_X P) (by simp)] at h
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩
/-
**Polynomial.isNilpotent_mul_X_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Polynomial R}, IsNilpotent (P * 
Polynomial.X) ↔ IsNilpotent P
参数：P * Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `Polynomial.isNilpotent_X_mul_iff`：∀ {R : Type u_1} [inst : Semiring R] {
P : Polynomial R}, IsNilpotent (Polynomial.X * P) ↔ IsNilpotent P
-/
@[simp] lemma isNilpotent_mul_X_iff :
    IsNilpotent (P * X) ↔ IsNilpotent P := by
  rw [← commute_X P]
  exact isNilpotent_X_mul_iff

end Semiring

section CommRing

variable [CommRing R] {P : R[X]}

/-
**Polynomial.isNilpotent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {P : Polynomial R}, IsNilpotent P ↔ ∀
 (i : ℕ), IsNilpotent (P.coeff i)
参数：i : ℕ；P.coeff i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero_eq_aeval_zero`：coeff_zero_eq_aeval_zero (p : R[X])
 : p.coeff 0 = aeval 0 p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isNilpotent_C_iff`：∀ {R : Type u_1} {r : R} [inst : Semiring 
R], IsNilpotent (Polynomial.C r) ↔ IsNilpotent r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isNilpotent_mul_X_iff`：∀ {R : Type u_1} [inst : Semiring R] {
P : Polynomial R}, IsNilpotent (P * Polynomial.X) ↔ IsNilpotent P
（共 33 条，此处仅展示前 30 条）
-/
protected lemma isNilpotent_iff :
    IsNilpotent P ↔ ∀ i, IsNilpotent (coeff P i) := by
  refine
    ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i ↦ ?_) (fun p _ hnp hpX i ↦ ?_), fun h ↦ ?_⟩
  · rw [← sum_monomial_eq P]
    exact isNilpotent_sum (fun i _ ↦ by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q ↦ coeff q 0) hk
    rcases i with - | i
    · simpa [hp₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hp
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
  · rcases i with - | i
    · simp
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i
/-
**Polynomial.isNilpotent_reflect_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {P : Polynomial R} {N : ℕ},   P.natDe
gree ≤ N → (IsNilpotent (Polynomial.reflect N P) ↔ IsNilpotent P)
参数：IsNilpotent (Polynomial.reflect N P) ↔ IsNilpotent P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Polynomial.revAt_eq_self_of_lt`：revAt_eq_self_of_lt {N i : Nat} (h : N <
 i) : revAt N i = i
-/
@[simp] lemma isNilpotent_reflect_iff {P : R[X]} {N : ℕ} (hN : P.natDegree ≤ N) :
    IsNilpotent (reflect N P) ↔ IsNilpotent P := by
  simp only [Polynomial.isNilpotent_iff]
  refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩ <;> rcases le_or_gt i N with hi | hi
  · simpa [tsub_tsub_cancel_of_le hi] using h (N - i)
  · simp [coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hN hi]
  · simpa [hi, revAt_le] using h (N - i)
  · simpa [revAt_eq_self_of_lt hi] using h i
/-
**Polynomial.isNilpotent_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {P : Polynomial R}, IsNilpotent P.rev
erse ↔ IsNilpotent P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isNilpotent_reflect_iff`：∀ {R : Type u_1} [inst : CommRing R]
 {P : Polynomial R} {N : ℕ},   P.natDegree ≤ N → (IsNilpotent (Polynomial.reflec
t N P) ↔ IsNilpotent P)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] lemma isNilpotent_reverse_iff :
    IsNilpotent P.reverse ↔ IsNilpotent P :=
  isNilpotent_reflect_iff (le_refl _)

/-- Let `P` be a polynomial over `R`. If its constant term is a unit and its other coefficients are
nilpotent, then `P` is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
/-
**Polynomial.isUnit_of_coeff_isUnit_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：isUnit_of_coeff_isUnit_isNilpotent (hunit : IsUnit (P.coeff 0)) (hnil : fo
rall i, i != 0 -> IsNilpotent (P.coeff i)) : IsUnit P
参数：hunit : IsUnit (P.coeff 0)；hnil : forall i, i != 0 -> IsNilpotent (P.coeff i)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.eraseLead_natDegree_le`：eraseLead_natDegree_le (f : R[X]) : (
eraseLead f).natDegree <= f.natDegree - 1
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eraseLead_coeff_of_ne`：eraseLead_coeff_of_ne (i : Nat) (hi : 
i != f.natDegree) : f.eraseLead.coeff i = f.coeff i
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff`：eraseLead_add_
monomial_natDegree_leadingCoeff (f : R[X]) : f.eraseLead + monomial f.natDegree 
f.leadingCoeff = f
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `IsNilpotent.isUnit_add_left_of_commute`：IsNilpotent.isUnit_add_left_of_c
ommute [Ring R] {r u : R} (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commu
te r u) : IsUnit (u + r)
· 使用引理 `Polynomial.isNilpotent_C_mul_pow_X_of_isNilpotent`：isNilpotent_C_mul_pow
_X_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) : IsNilpotent ((C r) * X ^ n)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
Let `P` be a polynomial over `R`. If its constant term is a unit and its other c
oefficients are
nilpotent, then `P` is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`.
-/
theorem isUnit_of_coeff_isUnit_isNilpotent (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with | _ k hind
  by_cases hdeg : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C
  set P₁ := P.eraseLead with hP₁
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P, ← C_mul_X_pow_eq_monomial, ← hP₁]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg)
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine hind P₁.natDegree ?_ ?_ (fun i hi => ?_) rfl
  · simp_rw [P₁, ← h, hdeg₂]
  · simp_rw [P₁, eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases! H : i ≤ P₁.natDegree
    · simp_rw [P₁, eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    · simp_rw [coeff_eq_zero_of_natDegree_lt H, IsNilpotent.zero]

/-- Let `P` be a polynomial over `R`. If `P` is a unit, then all its coefficients are nilpotent,
except its constant term which is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
/-
**Polynomial.coeff_isUnit_isNilpotent_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：coeff_isUnit_isNilpotent_of_isUnit (hunit : IsUnit P) : IsUnit (P.coeff 0)
 ∧ (forall i, i != 0 -> IsNilpotent (P.coeff i))
参数：hunit : IsUnit P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `nilpotent_iff_mem_prime`：nilpotent_iff_mem_prime : IsNilpotent x ↔ foral
l J : Ideal R, J.IsPrime -> x in J
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Nat.WithBot.add_eq_zero_iff`：add_eq_zero_iff {n m : WithBot Nat} : n + m
 = 0 ↔ n = 0 ∧ m = 0
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithBot.coe_pos`：∀ {α : Type u} [inst : Zero α] {a : α} [inst_1 : LT α],
 0 < ↑a ↔ 0 < a
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f

--- 原说明 ---
Let `P` be a polynomial over `R`. If `P` is a unit, then all its coefficients ar
e nilpotent,
except its constant term which is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`.
-/
theorem coeff_isUnit_isNilpotent_of_isUnit (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  · refine .of_mul_eq_one (Q.coeff 0) ?_
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h
  · intro n hn
    rw [nilpotent_iff_mem_prime]
    intro I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff, ← degree_mul, ← map_mul, hQ, map_one, degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine coeff_eq_zero_of_degree_lt ?_
      rw [hPQ.1]
      exact WithBot.coe_pos.2 hn.bot_lt
    rw [coe_mapRingHom, coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at hcoeff
    exact hcoeff

/-- Let `P` be a polynomial over `R`. `P` is a unit if and only if all its coefficients are
nilpotent, except its constant term which is a unit.

See also `Polynomial.isUnit_iff'`. -/
/-
**Polynomial.isUnit_iff_coeff_isUnit_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：isUnit_iff_coeff_isUnit_isNilpotent : IsUnit P ↔ IsUnit (P.coeff 0) ∧ (for
all i, i != 0 -> IsNilpotent (P.coeff i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_isUnit_isNilpotent_of_isUnit`：coeff_isUnit_isNilpotent_
of_isUnit (hunit : IsUnit P) : IsUnit (P.coeff 0) ∧ (forall i, i != 0 -> IsNilpo
tent (P.coeff i))
· 使用定理 `Polynomial.isUnit_of_coeff_isUnit_isNilpotent`：isUnit_of_coeff_isUnit_is
Nilpotent (hunit : IsUnit (P.coeff 0)) (hnil : forall i, i != 0 -> IsNilpotent (
P.coeff i)) : IsUnit P
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Let `P` be a polynomial over `R`. `P` is a unit if and only if all its coefficie
nts are
nilpotent, except its constant term which is a unit.

See also `Polynomial.isUnit_iff'`.
-/
theorem isUnit_iff_coeff_isUnit_isNilpotent :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) :=
  ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩
/-
**Polynomial.isUnit_C_add_X_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {r : R} [inst : CommRing R] {P : Polynomial R},   IsUnit 
(Polynomial.C r + Polynomial.X * P) ↔ IsUnit r ∧ IsNilpotent P
参数：Polynomial.C r + Polynomial.X * P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `Polynomial.coeff_X_mul`：coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p)
 (n + 1) = coeff p n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isUnit_C_add_X_mul_iff :
    IsUnit (C r + X * P) ↔ IsUnit r ∧ IsNilpotent P := by
  have : ∀ i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    ← Polynomial.isNilpotent_iff]
/-
**Polynomial.isUnit_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_iff' : IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.modByMonic_X`：modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnit_iff' :
    IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X) := by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P X]
  simp [modByMonic_X]
/-
**Polynomial.not_isUnit_of_natDegree_pos_of_isReduced** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：not_isUnit_of_natDegree_pos_of_isReduced [IsReduced R] (p : R[X]) (hpl : 0
 < p.natDegree) : ¬ IsUnit p
参数：p : R[X]；hpl : 0 < p.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem not_isUnit_of_natDegree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.natDegree) : ¬ IsUnit p := by
  simp only [ne_eq, isNilpotent_iff_eq_zero, not_and, not_forall, exists_prop,
    Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  intro _
  refine ⟨p.natDegree, hpl.ne', ?_⟩
  contrapose! hpl
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at hpl
  simp [hpl]
/-
**Polynomial.not_isUnit_of_degree_pos_of_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：not_isUnit_of_degree_pos_of_isReduced [IsReduced R] (p : R[X]) (hpl : 0 < 
p.degree) : ¬ IsUnit p
参数：p : R[X]；hpl : 0 < p.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.not_isUnit_of_natDegree_pos_of_isReduced`：not_isUnit_of_natDe
gree_pos_of_isReduced [IsReduced R] (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUni
t p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
-/
theorem not_isUnit_of_degree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.degree) : ¬ IsUnit p :=
  not_isUnit_of_natDegree_pos_of_isReduced _ (natDegree_pos_iff_degree_pos.mpr hpl)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (C : _ →+* Polynomial R) where
  map_nonunit := by simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (algebraMap R (Polynomial R)) :=
  inferInstanceAs (IsLocalHom C)

end CommRing

section CommAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {a b : S}

/-
**Polynomial.isNilpotent_aeval_sub_of_isNilpotent_sub** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
形式化陈述：isNilpotent_aeval_sub_of_isNilpotent_sub (h : IsNilpotent (a - b)) : IsNil
potent (aeval a P - aeval b P)
参数：h : IsNilpotent (a - b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isNilpotent_aeval_sub_of_isNilpotent_sub (h : IsNilpotent (a - b)) :
    IsNilpotent (aeval a P - aeval b P) := by
  simp only [← eval_map_algebraMap]
  have ⟨c, hc⟩ := evalSubFactor (map (algebraMap R S) P) a b
  exact hc ▸ (Commute.all _ _).isNilpotent_mul_left h

variable {P}
/-
**Polynomial.isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub** 是 Mathlib 中的一个引理，
位于命名空间 `Polynomial`。
形式化陈述：isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub (hb : IsUnit (aeval b P)) 
(hab : IsNilpotent (a - b)) : IsUnit (aeval a P)
参数：hb : IsUnit (aeval b P)；hab : IsNilpotent (a - b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `IsNilpotent.isUnit_add_left_of_commute`：IsNilpotent.isUnit_add_left_of_c
ommute [Ring R] {r u : R} (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commu
te r u) : IsUnit (u + r)
· 使用引理 `Polynomial.isNilpotent_aeval_sub_of_isNilpotent_sub`：isNilpotent_aeval_s
ub_of_isNilpotent_sub (h : IsNilpotent (a - b)) : IsNilpotent (aeval a P - aeval
 b P)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
    (hb : IsUnit (aeval b P)) (hab : IsNilpotent (a - b)) :
    IsUnit (aeval a P) := by
  rw [← add_sub_cancel (aeval b P) (aeval a P)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ hb (Commute.all _ _)
  exact isNilpotent_aeval_sub_of_isNilpotent_sub P hab

end CommAlgebra

end Polynomial

