/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $R[X]$

-/

@[expose] public section


noncomputable section

open Polynomial
open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R]

/-
**Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero*
* 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero (p : R[
X]) (t : R) (hnezero : derivative p != 0) : p.rootMultiplicity t - 1 <= p.deriva
tive.rootMultiplicity t
参数：p : R[X]；t : R；hnezero : derivative p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd`：pow_sub_one_dvd_deriva
tive_of_pow_dvd {p q : R[X]} {n : Nat} (dvd : q ^ n ∣ p) : q ^ (n - 1) ∣ derivat
ive p
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
    (p : R[X]) (t : R) (hnezero : derivative p ≠ 0) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t :=
  (le_rootMultiplicity_iff hnezero).2 <|
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)
/-
**Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors** 是 Math
lib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors {p : R[X]} {t :
 R} (hpt : Polynomial.IsRoot p t) (hnzd : (p.rootMultiplicity t : R) in nonZeroD
ivisors R) : (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1
参数：hpt : Polynomial.IsRoot p t；hnzd : (p.rootMultiplicity t : R) in nonZeroDivis
ors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.rootMultiplicity_pos`：rootMultiplicity_pos {p : R[X]} (hp : p
 != 0) {x : R} : 0 < rootMultiplicity x p ↔ IsRoot p x
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Polynomial.derivative_X_sub_C_pow`：derivative_X_sub_C_pow (c : R) (m : N
at) : derivative ((X - C c) ^ m) = C (m : R) * (X - C c) ^ (m - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `dvd_cancel_left_mem_nonZeroDivisors`：dvd_cancel_left_mem_nonZeroDivisors
 (hr : r in R⁰) : r * x ∣ r * y ↔ x ∣ y
· 使用定理 `Polynomial.Monic.mem_nonZeroDivisors`：∀ {R : Type u} [inst : CommRing R]
 {p : Polynomial R}, p.Monic → p ∈ nonZeroDivisors (Polynomial R)
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
（共 36 条，此处仅展示前 30 条）
-/
theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t)
    (hnzd : (p.rootMultiplicity t : R) ∈ nonZeroDivisors R) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel <| (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ derivative p := by
    rw [hp, derivative_mul, dvd_add_left (dvd_mul_right _ _),
      derivative_X_sub_C_pow, ← hm, pow_succ, hm, mul_comm (C _), mul_assoc,
      dvd_cancel_left_mem_nonZeroDivisors (monic_X_sub_C t |>.pow _ |>.mem_nonZeroDivisors)]
    rw [dvd_iff_isRoot, IsRoot] at hndvd ⊢
    rwa [eval_mul, eval_C, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd]
  have hnezero : derivative p ≠ 0 := fun h ↦ hndvd (by rw [h]; exact dvd_zero _)
  exact le_antisymm (by rwa [rootMultiplicity_le_iff hnezero, hm])
    (rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero _ t hnezero)
/-
**Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : N
at} (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t
参数：hn : n < p.rootMultiplicity t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用定理 `Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd`：pow_sub_dvd_iterat
e_derivative_of_pow_dvd {p q : R[X]} {n : Nat} (m : Nat) (dvd : q ^ n ∣ p) : q ^
 (n - m) ∣ derivative^[m] p
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
theorem isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : ℕ}
    (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t :=
  dvd_iff_isRoot.mp <| (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

open Finset in
/-
**Polynomial.eval_iterate_derivative_rootMultiplicity** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} : (derivative^
[p.rootMultiplicity t] p).eval t = (p.rootMultiplicity t).factorial • (p /ₘ (X -
 C t) ^ p.rootMultiplicity t).eval t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`：pow_mul_divByMonic_ro
otMultiplicity_eq (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p * (p /ₘ 
(X - C a) ^ rootMultiplicity a p) = p
· 使用定理 `Polynomial.iterate_derivative_mul`：iterate_derivative_mul {n} (p q : R[X
]) : derivative^[n] (p * q) = ∑ k in range n.succ, (n.choose k • (derivative^[n 
- k] p * derivative^[k]…
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Polynomial.iterate_derivative_X_sub_pow`：iterate_derivative_X_sub_pow (n
 k : Nat) (c : R) : derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C 
c) ^ (n - k)
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
· 使用定理 `Polynomial.iterate_derivative_X_sub_pow_self`：iterate_derivative_X_sub_p
ow_self (n : Nat) (c : R) : derivative^[n] ((X - C c) ^ n) = n.factorial
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
（共 31 条，此处仅展示前 30 条）
-/
theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul, eval_finsetSum, sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C, sub_self,
      zero_pow hb0, smul_zero, zero_mul, smul_zero]
/-
**Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivi
sors** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors {p
 : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (derivative^[m] 
p).IsRoot t) (hnzd : (n.factorial : R) in nonZeroDivisors R) : n < p.rootMultipl
icity t
参数：h : p != 0；hroot : forall m <= n, (derivative^[m] p).IsRoot t；hnzd : (n.facto
rial : R) in nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `Nat.cast_dvd_cast`：cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α)
· 使用定理 `Nat.factorial_dvd_factorial`：factorial_dvd_factorial {m n} (h : m <= n) 
: m ! ∣ n !
· 使用定理 `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`：eval_divByMonic
_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p != 0) : eval a (p /ₘ (X
 - C a) ^ rootMultiplicity a p) != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_left_mem_nonZeroDivisors_eq_zero_iff`：mul_left_mem_nonZeroDivisors_e
q_zero_iff (hr : r in M₀⁰) : r * x = 0 ↔ x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_iterate_derivative_rootMultiplicity`：eval_iterate_deriva
tive_rootMultiplicity {p : R[X]} {t : R} : (derivative^[p.rootMultiplicity t] p)
.eval t = (p.rootMultiplicity t).factoria…
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : (n.factorial : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ : ((rootMultiplicity t p)! : R) ∣ n ! := by gcongr
  rw [hq, mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd.1] at hroot
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero t h hroot
/-
**Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivi
sors'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' {
p : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (derivative^[m]
 p).IsRoot t) (hnzd : forall m <= n, m != 0 -> (m : R) in nonZeroDivisors R) : n
 < p.rootMultiplicity t
参数：h : p != 0；hroot : forall m <= n, (derivative^[m] p).IsRoot t；hnzd : forall m
 <= n, m != 0 -> (m : R) in nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZe
roDivisors`：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivis
ors {p : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (d…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  apply lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, mul_mem_nonZeroDivisors]
    exact ⟨hnzd _ le_rfl n.succ_ne_zero, ih fun m h ↦ hnzd m (h.trans n.le_succ)⟩
/-
**Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDiv
isors** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors {
p : R[X]} {t : R} {n : Nat} (h : p != 0) (hnzd : (n.factorial : R) in nonZeroDiv
isors R) : n < p.rootMultiplicity t ↔ forall m <= n, (derivative^[m] p).IsRoot t
参数：h : p != 0；hnzd : (n.factorial : R) in nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity`：isRoot_iter
ate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : Nat} (hn : n < p.r
ootMultiplicity t) : (derivative^[n] p).IsRoot t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZe
roDivisors`：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivis
ors {p : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (d…
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hnzd : (n.factorial : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| hm.trans_lt hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hr hnzd⟩
/-
**Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDiv
isors'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors' 
{p : R[X]} {t : R} {n : Nat} (h : p != 0) (hnzd : forall m <= n, m != 0 -> (m : 
R) in nonZeroDivisors R) : n < p.rootMultiplicity t ↔ forall m <= n, (derivative
^[m] p).IsRoot t
参数：h : p != 0；hnzd : forall m <= n, m != 0 -> (m : R) in nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity`：isRoot_iter
ate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : Nat} (hn : n < p.r
ootMultiplicity t) : (derivative^[n] p).IsRoot t
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZe
roDivisors'`：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivi
sors' {p : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (…
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| Nat.lt_of_le_of_lt hm hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩
/-
**Polynomial.one_lt_rootMultiplicity_iff_isRoot_iterate_derivative** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial`。
形式化陈述：one_lt_rootMultiplicity_iff_isRoot_iterate_derivative {p : R[X]} {t : R} (
h : p != 0) : 1 < p.rootMultiplicity t ↔ forall m <= 1, (derivative^[m] p).IsRoo
t t
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZ
eroDivisors`：lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDiv
isors {p : R[X]} {t : R} {n : Nat} (h : p != 0) (hnzd : (n.factorial : R)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_one`：Nat.factorial 1 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
-/
theorem one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ ∀ m ≤ 1, (derivative^[m] p).IsRoot t :=
  lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)
/-
**Polynomial.one_lt_rootMultiplicity_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：one_lt_rootMultiplicity_iff_isRoot {p : R[X]} {t : R} (h : p != 0) : 1 < p
.rootMultiplicity t ↔ p.IsRoot t ∧ (derivative p).IsRoot t
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_lt_rootMultiplicity_iff_isRoot_iterate_derivative`：one_lt
_rootMultiplicity_iff_isRoot_iterate_derivative {p : R[X]} {t : R} (h : p != 0) 
: 1 < p.rootMultiplicity t ↔ forall m <= 1, (derivativ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem one_lt_rootMultiplicity_iff_isRoot
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ p.IsRoot t ∧ (derivative p).IsRoot t := by
  rw [one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h ↦ ⟨h 0 (by simp), h 1 (by simp)⟩, fun ⟨h0, h1⟩ m hm ↦ ?_⟩
  obtain (_ | _ | m) := m
  exacts [h0, h1, by lia]

end CommRing

section IsDomain

variable [CommRing R]

/-
**Polynomial.one_lt_rootMultiplicity_iff_isRoot_gcd** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：one_lt_rootMultiplicity_iff_isRoot_gcd [GCDMonoid R[X]] {p : R[X]} {t : R}
 (h : p != 0) : 1 < p.rootMultiplicity t ↔ (gcd p (derivative p)).IsRoot t
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_lt_rootMultiplicity_iff_isRoot`：one_lt_rootMultiplicity_i
ff_isRoot {p : R[X]} {t : R} (h : p != 0) : 1 < p.rootMultiplicity t ↔ p.IsRoot 
t ∧ (derivative p).IsRoot t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_rootMultiplicity_iff_isRoot_gcd
    [GCDMonoid R[X]] {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ (gcd p (derivative p)).IsRoot t := by
  simp_rw [one_lt_rootMultiplicity_iff_isRoot h, ← dvd_iff_isRoot, dvd_gcd_iff]

variable [NoZeroDivisors R]
/-
**Polynomial.derivative_rootMultiplicity_of_root** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt :
 p.IsRoot t) : p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1
参数：hpt : p.IsRoot t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors`：d
erivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors {p : R[X]} {t : R} (hp
t : Polynomial.IsRoot p t) (hnzd : (p.rootMultiplicity t : …
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.rootMultiplicity_pos`：rootMultiplicity_pos {p : R[X]} (hp : p
 != 0) {x : R} : 0 < rootMultiplicity x p ↔ IsRoot p x
-/
theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
  exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'
/-
**Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity** 是 Mathlib
 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : 
R[X]) (t : R) : p.rootMultiplicity t - 1 <= p.derivative.rootMultiplicity t
参数：p : R[X]；t : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.derivative_rootMultiplicity_of_root`：derivative_rootMultiplic
ity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) : p.derivative.ro
otMultiplicity t = p.rootMultiplicit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_zero`：rootMultiplicity_eq_zero {p : R[X]}
 {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · simp [rootMultiplicity_eq_zero h]
/-
**Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_of_isRoot_iterate_derivative [CharZero R] {p : R[X]} {
t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (derivative^[m] p).IsRoot 
t) : n < p.rootMultiplicity t
参数：h : p != 0；hroot : forall m <= n, (derivative^[m] p).IsRoot t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZe
roDivisors`：lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivis
ors {p : R[X]} {t : R} {n : Nat} (h : p != 0) (hroot : forall m <= n, (d…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t) :
    n < p.rootMultiplicity t :=
  lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 <| by positivity
/-
**Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial`。
形式化陈述：lt_rootMultiplicity_iff_isRoot_iterate_derivative [CharZero R] {p : R[X]} 
{t : R} {n : Nat} (h : p != 0) : n < p.rootMultiplicity t ↔ forall m <= n, (deri
vative^[m] p).IsRoot t
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity`：isRoot_iter
ate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : Nat} (hn : n < p.r
ootMultiplicity t) : (derivative^[n] p).IsRoot t
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative`：lt_rootMult
iplicity_of_isRoot_iterate_derivative [CharZero R] {p : R[X]} {t : R} {n : Nat} 
(h : p != 0) (hroot : forall m <= n, (derivative^…
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| Nat.lt_of_le_of_lt hm hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative h hr⟩

/-- A sufficient condition for the set of roots of a nonzero polynomial `f` to be a subset of the
set of roots of `g` is that `f` divides `f.derivative * g`. Over an algebraically closed field of
characteristic zero, this is also a necessary condition.
See `isRoot_of_isRoot_iff_dvd_derivative_mul` -/
/-
**Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：isRoot_of_isRoot_of_dvd_derivative_mul [CharZero R] {f g : R[X]} (hf0 : f 
!= 0) (hfd : f ∣ f.derivative * g) {a : R} (haf : f.IsRoot a) : g.IsRoot a
参数：hf0 : f != 0；hfd : f ∣ f.derivative * g；haf : f.IsRoot a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.eq_C_of_derivative_eq_zero`：eq_C_of_derivative_eq_zero (h : d
erivative p = 0) : p = C (p.coeff 0)
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
· 使用定理 `Polynomial.not_isRoot_C`：not_isRoot_C (r a : R) (hr : r != 0) : ¬IsRoot 
(C r) a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.C_ne_zero`：C_ne_zero : C a != 0 ↔ a != 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Nat.sub_eq_iff_eq_add`：∀ {b a c : ℕ}, b ≤ a → (a - b = c ↔ a = c + b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Polynomial.rootMultiplicity_pos`：rootMultiplicity_pos {p : R[X]} (hp : p
 != 0) {x : R} : 0 < rootMultiplicity x p ↔ IsRoot p x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.rootMultiplicity_mul`：rootMultiplicity_mul {p q : R[X]} {x : 
R} (hpq : p * q != 0) : rootMultiplicity x (p * q) = rootMultiplicity x p + root
Multiplicity x q
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.rootMultiplicity_eq_zero`：rootMultiplicity_eq_zero {p : R[X]}
 {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0
· 使用定理 `Polynomial.derivative_rootMultiplicity_of_root`：derivative_rootMultiplic
ity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) : p.derivative.ro
otMultiplicity t = p.rootMultiplicit…

--- 原说明 ---
A sufficient condition for the set of roots of a nonzero polynomial `f` to be a 
subset of the
set of roots of `g` is that `f` divides `f.derivative * g`. Over an algebraicall
y closed field of
characteristic zero, this is also a necessary condition.
See `isRoot_of_isRoot_iff_dvd_derivative_mul`
-/
theorem isRoot_of_isRoot_of_dvd_derivative_mul [CharZero R] {f g : R[X]} (hf0 : f ≠ 0)
    (hfd : f ∣ f.derivative * g) {a : R} (haf : f.IsRoot a) : g.IsRoot a := by
  rcases hfd with ⟨r, hr⟩
  have hdf0 : derivative f ≠ 0 := by
    contrapose haf
    rw [eq_C_of_derivative_eq_zero haf] at hf0 ⊢
    exact not_isRoot_C _ _ <| C_ne_zero.mp hf0
  by_contra hg
  have hdfg0 : f.derivative * g ≠ 0 := mul_ne_zero hdf0 (by rintro rfl; simp at hg)
  have hr' := congr_arg (rootMultiplicity a) hr
  have : IsDomain R := {}
  rw [rootMultiplicity_mul hdfg0, derivative_rootMultiplicity_of_root haf,
    rootMultiplicity_eq_zero hg, add_zero, rootMultiplicity_mul (hr ▸ hdfg0), add_comm,
    Nat.sub_eq_iff_eq_add (Nat.succ_le_iff.2 ((rootMultiplicity_pos hf0).2 haf))] at hr'
  lia
/-
**Polynomial.instNormalizationMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instNormalizationMonoid [NormalizationMonoid R] : NormalizationMonoid R[X]
 where normUnit p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormalizationMonoid [NormalizationMonoid R] : NormalizationMonoid R[X] where
  normUnit p :=
    ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← map_mul, Units.mul_inv, C_1], by rw [← map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_one := Units.ext (by simp)
  normUnit_mul_units u h := Units.ext <| by
    dsimp only [Units.val_mul]
    obtain ⟨_, ⟨w, rfl⟩, h2⟩ := isUnit_iff.1 ⟨u, rfl⟩
    rw [leadingCoeff_mul, ← h2, leadingCoeff_C, normUnit_mul_units _ (leadingCoeff_ne_zero.2 h),
      Units.eq_inv_mul_iff_mul_eq, Units.val_mul, C_mul, ← mul_assoc, ← h2, ← C_mul]
    simp
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [StrongNormalizationMonoid R] : StrongNormalizationMonoid R[X] where
  normUnit_mul hp0 hq0 :=
    Units.ext
      (by
        dsimp
        rw [Ne, ← leadingCoeff_eq_zero] at *
        simp_rw [normUnit, leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units := normUnit_coe_units

section NormalizationMonoid

variable [NormalizationMonoid R]

@[simp]
/-
**Polynomial.coe_normUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_normUnit {p : R[X]} : (normUnit p : R[X]) = C ↑(normUnit p.leadingCoef
f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_normUnit {p : R[X]} : (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff) := by
  simp [normUnit]

@[simp]
/-
**Polynomial.leadingCoeff_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_normalize (p : R[X]) : leadingCoeff (normalize p) = normalize
 (leadingCoeff p)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_normalize (p : R[X]) :
    leadingCoeff (normalize p) = normalize (leadingCoeff p) := by simp [normalize_apply]
/-
**Polynomial.Monic.normalize_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic
`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : NoZeroDivisors R] [inst_2 : N
ormalizationMonoid R] {p : Polynomial R},   p.Monic → normalize p = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `NormalizationMonoid.normUnit_one`：∀ {α : Type u_2} {inst : MonoidWithZer
o α} [self : NormalizationMonoid α], normUnit 1 = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Monic.normalize_eq_self {p : R[X]} (hp : p.Monic) : normalize p = p := by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]
/-
**Polynomial.roots_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_normalize {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p :
 R[X]} : (normalize p).roots = p.roots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem roots_normalize {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p : R[X]} :
    (normalize p).roots = p.roots := by
  rw [normalize_apply, mul_comm, coe_normUnit, roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]
/-
**Polynomial.normUnit_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：normUnit_X : normUnit (X : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
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
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `NormalizationMonoid.normUnit_one`：∀ {α : Type u_2} {inst : MonoidWithZer
o α} [self : NormalizationMonoid α], normUnit 1 = 1
· 使用定理 `Polynomial.leadingCoeff_X`：leadingCoeff_X : leadingCoeff (X : R[X]) = 1
-/
theorem normUnit_X : normUnit (X : R[X]) = 1 := by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this
/-
**Polynomial.X_eq_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_eq_normalize : X = normalize (X : R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.normUnit_X`：normUnit_X : normUnit (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem X_eq_normalize : X = normalize (X : R[X]) := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

end NormalizationMonoid

end IsDomain

section DivisionRing

variable [DivisionRing R] {p q : R[X]}

/-
**Polynomial.degree_pos_of_ne_zero_of_nonunit** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：degree_pos_of_ne_zero_of_nonunit (hp0 : p != 0) (hp : ¬IsUnit p) : 0 < deg
ree p
参数：hp0 : p != 0；hp : ¬IsUnit p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.C_inj`：C_inj : C a = C b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬IsUnit p) : 0 < degree p :=
  lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

end DivisionRing

section SimpleRing

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

@[simp]
/-
**Polynomial.map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsSimpleRing R] [inst_2 : Sem
iring S] [Nontrivial S] {p : Polynomial R}   (f : R →+* S), Polynomial.map f p =
 0 ↔ p = 0
参数：f : R →+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_eq_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
protected theorem map_eq_zero (f : R →+* S) : p.map f = 0 ↔ p = 0 :=
  Polynomial.map_eq_zero_iff f.injective
/-
**Polynomial.map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map f != 0
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.map_eq_zero`：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsS
impleRing R] [inst_2 : Semiring S] [Nontrivial S] {p : Polynomial R}   (f : R →+
* S), Polyno…
-/
theorem map_ne_zero {f : R →+* S} (hp : p ≠ 0) : p.map f ≠ 0 :=
  mt (Polynomial.map_eq_zero f).1 hp

@[simp]
/-
**Polynomial.degree_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).degree = p.degree
参数：p : R[X]；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
theorem degree_map (p : R[X]) (f : R →+* S) : (p.map f).degree = p.degree :=
  degree_map_eq_of_injective f.injective _

@[simp]
/-
**Polynomial.natDegree_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_map (f : R ->+* S) : (p.map f).natDegree = p.natDegree
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
theorem natDegree_map (f : R →+* S) : (p.map f).natDegree = p.natDegree :=
  natDegree_map_eq_of_injective f.injective _

@[simp]
/-
**Polynomial.leadingCoeff_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_map (f : R ->+* S) : (p.map f).leadingCoeff = f p.leadingCoef
f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
theorem leadingCoeff_map (f : R →+* S) : (p.map f).leadingCoeff = f p.leadingCoeff :=
  leadingCoeff_map_of_injective f.injective _
/-
**Polynomial.nextCoeff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_map_eq (p : R[X]) (f : R ->+* S) : (p.map f).nextCoeff = f p.nex
tCoeff
参数：p : R[X]；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.nextCoeff_map`：nextCoeff_map {f : R ->+* S} (hf : Function.In
jective f) (p : Polynomial R) : (p.map f).nextCoeff = f p.nextCoeff
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
theorem nextCoeff_map_eq (p : R[X]) (f : R →+* S) : (p.map f).nextCoeff = f p.nextCoeff :=
  nextCoeff_map f.injective _
/-
**Polynomial.monic_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsSimpleRing R] [inst_2 : Sem
iring S] [Nontrivial S] {f : R →+* S}   {p : Polynomial R}, (Polynomial.map f p)
.Monic ↔ p.Monic
参数：Polynomial.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.monic_map_iff`：∀ {R : Type u} {S : Type v} [inst : Se
miring R] [inst_1 : Semiring S] {f : R →+* S},   Function.Injective ⇑f → ∀ {p : 
Polynomial R}, p.Monic…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
@[simp] theorem monic_map_iff {f : R →+* S} {p : R[X]} : (p.map f).Monic ↔ p.Monic :=
  Function.Injective.monic_map_iff f.injective |>.symm

end SimpleRing

section Field

variable [Field R] {p q : R[X]}

/-
**Polynomial.isUnit_iff_degree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
-/
theorem isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 :=
  ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p ≤ 0 := by simp [*]
    have hc : coeff p 0 ≠ 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this, hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of_degree_le_zero this]
        rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩⟩

/-- Division of polynomials. See `Polynomial.divByMonic` for more details. -/
/-
**Polynomial.div** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：div (p q : R[X])
参数：p q : R[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division of polynomials. See `Polynomial.divByMonic` for more details.
-/
def div (p q : R[X]) :=
  C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))

/-- Remainder of polynomial division. See `Polynomial.modByMonic` for more details. -/
/-
**Polynomial.mod** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mod (p q : R[X])
参数：p q : R[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remainder of polynomial division. See `Polynomial.modByMonic` for more details.
-/
def mod (p q : R[X]) :=
  p %ₘ (q * C (leadingCoeff q)⁻¹)
/-
**Polynomial.quotient_mul_add_remainder_eq_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * div p q + mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * C q.leadingCoeff⁻¹)]
    rw [div, mod, add_comm, mul_assoc]
/-
**Polynomial.remainder_lt_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem remainder_lt_aux (p : R[X]) (hq : q ≠ 0) : degree (mod p q) < degree q := by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div R[X] :=
  ⟨div⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mod R[X] :=
  ⟨mod⟩
/-
**Polynomial.div_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  rfl
/-
**Polynomial.mod_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹) := rfl
/-
**Polynomial.modByMonic_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：modByMonic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q
参数：p : R[X]；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modByMonic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q :=
  show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]
/-
**Polynomial.divByMonic_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q
参数：p : R[X]；hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divByMonic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q :=
  show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]
/-
**Polynomial.mod_X_sub_C_eq_C_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - C a) = C (p.eval a)
参数：p : R[X]；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
· 使用定理 `Polynomial.modByMonic_eq_mod`：modByMonic_eq_mod (p : R[X]) (hq : Monic q
) : p %ₘ q = p % q
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - C a) = C (p.eval a) :=
  modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _
/-
**Polynomial.mul_div_eq_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_div_eq_iff_isRoot : (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mul_divByMonic_eq_iff_isRoot`：mul_divByMonic_eq_iff_isRoot : 
(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
· 使用定理 `Polynomial.divByMonic_eq_div`：divByMonic_eq_div (p : R[X]) (hq : Monic q
) : p /ₘ q = p / q
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem mul_div_eq_iff_isRoot : (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a :=
  divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot
/-
**Polynomial.instEuclideanDomain** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instEuclideanDomain : EuclideanDomain R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEuclideanDomain : EuclideanDomain R[X] :=
  { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := private quotient_mul_add_remainder_eq_aux
    remainder_lt := private fun _ _ hq => remainder_lt_aux _ hq
    mul_left_not_lt := fun _ _ hq => not_lt_of_ge (degree_le_mul_left _ hq) }
/-
**Polynomial.mod_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mod_eq_self_iff (hq0 : q != 0) : p % q = p ↔ degree p < degree q
参数：hq0 : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
· 使用定理 `Polynomial.mod_def`：mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
· 使用定理 `Polynomial.modByMonic.eq_1`：∀ {R : Type u} [inst : Ring R] (p q : Polyno
mial R), p %ₘ q = if hq : q.Monic then (p.divModByMonicAux hq).2 else p
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.div_wf_lemma`：div_wf_lemma (h : degree q <= degree p ∧ p != 0
) (hq : Monic q) : degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natD
egree q))) < …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.divModByMonicAux.eq_def`：∀ {R : Type u} [inst : Ring R] (x x_
1 : Polynomial R) (x_2 : x_1.Monic),   x.divModByMonicAux x_2 =     match x, x_1
, x_2 with     | p, q, h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mod_eq_self_iff (hq0 : q ≠ 0) : p % q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    have : ¬degree (q * C (leadingCoeff q)⁻¹) ≤ degree p :=
      not_le_of_gt <| by rwa [degree_mul_leadingCoeff_inv q hq0]
    rw [mod_def, modByMonic, dif_pos (monic_mul_leadingCoeff_inv hq0)]
    unfold divModByMonicAux
    dsimp
    simp only [this, false_and, if_false]⟩
/-
**Polynomial.div_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Field R] {p q : Polynomial R}, q ≠ 0 → (p / q = 0 ↔
 p.degree < q.degree)
参数：p / q = 0 ↔ p.degree < q.degree。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mod_eq_self_iff`：mod_eq_self_iff (hq0 : q != 0) : p % q = p ↔
 degree p < degree q
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.div_def`：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * 
C (leadingCoeff q)⁻¹))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.divByMonic_eq_zero_iff`：divByMonic_eq_zero_iff [Nontrivial R]
 (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
protected theorem div_eq_zero_iff (hq0 : q ≠ 0) : p / q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q
    rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
  fun h => by
    have hlt : degree p < degree (q * C (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leadingCoeff_inv q hq0]
    have hm : Monic (q * C (leadingCoeff q)⁻¹) := monic_mul_leadingCoeff_inv hq0
    rw [div_def, (divByMonic_eq_zero_iff hm).2 hlt, mul_zero]⟩
/-
**Polynomial.degree_add_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_div (hq0 : q != 0) (hpq : degree q <= degree p) : degree q + de
gree (p / q) = degree p
参数：hq0 : q != 0；hpq : degree q <= degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用引理 `Polynomial.degree_le_mul_left`：degree_le_mul_left (p : R[X]) (hq : q != 
0) : degree p <= degree (p * q)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.div_eq_zero_iff`：∀ {R : Type u} [inst : Field R] {p q : Polyn
omial R}, q ≠ 0 → (p / q = 0 ↔ p.degree < q.degree)
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
-/
theorem degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) :
    degree q + degree (p / q) = degree p := by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ ≤ _ := degree_le_mul_left _ (mt (Polynomial.div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))
  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q, degree_add_eq_left_of_degree_lt this, degree_mul]
/-
**Polynomial.degree_div_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_div_le (p q : R[X]) : degree (p / q) <= degree p
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `Polynomial.div_def`：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * 
C (leadingCoeff q)⁻¹))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
· 使用定理 `Polynomial.degree_divByMonic_le`：degree_divByMonic_le (p q : R[X]) : deg
ree (p /ₘ q) <= degree p
-/
theorem degree_div_le (p q : R[X]) : degree (p / q) ≤ degree p := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _
/-
**Polynomial.degree_div_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_div_lt (hp : p != 0) (hq : 0 < degree q) : degree (p / q) < degree 
p
参数：hp : p != 0；hq : 0 < degree q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.div_def`：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * 
C (leadingCoeff q)⁻¹))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
· 使用定理 `Polynomial.degree_divByMonic_lt`：degree_divByMonic_lt (p q : R[X]) (hp0 
: p != 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p
-/
theorem degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p := by
  have hq0 : q ≠ 0 := fun hq0 => by simp [hq0] at hq
  rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq0]
  exact degree_divByMonic_lt _ (q * C q.leadingCoeff⁻¹) hp
    (by rw [degree_mul_leadingCoeff_inv _ hq0]; exact hq)
/-
**Polynomial.isUnit_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_map [Field k] (f : R ->+* k) : IsUnit (p.map f) ↔ IsUnit p
参数：f : R ->+* k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_map [Field k] (f : R →+* k) : IsUnit (p.map f) ↔ IsUnit p := by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]
/-
**Polynomial.map_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_div [Field k] (f : R ->+* k) : (p / q).map f = p.map f / q.map f
参数：f : R ->+* k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.div_def`：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * 
C (leadingCoeff q)⁻¹))
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_divByMonic`：map_divByMonic [Ring S] (f : R ->+* S) (hq : 
Monic q) : (p /ₘ q).map f = p.map f /ₘ q.map f
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem map_div [Field k] (f : R →+* k) : (p / q).map f = p.map f / q.map f := by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def, div_def, Polynomial.map_mul, map_divByMonic f (monic_mul_leadingCoeff_inv hq0),
      Polynomial.map_mul, map_C, leadingCoeff_map, map_inv₀]
/-
**Polynomial.map_mod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_mod [Field k] (f : R ->+* k) : (p % q).map f = p.map f % q.map f
参数：f : R ->+* k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.mod_zero`：mod_zero (a : R) : a % 0 = a
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.mod_def`：mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_modByMonic`：map_modByMonic [Ring S] (f : R ->+* S) (hq : 
Monic q) : (p %ₘ q).map f = p.map f %ₘ q.map f
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
-/
theorem map_mod [Field k] (f : R →+* k) : (p % q).map f = p.map f % q.map f := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]
/-
**Polynomial.natDegree_mod_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mod_lt [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree != 0) :
 (p % q).natDegree < q.natDegree
参数：p : k[X]；hq : q.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.mod_def`：mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.natDegree_modByMonic_lt`：natDegree_modByMonic_lt (p : R[X]) {
q : R[X]} (hmq : Monic q) (hq : q != 1) : natDegree (p %ₘ q) < q.natDegree
· 使用定理 `Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one`：monic_mul_C_of_leadin
gCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) : Monic (p * C b)
· 使用引理 `mul_inv_eq_one₀`：mul_inv_eq_one₀ (hb : b != 0) : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_mul_C_eq_of_mul_eq_one`：natDegree_mul_C_eq_of_mul_e
q_one {ai : R} (au : a * ai = 1) : (p * C a).natDegree = p.natDegree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_mul_eq_one₀`：inv_mul_eq_one₀ (ha : a != 0) : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.natDegree_mul_C_le`：natDegree_mul_C_le (f : R[X]) (a : R) : (
f * C a).natDegree <= f.natDegree
-/
lemma natDegree_mod_lt [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree ≠ 0) :
    (p % q).natDegree < q.natDegree := by
  have hq' : q.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_ne_zero]
    contrapose hq
    simp [hq]
  rw [mod_def]
  refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rw [mul_inv_eq_one₀ hq']
  · contrapose hq
    rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
    simp [hq]
  · exact natDegree_mul_C_le q q.leadingCoeff⁻¹
/-
**Polynomial.degree_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mod_lt (p : R[X]) {q : R[X]} (hq : q != 0) : (p % q).degree < q.deg
ree
参数：p : R[X]；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mod_def`：mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_add_degree_leadingCoeff_inv`：∀ {K : Type u_1} [inst : 
DivisionRing K] (p : Polynomial K),   p.degree + (Polynomial.C p.leadingCoeff⁻¹)
.degree = p.degree
-/
theorem degree_mod_lt (p : R[X]) {q : R[X]} (hq : q ≠ 0) : (p % q).degree < q.degree := by
  rw [Polynomial.mod_def]
  refine (Polynomial.degree_modByMonic_lt p ?_).trans_eq (by simp)
  simp [Polynomial.Monic.def, hq]
/-
**Polynomial.add_mod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：add_mod (p₁ p₂ q : R[X]) : (p₁ + p₂) % q = p₁ % q + p₂ % q
参数：p₁ p₂ q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.add_modByMonic`：add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ 
q = p₁ %ₘ q + p₂ %ₘ q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_mod (p₁ p₂ q : R[X]) : (p₁ + p₂) % q = p₁ % q + p₂ % q := by
  simp [Polynomial.mod_def, Polynomial.add_modByMonic]
/-
**Polynomial.sub_mod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sub_mod (p₁ p₂ q : R[X]) : (p₁ - p₂) % q = p₁ % q - p₂ % q
参数：p₁ p₂ q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.sub_modByMonic`：sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %
ₘ q = p₁ %ₘ q - p₂ %ₘ q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_mod (p₁ p₂ q : R[X]) : (p₁ - p₂) % q = p₁ % q - p₂ % q := by
  simp [Polynomial.mod_def, Polynomial.sub_modByMonic]
/-
**Polynomial.mul_mod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_mod (p₁ p₂ q : R[X]) : (p₁ * p₂) % q = (p₁ % q) * (p₂ % q) % q
参数：p₁ p₂ q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.mul_modByMonic`：mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %
ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q
-/
theorem mul_mod (p₁ p₂ q : R[X]) : (p₁ * p₂) % q = (p₁ % q) * (p₂ % q) % q := by
  simp_rw [Polynomial.mod_def]
  apply Polynomial.mul_modByMonic

section

open EuclideanDomain

/-
**Polynomial.gcd_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f : R ->+* k) : gcd (p.
map f) (q.map f) = (gcd p q).map f
参数：f : R ->+* k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction`：∀ {R : Type u} [inst : EuclideanDomain R]
 {P : R → R → Prop} (a b : R),   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b
 % a) a → P a b) → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanDomain.gcd_val`：gcd_val (a b : R) : gcd a b = gcd (b % a) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_mod`：map_mod [Field k] (f : R ->+* k) : (p % q).map f = p
.map f % q.map f
-/
theorem gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f : R →+* k) :
    gcd (p.map f) (q.map f) = (gcd p q).map f :=
  GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]

end

/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_gcd_eq_zero [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0)
    (hg : g.eval₂ ϕ α = 0) : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 := by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, hf, hg, zero_mul, zero_mul, zero_add]
/-
**Polynomial.eval_gcd_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_gcd_eq_zero [DecidableEq R] {f g : R[X]} {α : R} (hf : f.eval α = 0) 
(hg : g.eval α = 0) : (EuclideanDomain.gcd f g).eval α = 0
参数：hf : f.eval α = 0；hg : g.eval α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_gcd_eq_zero`：eval₂_gcd_eq_zero [CommSemiring k] [Decida
bleEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0) (hg : g.eval
₂ ϕ α = 0) : (Eucl…
-/
theorem eval_gcd_eq_zero [DecidableEq R] {f g : R[X]} {α : R}
    (hf : f.eval α = 0) (hg : g.eval α = 0) : (EuclideanDomain.gcd f g).eval α = 0 :=
  eval₂_gcd_eq_zero hf hg
/-
**Polynomial.root_left_of_root_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：root_left_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g
 : R[X]} {α : k} (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 
0
参数：hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.gcd_dvd_left`：gcd_dvd_left (a b : R) : gcd a b ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem root_left_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 0 := by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_left f g
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]
/-
**Polynomial.root_right_of_root_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：root_right_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f 
g : R[X]} {α : k} (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α =
 0
参数：hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.gcd_dvd_right`：gcd_dvd_right (a b : R) : gcd a b ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem root_right_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α = 0 := by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_right f g
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]
/-
**Polynomial.root_gcd_iff_root_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：root_gcd_iff_root_left_right [CommSemiring k] [DecidableEq R] {ϕ : R ->+* 
k} {f g : R[X]} {α : k} : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α 
= 0 ∧ g.eval₂ ϕ α = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.root_left_of_root_gcd`：root_left_of_root_gcd [CommSemiring k]
 [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k} (hα : (EuclideanDomain.gcd 
f g).eval₂ ϕ α = 0) : …
· 使用定理 `Polynomial.root_right_of_root_gcd`：root_right_of_root_gcd [CommSemiring 
k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k} (hα : (EuclideanDomain.gc
d f g).eval₂ ϕ α = 0) :…
· 使用定理 `Polynomial.eval₂_gcd_eq_zero`：eval₂_gcd_eq_zero [CommSemiring k] [Decida
bleEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0) (hg : g.eval
₂ ϕ α = 0) : (Eucl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem root_gcd_iff_root_left_right [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} :
    (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α = 0 ∧ g.eval₂ ϕ α = 0 :=
  ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩
/-
**Polynomial.isRoot_gcd_iff_isRoot_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：isRoot_gcd_iff_isRoot_left_right [DecidableEq R] {f g : R[X]} {α : R} : (E
uclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.root_gcd_iff_root_left_right`：root_gcd_iff_root_left_right [C
ommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k} : (EuclideanD
omain.gcd f g).eval₂ ϕ α = 0 …
-/
theorem isRoot_gcd_iff_isRoot_left_right [DecidableEq R] {f g : R[X]} {α : R} :
    (EuclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α :=
  root_gcd_iff_root_left_right
/-
**Polynomial.isCoprime_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isCoprime_map [Field k] (f : R ->+* k) : IsCoprime (p.map f) (q.map f) ↔ I
sCoprime p q
参数：f : R ->+* k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.gcd_isUnit_iff`：gcd_isUnit_iff [DecidableEq α] {x y : α}
 : IsUnit (gcd x y) ↔ IsCoprime x y
· 使用定理 `Polynomial.gcd_map`：gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f
 : R ->+* k) : gcd (p.map f) (q.map f) = (gcd p q).map f
· 使用定理 `Polynomial.isUnit_map`：isUnit_map [Field k] (f : R ->+* k) : IsUnit (p.m
ap f) ↔ IsUnit p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoprime_map [Field k] (f : R →+* k) : IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff, ← EuclideanDomain.gcd_isUnit_iff, gcd_map, isUnit_map]
/-
**Polynomial.mem_roots_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots_map [CommRing k] [IsDomain k] {f : R ->+* k} {x : k} (hp : p != 
0) : x in (p.map f).roots ↔ p.eval₂ f x = 0
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_roots_map [CommRing k] [IsDomain k] {f : R →+* k} {x : k} (hp : p ≠ 0) :
    x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots (map_ne_zero hp), IsRoot, Polynomial.eval_map]
/-
**Polynomial.rootSet_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_monomial [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n
 != 0) {a : R} (ha : a != 0) : (monomial n a).rootSet S = {0}
参数：hn : n != 0；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Polynomial.aroots_monomial`：aroots_monomial [IsDomain T] [CommRing S] [I
sDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (ha : a != 0) (n : N
at) : (monomial …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
-/
theorem rootSet_monomial [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R}
    (ha : a ≠ 0) : (monomial n a).rootSet S = {0} := by
  classical
  rw [rootSet, aroots_monomial ha,
    Multiset.toFinset_nsmul _ _ hn, Multiset.toFinset_singleton, Finset.coe_singleton]
/-
**Polynomial.rootSet_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn 
: n != 0) {a : R} (ha : a != 0) : rootSet (C a * X ^ n) S = {0}
参数：hn : n != 0；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.rootSet_monomial`：rootSet_monomial [CommRing S] [IsDomain S] 
[Algebra R S] {n : Nat} (hn : n != 0) {a : R} (ha : a != 0) : (monomial n a).roo
tSet S = {0}
-/
theorem rootSet_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R}
    (ha : a ≠ 0) : rootSet (C a * X ^ n) S = {0} := by
  rw [C_mul_X_pow_eq_monomial, rootSet_monomial hn ha]
/-
**Polynomial.rootSet_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n !=
 0) : (X ^ n : R[X]).rootSet S = {0}
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.rootSet_C_mul_X_pow`：rootSet_C_mul_X_pow [CommRing S] [IsDoma
in S] [Algebra R S] {n : Nat} (hn : n != 0) {a : R} (ha : a != 0) : rootSet (C a
 * X ^ n) S = {0}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem rootSet_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) :
    (X ^ n : R[X]).rootSet S = {0} := by
  rw [← one_mul (X ^ n : R[X]), ← C_1, rootSet_C_mul_X_pow hn]
  exact one_ne_zero
/-
**Polynomial.rootSet_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_prod [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι ->
 R[X]) (s : Finset ι) (h : s.prod f != 0) : (s.prod f).rootSet S = ⋃ i in s, (f 
i).rootSet S
参数：f : ι -> R[X]；s : Finset ι；h : s.prod f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Polynomial.roots_prod`：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finse
t ι) : s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.map_eq_zero`：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsS
impleRing R] [inst_2 : Semiring S] [Nontrivial S] {p : Polynomial R}   (f : R →+
* S), Polyno…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Finset.bind_toFinset`：bind_toFinset [DecidableEq α] (s : Multiset α) (t 
: α -> Multiset β) : (s.bind t).toFinset = s.toFinset.biUnion fun a => (t a).toF
inset
· 使用定理 `Finset.val_toFinset`：val_toFinset [DecidableEq α] (s : Finset α) : s.val
.toFinset = s
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
-/
theorem rootSet_prod [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι → R[X])
    (s : Finset ι) (h : s.prod f ≠ 0) : (s.prod f).rootSet S = ⋃ i ∈ s, (f i).rootSet S := by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod, roots_prod, Finset.bind_toFinset, s.val_toFinset, Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, Polynomial.map_eq_zero]
/-
**Polynomial.roots_C_mul_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_C_mul_X_sub_C (b : R) (ha : a != 0) : (C a * X - C b).roots = {a⁻¹ *
 b}
参数：b : R；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_C_mul_X_sub_C_of_IsUnit`：roots_C_mul_X_sub_C_of_IsUnit 
(b : R) (a : Rˣ) : (C (a : R) * X - C b).roots = {a⁻¹ * b}
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_C_mul_X_sub_C (b : R) (ha : a ≠ 0) : (C a * X - C b).roots = {a⁻¹ * b} := by
  simp [roots_C_mul_X_sub_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]
/-
**Polynomial.roots_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_C_mul_X_add_C (b : R) (ha : a != 0) : (C a * X + C b).roots = {-(a⁻¹
 * b)}
参数：b : R；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_C_mul_X_add_C_of_IsUnit`：roots_C_mul_X_add_C_of_IsUnit 
(b : R) (a : Rˣ) : (C (a : R) * X + C b).roots = {-(a⁻¹ * b)}
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_C_mul_X_add_C (b : R) (ha : a ≠ 0) : (C a * X + C b).roots = {-(a⁻¹ * b)} := by
  simp [roots_C_mul_X_add_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]
/-
**Polynomial.roots_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_degree_eq_one (h : degree p = 1) : p.roots = {-((p.coeff 1)⁻¹ * p.co
eff 0)}
参数：h : degree p = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_X_add_C_of_degree_le_one`：eq_X_add_C_of_degree_le_one (h :
 degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.coeff_ne_zero_of_eq_degree`：coeff_ne_zero_of_eq_degree (hn : 
degree p = n) : coeff p n != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.roots_C_mul_X_add_C`：roots_C_mul_X_add_C (b : R) (ha : a != 0
) : (C a * X + C b).roots = {-(a⁻¹ * b)}
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_degree_eq_one (h : degree p = 1) : p.roots = {-((p.coeff 1)⁻¹ * p.coeff 0)} := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  have : p.coeff 1 ≠ 0 := coeff_ne_zero_of_eq_degree h
  simp [roots_C_mul_X_add_C _ this]
/-
**Polynomial.exists_root_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：exists_root_of_degree_eq_one (h : degree p = 1) : exists x, IsRoot p x
参数：h : degree p = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots_degree_eq_one`：roots_degree_eq_one (h : degree p = 1) :
 p.roots = {-((p.coeff 1)⁻¹ * p.coeff 0)}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, IsRoot p x :=
  ⟨-((p.coeff 1)⁻¹ * p.coeff 0), by
    rw [← mem_roots (by simp [← zero_le_degree_iff, h])]
    simp [roots_degree_eq_one h]⟩
/-
**Polynomial.coeff_inv_units** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_inv_units (u : R[X]ˣ) (n : Nat) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : 
R[X]).coeff n
参数：u : R[X]ˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
· 使用引理 `Polynomial.degree_coe_units`：degree_coe_units [Nontrivial R] (u : R[X]ˣ)
 : degree (u : R[X]) = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `div_eq_iff_mul_eq`：div_eq_iff_mul_eq (hb : b != 0) : a / b = c ↔ c * b =
 a
· 使用定理 `Polynomial.coeff_coe_units_zero_ne_zero`：coeff_coe_units_zero_ne_zero [N
ontrivial R] (u : R[X]ˣ) : coeff (u : R[X]) 0 != 0
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem coeff_inv_units (u : R[X]ˣ) (n : ℕ) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  · simp
/-
**Polynomial.monic_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_normalize [DecidableEq R] (hp0 : p != 0) : Monic (normalize p)
参数：hp0 : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Polynomial.leadingCoeff_normalize`：leadingCoeff_normalize (p : R[X]) : l
eadingCoeff (normalize p) = normalize (leadingCoeff p)
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem monic_normalize [DecidableEq R] (hp0 : p ≠ 0) : Monic (normalize p) := by
  rw [Ne, ← leadingCoeff_eq_zero, ← Ne, ← isUnit_iff_ne_zero] at hp0
  rw [Monic, leadingCoeff_normalize, normalize_eq_one]
  apply hp0
/-
**Polynomial.normalize_eq_self_iff_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：normalize_eq_self_iff_monic [DecidableEq R] {p : R[X]} (hp : p != 0) : nor
malize p = p ↔ p.Monic
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.monic_normalize`：monic_normalize [DecidableEq R] (hp0 : p != 
0) : Monic (normalize p)
· 使用定理 `Polynomial.Monic.normalize_eq_self`：∀ {R : Type u} [inst : CommRing R] [
inst_1 : NoZeroDivisors R] [inst_2 : NormalizationMonoid R] {p : Polynomial R}, 
  p.Monic → normalize p …
-/
theorem normalize_eq_self_iff_monic [DecidableEq R] {p : R[X]} (hp : p ≠ 0) :
    normalize p = p ↔ p.Monic :=
  ⟨fun h ↦ h ▸ monic_normalize hp, fun h ↦ Monic.normalize_eq_self h⟩
/-
**Polynomial.leadingCoeff_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_div (hpq : q.degree <= p.degree) : (p / q).leadingCoeff = p.l
eadingCoeff / q.leadingCoeff
参数：hpq : q.degree <= p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.div_def`：div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * 
C (leadingCoeff q)⁻¹))
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `Polynomial.leadingCoeff_divByMonic_of_monic`：leadingCoeff_divByMonic_of_
monic (hmonic : q.Monic) (hdegree : q.degree <= p.degree) : (p /ₘ q).leadingCoef
f = p.leadingCoeff
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem leadingCoeff_div (hpq : q.degree ≤ p.degree) :
    (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _, mul_comm,
    div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]
/-
**Polynomial.div_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：div_C_mul : p / (C a * q) = C a⁻¹ * (p / q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem div_C_mul : p / (C a * q) = C a⁻¹ * (p / q) := by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q, ← mul_assoc, ← C.map_mul, mul_inv_cancel₀ ha, C.map_one, one_mul]
/-
**Polynomial.div_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：div_C : p / C a = p * C a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `EuclideanDomain.div_one`：div_one (p : R) : p / 1 = p
· 使用定理 `Polynomial.div_C_mul`：div_C_mul : p / (C a * q) = C a⁻¹ * (p / q)
-/
lemma div_C : p / C a = p * C a⁻¹ := by
  simpa [mul_comm] using div_C_mul (q := 1)
/-
**Polynomial.C_div** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：C_div : C (a / b) = C a / C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.div_C`：div_C : p / C a = p * C a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma C_div : C (a / b) = C a / C b := by
  rw [div_C, ← C_mul, div_eq_mul_inv]
/-
**Polynomial.C_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem C_mul_dvd (ha : a ≠ 0) : C a * p ∣ q ↔ p ∣ q :=
  ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_assoc, mul_left_comm p, ← mul_assoc, ← C.map_mul, mul_inv_cancel₀ ha, C.map_one,
        one_mul, hr]⟩⟩
/-
**Polynomial.dvd_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dvd_C_mul (ha : a != 0) : p ∣ Polynomial.C a * q ↔ p ∣ q
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
-/
theorem dvd_C_mul (ha : a ≠ 0) : p ∣ Polynomial.C a * q ↔ p ∣ q :=
  ⟨fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_left_comm p, ← hr, ← mul_assoc, ← C.map_mul, inv_mul_cancel₀ ha, C.map_one,
        one_mul]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩
/-
**Polynomial.coe_normUnit_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_normUnit_of_ne_zero [DecidableEq R] (hp : p != 0) : (normUnit p : R[X]
) = C p.leadingCoeff⁻¹
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用定理 `CommGroupWithZero.coe_normUnit`：coe_normUnit {a : G₀} (h0 : a != 0) : (↑
(normUnit a) : G₀) = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_normUnit_of_ne_zero [DecidableEq R] (hp : p ≠ 0) :
    (normUnit p : R[X]) = C p.leadingCoeff⁻¹ := by
  have : p.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  simp [CommGroupWithZero.coe_normUnit _ this]
/-
**Polynomial.map_dvd_map'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x
 ∣ y
参数：f : R ->+* k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Polynomial.map_eq_zero`：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsS
impleRing R] [inst_2 : Semiring S] [Nontrivial S] {p : Polynomial R}   (f : R →+
* S), Polyno…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `normalize_dvd_iff`：normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `Polynomial.coe_normUnit_of_ne_zero`：coe_normUnit_of_ne_zero [DecidableEq
 R] (hp : p != 0) : (normUnit p : R[X]) = C p.leadingCoeff⁻¹
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_dvd_map`：map_dvd_map [Ring S] (f : R ->+* S) (hf : Functi
on.Injective f) {x y : R[X]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
-/
theorem map_dvd_map' [Field k] (f : R →+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y := by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, Polynomial.map_eq_zero]
  · classical
    rw [← normalize_dvd_iff, ← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (Polynomial.map_eq_zero f).1 H),
      leadingCoeff_map, ← map_inv₀ f, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leadingCoeff_inv H)]

@[simp]
/-
**Polynomial.degree_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_normalize [DecidableEq R] : degree (normalize p) = degree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_normalize [DecidableEq R] : degree (normalize p) = degree p := by
  simp [normalize_apply]
/-
**Polynomial.prime_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p
参数：hp1 : degree p = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Monic.prime_of_degree_eq_one`：∀ {R : Type u} [inst : CommRing
 R] [IsDomain R] {p : Polynomial R}, p.degree = 1 → p.Monic → Prime p
· 使用定理 `Polynomial.degree_normalize`：degree_normalize [DecidableEq R] : degree (
normalize p) = degree p
· 使用定理 `Polynomial.monic_normalize`：monic_normalize [DecidableEq R] (hp0 : p != 
0) : Monic (normalize p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Associated.prime`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {p q : 
M}, Associated p q → Prime p → Prime q
· 使用定理 `normalize_associated`：normalize_associated (x : α) : Associated (normali
ze x) x
-/
theorem prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p := by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 ↦ absurd hp1 (by simp [hp0]))
  exact (normalize_associated _).prime this
/-
**Polynomial.irreducible_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p
参数：hp1 : degree p = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.prime_of_degree_eq_one`：prime_of_degree_eq_one (hp1 : degree 
p = 1) : Prime p
-/
theorem irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p :=
  (prime_of_degree_eq_one hp1).irreducible
/-
**Polynomial.not_irreducible_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_irreducible_C (x : R) : ¬Irreducible (C x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `not_irreducible_zero`：not_irreducible_zero [MonoidWithZero M] : ¬Irreduc
ible (0 : M) | ⟨hn0, h⟩ => have : IsUnit (0 : M) ∨ IsUnit (0 : M)
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
-/
theorem not_irreducible_C (x : R) : ¬Irreducible (C x) := by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
  · exact fun hx => hx.not_isUnit <| isUnit_C.2 <| isUnit_iff_ne_zero.2 H
/-
**Polynomial.degree_pos_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree
参数：hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.not_irreducible_C`：not_irreducible_C (x : R) : ¬Irreducible (
C x)
-/
theorem degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree :=
  lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
    not_irreducible_C (p.coeff 0) <| this ▸ hp
/-
**Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Ring K] (f : K[X]) (
a : K) : (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a)
参数：f : K[X]；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
-/
theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Ring K] (f : K[X]) (a : K) :
    (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', modByMonic_eq_sub_mul_div]
/-
**Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative** 是 
Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative {K : Type*}
 [CommRing K] (f : K[X]) (a : K) : f /ₘ (X - C a) + (X - C a) * derivative (f /ₘ
 (X - C a)) = derivative f
参数：f : K[X]；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic`：X_sub_C_mul_divByMo
nic_eq_sub_modByMonic {K : Type*} [Ring K] (f : K[X]) (a : K) : (X - C a) * (f /
ₘ (X - C a)) = f - f %ₘ (X - C a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
-/
theorem divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
    {K : Type*} [CommRing K] (f : K[X]) (a : K) :
    f /ₘ (X - C a) + (X - C a) * derivative (f /ₘ (X - C a)) = derivative f := by
  have key := by apply congrArg derivative <| X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    modByMonic_X_sub_C_eq_C_eval] using key
/-
**Polynomial.X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f 
: K[X]) {a : K} (hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ derivative f
参数：f : K[X]；hf : (X - C a) ∣ f /ₘ (X - C a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivativ
e`：divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative {K : Type*} [C
ommRing K] (f : K[X]) (a : K) : f /ₘ (X - C a) + (X - C a) * de…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K}
    (hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ derivative f := by
  have key := divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key, hu, ← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
/-
**Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：isCoprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [Field K] (f :
 K[X]) (a : K) (hf' : f.derivative.eval a != 0) : IsCoprime (X - C a : K[X]) (f 
/ₘ (X - C a))
参数：f : K[X]；a : K；hf' : f.derivative.eval a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `EuclideanDomain.dvd_or_coprime`：dvd_or_coprime (x y : α) (h : Irreducibl
e x) : x ∣ y ∨ IsCoprime x y
· 使用定理 `Polynomial.irreducible_of_degree_eq_one`：irreducible_of_degree_eq_one (h
p1 : degree p = 1) : Irreducible p
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Polynomial.X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic`：X_sub_C_dvd
_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K} (
hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ deri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_inj`：C_inj : C a = C b ↔ a = b
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.modByMonic_X_sub_C_eq_C_eval`：modByMonic_X_sub_C_eq_C_eval (p
 : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a)
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)

--- 原说明 ---
If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)
`.
-/
theorem isCoprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [Field K] (f : K[X]) (a : K)
    (hf' : f.derivative.eval a ≠ 0) : IsCoprime (X - C a : K[X]) (f /ₘ (X - C a)) := by
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose hf' with h
  have : X - C a ∣ derivative f := X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval] at this
  rwa [← C_inj, C_0]

/-- To check a polynomial over a field is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
/-
**Polynomial.irreducible_iff_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_iff_degree_lt (p : R[X]) (hp0 : p != 0) (hpu : ¬ IsUnit p) : I
rreducible p ↔ forall q, q.degree <= ↑(natDegree p / 2) -> q ∣ p -> IsUnit q
参数：p : R[X]；hp0 : p != 0；hpu : ¬ IsUnit p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.irreducible_mul_leadingCoeff_inv`：irreducible_mul_leadingCoef
f_inv {p : K[X]} : Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p
· 使用定理 `Polynomial.Monic.irreducible_iff_degree_lt`：∀ {R : Type u} [inst : CommR
ing R] [IsDomain R] {p : Polynomial R},   p.Monic → p ≠ 1 → (Irreducible p ↔ ∀ (
q : Polynomial R), q.degree ≤ ↑(…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.natDegree_mul_leadingCoeff_inv`：natDegree_mul_leadingCoeff_in
v (p : K[X]) {q : K[X]} (h : q != 0) : natDegree (p * C (leadingCoeff q)⁻¹) = na
tDegree p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsLocalHomOfMonoidWithZeroHomClassOfNontrivial`：∀ {M₀ : Type u_2} {G
₀ : Type u_3} {F : Type u_6} [inst : MonoidWithZero M₀] [inst_1 : GroupWithZero 
G₀]   [inst_2 : FunLike F G₀ M₀] [Monoid…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
To check a polynomial over a field is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem irreducible_iff_degree_lt (p : R[X]) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ ∀ q, q.degree ≤ ↑(natDegree p / 2) → q ∣ p → IsUnit q := by
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_degree_lt]
  · simp [hp0, natDegree_mul_leadingCoeff_inv]
  · contrapose hpu
    exact .of_mul_eq_one _ hpu

/-- To check a polynomial `p` over a field is irreducible, it suffices to check there are no
divisors of degree `0 < d ≤ degree p / 2`.

See also: `Polynomial.Monic.irreducible_iff_natDegree'`.
-/
/-
**Polynomial.irreducible_iff_lt_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：irreducible_iff_lt_natDegree_lt {p : R[X]} (hp0 : p != 0) (hpu : ¬ IsUnit 
p) : Irreducible p ↔ forall q, Monic q -> natDegree q in Finset.Ioc 0 (natDegree
 p / 2) -> ¬ q ∣ p
参数：hp0 : p != 0；hpu : ¬ IsUnit p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.irreducible_mul_leadingCoeff_inv`：irreducible_mul_leadingCoef
f_inv {p : K[X]} : Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p
· 使用定理 `Polynomial.Monic.irreducible_iff_lt_natDegree_lt`：∀ {R : Type u} [inst :
 CommSemiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     p ≠ 1 → 
(Irreducible p ↔ ∀ (q : Polynomial R),…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.natDegree_mul_leadingCoeff_inv`：natDegree_mul_leadingCoeff_in
v (p : K[X]) {q : K[X]} (h : q != 0) : natDegree (p * C (leadingCoeff q)⁻¹) = na
tDegree p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsUnit.dvd_mul_right`：dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
To check a polynomial `p` over a field is irreducible, it suffices to check ther
e are no
divisors of degree `0 < d ≤ degree p / 2`.

See also: `Polynomial.Monic.irreducible_iff_natDegree'`.
-/
theorem irreducible_iff_lt_natDegree_lt {p : R[X]} (hp0 : p ≠ 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  have : p * C (leadingCoeff p)⁻¹ ≠ 1 := by
    contrapose hpu
    exact .of_mul_eq_one _ hpu
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this,
      natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (isUnit_C.mpr (IsUnit.mk0 (leadingCoeff p)⁻¹ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))]

open UniqueFactorizationMonoid in
/--
The normalized factors of a polynomial over a field times its leading coefficient give
the polynomial.
-/
/-
**Polynomial.leadingCoeff_mul_prod_normalizedFactors** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：leadingCoeff_mul_prod_normalizedFactors [DecidableEq R] (a : R[X]) : C a.l
eadingCoeff * (normalizedFactors a).prod = a
参数：a : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.congr_simp`：∀ {α : Type u_1}
 [inst : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : Unique
FactorizationMonoid α]   (a a_1 : α), a = a_…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors_eq`：prod_normalizedFact
ors_eq {α} [CommMonoidWithZero α] [StrongNormalizationMonoid α] [UniqueFactoriza
tionMonoid α] {a : α} (ane0 : a != 0) : (…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `Polynomial.coe_normUnit`：coe_normUnit {p : R[X]} : (normUnit p : R[X]) =
 C ↑(normUnit p.leadingCoeff)
· 使用定理 `CommGroupWithZero.coe_normUnit`：coe_normUnit {a : G₀} (h0 : a != 0) : (↑
(normUnit a) : G₀) = a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The normalized factors of a polynomial over a field times its leading coefficien
t give
the polynomial.
-/
theorem leadingCoeff_mul_prod_normalizedFactors [DecidableEq R] (a : R[X]) :
    C a.leadingCoeff * (normalizedFactors a).prod = a := by
  by_cases ha : a = 0
  · simp [ha]
  rw [prod_normalizedFactors_eq, normalize_apply, coe_normUnit, CommGroupWithZero.coe_normUnit,
    mul_comm, mul_assoc, ← map_mul, inv_mul_cancel₀] <;>
  simp_all

open UniqueFactorizationMonoid in
/-
**Polynomial.mem_normalizedFactors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Field R] {p q : Polynomial R} [inst_1 : DecidableEq
 R],   q ≠ 0 → (p ∈ UniqueFactorizationMonoid.normalizedFactors q ↔ Irreducible 
p ∧ p.Monic ∧ p ∣ q)
参数：p ∈ UniqueFactorizationMonoid.normalizedFactors q ↔ Irreducible p ∧ p.Monic ∧
 p ∣ q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`：zero_notMem_nor
malizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
· 使用定理 `UniqueFactorizationMonoid.mem_normalizedFactors_iff'`：mem_normalizedFact
ors_iff' {p x : α} (h : x != 0) : p in normalizedFactors x ↔ Irreducible p ∧ nor
malize p = p ∧ p ∣ x
· 使用定理 `Polynomial.normalize_eq_self_iff_monic`：normalize_eq_self_iff_monic [Dec
idableEq R] {p : R[X]} (hp : p != 0) : normalize p = p ↔ p.Monic
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mem_normalizedFactors_iff [DecidableEq R] (hq : q ≠ 0) :
    p ∈ normalizedFactors q ↔ Irreducible p ∧ p.Monic ∧ p ∣ q := by
  by_cases hp : p = 0
  · simpa [hp] using zero_notMem_normalizedFactors _
  · rw [mem_normalizedFactors_iff' hq, normalize_eq_self_iff_monic hp]

variable (p) in
@[simp]
/-
**Polynomial.map_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_normalize [DecidableEq R] [Field S] [DecidableEq S] (f : R ->+* S) : m
ap f (normalize p) = normalize (map f p)
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Units.mk.congr_simp`：∀ {α : Type u} [inst : Monoid α] (val val_1 : α) (e
_val : val = val_1) (inv inv_1 : α) (e_inv : inv = inv_1)   (val_inv : val * inv
 = 1) (in…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
-/
theorem map_normalize [DecidableEq R] [Field S] [DecidableEq S] (f : R →+* S) :
    map f (normalize p) = normalize (map f p) := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [normalize_apply, Polynomial.map_mul, normUnit, hp]
/-
**Polynomial.monic_mapAlg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_mapAlg_iff [Semiring S] [Nontrivial S] [Algebra R S] {p : R[X]} : (m
apAlg R S p).Monic ↔ p.Monic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monic_mapAlg_iff [Semiring S] [Nontrivial S] [Algebra R S] {p : R[X]} :
    (mapAlg R S p).Monic ↔ p.Monic := by
  simp [mapAlg_eq_map, monic_map_iff]
/-
**Polynomial.mod_eq_of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mod_eq_of_dvd_sub {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂) : p₁ % q = p₂ % q
参数：h : q ∣ p₁ - p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.mod_zero`：mod_zero (a : R) : a % 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.modByMonic_eq_of_dvd_sub`：modByMonic_eq_of_dvd_sub (hq : q.Mo
nic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.C_mul_dvd`：C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q
-/
theorem mod_eq_of_dvd_sub {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂) : p₁ % q = p₂ % q := by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  apply Polynomial.modByMonic_eq_of_dvd_sub (by simp [Polynomial.Monic.def, hq])
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

end Field

end Polynomial

namespace Irreducible

variable {F : Type*} [DivisionSemiring F] {f : F[X]}

/-- An irreducible polynomial over a field must have positive degree. -/
/-
**Irreducible.natDegree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Irreducible`。
形式化陈述：natDegree_pos (h : Irreducible f) : 0 < f.natDegree
参数：h : Irreducible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `not_irreducible_zero`：not_irreducible_zero [MonoidWithZero M] : ¬Irreduc
ible (0 : M) | ⟨hn0, h⟩ => have : IsUnit (0 : M) ∨ IsUnit (0 : M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a

--- 原说明 ---
An irreducible polynomial over a field must have positive degree.
-/
theorem natDegree_pos (h : Irreducible f) : 0 < f.natDegree := Nat.pos_of_ne_zero fun H ↦ by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))

/-- An irreducible polynomial over a field must have positive degree. -/
/-
**Irreducible.degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Irreducible`。
形式化陈述：degree_pos (h : Irreducible f) : 0 < f.degree
参数：h : Irreducible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree

--- 原说明 ---
An irreducible polynomial over a field must have positive degree.
-/
theorem degree_pos (h : Irreducible f) : 0 < f.degree := by
  rw [← natDegree_pos_iff_degree_pos]
  exact h.natDegree_pos

end Irreducible

