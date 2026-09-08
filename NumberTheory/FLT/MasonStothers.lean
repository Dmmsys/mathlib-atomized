/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
module

public import Mathlib.RingTheory.Polynomial.Radical

/-!
# Mason-Stothers theorem

This file states and proves the Mason-Stothers theorem, which is a polynomial version of the
ABC conjecture. For (pairwise) coprime polynomials `a, b, c` (over a field) with `a + b + c = 0`,
we have `max {deg(a), deg(b), deg(c)} + 1 ≤ deg(rad(abc))` or `a' = b' = c' = 0`.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf,
which is essentially based on Noah Snyder's paper "An Alternative Proof of Mason's Theorem",
but slightly different.

-/

public section

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

variable {k : Type*} [Field k] [DecidableEq k]

-- we use this three times; the assumptions are symmetric in a, b, c.
/-
**abc_subcall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem abc_subcall {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (abc_dr_dvd_w : divRadical (a * b * c) ∣ w) :
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  have ab_nz := mul_ne_zero ha hb
  have abc_nz := mul_ne_zero ab_nz hc
  -- bound the degree of `divRadical (a * b * c)` using Wronskian `w`
  set abc_dr := divRadical (a * b * c)
  have abc_dr_ndeg_lt : abc_dr.natDegree < a.natDegree + b.natDegree := by
    calc
      abc_dr.natDegree ≤ w.natDegree := Polynomial.natDegree_le_of_dvd abc_dr_dvd_w hw
      _ < a.natDegree + b.natDegree := by rw [wab] at hw ⊢; exact natDegree_wronskian_lt_add hw
  -- add the degree of `radical (a * b * c)` to both sides and rearrange
  set abc_r := radical (a * b * c)
  apply Nat.lt_of_add_lt_add_left
  calc
    a.natDegree + b.natDegree + c.natDegree = (a * b * c).natDegree := by
      rw [Polynomial.natDegree_mul ab_nz hc, Polynomial.natDegree_mul ha hb]
    _ = ((divRadical (a * b * c)) * (radical (a * b * c))).natDegree := by
      rw [mul_comm _ (radical _), radical_mul_divRadical]
    _ = abc_dr.natDegree + abc_r.natDegree := by
      rw [← Polynomial.natDegree_mul (divRadical_ne_zero abc_nz) radical_ne_zero]
    _ < a.natDegree + b.natDegree + abc_r.natDegree := by
      exact Nat.add_lt_add_right abc_dr_ndeg_lt _

/-- **Polynomial ABC theorem.** -/
/-
**Polynomial.abc** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] {a b c : Polyno
mial k},   a ≠ 0 →     b ≠ 0 →       c ≠ 0 →         IsCoprime a b →           a
 + b + c = 0 →             a.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical 
(a * b * c)).natDegree ∧                 b.natDegree + 1 ≤ (UniqueFactorizationM
onoid.radical (a * b * c)).natDegree ∧                   c.natDegree + 1 ≤ (Uniq
ueFactorizationMonoid.radical (a * b * c)).natDegree ∨               Polynomial.
derivative a = 0 ∧ Polynomial.derivative b = 0 ∧ Polynomial.derivative c = 0
参数：UniqueFactorizationMonoid.radical (a * b * c)；UniqueFactorizationMonoid.radic
al (a * b * c)；UniqueFactorizationMonoid.radical (a * b * c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `IsCoprime.neg_right_iff`：neg_right_iff (x y : R) : IsCoprime x (-y) ↔ Is
Coprime x y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsCoprime.add_mul_left_right`：add_mul_left_right {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime x (y + x * z)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `add_rotate`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G), a 
+ b + c = b + c + a
· 使用定理 `Polynomial.wronskian_eq_of_sum_zero`：wronskian_eq_of_sum_zero {a b c : R
[X]} (hAdd : a + b + c = 0) : wronskian a b = wronskian b c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `divRadical_dvd_wronskian_left`：divRadical_dvd_wronskian_left (a b : k[X]
) : divRadical a ∣ wronskian a b
· 使用定理 `divRadical_dvd_wronskian_right`：divRadical_dvd_wronskian_right (a b : k[
X]) : divRadical b ∣ wronskian a b
· 使用定理 `EuclideanDomain.divRadical_mul`：divRadical_mul (hab : IsCoprime a b) : d
ivRadical (a * b) = divRadical a * divRadical b
· 使用定理 `IsCoprime.mul_left`：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCopr
ime y z) : IsCoprime (x * y) z
· 使用定理 `IsCoprime.mul_dvd`：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H
2 : y ∣ z) : x * y ∣ z
· 使用定理 `IsCoprime.divRadical`：∀ {E : Type u_1} [inst : EuclideanDomain E] [inst_
1 : NormalizationMonoid E] [inst_2 : UniqueFactorizationMonoid E]   {a b : E}, I
sCoprime a…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoprime.wronskian_eq_zero_iff`：∀ {R : Type u_1} [inst : CommRing R] [N
oZeroDivisors R] {a b : Polynomial R},   IsCoprime a b → (a.wronskian b = 0 ↔ Po
lynomial.derivative a…
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `_private.Mathlib.NumberTheory.FLT.MasonStothers.0.abc_subcall`：∀ {k : Ty
pe u_1} [inst : Field k] [inst_1 : DecidableEq k] {a b c w : Polynomial k} {hw :
 w ≠ 0},   w = a.wronskian b →     a ≠ 0 →       b …

--- 原说明 ---
**Polynomial ABC theorem.**
-/
protected theorem Polynomial.abc
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (natDegree a + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree b + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree c + 1 ≤ (radical (a * b * c)).natDegree) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  set w := wronskian a b with wab
  have hbc : IsCoprime b c := by
    rw [add_eq_zero_iff_neg_eq] at hsum
    rw [← hsum, IsCoprime.neg_right_iff]
    convert! IsCoprime.add_mul_left_right hab.symm 1
    rw [mul_one]
  have hsum' : b + c + a = 0 := by rwa [add_rotate] at hsum
  have hca : IsCoprime c a := by
    rw [add_eq_zero_iff_neg_eq] at hsum'
    rw [← hsum', IsCoprime.neg_right_iff]
    convert! IsCoprime.add_mul_left_right hbc.symm 1
    rw [mul_one]
  have wbc : w = wronskian b c := wronskian_eq_of_sum_zero hsum
  have wca : w = wronskian c a := by
    rw [add_rotate] at hsum
    simpa only [← wbc] using wronskian_eq_of_sum_zero hsum
  -- have `divRadical x` dividing `w` for `x = a, b, c`, and use coprimality
  have abc_dr_dvd_w : divRadical (a * b * c) ∣ w := by
    have adr_dvd_w := divRadical_dvd_wronskian_left a b
    have bdr_dvd_w := divRadical_dvd_wronskian_right a b
    have cdr_dvd_w := divRadical_dvd_wronskian_right b c
    rw [← wab] at adr_dvd_w bdr_dvd_w
    rw [← wbc] at cdr_dvd_w
    rw [divRadical_mul (hca.symm.mul_left hbc), divRadical_mul hab]
    exact (hca.divRadical.symm.mul_left hbc.divRadical).mul_dvd
      (hab.divRadical.mul_dvd adr_dvd_w bdr_dvd_w) cdr_dvd_w
  by_cases hw : w = 0
  · right
    rw [hw] at wab wbc
    obtain ⟨ga, gb⟩ := hab.wronskian_eq_zero_iff.mp wab.symm
    obtain ⟨_, gc⟩ := hbc.wronskian_eq_zero_iff.mp wbc.symm
    exact ⟨ga, gb, gc⟩
  · left
    -- use `abc_subcall` three times, using the symmetry in `a, b, c`
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [← mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption
