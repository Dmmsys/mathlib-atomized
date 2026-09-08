/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.MasonStothers
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Tactic.GCongr
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Fermat's Last Theorem for polynomials over a field

This file states and proves the Fermat's Last Theorem for polynomials over a field.
For `n ≥ 3` not divisible by the characteristic of the coefficient field `k` and (pairwise) nonzero
coprime polynomials `a, b, c` (over a field) with `a ^ n + b ^ n = c ^ n`,
all polynomials must be constants.

More generally, we can prove non-solvability of the Fermat-Catalan equation: there are no
non-constant polynomial solutions to the equation `u * a ^ p + v * b ^ q + w * c ^ r = 0`, where
`p, q, r ≥ 3` with `p * q + q * r + r * p ≤ p * q * r`, `p, q, r` not divisible by `char k`,
and `u, v, w` are nonzero elements in `k`.
FLT is the special case where `p = q = r = n`, `u = v = 1`, and `w = -1`.

The proof uses the Mason-Stothers theorem (Polynomial ABC theorem) and infinite descent
(in the characteristic p case).
-/

public section

open Polynomial UniqueFactorizationMonoid

variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

/-
**Ne.isUnit_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Ne.isUnit_C {u : k} (hu : u ≠ 0) : IsUnit (C u) :=
  Polynomial.isUnit_C.mpr hu.isUnit

-- auxiliary lemma that 'rotates' coprimality
/-
**rot_coprime** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma rot_coprime
    {p q r : ℕ} {a b c : k[X]} {u v w : k}
    {hp : p ≠ 0} {hq : q ≠ 0} {hr : r ≠ 0}
    {hu : u ≠ 0} {hv : v ≠ 0} {hw : w ≠ 0}
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) (hab : IsCoprime a b) : IsCoprime b c := by
  have hCu : IsUnit (C u) := hu.isUnit_C
  have hCv : IsUnit (C v) := hv.isUnit_C
  have hCw : IsUnit (C w) := hw.isUnit_C
  rw [← IsCoprime.pow_iff hp.bot_lt hq.bot_lt, ← isCoprime_mul_units_left hCu hCv] at hab
  rw [add_eq_zero_iff_neg_eq] at heq
  rw [← IsCoprime.pow_iff hq.bot_lt hr.bot_lt, ← isCoprime_mul_units_left hCv hCw,
    ← heq, IsCoprime.neg_right_iff]
  convert! IsCoprime.add_mul_left_right hab.symm 1 using 2
  rw [mul_one]
/-
**ineq_pqr_contradiction** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ineq_pqr_contradiction {p q r a b c : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (hpa : p * a < a + b + c)
    (hqb : q * b < a + b + c)
    (hrc : r * c < a + b + c) : False := by
  suffices h : p * q * r * (a + b + c) + 1 ≤ p * q * r * (a + b + c) by simp at h
  calc
    _ = (p * a) * (q * r) + (q * b) * (r * p) + (r * c) * (p * q) + 1 := by ring
    _ ≤ (a + b + c) * (q * r) + (a + b + c) * (r * p) + (a + b + c) * (p * q) := by
      rw [Nat.succ_le_iff]
      gcongr
    _ = (q * r + r * p + p * q) * (a + b + c) := by ring
    _ ≤ _ := by gcongr
/-
**Polynomial.flt_catalan_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Polynomial.flt_catalan_deriv
    {p q r : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  have hbc : IsCoprime b c := by apply rot_coprime heq <;> assumption
  have hca : IsCoprime c a := by
    rw [add_rotate] at heq; apply rot_coprime heq <;> assumption
  have hCu := C_ne_zero.mpr hu
  have hCv := C_ne_zero.mpr hv
  have hCw := C_ne_zero.mpr hw
  have hap := pow_ne_zero p ha
  have hbq := pow_ne_zero q hb
  have hcr := pow_ne_zero r hc
  have habp : IsCoprime (C u * a ^ p) (C v * b ^ q) := by
    rw [isCoprime_mul_units_left hu.isUnit_C hv.isUnit_C]; exact hab.pow
  have hbcp : IsCoprime (C v * b ^ q) (C w * c ^ r) := by
    rw [isCoprime_mul_units_left hv.isUnit_C hw.isUnit_C]; exact hbc.pow
  have hcap : IsCoprime (C w * c ^ r) (C u * a ^ p) := by
    rw [isCoprime_mul_units_left hw.isUnit_C hu.isUnit_C]; exact hca.pow
  have habcp := hcap.symm.mul_left hbcp
  -- Use Mason-Stothers theorem
  classical
  rcases Polynomial.abc
      (mul_ne_zero hCu hap) (mul_ne_zero hCv hbq) (mul_ne_zero hCw hcr)
      habp heq with nd_lt | dr0
  · simp_rw [radical_mul habcp.isRelPrime, radical_mul habp.isRelPrime,
      radical_mul_of_isUnit_left hu.isUnit_C,
      radical_mul_of_isUnit_left hv.isUnit_C,
      radical_mul_of_isUnit_left hw.isUnit_C,
      radical_pow a hp, radical_pow b hq, radical_pow c hr,
      natDegree_mul hCu hap,
      natDegree_mul hCv hbq,
      natDegree_mul hCw hcr,
      natDegree_C, natDegree_pow, zero_add,
      ← radical_mul hab.isRelPrime,
      ← radical_mul (hca.symm.mul_left hbc).isRelPrime] at nd_lt
    obtain ⟨hpa', hqb', hrc'⟩ := nd_lt
    have hpa := hpa'.trans natDegree_radical_le
    have hqb := hqb'.trans natDegree_radical_le
    have hrc := hrc'.trans natDegree_radical_le
    rw [natDegree_mul (mul_ne_zero ha hb) hc,
      natDegree_mul ha hb, Nat.add_one_le_iff] at hpa hqb hrc
    exfalso
    exact (ineq_pqr_contradiction hp hq hr hineq hpa hqb hrc)
  · rw [derivative_C_mul, derivative_C_mul, derivative_C_mul,
      mul_eq_zero_iff_left (C_ne_zero.mpr hu),
      mul_eq_zero_iff_left (C_ne_zero.mpr hv),
      mul_eq_zero_iff_left (C_ne_zero.mpr hw),
      derivative_pow_eq_zero chp,
      derivative_pow_eq_zero chq,
      derivative_pow_eq_zero chr] at dr0
    exact dr0

-- helper lemma that gives a baggage of small facts on `contract (ringChar k) a`
/-
**find_contract** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma find_contract {a : k[X]}
    (ha : a ≠ 0) (hda : derivative a = 0) (chn0 : ringChar k ≠ 0) :
    ∃ ca, ca ≠ 0 ∧
      a = expand k (ringChar k) ca ∧
      a.natDegree = ca.natDegree * ringChar k := by
  have heq := (expand_contract (ringChar k) hda chn0).symm
  refine ⟨contract (ringChar k) a, ?_, heq, ?_⟩
  · intro h
    rw [h, map_zero] at heq
    exact ha heq
  · rw [← natDegree_expand, ← heq]
/-
**Polynomial.flt_catalan_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Polynomial.flt_catalan_aux
    {p q r : ℕ} {a b c : k[X]} {u v w : k}
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    a.natDegree = 0 := by
  rcases eq_or_ne (ringChar k) 0 with ch0 | chn0
  -- characteristic zero
  · obtain ⟨da, -, -⟩ := flt_catalan_deriv
      hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq
    have czk : CharZero k := by
      apply charZero_of_inj_zero
      intro n
      rw [ringChar.spec, ch0]
      exact zero_dvd_iff.mp
    rw [eq_C_of_derivative_eq_zero da]
    exact natDegree_C _
  -- characteristic p > 0
  · generalize eq_d : a.natDegree = d
    -- set up infinite descent
    -- strong induct on `d := a.natDegree`
    induction d
      using Nat.case_strong_induction_on
      generalizing a b c ha hb hc hab heq with
    | hz => rfl
    | hi d ih_d => -- have derivatives of `a, b, c` zero
      obtain ⟨ad, bd, cd⟩ := flt_catalan_deriv
        hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq
      -- find contracts `ca, cb, cc` so that `a(k) = ca(k^ch)`
      obtain ⟨ca, ca_nz, eq_a, eq_deg_a⟩ := find_contract ha ad chn0
      obtain ⟨cb, cb_nz, eq_b, eq_deg_b⟩ := find_contract hb bd chn0
      obtain ⟨cc, cc_nz, eq_c, eq_deg_c⟩ := find_contract hc cd chn0
      set ch := ringChar k
      suffices hca : ca.natDegree = 0 by
        rw [← eq_d, eq_deg_a, hca, zero_mul]
      by_contra hnca; apply hnca
      apply ih_d _ _ _ ca_nz cb_nz cc_nz <;> clear ih_d <;> try rfl
      · apply (isCoprime_expand chn0).mp
        rwa [← eq_a, ← eq_b]
      · have _ : ch ≠ 1 := CharP.ringChar_ne_one
        have hch2 : 2 ≤ ch := by lia
        rw [← add_le_add_iff_right 1, ← eq_d, eq_deg_a]
        grw [← hch2]
        lia
      · rw [eq_a, eq_b, eq_c, ← expand_C ch u, ← expand_C ch v, ← expand_C ch w] at heq
        simp_rw [← map_pow, ← map_mul, ← map_add] at heq
        rwa [Polynomial.expand_eq_zero (zero_lt_iff.mpr chn0)] at heq

/-- Nonsolvability of the Fermat-Catalan equation. -/
/-
**Polynomial.flt_catalan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.flt_catalan {p q r : Nat} (hp : p != 0) (hq : q != 0) (hr : r !
= 0) (hineq : q * r + r * p + p * q <= p * q * r) (chp : (p : k) != 0) (chq : (q
 : k) != 0) (chr : (r : k) != 0) {a b c : k[X]} (ha : a != 0) (hb : b != 0) (hc 
: c != 0) (hab : IsCoprime a b) {u v w : k} (hu : u != 0) (hv : v != 0) (hw : w 
!= 0) (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) : a.natDegree = 0 ∧ b.
natDegree = 0 ∧ c.natDegree = 0
参数：hp : p != 0；hq : q != 0；hr : r != 0；hineq : q * r + r * p + p * q <= p * q * 
r；chp : (p : k) != 0；chq : (q : k) != 0；chr : (r : k) != 0；ha : a != 0；hb : b !=
 0；hc : c != 0；hab : IsCoprime a b；hu : u != 0；hv : v != 0；hw : w != 0；heq : C u
 * a ^ p + C v * b ^ q + C w * c ^ r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.FLT.Polynomial.0.rot_coprime`：∀ {k : Type 
u_1} [inst : Field k] {p q r : ℕ} {a b c : Polynomial k} {u v w : k} {hp : p ≠ 0
} {hq : q ≠ 0} {hr : r ≠ 0}   {hu : u ≠ 0} {hv :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_rotate`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G), a 
+ b + c = b + c + a
· 使用定理 `_private.Mathlib.NumberTheory.FLT.Polynomial.0.Polynomial.flt_catalan_au
x`：∀ {k : Type u_1} [inst : Field k] {p q r : ℕ} {a b c : Polynomial k} {u v w :
 k},   Polynomial.C u * a ^ p + Polynomial.C v * b ^ q + Polyno…
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Nonsolvability of the Fermat-Catalan equation.
-/
theorem Polynomial.flt_catalan
    {p q r : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  -- WLOG argument: essentially three times flt_catalan_aux
  have hbc : IsCoprime b c := by
    apply rot_coprime heq hab <;> assumption
  have heq' : C v * b ^ q + C w * c ^ r + C u * a ^ p = 0 := by
    rwa [add_rotate] at heq
  have hca : IsCoprime c a := by
    apply rot_coprime heq' hbc <;> assumption
  refine ⟨?_, ?_, ?_⟩
  · apply flt_catalan_aux heq <;> assumption
  · rw [add_rotate] at heq hineq
    rw [mul_rotate] at hineq
    apply flt_catalan_aux heq <;> assumption
  · rw [← add_rotate] at heq hineq
    rw [← mul_rotate] at hineq
    apply flt_catalan_aux heq <;> assumption
/-
**Polynomial.flt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.flt {n : Nat} (hn : 3 <= n) (chn : (n : k) != 0) {a b c : k[X]}
 (ha : a != 0) (hb : b != 0) (hc : c != 0) (hab : IsCoprime a b) (heq : a ^ n + 
b ^ n = c ^ n) : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
参数：hn : 3 <= n；chn : (n : k) != 0；ha : a != 0；hb : b != 0；hc : c != 0；hab : IsCo
prime a b；heq : a ^ n + b ^ n = c ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 76 条，此处仅展示前 30 条）
-/
theorem Polynomial.flt
    {n : ℕ} (hn : 3 ≤ n) (chn : (n : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have hn' : 0 < n := by linarith
  rw [← sub_eq_zero, ← one_mul (a ^ n), ← one_mul (b ^ n), ← one_mul (c ^ n), sub_eq_add_neg,
    ← neg_mul] at heq
  have hone : (1 : k[X]) = C 1 := by rfl
  have hneg_one : (-1 : k[X]) = C (-1) := by simp only [map_neg, map_one]
  simp_rw [hneg_one, hone] at heq
  apply flt_catalan hn'.ne' hn'.ne' hn'.ne' _
    chn chn chn ha hb hc hab one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq
  have eq_lhs : n * n + n * n + n * n = 3 * n * n := by ring
  rw [eq_lhs, mul_assoc, mul_assoc]
  exact Nat.mul_le_mul_right (n * n) hn
/-
**fermatLastTheoremWith'_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {k : Type u_1} [inst : Field k] {n : ℕ}, 3 ≤ n → ↑n ≠ 0 → FermatLastTheo
remWith' (Polynomial k) n
参数：Polynomial k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FermatLastTheoremWith'.eq_1`：∀ (R : Type u_2) [inst : CommSemiring R] (n
 : ℕ),   FermatLastTheoremWith' R n =     ∀ (a b c : R),       a ≠ 0 →         b
 ≠ 0 →           …
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
· 使用定理 `gcd_ne_zero_of_left`：gcd_ne_zero_of_left [GCDMonoid α] {a b : α} (ha : a
 != 0) : gcd a b != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.pow_dvd_pow_iff`：pow_dvd_pow_iff [IsDomain R] [IsInte
grallyClosed R] {n : Nat} (hn : n != 0) {a b : R} : a ^ n ∣ b ^ n ↔ a ∣ b
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsIntegrallyClosedPolynomialOfIsDomain`：∀ {R : Type u_4} [inst : Com
mRing R] [IsDomain R] [IsIntegrallyClosed R], IsIntegrallyClosed (Polynomial R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.flt`：Polynomial.flt {n : Nat} (hn : 3 <= n) (chn : (n : k) !=
 0) {a b c : k[X]} (ha : a != 0) (hb : b != 0) (hc : c != 0) (hab : IsCoprime a 
b) (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_left`：eq_div_of_mul_eq_left {a b c : R}
 (hb : b != 0) (h : a * b = c) : a = c / b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isCoprime_div_gcd_div_gcd`：isCoprime_div_gcd_div_gcd (hq : q != 0) : IsC
oprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `Polynomial.instIsRightCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst :
 Semiring R] [IsCancelAdd R] [IsRightCancelMulZero R], IsRightCancelMulZero (Pol
ynomial R)
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
（共 35 条，此处仅展示前 30 条）
-/
theorem fermatLastTheoremWith'_polynomial {n : ℕ} (hn : 3 ≤ n) (chn : (n : k) ≠ 0) :
    FermatLastTheoremWith' k[X] n := by
  classical
  rw [FermatLastTheoremWith']
  intro a b c ha hb hc heq
  obtain ⟨a', eq_a⟩ := gcd_dvd_left a b
  obtain ⟨b', eq_b⟩ := gcd_dvd_right a b
  set d := gcd a b
  have hd : d ≠ 0 := gcd_ne_zero_of_left ha
  rw [eq_a, eq_b, mul_pow, mul_pow, ← mul_add] at heq
  obtain ⟨c', eq_c⟩ : ∃ c', c = d * c' :=
    (IsIntegrallyClosed.pow_dvd_pow_iff (by lia)).mp ⟨_, heq.symm⟩
  rw [eq_a, mul_ne_zero_iff] at ha
  rw [eq_b, mul_ne_zero_iff] at hb
  rw [eq_c, mul_ne_zero_iff] at hc
  rw [mul_comm] at eq_a eq_b eq_c
  refine ⟨d, a', b', c', ⟨eq_a, eq_b, eq_c⟩, ?_⟩
  rw [eq_c, mul_pow, mul_comm, mul_left_inj' (pow_ne_zero n hd)] at heq
  suffices goal : a'.natDegree = 0 ∧ b'.natDegree = 0 ∧ c'.natDegree = 0 by
    simp only [natDegree_eq_zero] at goal
    obtain ⟨⟨ca', ha'⟩, ⟨cb', hb'⟩, ⟨cc', hc'⟩⟩ := goal
    rw [← ha', ← hb', ← hc']
    rw [← ha', C_ne_zero] at ha
    rw [← hb', C_ne_zero] at hb
    rw [← hc', C_ne_zero] at hc
    exact ⟨ha.right.isUnit_C, hb.right.isUnit_C, hc.right.isUnit_C⟩
  apply flt hn chn ha.right hb.right hc.right _ heq
  convert! isCoprime_div_gcd_div_gcd _
  · exact EuclideanDomain.eq_div_of_mul_eq_left ha.left eq_a.symm
  · exact EuclideanDomain.eq_div_of_mul_eq_left ha.left eq_b.symm
  · rw [eq_b]
    exact mul_ne_zero hb.right hb.left
