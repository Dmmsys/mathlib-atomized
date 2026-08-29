/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# Divisibility properties of binomial coefficients
-/

public section


namespace Nat

namespace Prime

variable {p a b k : Nat}

/--
theorem `dvd_choose_add` / 定理 `dvd_choose_add`

English:
theorem dvd_choose_add
  given: (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p <= a + b)
  proof: by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial]; rw [← choose_symm_add]; rw [hp.dvd_mul]; rw [hp.dvd_mul]; rw [hp.dvd_factorial]; rw [hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_ge).resolve_right hap.not_ge

中文:
定理 dvd_choose_add
  条件: (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p <= a + b)
  证明: by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial]; rw [← choose_symm_add]; rw [hp.dvd_mul]; rw [hp.dvd_mul]; rw [hp.dvd_factorial]; rw [hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_ge).resolve_right hap.not_ge

Depends on / 依赖: add_choose_mul_factorial_mul_factorial, choose_symm_add, dvd_factorial, dvd_mul, hap.not_ge, hbp.not_ge, hp.dvd_factorial, hp.dvd_mul, not_ge, resolve_right
-/
theorem dvd_choose_add (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p <= a + b) :
    p ∣ choose (a + b) a := by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial]; rw [← choose_symm_add]; rw [hp.dvd_mul]; rw [hp.dvd_mul]; rw [hp.dvd_factorial]; rw [hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_ge).resolve_right hap.not_ge

/--
lemma `dvd_choose` / 引理 `dvd_choose`

English:
lemma dvd_choose
  given: (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p <= b)
  statement: p ∣ choose b a
  proof: have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

中文:
引理 dvd_choose
  条件: (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p <= b)
  结论: p ∣ choose b a
  证明: have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

Depends on / 依赖: Nat.add_sub_of_le, add_sub_of_le, dvd_choose_add, ha.le.trans, hp.dvd_choose_add, this.symm
-/
lemma dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p <= b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

/--
lemma `dvd_choose_self` / 引理 `dvd_choose_self`

English:
lemma dvd_choose_self
  given: (hp : Prime p) (hk : k != 0) (hkp : k < p)
  statement: p ∣ choose p k
  proof: hp.dvd_choose hkp (sub_lt ((zero_le _).trans_lt hkp) <| zero_lt_of_ne_zero hk) le_rfl

中文:
引理 dvd_choose_self
  条件: (hp : Prime p) (hk : k != 0) (hkp : k < p)
  结论: p ∣ choose p k
  证明: hp.dvd_choose hkp (sub_lt ((zero_le _).trans_lt hkp) <| zero_lt_of_ne_zero hk) le_rfl

Depends on / 依赖: dvd_choose, hp.dvd_choose, le_rfl, sub_lt, trans_lt, zero_le, zero_lt_of_ne_zero
-/
lemma dvd_choose_self (hp : Prime p) (hk : k != 0) (hkp : k < p) : p ∣ choose p k :=
  hp.dvd_choose hkp (sub_lt ((zero_le _).trans_lt hkp) <| zero_lt_of_ne_zero hk) le_rfl

/--
lemma `coprime_choose_of_lt` / 引理 `coprime_choose_of_lt`

English:
lemma coprime_choose_of_lt
  given: (hp : p.Prime) (hb : b < p) (ha : a <= b)
  proof: by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  exact (hp.coprime_descFactorial_of_lt_of_le hb ha).coprime_div_right
    (Nat.factorial_dvd_descFactorial b a)

中文:
引理 coprime_choose_of_lt
  条件: (hp : p.Prime) (hb : b < p) (ha : a <= b)
  证明: by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  exact (hp.coprime_descFactorial_of_lt_of_le hb ha).coprime_div_right
    (Nat.factorial_dvd_descFactorial b a)

Depends on / 依赖: Nat.choose_eq_descFactorial_div_factorial, Nat.factorial_dvd_descFactorial, choose_eq_descFactorial_div_factorial, coprime_descFactorial_of_lt_of_le, coprime_div_right, factorial_dvd_descFactorial, hp.coprime_descFactorial_of_lt_of_le
-/
lemma coprime_choose_of_lt (hp : p.Prime) (hb : b < p) (ha : a <= b) :
    p.Coprime (b.choose a) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  exact (hp.coprime_descFactorial_of_lt_of_le hb ha).coprime_div_right
    (Nat.factorial_dvd_descFactorial b a)

end Prime

end Nat
