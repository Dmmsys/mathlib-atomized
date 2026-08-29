/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Characteristic of semirings
-/

@[expose] public section

assert_not_exists Algebra LinearMap orderOf

open Finset

variable {R S : Type*}

namespace Commute

variable [Semiring R] {p : Nat} (hp : p.Prime) {x y : R}
include hp

/--
lemma `add_pow_prime_pow_eq'` / 引理 `add_pow_prime_pow_eq'`

English:
lemma add_pow_prime_pow_eq'
  given: (h : Commute x y) (n : Nat)
  proof: calc
  _ = ∑ k in Icc 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    rw [h.add_pow]; rw [← Nat.Ico_zero_eq_range]; rw [Ico_add_one_right_eq_Icc]
  _ = x ^ p ^ n + y ^ p ^ n + ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    simp_rw [Icc_eq_cons_Ico zero_le, Ico_eq_cons_Ioo (pow_pos hp.pos _)]
    simp [-cons_eq_insert, add_assoc]
  _ = _ := by
    simp_rw [mul_sum]
    congr! 2 with k hk
    obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
    -- The maths is over now. We just commute things to their place.
    rw [Nat.cast_comm]; rw [mul_assoc (_ * _)]
    norm_cast
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow _ _)] <;> lia

中文:
引理 add_pow_prime_pow_eq'
  条件: (h : Commute x y) (n : 自然数)
  证明: calc
  _ = ∑ k in Icc 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    rw [h.add_pow]; rw [← Nat.Ico_zero_eq_range]; rw [Ico_add_one_right_eq_Icc]
  _ = x ^ p ^ n + y ^ p ^ n + ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    simp_rw [Icc_eq_cons_Ico zero_le, Ico_eq_cons_Ioo (pow_pos hp.pos _)]
    simp [-cons_eq_insert, add_assoc]
  _ = _ := by
    simp_rw [mul_sum]
    congr! 2 with k hk
    obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
    -- The maths is over now. We just commute things to their place.
    rw [Nat.cast_comm]; rw [mul_assoc (_ * _)]
    norm_cast
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow _ _)] <;> lia
-/
protected lemma add_pow_prime_pow_eq' (h : Commute x y) (n : Nat) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) := calc
  _ = ∑ k in Icc 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    rw [h.add_pow]; rw [← Nat.Ico_zero_eq_range]; rw [Ico_add_one_right_eq_Icc]
  _ = x ^ p ^ n + y ^ p ^ n + ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    simp_rw [Icc_eq_cons_Ico zero_le, Ico_eq_cons_Ioo (pow_pos hp.pos _)]
    simp [-cons_eq_insert, add_assoc]
  _ = _ := by
    simp_rw [mul_sum]
    congr! 2 with k hk
    obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
    -- The maths is over now. We just commute things to their place.
    rw [Nat.cast_comm]; rw [mul_assoc (_ * _)]
    norm_cast
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow _ _)] <;> lia

/--
lemma `add_pow_prime_pow_eq` / 引理 `add_pow_prime_pow_eq`

English:
lemma add_pow_prime_pow_eq
  given: (h : Commute x y) (n : Nat)
  proof: by
  rw [h.add_pow_prime_pow_eq' hp]; rw [mul_assoc _ x]; rw [mul_assoc]; rw [mul_sum _ _ (_ * _)]
  congr! 3 with k hk
  obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
  rw [← mul_pow_sub_one (by lia)]; rw [← mul_pow_sub_one (n := p ^ n - k) (by lia)]
  rw [(h.pow_left _).mul_mul_mul_comm]; rw [mul_assoc (x * y)]

中文:
引理 add_pow_prime_pow_eq
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  rw [h.add_pow_prime_pow_eq' hp]; rw [mul_assoc _ x]; rw [mul_assoc]; rw [mul_sum _ _ (_ * _)]
  congr! 3 with k hk
  obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
  rw [← mul_pow_sub_one (by lia)]; rw [← mul_pow_sub_one (n := p ^ n - k) (by lia)]
  rw [(h.pow_left _).mul_mul_mul_comm]; rw [mul_assoc (x * y)]
-/
protected lemma add_pow_prime_pow_eq (h : Commute x y) (n : Nat) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * x * y *
          ∑ k in Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p) := by
  rw [h.add_pow_prime_pow_eq' hp]; rw [mul_assoc _ x]; rw [mul_assoc]; rw [mul_sum _ _ (_ * _)]
  congr! 3 with k hk
  obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
  rw [← mul_pow_sub_one (by lia)]; rw [← mul_pow_sub_one (n := p ^ n - k) (by lia)]
  rw [(h.pow_left _).mul_mul_mul_comm]; rw [mul_assoc (x * y)]

/--
lemma `add_pow_prime_eq'` / 引理 `add_pow_prime_eq'`

English:
lemma add_pow_prime_eq'
  given: (h : Commute x y)
  proof: by
  simpa using h.add_pow_prime_pow_eq' hp 1

中文:
引理 add_pow_prime_eq'
  条件: (h : Commute x y)
  证明: by
  simpa using h.add_pow_prime_pow_eq' hp 1
-/
protected lemma add_pow_prime_eq' (h : Commute x y) :
    (x + y) ^ p = x ^ p + y ^ p + p * ∑ k in Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq' hp 1

/--
lemma `add_pow_prime_eq` / 引理 `add_pow_prime_eq`

English:
lemma add_pow_prime_eq
  given: (h : Commute x y)
  proof: by
  simpa using h.add_pow_prime_pow_eq hp 1

中文:
引理 add_pow_prime_eq
  条件: (h : Commute x y)
  证明: by
  simpa using h.add_pow_prime_pow_eq hp 1
-/
protected lemma add_pow_prime_eq (h : Commute x y) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * x * y *
        ∑ k in Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq hp 1

/--
theorem `exists_add_pow_prime_pow_eq` / 定理 `exists_add_pow_prime_pow_eq`

English:
theorem exists_add_pow_prime_pow_eq
  given: (h : Commute x y) (n : Nat)
  proof: ⟨_, h.add_pow_prime_pow_eq hp n⟩

中文:
定理 存在_add_pow_prime_pow_eq
  条件: (h : Commute x y) (n : 自然数)
  证明: ⟨_, h.add_pow_prime_pow_eq hp n⟩
-/
protected theorem exists_add_pow_prime_pow_eq (h : Commute x y) (n : Nat) :
    exists r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  ⟨_, h.add_pow_prime_pow_eq hp n⟩

/--
theorem `exists_add_pow_prime_eq` / 定理 `exists_add_pow_prime_eq`

English:
theorem exists_add_pow_prime_eq
  given: (h : Commute x y)
  proof: ⟨_, h.add_pow_prime_eq hp⟩

中文:
定理 存在_add_pow_prime_eq
  条件: (h : Commute x y)
  证明: ⟨_, h.add_pow_prime_eq hp⟩
-/
protected theorem exists_add_pow_prime_eq (h : Commute x y) :
    exists r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r :=
  ⟨_, h.add_pow_prime_eq hp⟩

end Commute

section CommSemiring

variable [CommSemiring R] {p : Nat} (hp : p.Prime) (x y : R) (n : Nat)
include hp

/--
lemma `add_pow_prime_pow_eq'` / 引理 `add_pow_prime_pow_eq'`

English:
lemma add_pow_prime_pow_eq'
  proof: (Commute.all x y).add_pow_prime_pow_eq' hp n

中文:
引理 add_pow_prime_pow_eq'
  证明: (Commute.all x y).add_pow_prime_pow_eq' hp n

Depends on / 依赖: Commute, Commute.all, add_pow_prime_pow_eq
-/
lemma add_pow_prime_pow_eq' :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq' hp n

/--
lemma `add_pow_prime_pow_eq` / 引理 `add_pow_prime_pow_eq`

English:
lemma add_pow_prime_pow_eq
  proof: (Commute.all x y).add_pow_prime_pow_eq hp n

中文:
引理 add_pow_prime_pow_eq
  证明: (Commute.all x y).add_pow_prime_pow_eq hp n

Depends on / 依赖: Commute, Commute.all, add_pow_prime_pow_eq
-/
lemma add_pow_prime_pow_eq :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * x * y *
          ∑ k in Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq hp n

/--
lemma `add_pow_prime_eq'` / 引理 `add_pow_prime_eq'`

English:
lemma add_pow_prime_eq'
  proof: (Commute.all x y).add_pow_prime_eq' hp

中文:
引理 add_pow_prime_eq'
  证明: (Commute.all x y).add_pow_prime_eq' hp

Depends on / 依赖: Commute, Commute.all, add_pow_prime_eq
-/
lemma add_pow_prime_eq' :
    (x + y) ^ p = x ^ p + y ^ p + p * ∑ k in Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq' hp

/--
theorem `add_pow_prime_eq` / 定理 `add_pow_prime_eq`

English:
theorem add_pow_prime_eq
  proof: (Commute.all x y).add_pow_prime_eq hp

中文:
定理 add_pow_prime_eq
  证明: (Commute.all x y).add_pow_prime_eq hp

Depends on / 依赖: Commute, Commute.all, add_pow_prime_eq
-/
theorem add_pow_prime_eq :
    (x + y) ^ p =
      x ^ p + y ^ p + p * x * y *
        ∑ k in Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq hp

/--
theorem `exists_add_pow_prime_pow_eq` / 定理 `exists_add_pow_prime_pow_eq`

English:
theorem exists_add_pow_prime_pow_eq
  proof: (Commute.all x y).exists_add_pow_prime_pow_eq hp n

中文:
定理 存在_add_pow_prime_pow_eq
  证明: (Commute.all x y).exists_add_pow_prime_pow_eq hp n

Depends on / 依赖: Commute, Commute.all, exists_add_pow_prime_pow_eq
-/
theorem exists_add_pow_prime_pow_eq :
    exists r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  (Commute.all x y).exists_add_pow_prime_pow_eq hp n

/--
theorem `exists_add_pow_prime_eq` / 定理 `exists_add_pow_prime_eq`

English:
theorem exists_add_pow_prime_eq
  statement: exists r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r
  proof: (Commute.all x y).exists_add_pow_prime_eq hp

中文:
定理 存在_add_pow_prime_eq
  结论: 存在 r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r
  证明: (Commute.all x y).exists_add_pow_prime_eq hp

Depends on / 依赖: Commute, Commute.all, exists_add_pow_prime_eq
-/
theorem exists_add_pow_prime_eq : exists r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r :=
  (Commute.all x y).exists_add_pow_prime_eq hp

end CommSemiring

section Semiring
variable [Semiring R] {x y : R} (p n : Nat)

section ExpChar
variable [hR : ExpChar R p]

/--
lemma `add_pow_expChar_of_commute` / 引理 `add_pow_expChar_of_commute`

English:
lemma add_pow_expChar_of_commute
  given: (h : Commute x y)
  statement: (x + y) ^ p = x ^ p + y ^ p
  proof: by
  obtain _ | hprime := hR
  · simp only [pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hprime
    simp [hr]

中文:
引理 add_pow_expChar_of_commute
  条件: (h : Commute x y)
  结论: (x + y) ^ p = x ^ p + y ^ p
  证明: by
  obtain _ | hprime := hR
  · simp only [pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hprime
    simp [hr]

Depends on / 依赖: exists_add_pow_prime_eq, h.exists_add_pow_prime_eq, hprime, pow_one
-/
lemma add_pow_expChar_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain _ | hprime := hR
  · simp only [pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hprime
    simp [hr]

/--
lemma `add_pow_expChar_pow_of_commute` / 引理 `add_pow_expChar_pow_of_commute`

English:
lemma add_pow_expChar_pow_of_commute
  given: (h : Commute x y)
  proof: by
  obtain _ | hprime := hR
  · simp only [one_pow, pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hprime n
    simp [hr]

中文:
引理 add_pow_expChar_pow_of_commute
  条件: (h : Commute x y)
  证明: by
  obtain _ | hprime := hR
  · simp only [one_pow, pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hprime n
    simp [hr]

Depends on / 依赖: exists_add_pow_prime_pow_eq, h.exists_add_pow_prime_pow_eq, hprime, one_pow, pow_one
-/
lemma add_pow_expChar_pow_of_commute (h : Commute x y) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  obtain _ | hprime := hR
  · simp only [one_pow, pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hprime n
    simp [hr]

/--
lemma `add_pow_eq_mul_pow_add_pow_div_expChar_of_commute` / 引理 `add_pow_eq_mul_pow_add_pow_div_expChar_of_commute`

English:
lemma add_pow_eq_mul_pow_add_pow_div_expChar_of_commute
  given: (h : Commute x y)
  proof: by
  rw [← add_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

中文:
引理 add_pow_eq_mul_pow_add_pow_div_expChar_of_commute
  条件: (h : Commute x y)
  证明: by
  rw [← add_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

Depends on / 依赖: Nat.mod_add_div, add_pow_expChar_of_commute, mod_add_div, pow_add, pow_mul
-/
lemma add_pow_eq_mul_pow_add_pow_div_expChar_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) := by
  rw [← add_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/--
lemma `add_pow_char_of_commute` / 引理 `add_pow_char_of_commute`

English:
lemma add_pow_char_of_commute
  given: (h : Commute x y)
  statement: (x + y) ^ p = x ^ p + y ^ p
  proof: add_pow_expChar_of_commute _ h

中文:
引理 add_pow_char_of_commute
  条件: (h : Commute x y)
  结论: (x + y) ^ p = x ^ p + y ^ p
  证明: add_pow_expChar_of_commute _ h

Depends on / 依赖: add_pow_expChar_of_commute
-/
lemma add_pow_char_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_expChar_of_commute _ h

/--
lemma `add_pow_char_pow_of_commute` / 引理 `add_pow_char_pow_of_commute`

English:
lemma add_pow_char_pow_of_commute
  given: (h : Commute x y)
  statement: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  proof: add_pow_expChar_pow_of_commute _ _ h

中文:
引理 add_pow_char_pow_of_commute
  条件: (h : Commute x y)
  结论: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  证明: add_pow_expChar_pow_of_commute _ _ h

Depends on / 依赖: add_pow_expChar_pow_of_commute
-/
lemma add_pow_char_pow_of_commute (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_expChar_pow_of_commute _ _ h

/--
lemma `add_pow_eq_mul_pow_add_pow_div_char_of_commute` / 引理 `add_pow_eq_mul_pow_add_pow_div_char_of_commute`

English:
lemma add_pow_eq_mul_pow_add_pow_div_char_of_commute
  given: (h : Commute x y)
  proof: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

中文:
引理 add_pow_eq_mul_pow_add_pow_div_char_of_commute
  条件: (h : Commute x y)
  证明: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

Depends on / 依赖: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute
-/
lemma add_pow_eq_mul_pow_add_pow_div_char_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

end CharP
end Semiring

section CommSemiring
variable [CommSemiring R] (x y : R) (p n : Nat)

section ExpChar
variable [hR : ExpChar R p]

/--
lemma `add_pow_expChar` / 引理 `add_pow_expChar`

English:
lemma add_pow_expChar
  statement: (x + y) ^ p = x ^ p + y ^ p
  proof: add_pow_expChar_of_commute _ .all ..

中文:
引理 add_pow_expChar
  结论: (x + y) ^ p = x ^ p + y ^ p
  证明: add_pow_expChar_of_commute _ .all ..

Depends on / 依赖: add_pow_expChar_of_commute
-/
lemma add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar_of_commute _ .all ..

/--
lemma `add_pow_expChar_pow` / 引理 `add_pow_expChar_pow`

English:
lemma add_pow_expChar_pow
  statement: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  proof: add_pow_expChar_pow_of_commute _ _ .all ..

中文:
引理 add_pow_expChar_pow
  结论: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  证明: add_pow_expChar_pow_of_commute _ _ .all ..

Depends on / 依赖: add_pow_expChar_pow_of_commute
-/
lemma add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
add_pow_expChar_pow_of_commute _ _ .all ..

/--
lemma `add_pow_eq_mul_pow_add_pow_div_expChar` / 引理 `add_pow_eq_mul_pow_add_pow_div_expChar`

English:
lemma add_pow_eq_mul_pow_add_pow_div_expChar
  proof: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ .all ..

中文:
引理 add_pow_eq_mul_pow_add_pow_div_expChar
  证明: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ .all ..

Depends on / 依赖: add_pow_eq_mul_pow_add_pow_div_expChar_of_commute
-/
lemma add_pow_eq_mul_pow_add_pow_div_expChar :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ .all ..

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/--
lemma `add_pow_char` / 引理 `add_pow_char`

English:
lemma add_pow_char
  statement: (x + y) ^ p = x ^ p + y ^ p
  proof: add_pow_expChar ..

中文:
引理 add_pow_char
  结论: (x + y) ^ p = x ^ p + y ^ p
  证明: add_pow_expChar ..

Depends on / 依赖: add_pow_expChar
-/
lemma add_pow_char : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar ..
/--
lemma `add_pow_char_pow` / 引理 `add_pow_char_pow`

English:
lemma add_pow_char_pow
  statement: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  proof: add_pow_expChar_pow ..

中文:
引理 add_pow_char_pow
  结论: (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
  证明: add_pow_expChar_pow ..

Depends on / 依赖: add_pow_expChar_pow
-/
lemma add_pow_char_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := add_pow_expChar_pow ..

/--
lemma `add_pow_eq_mul_pow_add_pow_div_char` / 引理 `add_pow_eq_mul_pow_add_pow_div_char`

English:
lemma add_pow_eq_mul_pow_add_pow_div_char
  proof: add_pow_eq_mul_pow_add_pow_div_expChar ..

中文:
引理 add_pow_eq_mul_pow_add_pow_div_char
  证明: add_pow_eq_mul_pow_add_pow_div_expChar ..

Depends on / 依赖: add_pow_eq_mul_pow_add_pow_div_expChar
-/
lemma add_pow_eq_mul_pow_add_pow_div_char :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar ..

end CharP
end CommSemiring

section Ring
variable [Ring R] {x y : R} (p n : Nat)

section ExpChar
variable [hR : ExpChar R p]
include hR

/--
lemma `sub_pow_expChar_of_commute` / 引理 `sub_pow_expChar_of_commute`

English:
lemma sub_pow_expChar_of_commute
  given: (h : Commute x y)
  statement: (x - y) ^ p = x ^ p - y ^ p
  proof: by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]

中文:
引理 sub_pow_expChar_of_commute
  条件: (h : Commute x y)
  结论: (x - y) ^ p = x ^ p - y ^ p
  证明: by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]

Depends on / 依赖: add_pow_expChar_of_commute, eq_sub_iff_add_eq, h.sub_left, sub_left
-/
lemma sub_pow_expChar_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]

/--
lemma `sub_pow_expChar_pow_of_commute` / 引理 `sub_pow_expChar_pow_of_commute`

English:
lemma sub_pow_expChar_pow_of_commute
  given: (h : Commute x y)
  proof: by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]

中文:
引理 sub_pow_expChar_pow_of_commute
  条件: (h : Commute x y)
  证明: by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]

Depends on / 依赖: add_pow_expChar_pow_of_commute, eq_sub_iff_add_eq, h.sub_left, sub_left
-/
lemma sub_pow_expChar_pow_of_commute (h : Commute x y) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]

/--
lemma `sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute` / 引理 `sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute`

English:
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute
  given: (h : Commute x y)
  proof: by
  rw [← sub_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

中文:
引理 sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute
  条件: (h : Commute x y)
  证明: by
  rw [← sub_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

Depends on / 依赖: Nat.mod_add_div, mod_add_div, pow_add, pow_mul, sub_pow_expChar_of_commute
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) := by
  rw [← sub_pow_expChar_of_commute _ h]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.mod_add_div]

variable (R)

/--
lemma `neg_one_pow_expChar` / 引理 `neg_one_pow_expChar`

English:
lemma neg_one_pow_expChar
  statement: (-1 : R) ^ p = -1
  proof: by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_expChar_of_commute _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (expChar_ne_zero R p)]

中文:
引理 neg_one_pow_expChar
  结论: (-1 : R) ^ p = -1
  证明: by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_expChar_of_commute _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (expChar_ne_zero R p)]

Depends on / 依赖: Commute, Commute.one_right, add_pow_expChar_of_commute, eq_neg_iff_add_eq_zero, expChar_ne_zero, neg_add_cancel, nth_rw, one_pow, one_right, zero_pow
-/
lemma neg_one_pow_expChar : (-1 : R) ^ p = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_expChar_of_commute _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (expChar_ne_zero R p)]

/--
lemma `neg_one_pow_expChar_pow` / 引理 `neg_one_pow_expChar_pow`

English:
lemma neg_one_pow_expChar_pow
  statement: (-1 : R) ^ p ^ n = -1
  proof: by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_expChar_pow_of_commute _ _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (pow_ne_zero _ <| expChar_ne_zero R p)]

中文:
引理 neg_one_pow_expChar_pow
  结论: (-1 : R) ^ p ^ n = -1
  证明: by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_expChar_pow_of_commute _ _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (pow_ne_zero _ <| expChar_ne_zero R p)]

Depends on / 依赖: Commute, Commute.one_right, add_pow_expChar_pow_of_commute, eq_neg_iff_add_eq_zero, expChar_ne_zero, neg_add_cancel, nth_rw, one_pow, one_right, pow_ne_zero, zero_pow
-/
lemma neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_expChar_pow_of_commute _ _ (Commute.one_right _)]; rw [neg_add_cancel]; rw [zero_pow (pow_ne_zero _ <| expChar_ne_zero R p)]

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/--
lemma `sub_pow_char_of_commute` / 引理 `sub_pow_char_of_commute`

English:
lemma sub_pow_char_of_commute
  given: (h : Commute x y)
  statement: (x - y) ^ p = x ^ p - y ^ p
  proof: sub_pow_expChar_of_commute _ h

中文:
引理 sub_pow_char_of_commute
  条件: (h : Commute x y)
  结论: (x - y) ^ p = x ^ p - y ^ p
  证明: sub_pow_expChar_of_commute _ h

Depends on / 依赖: sub_pow_expChar_of_commute
-/
lemma sub_pow_char_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_expChar_of_commute _ h

/--
lemma `sub_pow_char_pow_of_commute` / 引理 `sub_pow_char_pow_of_commute`

English:
lemma sub_pow_char_pow_of_commute
  given: (h : Commute x y)
  statement: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  proof: sub_pow_expChar_pow_of_commute _ _ h

中文:
引理 sub_pow_char_pow_of_commute
  条件: (h : Commute x y)
  结论: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  证明: sub_pow_expChar_pow_of_commute _ _ h

Depends on / 依赖: sub_pow_expChar_pow_of_commute
-/
lemma sub_pow_char_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_expChar_pow_of_commute _ _ h

variable (R)

/--
lemma `neg_one_pow_char` / 引理 `neg_one_pow_char`

English:
lemma neg_one_pow_char
  statement: (-1 : R) ^ p = -1
  proof: neg_one_pow_expChar ..

中文:
引理 neg_one_pow_char
  结论: (-1 : R) ^ p = -1
  证明: neg_one_pow_expChar ..

Depends on / 依赖: neg_one_pow_expChar
-/
lemma neg_one_pow_char : (-1 : R) ^ p = -1 := neg_one_pow_expChar ..

/--
lemma `neg_one_pow_char_pow` / 引理 `neg_one_pow_char_pow`

English:
lemma neg_one_pow_char_pow
  statement: (-1 : R) ^ p ^ n = -1
  proof: neg_one_pow_expChar_pow ..

中文:
引理 neg_one_pow_char_pow
  结论: (-1 : R) ^ p ^ n = -1
  证明: neg_one_pow_expChar_pow ..

Depends on / 依赖: neg_one_pow_expChar_pow
-/
lemma neg_one_pow_char_pow : (-1 : R) ^ p ^ n = -1 := neg_one_pow_expChar_pow ..

/--
lemma `sub_pow_eq_mul_pow_sub_pow_div_char_of_commute` / 引理 `sub_pow_eq_mul_pow_sub_pow_div_char_of_commute`

English:
lemma sub_pow_eq_mul_pow_sub_pow_div_char_of_commute
  given: (h : Commute x y)
  proof: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ h

中文:
引理 sub_pow_eq_mul_pow_sub_pow_div_char_of_commute
  条件: (h : Commute x y)
  证明: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ h

Depends on / 依赖: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_char_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ h

end CharP
end Ring

section CommRing
variable [CommRing R] (x y : R) (n : Nat) {p : Nat}

section ExpChar
variable [hR : ExpChar R p]

/--
lemma `sub_pow_expChar` / 引理 `sub_pow_expChar`

English:
lemma sub_pow_expChar
  statement: (x - y) ^ p = x ^ p - y ^ p
  proof: sub_pow_expChar_of_commute _ .all ..

中文:
引理 sub_pow_expChar
  结论: (x - y) ^ p = x ^ p - y ^ p
  证明: sub_pow_expChar_of_commute _ .all ..

Depends on / 依赖: sub_pow_expChar_of_commute
-/
lemma sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar_of_commute _ .all ..

/--
lemma `sub_pow_expChar_pow` / 引理 `sub_pow_expChar_pow`

English:
lemma sub_pow_expChar_pow
  statement: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  proof: sub_pow_expChar_pow_of_commute _ _ .all ..

中文:
引理 sub_pow_expChar_pow
  结论: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  证明: sub_pow_expChar_pow_of_commute _ _ .all ..

Depends on / 依赖: sub_pow_expChar_pow_of_commute
-/
lemma sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
sub_pow_expChar_pow_of_commute _ _ .all ..

/--
lemma `sub_pow_eq_mul_pow_sub_pow_div_expChar` / 引理 `sub_pow_eq_mul_pow_sub_pow_div_expChar`

English:
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar
  proof: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ .all ..

中文:
引理 sub_pow_eq_mul_pow_sub_pow_div_expChar
  证明: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ .all ..

Depends on / 依赖: sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ .all ..

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/--
lemma `sub_pow_char` / 引理 `sub_pow_char`

English:
lemma sub_pow_char
  statement: (x - y) ^ p = x ^ p - y ^ p
  proof: sub_pow_expChar ..

中文:
引理 sub_pow_char
  结论: (x - y) ^ p = x ^ p - y ^ p
  证明: sub_pow_expChar ..

Depends on / 依赖: sub_pow_expChar
-/
lemma sub_pow_char : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar ..
/--
lemma `sub_pow_char_pow` / 引理 `sub_pow_char_pow`

English:
lemma sub_pow_char_pow
  statement: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  proof: sub_pow_expChar_pow ..

中文:
引理 sub_pow_char_pow
  结论: (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
  证明: sub_pow_expChar_pow ..

Depends on / 依赖: sub_pow_expChar_pow
-/
lemma sub_pow_char_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sub_pow_expChar_pow ..

/--
lemma `sub_pow_eq_mul_pow_sub_pow_div_char` / 引理 `sub_pow_eq_mul_pow_sub_pow_div_char`

English:
lemma sub_pow_eq_mul_pow_sub_pow_div_char
  proof: sub_pow_eq_mul_pow_sub_pow_div_expChar ..

中文:
引理 sub_pow_eq_mul_pow_sub_pow_div_char
  证明: sub_pow_eq_mul_pow_sub_pow_div_expChar ..

Depends on / 依赖: sub_pow_eq_mul_pow_sub_pow_div_expChar
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_char :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar ..

end CharP

/--
lemma `Nat.Prime.dvd_add_pow_sub_pow_of_dvd` / 引理 `Nat.Prime.dvd_add_pow_sub_pow_of_dvd`

English:
lemma Nat.Prime.dvd_add_pow_sub_pow_of_dvd
  statement: (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p)
  proof: by
  rw [add_pow_prime_eq hpri]; rw [add_right_comm]; rw [add_assoc]; rw [add_sub_assoc]; rw [add_sub_cancel_right]
  exact dvd_add h₁ (h₂.trans <| (dvd_mul_right ..).trans <| dvd_mul_right ..)

中文:
引理 自然数.素.dvd_add_pow_sub_pow_of_dvd
  结论: (hpri : p.素) {r : R} (h₁ : r ∣ x ^ p)
  证明: by
  rw [add_pow_prime_eq hpri]; rw [add_right_comm]; rw [add_assoc]; rw [add_sub_assoc]; rw [add_sub_cancel_right]
  exact dvd_add h₁ (h₂.trans <| (dvd_mul_right ..).trans <| dvd_mul_right ..)

Depends on / 依赖: add_assoc, add_pow_prime_eq, add_right_comm, add_sub_assoc, add_sub_cancel_right, dvd_add, dvd_mul_right
-/
lemma Nat.Prime.dvd_add_pow_sub_pow_of_dvd (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p)
    (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p - y ^ p := by
  rw [add_pow_prime_eq hpri]; rw [add_right_comm]; rw [add_assoc]; rw [add_sub_assoc]; rw [add_sub_cancel_right]
  exact dvd_add h₁ (h₂.trans <| (dvd_mul_right ..).trans <| dvd_mul_right ..)

end CommRing


namespace CharP

section

variable (R) [NonAssocRing R]

/--
theorem `char_ne_zero_of_finite` / 定理 `char_ne_zero_of_finite`

English:
theorem char_ne_zero_of_finite
  given: (p : Nat) [CharP R p] [Finite R]
  statement: p != 0
  proof: by
  rintro rfl
  have : CharZero R := charP_to_charZero R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : Nat -> R))

中文:
定理 char_ne_zero_of_finite
  条件: (p : 自然数) [特征p R p] [有限 R]
  结论: p != 0
  证明: by
  rintro rfl
  have : CharZero R := charP_to_charZero R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : Nat -> R))

Depends on / 依赖: CharZero, Nat.cast_injective, absurd, cast_injective, charP_to_charZero, not_injective_infinite_finite
-/
theorem char_ne_zero_of_finite (p : Nat) [CharP R p] [Finite R] : p != 0 := by
  rintro rfl
  have : CharZero R := charP_to_charZero R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : Nat -> R))

/--
theorem `ringChar_ne_zero_of_finite` / 定理 `ringChar_ne_zero_of_finite`

English:
theorem ringChar_ne_zero_of_finite
  given: [Finite R]
  statement: ringChar R != 0
  proof: char_ne_zero_of_finite R (ringChar R)

中文:
定理 ringChar_ne_zero_of_finite
  条件: [有限 R]
  结论: ringChar R != 0
  证明: char_ne_zero_of_finite R (ringChar R)

Depends on / 依赖: char_ne_zero_of_finite, ringChar
-/
theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R != 0 :=
  char_ne_zero_of_finite R (ringChar R)

end

section Ring

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

/--
theorem `char_is_prime` / 定理 `char_is_prime`

English:
theorem char_is_prime
  given: (p : Nat) [CharP R p]
  statement: p.Prime
  proof: Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)

中文:
定理 char_is_prime
  条件: (p : 自然数) [特征p R p]
  结论: p.素
  证明: Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)

Depends on / 依赖: Or.resolve_right, char_is_prime_or_zero, char_ne_zero_of_finite, resolve_right
-/
theorem char_is_prime (p : Nat) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)

/--
lemma `prime_ringChar` / 引理 `prime_ringChar`

English:
lemma prime_ringChar
  statement: Nat.Prime (ringChar R)
  proof: by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

中文:
引理 prime_ringChar
  结论: 自然数.素 (ringChar R)
  证明: by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

Depends on / 依赖: CharP.char_prime_of_ne_zero, CharP.ringChar_ne_zero_of_finite, char_prime_of_ne_zero, ringChar_ne_zero_of_finite
-/
lemma prime_ringChar : Nat.Prime (ringChar R) := by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

end Ring
end CharP

/-
Preliminary definitions and results for the Frobenius map.
Necessary here for simple results about sums of `p`-powers that are used in files forbidding
to import algebra-related definitions.
-/
section Frobenius

variable (R : Type*) [CommSemiring R]
variable (p n : Nat) [ExpChar R p]

/--
Definition of `frobenius` / `frobenius` 的定义

English:
definition frobenius
  signature: : R ->+* R where
  body: powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' _ _ := add_pow_expChar ..

中文:
定义 frobenius
  签名: : R ->+* R where
  定义体: powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' _ _ := add_pow_expChar ..

Depends on / 依赖: powMonoidHom
-/
def frobenius : R ->+* R where
  __ := powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' _ _ := add_pow_expChar ..

/--
Definition of `iterateFrobenius` / `iterateFrobenius` 的定义

English:
definition iterateFrobenius
  signature: : R ->+* R where
  body: powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' _ _ := add_pow_expChar_pow ..

中文:
定义 iterateFrobenius
  签名: : R ->+* R where
  定义体: powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' _ _ := add_pow_expChar_pow ..

Depends on / 依赖: powMonoidHom
-/
def iterateFrobenius : R ->+* R where
  __ := powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' _ _ := add_pow_expChar_pow ..

variable {R}

/--
lemma `list_sum_pow_char` / 引理 `list_sum_pow_char`

English:
lemma list_sum_pow_char
  given: (l : List R)
  statement: l.sum ^ p = (l.map (· ^ p : R -> R)).sum
  proof: map_list_sum (frobenius R p) _

中文:
引理 list_sum_pow_char
  条件: (l : 列表 R)
  结论: l.求和 ^ p = (l.map (· ^ p : R -> R)).求和
  证明: map_list_sum (frobenius R p) _

Depends on / 依赖: frobenius, map_list_sum
-/
lemma list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R -> R)).sum :=
  map_list_sum (frobenius R p) _

/--
lemma `multiset_sum_pow_char` / 引理 `multiset_sum_pow_char`

English:
lemma multiset_sum_pow_char
  given: (s : Multiset R)
  statement: s.sum ^ p = (s.map (· ^ p : R -> R)).sum
  proof: map_multiset_sum (frobenius R p) _

中文:
引理 multiset_sum_pow_char
  条件: (s : Multiset R)
  结论: s.求和 ^ p = (s.map (· ^ p : R -> R)).求和
  证明: map_multiset_sum (frobenius R p) _

Depends on / 依赖: frobenius, map_multiset_sum
-/
lemma multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R -> R)).sum :=
  map_multiset_sum (frobenius R p) _

/--
lemma `sum_pow_char` / 引理 `sum_pow_char`

English:
lemma sum_pow_char
  given: {ι : Type*} (s : Finset ι) (f : ι -> R)
  statement: (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p
  proof: map_sum (frobenius R p) _ _

中文:
引理 sum_pow_char
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R)
  结论: (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p
  证明: map_sum (frobenius R p) _ _

Depends on / 依赖: frobenius, map_sum
-/
lemma sum_pow_char {ι : Type*} (s : Finset ι) (f : ι -> R) : (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p :=
  map_sum (frobenius R p) _ _

/--
lemma `list_sum_pow_char_pow` / 引理 `list_sum_pow_char_pow`

English:
lemma list_sum_pow_char_pow
  given: (l : List R)
  statement: l.sum ^ p ^ n = (l.map (· ^ p ^ n : R -> R)).sum
  proof: map_list_sum (iterateFrobenius R p n) _

中文:
引理 list_sum_pow_char_pow
  条件: (l : 列表 R)
  结论: l.求和 ^ p ^ n = (l.map (· ^ p ^ n : R -> R)).求和
  证明: map_list_sum (iterateFrobenius R p n) _

Depends on / 依赖: iterateFrobenius, map_list_sum
-/
lemma list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R -> R)).sum :=
  map_list_sum (iterateFrobenius R p n) _

/--
lemma `multiset_sum_pow_char_pow` / 引理 `multiset_sum_pow_char_pow`

English:
lemma multiset_sum_pow_char_pow
  given: (s : Multiset R)
  proof: map_multiset_sum (iterateFrobenius R p n) _

中文:
引理 multiset_sum_pow_char_pow
  条件: (s : Multiset R)
  证明: map_multiset_sum (iterateFrobenius R p n) _

Depends on / 依赖: iterateFrobenius, map_multiset_sum
-/
lemma multiset_sum_pow_char_pow (s : Multiset R) :
    s.sum ^ p ^ n = (s.map (· ^ p ^ n : R -> R)).sum :=
  map_multiset_sum (iterateFrobenius R p n) _

/--
lemma `sum_pow_char_pow` / 引理 `sum_pow_char_pow`

English:
lemma sum_pow_char_pow
  given: {ι : Type*} (s : Finset ι) (f : ι -> R)
  proof: map_sum (iterateFrobenius R p n) _ _

中文:
引理 sum_pow_char_pow
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R)
  证明: map_sum (iterateFrobenius R p n) _ _

Depends on / 依赖: iterateFrobenius, map_sum
-/
lemma sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι -> R) :
    (∑ i in s, f i) ^ p ^ n = ∑ i in s, f i ^ p ^ n := map_sum (iterateFrobenius R p n) _ _

end Frobenius
