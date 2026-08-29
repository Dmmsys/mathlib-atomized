/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic

/-!
# Lemmas about `Nat.Prime` using `Int`s
-/

public section


open Nat

namespace Int

/--
theorem `not_prime_of_int_mul` / 定理 `not_prime_of_int_mul`

English:
theorem not_prime_of_int_mul
  statement: {a b : Int} {c : Nat} (ha : a.natAbs != 1) (hb : b.natAbs != 1)
  proof: not_prime_of_mul_eq (natAbs_mul_natAbs_eq hc) ha hb

中文:
定理 not_prime_of_int_mul
  结论: {a b : 整数} {c : 自然数} (ha : a.natAbs != 1) (hb : b.natAbs != 1)
  证明: not_prime_of_mul_eq (natAbs_mul_natAbs_eq hc) ha hb

Depends on / 依赖: natAbs_mul_natAbs_eq, not_prime_of_mul_eq
-/
theorem not_prime_of_int_mul {a b : Int} {c : Nat} (ha : a.natAbs != 1) (hb : b.natAbs != 1)
    (hc : a * b = (c : Int)) : ¬Nat.Prime c :=
  not_prime_of_mul_eq (natAbs_mul_natAbs_eq hc) ha hb

/--
theorem `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` / 定理 `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`

English:
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  statement: {p : Nat} (p_prime : Nat.Prime p) {m n : Int}
  proof: have hpm' : p ^ k ∣ m.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpm
have hpn' : p ^ l ∣ n.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
rw [← Int.natAbs_mul]; apply Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpmn
  let 

中文:
定理 succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  结论: {p : 自然数} (p_prime : 自然数.素 p) {m n : 整数}
  证明: have hpm' : p ^ k ∣ m.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpm
have hpn' : p ^ l ∣ n.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
rw [← Int.natAbs_mul]; apply Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpmn
  let 

Depends on / 依赖: Int.dvd_natAbs, Int.natAbs_mul, Int.natCast_dvd_natCast, Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul, Or.inl, Or.inr, dvd_natAbs, hsd.elim, m.natAbs, n.natAbs, natAbs, natAbs_mul, natCast_dvd_natCast, p_prime, succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : Nat} (p_prime : Nat.Prime p) {m n : Int}
    {k l : Nat} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
have hpm' : p ^ k ∣ m.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpm
have hpn' : p ^ l ∣ n.natAbs := Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
rw [← Int.natAbs_mul]; apply Int.natCast_dvd_natCast.1 Int.dvd_natAbs.2 hpmn
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim (fun hsd1 => Or.inl (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd1))
    fun hsd2 => Or.inr (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd2)

/--
theorem `Prime.dvd_natAbs_of_coe_dvd_sq` / 定理 `Prime.dvd_natAbs_of_coe_dvd_sq`

English:
theorem Prime.dvd_natAbs_of_coe_dvd_sq
  given: {p : Nat} (hp : p.Prime) (k : Int) (h : (p : Int) ∣ k ^ 2)
  proof: by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← natAbs_mul, ← natCast_dvd, ← sq]

中文:
定理 素.dvd_natAbs_of_coe_dvd_sq
  条件: {p : 自然数} (hp : p.素) (k : 整数) (h : (p : 整数) ∣ k ^ 2)
  证明: by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← natAbs_mul, ← natCast_dvd, ← sq]

Depends on / 依赖: Nat.Prime.dvd_of_dvd_pow, dvd_of_dvd_pow, natAbs_mul, natCast_dvd
-/
theorem Prime.dvd_natAbs_of_coe_dvd_sq {p : Nat} (hp : p.Prime) (k : Int) (h : (p : Int) ∣ k ^ 2) :
    p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← natAbs_mul, ← natCast_dvd, ← sq]

end Int
