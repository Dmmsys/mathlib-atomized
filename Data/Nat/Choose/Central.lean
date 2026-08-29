/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `Nat.choose (2 * n) n`).

## Main definition and results

* `Nat.centralBinom`: the central binomial coefficient, `(2 * n).choose n`.
* `Nat.succ_mul_centralBinom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `Nat.four_pow_lt_mul_centralBinom`: an exponential lower bound on the central binomial
  coefficient.
* `succ_dvd_centralBinom`: The result that `n+1 ∣ n.centralBinom`, ensuring that the explicit
  definition of the Catalan numbers is integer-valued.
-/

@[expose] public section


namespace Nat

/--
Definition of `centralBinom` / `centralBinom` 的定义

English:
definition centralBinom
  signature: (n : Nat)
  body: (2 * n).choose n

中文:
定义 centralBinom
  签名: (n : 自然数)
  定义体: (2 * n).choose n
-/
def centralBinom (n : Nat) :=
  (2 * n).choose n

/--
theorem `centralBinom_eq_two_mul_choose` / 定理 `centralBinom_eq_two_mul_choose`

English:
theorem centralBinom_eq_two_mul_choose
  given: (n : Nat)
  statement: centralBinom n = (2 * n).choose n
  proof: rfl

中文:
定理 centralBinom_eq_two_mul_choose
  条件: (n : 自然数)
  结论: centralBinom n = (2 * n).choose n
  证明: rfl
-/
theorem centralBinom_eq_two_mul_choose (n : Nat) : centralBinom n = (2 * n).choose n :=
  rfl

/--
theorem `centralBinom_pos` / 定理 `centralBinom_pos`

English:
theorem centralBinom_pos
  given: (n : Nat)
  statement: 0 < centralBinom n
  proof: choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)

中文:
定理 centralBinom_pos
  条件: (n : 自然数)
  结论: 0 < centralBinom n
  证明: choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)

Depends on / 依赖: Nat.le_mul_of_pos_left, choose_pos, le_mul_of_pos_left, zero_lt_two
-/
theorem centralBinom_pos (n : Nat) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)

/--
theorem `centralBinom_ne_zero` / 定理 `centralBinom_ne_zero`

English:
theorem centralBinom_ne_zero
  given: (n : Nat)
  statement: centralBinom n != 0
  proof: (centralBinom_pos n).ne'

@[simp]

中文:
定理 centralBinom_ne_zero
  条件: (n : 自然数)
  结论: centralBinom n != 0
  证明: (centralBinom_pos n).ne'

@[simp]

Depends on / 依赖: centralBinom_pos
-/
theorem centralBinom_ne_zero (n : Nat) : centralBinom n != 0 :=
  (centralBinom_pos n).ne'

@[simp]
/--
theorem `centralBinom_zero` / 定理 `centralBinom_zero`

English:
theorem centralBinom_zero
  statement: centralBinom 0 = 1
  proof: choose_zero_right _

中文:
定理 centralBinom_zero
  结论: centralBinom 0 = 1
  证明: choose_zero_right _

Depends on / 依赖: choose_zero_right
-/
theorem centralBinom_zero : centralBinom 0 = 1 :=
  choose_zero_right _

/--
theorem `choose_le_centralBinom` / 定理 `choose_le_centralBinom`

English:
theorem choose_le_centralBinom
  given: (r n : Nat)
  statement: choose (2 * n) r <= centralBinom n
  proof: calc
    (2 * n).choose r <= (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]

中文:
定理 choose_le_centralBinom
  条件: (r n : 自然数)
  结论: choose (2 * n) r <= centralBinom n
  证明: calc
    (2 * n).choose r <= (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]

Depends on / 依赖: Nat.mul_div_cancel_left, choose_le_middle, mul_div_cancel_left, zero_lt_two
-/
theorem choose_le_centralBinom (r n : Nat) : choose (2 * n) r <= centralBinom n :=
  calc
    (2 * n).choose r <= (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]

/--
theorem `centralBinom_strictMono` / 定理 `centralBinom_strictMono`

English:
theorem centralBinom_strictMono
  statement: StrictMono centralBinom
  proof: strictMono_nat_of_lt_succ (by grind [Nat.choose_pos, centralBinom])

中文:
定理 centralBinom_strictMono
  结论: 严格递增 centralBinom
  证明: strictMono_nat_of_lt_succ (by grind [Nat.choose_pos, centralBinom])

Depends on / 依赖: Nat.choose_pos, centralBinom, choose_pos, strictMono_nat_of_lt_succ
-/
theorem centralBinom_strictMono : StrictMono centralBinom :=
  strictMono_nat_of_lt_succ (by grind [Nat.choose_pos, centralBinom])

/--
theorem `two_le_centralBinom` / 定理 `two_le_centralBinom`

English:
theorem two_le_centralBinom
  given: (n : Nat) (n_pos : 0 < n)
  statement: 2 <= centralBinom n
  proof: calc
    2 <= 2 * n := Nat.le_mul_of_pos_right _ n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ <= centralBinom n := choose_le_centralBinom 1 n

中文:
定理 two_le_centralBinom
  条件: (n : 自然数) (n_pos : 0 < n)
  结论: 2 <= centralBinom n
  证明: calc
    2 <= 2 * n := Nat.le_mul_of_pos_right _ n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ <= centralBinom n := choose_le_centralBinom 1 n

Depends on / 依赖: Nat.le_mul_of_pos_right, centralBinom, choose_le_centralBinom, choose_one_right, le_mul_of_pos_right, n_pos
-/
theorem two_le_centralBinom (n : Nat) (n_pos : 0 < n) : 2 <= centralBinom n :=
  calc
    2 <= 2 * n := Nat.le_mul_of_pos_right _ n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ <= centralBinom n := choose_le_centralBinom 1 n

/--
theorem `centralBinom_le_four_pow` / 定理 `centralBinom_le_four_pow`

English:
theorem centralBinom_le_four_pow
  given: (n : Nat)
  statement: centralBinom n <= 4 ^ n
  proof: by
  grw [show 4 = 2 ^ 2 by rfl, ← pow_mul, centralBinom_eq_two_mul_choose, choose_le_two_pow]

中文:
定理 centralBinom_le_four_pow
  条件: (n : 自然数)
  结论: centralBinom n <= 4 ^ n
  证明: by
  grw [show 4 = 2 ^ 2 by rfl, ← pow_mul, centralBinom_eq_two_mul_choose, choose_le_two_pow]

Depends on / 依赖: centralBinom_eq_two_mul_choose, choose_le_two_pow, pow_mul
-/
theorem centralBinom_le_four_pow (n : Nat) : centralBinom n <= 4 ^ n := by
  grw [show 4 = 2 ^ 2 by rfl, ← pow_mul, centralBinom_eq_two_mul_choose, choose_le_two_pow]

/--
theorem `centralBinom_lt_four_pow` / 定理 `centralBinom_lt_four_pow`

English:
theorem centralBinom_lt_four_pow
  given: {n : Nat} (h : n != 0)
  statement: centralBinom n < 4 ^ n
  proof: by
  rw [show 4 = 2 ^ 2 by rfl]; rw [← pow_mul]
  apply choose_lt_two_pow
  lia

中文:
定理 centralBinom_lt_four_pow
  条件: {n : 自然数} (h : n != 0)
  结论: centralBinom n < 4 ^ n
  证明: by
  rw [show 4 = 2 ^ 2 by rfl]; rw [← pow_mul]
  apply choose_lt_two_pow
  lia

Depends on / 依赖: choose_lt_two_pow, pow_mul
-/
theorem centralBinom_lt_four_pow {n : Nat} (h : n != 0) : centralBinom n < 4 ^ n := by
  rw [show 4 = 2 ^ 2 by rfl]; rw [← pow_mul]
  apply choose_lt_two_pow
  lia

/--
theorem `succ_mul_centralBinom_succ` / 定理 `succ_mul_centralBinom_succ`

English:
theorem succ_mul_centralBinom_succ
  given: (n : Nat)
  proof: calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1

中文:
定理 succ_mul_centralBinom_succ
  条件: (n : 自然数)
  证明: calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1

Depends on / 依赖: Nat.add_sub_cancel_left, add_assoc, add_sub_cancel_left, choose_mul_succ_eq, choose_succ_right_eq, mul_assoc, mul_comm, two_mul
-/
theorem succ_mul_centralBinom_succ (n : Nat) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n :=
  calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n)) := by rw [two_mul n, add_assoc,
                                                               Nat.add_sub_cancel_left]
    _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [choose_mul_succ_eq]
    _ = 2 * (2 * n + 1) * (2 * n).choose n := by rw [mul_assoc, mul_comm (2 * n + 1)]

/--
theorem `four_pow_lt_mul_centralBinom` / 定理 `four_pow_lt_mul_centralBinom`

English:
theorem four_pow_lt_mul_centralBinom
  given: (n : Nat) (n_big : 4 <= n)
  statement: 4 ^ n < n * centralBinom n
  proof: by
  induction n using Nat.strong_induction_on with | _ n IH
  rcases lt_trichotomy n 4 with (hn | rfl | hn)
  · clear IH; exact False.elim ((not_lt.2 n_big) hn)
  · norm_num [centralBinom, choose]
  obtain ⟨n, rfl⟩ : exists m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  calc

中文:
定理 four_pow_lt_mul_centralBinom
  条件: (n : 自然数) (n_big : 4 <= n)
  结论: 4 ^ n < n * centralBinom n
  证明: by
  induction n using Nat.strong_induction_on with | _ n IH
  rcases lt_trichotomy n 4 with (hn | rfl | hn)
  · clear IH; exact False.elim ((not_lt.2 n_big) hn)
  · norm_num [centralBinom, choose]
  obtain ⟨n, rfl⟩ : exists m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  calc

Depends on / 依赖: False.elim, Nat.exists_eq_succ_of_ne_zero, Nat.le_of_lt_succ, Nat.ne_zero_of_lt, Nat.strong_induction_on, centralBinom, exists_eq_succ_of_ne_zero, le_of_lt_succ, lt_succ_self, lt_trichotomy, mul_assoc, n.lt_succ_self, n_big, ne_zero_of_lt, not_lt, pow_succ, strong_induction_on
-/
theorem four_pow_lt_mul_centralBinom (n : Nat) (n_big : 4 <= n) : 4 ^ n < n * centralBinom n := by
  induction n using Nat.strong_induction_on with | _ n IH
  rcases lt_trichotomy n 4 with (hn | rfl | hn)
  · clear IH; exact False.elim ((not_lt.2 n_big) hn)
  · norm_num [centralBinom, choose]
  obtain ⟨n, rfl⟩ : exists m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  calc
    4 ^ (n + 1)
    _ = 4 * 4 ^ n := by rw [pow_succ']
    _ < 4 * (n * centralBinom n) := by gcongr; exact IH n n.lt_succ_self (Nat.le_of_lt_succ hn)
    _ <= 2 * (2 * n + 1) * centralBinom n := by rw [← mul_assoc]; linarith
    _ = (n + 1) * centralBinom (n + 1) := (succ_mul_centralBinom_succ n).symm

/--
theorem `four_pow_le_two_mul_self_mul_centralBinom` / 定理 `four_pow_le_two_mul_self_mul_centralBinom`

English:
theorem four_pow_le_two_mul_self_mul_centralBinom
  proof: (four_pow_lt_mul_centralBinom _ le_add_self).le
      _ <= 2 * (n + 4) * centralBinom (n + 4) := by
        rw [mul_assoc]; refine Nat.le_mul_of_pos_left _ zero_lt_two

中文:
定理 four_pow_le_two_mul_self_mul_centralBinom
  证明: (four_pow_lt_mul_centralBinom _ le_add_self).le
      _ <= 2 * (n + 4) * centralBinom (n + 4) := by
        rw [mul_assoc]; refine Nat.le_mul_of_pos_left _ zero_lt_two

Depends on / 依赖: Nat.le_mul_of_pos_left, centralBinom, four_pow_lt_mul_centralBinom, le_add_self, le_mul_of_pos_left, mul_assoc, zero_lt_two
-/
theorem four_pow_le_two_mul_self_mul_centralBinom :
    forall (n : Nat) (_ : 0 < n), 4 ^ n <= 2 * n * centralBinom n
  | 0, pr => (Nat.not_lt_zero _ pr).elim
  | 1, _ => by simp [centralBinom, choose]
  | 2, _ => by simp [centralBinom, choose]
  | 3, _ => by simp [centralBinom, choose]
  | n + 4, _ =>
    calc
      4 ^ (n + 4) <= (n + 4) * centralBinom (n + 4) :=
        (four_pow_lt_mul_centralBinom _ le_add_self).le
      _ <= 2 * (n + 4) * centralBinom (n + 4) := by
        rw [mul_assoc]; refine Nat.le_mul_of_pos_left _ zero_lt_two

/--
theorem `two_dvd_centralBinom_succ` / 定理 `two_dvd_centralBinom_succ`

English:
theorem two_dvd_centralBinom_succ
  given: (n : Nat)
  statement: 2 ∣ centralBinom (n + 1)
  proof: by
  use (n + 1 + n).choose n
  rw [centralBinom_eq_two_mul_choose]; rw [two_mul]; rw [← add_assoc]; rw [choose_succ_succ' (n + 1 + n) n]; rw [choose_symm_add]; rw [← two_mul]

中文:
定理 two_dvd_centralBinom_succ
  条件: (n : 自然数)
  结论: 2 ∣ centralBinom (n + 1)
  证明: by
  use (n + 1 + n).choose n
  rw [centralBinom_eq_two_mul_choose]; rw [two_mul]; rw [← add_assoc]; rw [choose_succ_succ' (n + 1 + n) n]; rw [choose_symm_add]; rw [← two_mul]

Depends on / 依赖: add_assoc, centralBinom_eq_two_mul_choose, choose_succ_succ, choose_symm_add, two_mul
-/
theorem two_dvd_centralBinom_succ (n : Nat) : 2 ∣ centralBinom (n + 1) := by
  use (n + 1 + n).choose n
  rw [centralBinom_eq_two_mul_choose]; rw [two_mul]; rw [← add_assoc]; rw [choose_succ_succ' (n + 1 + n) n]; rw [choose_symm_add]; rw [← two_mul]

/--
theorem `two_dvd_centralBinom_of_one_le` / 定理 `two_dvd_centralBinom_of_one_le`

English:
theorem two_dvd_centralBinom_of_one_le
  given: {n : Nat} (h : 0 < n)
  statement: 2 ∣ centralBinom n
  proof: by
  rw [← Nat.succ_pred_eq_of_pos h]
  exact two_dvd_centralBinom_succ n.pred

中文:
定理 two_dvd_centralBinom_of_one_le
  条件: {n : 自然数} (h : 0 < n)
  结论: 2 ∣ centralBinom n
  证明: by
  rw [← Nat.succ_pred_eq_of_pos h]
  exact two_dvd_centralBinom_succ n.pred

Depends on / 依赖: Nat.succ_pred_eq_of_pos, n.pred, succ_pred_eq_of_pos, two_dvd_centralBinom_succ
-/
theorem two_dvd_centralBinom_of_one_le {n : Nat} (h : 0 < n) : 2 ∣ centralBinom n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  exact two_dvd_centralBinom_succ n.pred

/--
theorem `succ_dvd_centralBinom` / 定理 `succ_dvd_centralBinom`

English:
theorem succ_dvd_centralBinom
  given: (n : Nat)
  statement: n + 1 ∣ n.centralBinom
  proof: by
  have h_s : (n + 1).Coprime (2 * n + 1) := by
    rw [two_mul]; rw [add_assoc]; rw [coprime_add_self_right]; rw [coprime_self_add_left]
    exact coprime_one_left n
  apply h_s.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_two
  rw [← mul_assoc]; rw [← succ_mul_centralBinom_suc

中文:
定理 succ_dvd_centralBinom
  条件: (n : 自然数)
  结论: n + 1 ∣ n.centralBinom
  证明: by
  have h_s : (n + 1).Coprime (2 * n + 1) := by
    rw [two_mul]; rw [add_assoc]; rw [coprime_add_self_right]; rw [coprime_self_add_left]
    exact coprime_one_left n
  apply h_s.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_two
  rw [← mul_assoc]; rw [← succ_mul_centralBinom_suc

Depends on / 依赖: Coprime, Nat.dvd_of_mul_dvd_mul_left, add_assoc, coprime_add_self_right, coprime_one_left, coprime_self_add_left, dvd_of_dvd_mul_left, dvd_of_mul_dvd_mul_left, h_s.dvd_of_dvd_mul_left, mul_assoc, mul_comm, mul_dvd_mul_left, succ_mul_centralBinom_succ, two_dvd_centralBinom_succ, two_mul, zero_lt_two
-/
theorem succ_dvd_centralBinom (n : Nat) : n + 1 ∣ n.centralBinom := by
  have h_s : (n + 1).Coprime (2 * n + 1) := by
    rw [two_mul]; rw [add_assoc]; rw [coprime_add_self_right]; rw [coprime_self_add_left]
    exact coprime_one_left n
  apply h_s.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_two
  rw [← mul_assoc]; rw [← succ_mul_centralBinom_succ]; rw [mul_comm]
  exact mul_dvd_mul_left _ (two_dvd_centralBinom_succ n)

end Nat
