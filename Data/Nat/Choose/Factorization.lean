/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the multiplicity of prime factors within certain size
bounds in binomial coefficients. These include:

* `Nat.factorization_choose_le_log`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `Nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul`: Primes from `2 * n / 3` to `n`
  do not appear in the factorization of the `n`th central binomial coefficient.
* `Nat.factorization_choose_eq_zero_of_lt`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

public section

open Finset List Finsupp

namespace Nat
variable {a b c : Nat}

/--
theorem `factorization_factorial` / 定理 `factorization_factorial`

English:
theorem factorization_factorial
  given: {p : Nat} (hp : p.Prime)
  proof: by
        rw [factorial_succ]; rw [factorization_mul (zero_ne_add_one n).symm n.factorial_ne_zero]; rw [coe_add]; rw [Pi.add_apply]
      _ = #{i in Ico 1 b | p ^ i ∣ n + 1} + ∑ i in Ico 1 b, n / p ^ i := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [ad

中文:
定理 factorization_factorial
  条件: {p : 自然数} (hp : p.素)
  证明: by
        rw [factorial_succ]; rw [factorization_mul (zero_ne_add_one n).symm n.factorial_ne_zero]; rw [coe_add]; rw [Pi.add_apply]
      _ = #{i in Ico 1 b | p ^ i ∣ n + 1} + ∑ i in Ico 1 b, n / p ^ i := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [ad

Depends on / 依赖: Nat.add_comm, Pi.add_apply, add_apply, add_comm, add_left_inj, coe_add, factorial_ne_zero, factorial_succ, factorization_eq_card_pow_dvd_of_lt, factorization_factorial, factorization_mul, hp.one_lt, le_succ, log_mono_right, lt_pow_of_log_lt, n.factorial_ne_zero, one_lt, sum_add_distrib, sum_bool, trans_lt
-/
theorem factorization_factorial {p : Nat} (hp : p.Prime) :
    forall {n b : Nat}, log p n < b -> (n)!.factorization p = ∑ i in Ico 1 b, n / p ^ i
  | 0, b, _ => by simp
  | n + 1, b, hb =>
    calc
      (n + 1)!.factorization p = (n + 1).factorization p + (n)!.factorization p := by
        rw [factorial_succ]; rw [factorization_mul (zero_ne_add_one n).symm n.factorial_ne_zero]; rw [coe_add]; rw [Pi.add_apply]
      _ = #{i in Ico 1 b | p ^ i ∣ n + 1} + ∑ i in Ico 1 b, n / p ^ i := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [add_left_inj]
        apply factorization_eq_card_pow_dvd_of_lt hp (zero_lt_succ n)
          (lt_pow_of_log_lt hp.one_lt hb)
      _ = ∑ i in Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) := by
        simp [Nat.add_comm, sum_add_distrib, sum_boole]
      _ = ∑ i in Ico 1 b, (n + 1) / p ^ i := Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/--
theorem `sub_one_mul_factorization_factorial` / 定理 `sub_one_mul_factorization_factorial`

English:
theorem sub_one_mul_factorization_factorial
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range,
    ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

中文:
定理 sub_one_mul_factorization_factorial
  条件: {n p : 自然数} (hp : p.素)
  证明: by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range,
    ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

Depends on / 依赖: Finset, Finset.sum_Ico_add, Ico_zero_eq_range, Nat.lt_add_one, factorization_factorial, lt_add_one, lt_succ_of_lt, sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, sum_Ico_add
-/
theorem sub_one_mul_factorization_factorial {n p : Nat} (hp : p.Prime) :
    (p - 1) * (n)!.factorization p = n - (p.digits n).sum := by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range,
    ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

/--
theorem `factorization_factorial_mul_succ` / 定理 `factorization_factorial_mul_succ`

English:
theorem factorization_factorial_mul_succ
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have h4 m (hm : m in Ico (p * n + 1) (p * (n + 1))) : m.factorization p = 0 := by
    apply factorization_eq_z

中文:
定理 factorization_factorial_mul_succ
  条件: {n p : 自然数} (hp : p.素)
  证明: by
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have h4 m (hm : m in Ico (p * n + 1) (p * (n + 1))) : m.factorization p = 0 := by
    apply factorization_eq_z

Depends on / 依赖: Nat.le_add_left, factorization, factorization_eq_zero_of_not_dvd, factorization_prod_apply, hp.two_le, le_add_left, m.factorization, mem_Ico, mem_Ico.mp, ne_zero_of_lt, not_dvd_of_lt_of_lt_mul_succ, prod_Ico_id_eq_factorial, two_le
-/
theorem factorization_factorial_mul_succ {n p : Nat} (hp : p.Prime) :
    (p * (n + 1))!.factorization p = (p * n)!.factorization p + (n + 1).factorization p + 1 := by
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have h4 m (hm : m in Ico (p * n + 1) (p * (n + 1))) : m.factorization p = 0 := by
    apply factorization_eq_zero_of_not_dvd
    exact not_dvd_of_lt_of_lt_mul_succ (mem_Ico.mp hm).left (mem_Ico.mp hm).right
  rw [← prod_Ico_id_eq_factorial]; rw [factorization_prod_apply (fun _ hx => ne_zero_of_lt
    (mem_Ico.mp hx).left)]; rw [← sum_Ico_consecutive _ h1 h3]; rw [add_assoc]; rw [sum_Ico_succ_top h2]; rw [← prod_Ico_id_eq_factorial]; rw [factorization_prod_apply (fun _ hx => ne_zero_of_lt
    (mem_Ico.mp hx).left)]; rw [factorization_mul (ne_zero_of_lt h0) (zero_ne_add_one n).symm]; rw [coe_add]; rw [Pi.add_apply]; rw [hp.factorization_self]; rw [sum_congr rfl h4]; rw [sum_const_zero]; rw [zero_add]; rw [add_comm 1]

/--
theorem `factorization_factorial_mul` / 定理 `factorization_factorial_mul`

English:
theorem factorization_factorial_mul
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring

中文:
定理 factorization_factorial_mul
  条件: {n p : 自然数} (hp : p.素)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring

Depends on / 依赖: factorial_ne_zero, factorial_succ, factorization_factorial_mul_succ, factorization_mul, zero_ne_add_one
-/
theorem factorization_factorial_mul {n p : Nat} (hp : p.Prime) :
    (p * n)!.factorization p = (n)!.factorization p + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring

/--
theorem `factorization_factorial_le_div_pred` / 定理 `factorization_factorial_le_div_pred`

English:
theorem factorization_factorial_le_div_pred
  given: {p : Nat} (hp : p.Prime) (n : Nat)
  proof: by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

中文:
定理 factorization_factorial_le_div_pred
  条件: {p : 自然数} (hp : p.素) (n : 自然数)
  证明: by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

Depends on / 依赖: Nat.geom_sum_Ico_le, Nat.lt_add_one, factorization_factorial, geom_sum_Ico_le, hp.two_le, lt_add_one, two_le
-/
theorem factorization_factorial_le_div_pred {p : Nat} (hp : p.Prime) (n : Nat) :
    (n)!.factorization p <= (n / (p - 1) : Nat) := by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

/--
lemma `multiplicity_choose_aux` / 引理 `multiplicity_choose_aux`

English:
lemma multiplicity_choose_aux
  given: {p n b k : Nat} (hp : p.Prime) (hkn : k <= n)
  proof: calc
    ∑ i in Finset.Ico 1 b, n / p ^ i = ∑ i in Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i in Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i <= k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div

中文:
引理 multiplicity_choose_aux
  条件: {p n b k : 自然数} (hp : p.素) (hkn : k <= n)
  证明: calc
    ∑ i in Finset.Ico 1 b, n / p ^ i = ∑ i in Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i in Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i <= k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div

Depends on / 依赖: Finset, Finset.Ico, Nat.add_div, add_div, add_tsub_cancel_of_le, hp.pos, pow_pos, sum_add_distrib, sum_boole
-/
lemma multiplicity_choose_aux {p n b k : Nat} (hp : p.Prime) (hkn : k <= n) :
    ∑ i in Finset.Ico 1 b, n / p ^ i =
      ((∑ i in Finset.Ico 1 b, k / p ^ i) + ∑ i in Finset.Ico 1 b, (n - k) / p ^ i) +
        #{i in Ico 1 b | p ^ i <= k % p ^ i + (n - k) % p ^ i} :=
  calc
    ∑ i in Finset.Ico 1 b, n / p ^ i = ∑ i in Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i in Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i <= k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by simp [sum_add_distrib, sum_boole]

/--
theorem `factorization_choose'` / 定理 `factorization_choose'`

English:
theorem factorization_choose'
  given: {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) < b)
  proof: by
  have h₁ : (choose (n + k) k).factorization p + (k ! * n !).factorization p
    = #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply]; rw [← 

中文:
定理 factorization_choose'
  条件: {p n k b : 自然数} (hp : p.素) (hnb : log p (n + k) < b)
  证明: by
  have h₁ : (choose (n + k) k).factorization p + (k ! * n !).factorization p
    = #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply]; rw [← 

Depends on / 依赖: Pi.add_apply, add_apply, add_tsub_cancel_right, choose_mul_factorial_mul_factorial, choose_pos, coe_add, factorial_, factorial_ne_zero, factorization, factorization_factorial, factorization_mul, le_add_left, mul_assoc, ne_of_gt
-/
theorem factorization_choose' {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) < b) :
    (choose (n + k) k).factorization p = #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} := by
  have h₁ : (choose (n + k) k).factorization p + (k ! * n !).factorization p
    = #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply]; rw [← coe_add]; rw [← factorization_mul (ne_of_gt <| choose_pos (le_add_left k n))
      (by positivity)]; rw [← mul_assoc]; rw [h2]; rw [factorization_factorial hp hnb]; rw [factorization_mul (factorial_ne_zero k) (factorial_ne_zero n)]; rw [coe_add]; rw [Pi.add_apply]; rw [factorization_factorial hp ((log_mono_right (le_add_left k n)).trans_lt
      hnb)]; rw [factorization_factorial hp ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb))]; rw [multiplicity_choose_aux hp (le_add_left k n)]
    simp only [add_tsub_cancel_right, add_comm]
  exact Nat.add_right_cancel h₁

/--
theorem `factorization_choose` / 定理 `factorization_choose`

English:
theorem factorization_choose
  given: {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : log p n < b)
  proof: by
  rw [← factorization_choose' hp ((Nat.sub_add_cancel hkn).symm ▸ hnb)]; rw [Nat.sub_add_cancel hkn]

中文:
定理 factorization_choose
  条件: {p n k b : 自然数} (hp : p.素) (hkn : k <= n) (hnb : log p n < b)
  证明: by
  rw [← factorization_choose' hp ((Nat.sub_add_cancel hkn).symm ▸ hnb)]; rw [Nat.sub_add_cancel hkn]

Depends on / 依赖: Nat.sub_add_cancel, factorization_choose, sub_add_cancel
-/
theorem factorization_choose {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : log p n < b) :
    (choose n k).factorization p = #{i in Ico 1 b | p ^ i <= k % p ^ i + (n - k) % p ^ i} := by
  rw [← factorization_choose' hp ((Nat.sub_add_cancel hkn).symm ▸ hnb)]; rw [Nat.sub_add_cancel hkn]

/--
theorem `factorization_le_factorization_of_dvd_right` / 定理 `factorization_le_factorization_of_dvd_right`

English:
theorem factorization_le_factorization_of_dvd_right
  given: (h : b ∣ c) (hb : b != 0) (hc : c != 0)
  proof: by
  obtain ⟨k, rfl⟩ := h; simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

中文:
定理 factorization_le_factorization_of_dvd_right
  条件: (h : b ∣ c) (hb : b != 0) (hc : c != 0)
  证明: by
  obtain ⟨k, rfl⟩ := h; simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

Depends on / 依赖: Nat.ne_zero_of_mul_ne_zero_right, factorization_mul, ne_zero_of_mul_ne_zero_right
-/
theorem factorization_le_factorization_of_dvd_right (h : b ∣ c) (hb : b != 0) (hc : c != 0) :
    b.factorization a <= c.factorization a := by
  obtain ⟨k, rfl⟩ := h; simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

/--
theorem `factorization_le_factorization_choose_add` / 定理 `factorization_le_factorization_choose_add`

English:
theorem factorization_le_factorization_choose_add
  given: {p : Nat}

中文:
定理 factorization_le_factorization_choose_add
  条件: {p : 自然数}
-/
theorem factorization_le_factorization_choose_add {p : Nat} :
    forall {n k : Nat}, k <= n -> k != 0 ->
      n.factorization p <= (choose n k).factorization p + k.factorization p
  | n, 0, _, _ => by tauto
  | 0, x + 1, _, _ => by simp
  | n + 1, k + 1, hkn, hk => by
    rw [← Pi.add_apply]; rw [← coe_add]; rw [← factorization_mul (ne_of_gt <| choose_pos hkn)
      (zero_ne_add_one k).symm]
    refine factorization_le_factorization_of_dvd_right ?_ (zero_ne_add_one n).symm
      (Nat.mul_ne_zero (ne_of_gt <| choose_pos hkn) (by positivity))
    rw [← add_one_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : Nat}

/--
theorem `factorization_choose_prime_pow_add_factorization` / 定理 `factorization_choose_prime_pow_add_factorization`

English:
theorem factorization_choose_prime_pow_add_factorization
  statement: (hp : p.Prime) (hkn : k <= p ^ n)
  proof: by
  apply le_antisymm
  · have hdisj : Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
        {i in Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, dvd_iff_mod_eq_zero, Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_s

中文:
定理 factorization_choose_prime_pow_add_factorization
  结论: (hp : p.素) (hkn : k <= p ^ n)
  证明: by
  apply le_antisymm
  · have hdisj : Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
        {i in Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, dvd_iff_mod_eq_zero, Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_s

Depends on / 依赖: Disjoint, Finset, Finset.disjoint_right, Nat.mod_lt, Nat.pow_lt_pow_succ, bot_lt, card_union_of_disjoint, contextual, disjoint_right, dvd_iff_mod_eq_zero, factorization_choose, factorization_eq_card_pow_dvd_of_lt, filter_l, filter_union_right, hk0.bot_lt, hp.one_lt, hp.pos, le_antisymm, log_pow, lt_of_le_of_lt
-/
theorem factorization_choose_prime_pow_add_factorization (hp : p.Prime) (hkn : k <= p ^ n)
    (hk0 : k != 0) : (choose (p ^ n) k).factorization p + k.factorization p = n := by
  apply le_antisymm
  · have hdisj : Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
        {i in Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, dvd_iff_mod_eq_zero, Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_succ_self _)]; rw [factorization_eq_card_pow_dvd_of_lt hp
      hk0.bot_lt (lt_of_le_of_lt hkn <| Nat.pow_lt_pow_succ hp.one_lt)]; rw [log_pow hp.one_lt]; rw [← card_union_of_disjoint hdisj]; rw [filter_union_right]
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le
      fun x => p ^ x <= k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
    rwa [card_Ico 1 n.succ] at filter_le_Ico
  · nth_rewrite 1 [← factorization_pow_self (n := n) hp]
    exact factorization_le_factorization_choose_add hkn hk0

/--
theorem `factorization_choose_prime_pow` / 定理 `factorization_choose_prime_pow`

English:
theorem factorization_choose_prime_pow
  given: {p n k : Nat} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0)
  proof: by
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]

中文:
定理 factorization_choose_prime_pow
  条件: {p n k : 自然数} (hp : p.素) (hkn : k <= p ^ n) (hk0 : k != 0)
  证明: by
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Nat.add_sub_cancel_right, add_sub_cancel_right, factorization_choose_prime_pow_add_factorization, nth_rewrite
-/
theorem factorization_choose_prime_pow {p n k : Nat} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0) :
    (choose (p ^ n) k).factorization p = n - k.factorization p := by
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]

end Nat


namespace Nat

variable {p n k : Nat}

/--
theorem `factorization_choose_le_log` / 定理 `factorization_choose_le_log`

English:
theorem factorization_choose_le_log
  statement: (choose n k).factorization p <= log p n
  proof: by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_not_prime h
  have hkn : k <= n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_choose hp hkn (Nat.lt_add_on

中文:
定理 factorization_choose_le_log
  结论: (choose n k).factorization p <= log p n
  证明: by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_not_prime h
  have hkn : k <= n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_choose hp hkn (Nat.lt_add_on

Depends on / 依赖: Nat.card_Ico, Nat.lt_add_one, Not.imp_symm, card_Ico, card_filter_le, choose_eq_zero_of_lt, factorization, factorization_choose, factorization_eq_zero_of_not_prime, imp_symm, le_of_not_gt, lt_add_one, p.Prime, trans_eq
-/
theorem factorization_choose_le_log : (choose n k).factorization p <= log p n := by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_not_prime h
  have hkn : k <= n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_choose hp hkn (Nat.lt_add_one _)]
  exact (card_filter_le ..).trans_eq (Nat.card_Ico _ _)

/--
theorem `pow_factorization_choose_le` / 定理 `pow_factorization_choose_le`

English:
theorem pow_factorization_choose_le
  given: (hn : 0 < n)
  statement: p ^ (choose n k).factorization p <= n
  proof: pow_le_of_le_log hn.ne' factorization_choose_le_log

中文:
定理 pow_factorization_choose_le
  条件: (hn : 0 < n)
  结论: p ^ (choose n k).factorization p <= n
  证明: pow_le_of_le_log hn.ne' factorization_choose_le_log

Depends on / 依赖: factorization_choose_le_log, hn.ne, pow_le_of_le_log
-/
theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p <= n :=
  pow_le_of_le_log hn.ne' factorization_choose_le_log

/--
theorem `factorization_choose_le_one` / 定理 `factorization_choose_le_one`

English:
theorem factorization_choose_le_one
  given: (p_large : n < p ^ 2)
  statement: (choose n k).factorization p <= 1
  proof: by
  apply factorization_choose_le_log.trans
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  exact Nat.lt_succ_iff.1 (log_lt_of_lt_pow hn0 p_large)

中文:
定理 factorization_choose_le_one
  条件: (p_large : n < p ^ 2)
  结论: (choose n k).factorization p <= 1
  证明: by
  apply factorization_choose_le_log.trans
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  exact Nat.lt_succ_iff.1 (log_lt_of_lt_pow hn0 p_large)

Depends on / 依赖: Nat.lt_succ_iff, eq_or_ne, factorization_choose_le_log, factorization_choose_le_log.trans, log_lt_of_lt_pow, lt_succ_iff, p_large
-/
theorem factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p <= 1 := by
  apply factorization_choose_le_log.trans
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  exact Nat.lt_succ_iff.1 (log_lt_of_lt_pow hn0 p_large)

/--
theorem `factorization_choose_of_lt_three_mul` / 定理 `factorization_choose_of_lt_three_mul`

English:
theorem factorization_choose_of_lt_three_mul
  statement: (hp' : p != 2) (hk : p <= k) (hk' : p <= n - k)
  proof: by
  rcases em' p.Prime with hp | hp
  · exact factorization_eq_zero_of_not_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  simp only [factorization_choose hp hkn (Nat.lt_add_one _), card_eq_zero, filter_eq_empty_iff,
    mem_Ico, not_le, and_imp]
  i

中文:
定理 factorization_choose_of_lt_three_mul
  结论: (hp' : p != 2) (hk : p <= k) (hk' : p <= n - k)
  证明: by
  rcases em' p.Prime with hp | hp
  · exact factorization_eq_zero_of_not_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  simp only [factorization_choose hp hkn (Nat.lt_add_one _), card_eq_zero, filter_eq_empty_iff,
    mem_Ico, not_le, and_imp]
  i

Depends on / 依赖: Nat.lt_add_one, add_add_add_comm, add_le_add, add_le_add_left, add_lt_add_iff_left, and_imp, card_eq_zero, choose_eq_zero_of_lt, eq_or_lt_of_le, factorization_choose, factorization_eq_zero_of_not_prime, filter_eq_empty_iff, le_mul_of_one_le_right, lt_add_one, lt_of_le_of_lt, lt_or_ge, mem_Ico, not_le, p.Prime, pow_one
-/
theorem factorization_choose_of_lt_three_mul (hp' : p != 2) (hk : p <= k) (hk' : p <= n - k)
    (hn : n < 3 * p) : (choose n k).factorization p = 0 := by
  rcases em' p.Prime with hp | hp
  · exact factorization_eq_zero_of_not_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  simp only [factorization_choose hp hkn (Nat.lt_add_one _), card_eq_zero, filter_eq_empty_iff,
    mem_Ico, not_le, and_imp]
  intro i hi₁ hi
  rcases eq_or_lt_of_le hi₁ with (rfl | hi)
  · rw [pow_one, ← add_lt_add_iff_left (2 * p), ← succ_mul, two_mul, add_add_add_comm]
    exact
      lt_of_le_of_lt
        (add_le_add
          (add_le_add_left (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk)) (k % p))
          (add_le_add_left (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk'))
            ((n - k) % p)))
        (by rwa [div_add_mod, div_add_mod, add_tsub_cancel_of_le hkn])
  · replace hn : n < p ^ i := by
      have : 3 <= p := lt_of_le_of_ne hp.two_le hp'.symm
      calc
        n < 3 * p := hn
        _ <= p * p := by gcongr
        _ = p ^ 2 := (sq p).symm
        _ <= p ^ i := pow_right_mono₀ hp.one_lt.le hi
    rwa [mod_eq_of_lt (lt_of_le_of_lt hkn hn), mod_eq_of_lt (lt_of_le_of_lt tsub_le_self hn),
      add_tsub_cancel_of_le hkn]

/--
theorem `factorization_centralBinom_of_two_mul_self_lt_three_mul` / 定理 `factorization_centralBinom_of_two_mul_self_lt_three_mul`

English:
theorem factorization_centralBinom_of_two_mul_self_lt_three_mul
  statement: (n_big : 2 < n) (p_le_n : p <= n)
  proof: by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · lia
  · rw [two_mul, add_tsub_cancel_left]

中文:
定理 factorization_centralBinom_of_two_mul_self_lt_three_mul
  结论: (n_big : 2 < n) (p_le_n : p <= n)
  证明: by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · lia
  · rw [two_mul, add_tsub_cancel_left]

Depends on / 依赖: add_tsub_cancel_left, factorization_choose_of_lt_three_mul, p_le_n, p_le_n.trans, two_mul
-/
theorem factorization_centralBinom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p_le_n : p <= n)
    (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0 := by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · lia
  · rw [two_mul, add_tsub_cancel_left]

/--
theorem `factorization_factorial_eq_zero_of_lt` / 定理 `factorization_factorial_eq_zero_of_lt`

English:
theorem factorization_factorial_eq_zero_of_lt
  given: (h : n < p)
  statement: (factorial n).factorization p = 0
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [factorial_succ]; rw [factorization_mul n.succ_ne_zero n.factorial_ne_zero]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [hn (lt_of_succ_lt h)]; rw [add_zero]; rw [factorization_eq_zero_of_lt h]

中文:
定理 factorization_factorial_eq_zero_of_lt
  条件: (h : n < p)
  结论: (factorial n).factorization p = 0
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [factorial_succ]; rw [factorization_mul n.succ_ne_zero n.factorial_ne_zero]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [hn (lt_of_succ_lt h)]; rw [add_zero]; rw [factorization_eq_zero_of_lt h]

Depends on / 依赖: Finsupp, Finsupp.coe_add, Pi.add_apply, add_apply, add_zero, coe_add, factorial_ne_zero, factorial_succ, factorization_eq_zero_of_lt, factorization_mul, lt_of_succ_lt, n.factorial_ne_zero, n.succ_ne_zero, succ_ne_zero
-/
theorem factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factorization p = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [factorial_succ]; rw [factorization_mul n.succ_ne_zero n.factorial_ne_zero]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [hn (lt_of_succ_lt h)]; rw [add_zero]; rw [factorization_eq_zero_of_lt h]

/--
theorem `factorization_choose_eq_zero_of_lt` / 定理 `factorization_choose_eq_zero_of_lt`

English:
theorem factorization_choose_eq_zero_of_lt
  given: (h : n < p)
  statement: (choose n k).factorization p = 0
  proof: by
  by_cases! hnk : n < k; · simp [choose_eq_zero_of_lt hnk]
  rw [choose_eq_factorial_div_factorial hnk]; rw [factorization_div (factorial_mul_factorial_dvd_factorial hnk)]; rw [Finsupp.coe_tsub]; rw [Pi.sub_apply]; rw [factorization_factorial_eq_zero_of_lt h]; rw [zero_tsub]

中文:
定理 factorization_choose_eq_zero_of_lt
  条件: (h : n < p)
  结论: (choose n k).factorization p = 0
  证明: by
  by_cases! hnk : n < k; · simp [choose_eq_zero_of_lt hnk]
  rw [choose_eq_factorial_div_factorial hnk]; rw [factorization_div (factorial_mul_factorial_dvd_factorial hnk)]; rw [Finsupp.coe_tsub]; rw [Pi.sub_apply]; rw [factorization_factorial_eq_zero_of_lt h]; rw [zero_tsub]

Depends on / 依赖: Finsupp, Finsupp.coe_tsub, Pi.sub_apply, choose_eq_factorial_div_factorial, choose_eq_zero_of_lt, coe_tsub, factorial_mul_factorial_dvd_factorial, factorization_div, factorization_factorial_eq_zero_of_lt, sub_apply, zero_tsub
-/
theorem factorization_choose_eq_zero_of_lt (h : n < p) : (choose n k).factorization p = 0 := by
  by_cases! hnk : n < k; · simp [choose_eq_zero_of_lt hnk]
  rw [choose_eq_factorial_div_factorial hnk]; rw [factorization_div (factorial_mul_factorial_dvd_factorial hnk)]; rw [Finsupp.coe_tsub]; rw [Pi.sub_apply]; rw [factorization_factorial_eq_zero_of_lt h]; rw [zero_tsub]

/--
theorem `factorization_centralBinom_eq_zero_of_two_mul_lt` / 定理 `factorization_centralBinom_eq_zero_of_two_mul_lt`

English:
theorem factorization_centralBinom_eq_zero_of_two_mul_lt
  given: (h : 2 * n < p)
  proof: factorization_choose_eq_zero_of_lt h

中文:
定理 factorization_centralBinom_eq_zero_of_two_mul_lt
  条件: (h : 2 * n < p)
  证明: factorization_choose_eq_zero_of_lt h

Depends on / 依赖: factorization_choose_eq_zero_of_lt
-/
theorem factorization_centralBinom_eq_zero_of_two_mul_lt (h : 2 * n < p) :
    (centralBinom n).factorization p = 0 :=
  factorization_choose_eq_zero_of_lt h

/--
theorem `le_two_mul_of_factorization_centralBinom_pos` / 定理 `le_two_mul_of_factorization_centralBinom_pos`

English:
theorem le_two_mul_of_factorization_centralBinom_pos
  proof: le_of_not_gt (pos_iff_ne_zero.mp h_pos ∘ factorization_centralBinom_eq_zero_of_two_mul_lt)

中文:
定理 le_two_mul_of_factorization_centralBinom_pos
  证明: le_of_not_gt (pos_iff_ne_zero.mp h_pos ∘ factorization_centralBinom_eq_zero_of_two_mul_lt)

Depends on / 依赖: factorization_centralBinom_eq_zero_of_two_mul_lt, h_pos, le_of_not_gt, pos_iff_ne_zero, pos_iff_ne_zero.mp
-/
theorem le_two_mul_of_factorization_centralBinom_pos
    (h_pos : 0 < (centralBinom n).factorization p) : p <= 2 * n :=
  le_of_not_gt (pos_iff_ne_zero.mp h_pos ∘ factorization_centralBinom_eq_zero_of_two_mul_lt)

/--
theorem `prod_pow_factorization_choose` / 定理 `prod_pow_factorization_choose`

English:
theorem prod_pow_factorization_choose
  given: (n k : Nat) (hkn : k <= n)
  proof: by
  conv_rhs => rw [← prod_factorization_pow_eq_self (choose_ne_zero hkn)]
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff]; rw [Classical.not_not]; rw [factorization_choose_eq_zero_of_lt hp]
  · intro p _ h2
    

中文:
定理 prod_pow_factorization_choose
  条件: (n k : 自然数) (hkn : k <= n)
  证明: by
  conv_rhs => rw [← prod_factorization_pow_eq_self (choose_ne_zero hkn)]
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff]; rw [Classical.not_not]; rw [factorization_choose_eq_zero_of_lt hp]
  · intro p _ h2
    

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.mem_range, Finset.prod_subset, Finsupp, Finsupp.mem_support_iff, choose_ne_zero, contrapose, conv_rhs, eq_comm, factorization_choose_eq_zero_of_lt, mem_range, mem_support_iff, not_not, prod_factorization_pow_eq_self, prod_subset
-/
theorem prod_pow_factorization_choose (n k : Nat) (hkn : k <= n) :
    (∏ p in Finset.range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k := by
  conv_rhs => rw [← prod_factorization_pow_eq_self (choose_ne_zero hkn)]
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff]; rw [Classical.not_not]; rw [factorization_choose_eq_zero_of_lt hp]
  · intro p _ h2
    simp [Classical.not_not.1 (mt Finsupp.mem_support_iff.2 h2)]

/--
theorem `prod_pow_factorization_centralBinom` / 定理 `prod_pow_factorization_centralBinom`

English:
theorem prod_pow_factorization_centralBinom
  given: (n : Nat)
  proof: by
  apply prod_pow_factorization_choose
  lia

中文:
定理 prod_pow_factorization_centralBinom
  条件: (n : 自然数)
  证明: by
  apply prod_pow_factorization_choose
  lia

Depends on / 依赖: prod_pow_factorization_choose
-/
theorem prod_pow_factorization_centralBinom (n : Nat) :
    (∏ p in Finset.range (2 * n + 1), p ^ (centralBinom n).factorization p) = centralBinom n := by
  apply prod_pow_factorization_choose
  lia

end Nat
