/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández, Yu Shao, Beibei Xiong, Weijie Jiang,
Yi Yuan
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as a natural number.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
  `m.bell * (m.map (fun j ↦ j !)).prod * Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq` shows that
  `uniformBell m n * n ! ^ m * m ! = (m * n) !`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

* `Nat.bell n`: the `n`th standard Bell number,
  which counts the number of partitions of a set of cardinality `n`

* `Nat.bell_succ n` shows that
  `Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell (n - k)`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

@[expose] public section

open Multiset Nat

namespace Multiset

/--
Definition of `bell` / `bell` 的定义

English:
definition bell
  signature: (m : Multiset Nat)
  body: Nat.multinomial m.toFinset (fun k => k * m.count k) *
    ∏ k in m.toFinset.erase 0, ∏ j in .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]

中文:
定义 bell
  签名: (m : Multiset 自然数)
  定义体: Nat.multinomial m.toFinset (fun k => k * m.count k) *
    ∏ k in m.toFinset.erase 0, ∏ j in .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]

Depends on / 依赖: Nat.multinomial, m.count, m.toFinset, m.toFinset.erase, multinomial, toFinset
-/
def bell (m : Multiset Nat) : Nat :=
  Nat.multinomial m.toFinset (fun k => k * m.count k) *
    ∏ k in m.toFinset.erase 0, ∏ j in .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]
/--
theorem `bell_zero` / 定理 `bell_zero`

English:
theorem bell_zero
  statement: bell 0 = 1
  proof: rfl

中文:
定理 bell_zero
  结论: bell 0 = 1
  证明: rfl
-/
theorem bell_zero : bell 0 = 1 := rfl

/--
theorem `bell_mul_eq_lemma` / 定理 `bell_mul_eq_lemma`

English:
theorem bell_mul_eq_lemma
  given: {x : Nat} (hx : x != 0)
  proof: by
        rw [factorial_succ]; rw [pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j in Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1) := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx]; rw [mul_comm c x]; rw [Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf

中文:
定理 bell_mul_eq_lemma
  条件: {x : 自然数} (hx : x != 0)
  证明: by
        rw [factorial_succ]; rw [pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j in Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1) := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx]; rw [mul_comm c x]; rw [Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf
-/
private theorem bell_mul_eq_lemma {x : Nat} (hx : x != 0) :
    forall c, x ! ^ c * c ! * ∏ j in Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j in Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j in Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        rw [factorial_succ]; rw [pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j in Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1) := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx]; rw [mul_comm c x]; rw [Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf

/--
theorem `bell_mul_eq` / 定理 `bell_mul_eq`

English:
theorem bell_mul_eq
  given: (m : Multiset Nat)
  proof: by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i in m.toFinset]; rw [(i * count i m)!) (by positivity)]
  simp only [← mul_assoc, Nat.multinomial_spec]
  rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm]
  congr
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 in m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_notMem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_notMem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    congr! 1 with x hx
    rw [← mul_assoc]; rw [bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

中文:
定理 bell_mul_eq
  条件: (m : Multiset 自然数)
  证明: by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i in m.toFinset]; rw [(i * count i m)!) (by positivity)]
  simp only [← mul_assoc, Nat.multinomial_spec]
  rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm]
  congr
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 in m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_notMem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_notMem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    congr! 1 with x hx
    rw [← mul_assoc]; rw [bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

Depends on / 依赖: Finset, Finset.prod_erase_mul, Finset.prod_mul_distrib, Finset.prod_multiset_map_count, Nat.mul_right_inj, Nat.multinomial_spec, factorial_zero, m.toFinset, mul_assoc, mul_comm, mul_one, mul_right_inj, multinomial_spec, nth_rewrite, one_pow, prod_erase_mul, prod_mul_distrib, prod_multiset_map_count, toFinset, zero_mul
-/
theorem bell_mul_eq (m : Multiset Nat) :
    m.bell * (m.map (fun j => j !)).prod * ∏ j in (m.toFinset.erase 0), (m.count j)! = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i in m.toFinset]; rw [(i * count i m)!) (by positivity)]
  simp only [← mul_assoc, Nat.multinomial_spec]
  rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm]
  congr
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 in m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_notMem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_notMem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    congr! 1 with x hx
    rw [← mul_assoc]; rw [bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

/--
theorem `bell_eq` / 定理 `bell_eq`

English:
theorem bell_eq
  given: (m : Multiset Nat)
  proof: by
  rw [← Nat.mul_left_inj]; rw [Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    exact Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)

中文:
定理 bell_eq
  条件: (m : Multiset 自然数)
  证明: by
  rw [← Nat.mul_left_inj]; rw [Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    exact Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)

Depends on / 依赖: Nat.div_mul_cancel, Nat.dvd_mul_left, Nat.factorial_pos, Nat.mul_left_inj, Nat.mul_pos, Nat.pos_iff_ne_zero, bell_mul_eq, div_mul_cancel, dvd_mul_left, factorial_pos, mul_assoc, mul_left_inj, mul_pos, pos_iff_ne_zero
-/
theorem bell_eq (m : Multiset Nat) :
    m.bell = m.sum ! / ((m.map fun j => j !).prod * ∏ j in m.toFinset.erase 0, (m.count j)!) := by
  rw [← Nat.mul_left_inj]; rw [Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    exact Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)

/--
theorem `bell_cons_mul_count` / 定理 `bell_cons_mul_count`

English:
theorem bell_cons_mul_count
  given: (m : Multiset Nat) {a : Nat} (ha : a != 0)
  proof: by
  let rest := ∏ j in (m.toFinset.erase 0).erase a, (m.count j)!
  have hrest : rest = ∏ j in ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! := by
    unfold rest
    congr! 1 with j hj
    · grind [Multiset.toFinset_cons]
    · simp [Finset.mem_erase.mp hj]
  let c := (m.map (· !)).prod * (m.count a)! * rest
  have hm0 : m.bell * c = m.sum ! := by
    have hsplit : (m.count a)! * rest = ∏ j in m.toFinset.erase 0, (m.count j)! := by
      by_cases hmem : a in m.toFinset.erase 0
      · rw [← Finset.mul_prod_erase _ _ hmem]
      · have hcount : m.count a = 0 := by grind [Multiset.count_eq_zero_of_notMem]
        simp [rest, Finset.erase_eq_of_notMem hmem, hcount]
    simpa [c, hsplit, mul_assoc] using Multiset.bell_mul_eq m
  have hm : m.sum ! * a ! = m.bell * a ! * c := by grind
have hc : 0 < a ! * c := Nat.mul_pos (by positivity)
    Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ (a := a) (by simp [*]), ← hrest] at hq
      simpa [c, Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm] using hq
    _ = ((m.sum + a).choose a * m.bell) * (a ! * c) := by
      simp [← Nat.add_choose_mul_factorial_mul_factorial, mul_assoc, hm]

中文:
定理 bell_cons_mul_count
  条件: (m : Multiset 自然数) {a : 自然数} (ha : a != 0)
  证明: by
  let rest := ∏ j in (m.toFinset.erase 0).erase a, (m.count j)!
  have hrest : rest = ∏ j in ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! := by
    unfold rest
    congr! 1 with j hj
    · grind [Multiset.toFinset_cons]
    · simp [Finset.mem_erase.mp hj]
  let c := (m.map (· !)).prod * (m.count a)! * rest
  have hm0 : m.bell * c = m.sum ! := by
    have hsplit : (m.count a)! * rest = ∏ j in m.toFinset.erase 0, (m.count j)! := by
      by_cases hmem : a in m.toFinset.erase 0
      · rw [← Finset.mul_prod_erase _ _ hmem]
      · have hcount : m.count a = 0 := by grind [Multiset.count_eq_zero_of_notMem]
        simp [rest, Finset.erase_eq_of_notMem hmem, hcount]
    simpa [c, hsplit, mul_assoc] using Multiset.bell_mul_eq m
  have hm : m.sum ! * a ! = m.bell * a ! * c := by grind
have hc : 0 < a ! * c := Nat.mul_pos (by positivity)
    Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ (a := a) (by simp [*]), ← hrest] at hq
      simpa [c, Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm] using hq
    _ = ((m.sum + a).choose a * m.bell) * (a ! * c) := by
      simp [← Nat.add_choose_mul_factorial_mul_factorial, mul_assoc, hm]
-/
private theorem bell_cons_mul_count (m : Multiset Nat) {a : Nat} (ha : a != 0) :
    (a ::ₘ m).bell * (a ::ₘ m).count a = (m.sum + a).choose a * m.bell := by
  let rest := ∏ j in (m.toFinset.erase 0).erase a, (m.count j)!
  have hrest : rest = ∏ j in ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! := by
    unfold rest
    congr! 1 with j hj
    · grind [Multiset.toFinset_cons]
    · simp [Finset.mem_erase.mp hj]
  let c := (m.map (· !)).prod * (m.count a)! * rest
  have hm0 : m.bell * c = m.sum ! := by
    have hsplit : (m.count a)! * rest = ∏ j in m.toFinset.erase 0, (m.count j)! := by
      by_cases hmem : a in m.toFinset.erase 0
      · rw [← Finset.mul_prod_erase _ _ hmem]
      · have hcount : m.count a = 0 := by grind [Multiset.count_eq_zero_of_notMem]
        simp [rest, Finset.erase_eq_of_notMem hmem, hcount]
    simpa [c, hsplit, mul_assoc] using Multiset.bell_mul_eq m
  have hm : m.sum ! * a ! = m.bell * a ! * c := by grind
have hc : 0 < a ! * c := Nat.mul_pos (by positivity)
    Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ (a := a) (by simp [*]), ← hrest] at hq
      simpa [c, Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm] using hq
    _ = ((m.sum + a).choose a * m.bell) * (a ! * c) := by
      simp [← Nat.add_choose_mul_factorial_mul_factorial, mul_assoc, hm]

end Multiset

namespace Nat

/--
Definition of `uniformBell` / `uniformBell` 的定义

English:
definition uniformBell
  signature: (m n : Nat)
  body: bell (replicate m n)

中文:
定义 uniformBell
  签名: (m n : 自然数)
  定义体: bell (replicate m n)

Depends on / 依赖: replicate
-/
def uniformBell (m n : Nat) : Nat := bell (replicate m n)

/--
theorem `uniformBell_eq` / 定理 `uniformBell_eq`

English:
theorem uniformBell_eq
  given: (m n : Nat)
  statement: m.uniformBell n =
  proof: by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

中文:
定理 uniformBell_eq
  条件: (m n : 自然数)
  结论: m.uniformBell n =
  证明: by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

Depends on / 依赖: Finset, Ne.symm, count_replicate, split_ifs, toFinset_replicate, uniformBell
-/
theorem uniformBell_eq (m n : Nat) : m.uniformBell n =
    ∏ p in (Finset.range m), choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

/--
theorem `uniformBell_zero_left` / 定理 `uniformBell_zero_left`

English:
theorem uniformBell_zero_left
  given: (n : Nat)
  statement: uniformBell 0 n = 1
  proof: by
  simp [uniformBell_eq]

中文:
定理 uniformBell_zero_left
  条件: (n : 自然数)
  结论: uniformBell 0 n = 1
  证明: by
  simp [uniformBell_eq]

Depends on / 依赖: uniformBell_eq
-/
theorem uniformBell_zero_left (n : Nat) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]

/--
theorem `uniformBell_zero_right` / 定理 `uniformBell_zero_right`

English:
theorem uniformBell_zero_right
  given: (m : Nat)
  statement: uniformBell m 0 = 1
  proof: by
  simp [uniformBell_eq]

中文:
定理 uniformBell_zero_right
  条件: (m : 自然数)
  结论: uniformBell m 0 = 1
  证明: by
  simp [uniformBell_eq]

Depends on / 依赖: uniformBell_eq
-/
theorem uniformBell_zero_right (m : Nat) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]

/--
theorem `uniformBell_succ_left` / 定理 `uniformBell_succ_left`

English:
theorem uniformBell_succ_left
  given: (m n : Nat)
  proof: by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

中文:
定理 uniformBell_succ_left
  条件: (m n : 自然数)
  证明: by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

Depends on / 依赖: Finset, Finset.prod_range_succ, mul_comm, prod_range_succ, uniformBell_eq
-/
theorem uniformBell_succ_left (m n : Nat) :
    uniformBell (m + 1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

/--
theorem `uniformBell_one_left` / 定理 `uniformBell_one_left`

English:
theorem uniformBell_one_left
  given: (n : Nat)
  statement: uniformBell 1 n = 1
  proof: by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

中文:
定理 uniformBell_one_left
  条件: (n : 自然数)
  结论: uniformBell 1 n = 1
  证明: by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

Depends on / 依赖: Finset, Finset.prod_singleton, Finset.range_one, choose_self, prod_singleton, range_one, uniformBell_eq, zero_add, zero_mul
-/
theorem uniformBell_one_left (n : Nat) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

/--
theorem `uniformBell_one_right` / 定理 `uniformBell_one_right`

English:
theorem uniformBell_one_right
  given: (m : Nat)
  statement: uniformBell m 1 = 1
  proof: by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

中文:
定理 uniformBell_one_right
  条件: (m : 自然数)
  结论: uniformBell m 1 = 1
  证明: by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

Depends on / 依赖: Finset, Finset.prod_const_one, add_tsub_cancel_right, choose_zero_right, le_refl, mul_one, prod_const_one, tsub_eq_zero_of_le, uniformBell_eq
-/
theorem uniformBell_one_right (m : Nat) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

/--
theorem `uniformBell_mul_eq` / 定理 `uniformBell_mul_eq`

English:
theorem uniformBell_mul_eq
  given: (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  convert! bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset Nat).erase 0 = ∅ from rfl]; rw [Finset.prod_empty]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

中文:
定理 uniformBell_mul_eq
  条件: (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  convert! bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset Nat).erase 0 = ∅ from rfl]; rw [Finset.prod_empty]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

Depends on / 依赖: Finset, Finset.prod_empty, Finset.prod_singleton, Finset.union_subset_iff, Finset.union_subset_left, Finset.union_subset_right, Ne.symm, bell_mul_eq, codeSupp, codeSupp_cons, contSupp, convert, count_replicate_self, eq_comm, factorial_zero, generalizing, map_replicate, prod_empty, prod_replicate, prod_singleton
-/
theorem uniformBell_mul_eq (m : Nat) {n : Nat} (hn : n != 0) :
    uniformBell m n * n ! ^ m * m ! = (m * n)! := by
  convert! bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset Nat).erase 0 = ∅ from rfl]; rw [Finset.prod_empty]
    · rw [show ({n} : Finset Nat).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

/--
theorem `uniformBell_eq_div` / 定理 `uniformBell_eq_div`

English:
theorem uniformBell_eq_div
  given: (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos n.factorial_pos) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

中文:
定理 uniformBell_eq_div
  条件: (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos n.factorial_pos) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, Nat.mul_pos, Nat.pow_pos, div_eq_of_eq_mul_left, eq_comm, factorial_pos, m.factorial_pos, mul_assoc, mul_pos, n.factorial_pos, pow_pos, uniformBell_mul_eq
-/
theorem uniformBell_eq_div (m : Nat) {n : Nat} (hn : n != 0) :
    uniformBell m n = (m * n)! / (n ! ^ m * m !) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos n.factorial_pos) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

/--
Definition of `bell` / `bell` 的定义

English:
definition bell
  signature: : Nat -> Nat

中文:
定义 bell
  签名: : 自然数 -> 自然数
-/
protected def bell : Nat -> Nat
  | 0 => 1
  | n + 1 => ∑ i <= n, choose n i * (n - i).bell

/--
theorem `bell_succ` / 定理 `bell_succ`

English:
theorem bell_succ
  given: (n : Nat)
  proof: by
  rw [Nat.bell]

中文:
定理 bell_succ
  条件: (n : 自然数)
  证明: by
  rw [Nat.bell]

Depends on / 依赖: Nat.bell
-/
theorem bell_succ (n : Nat) :
    (n + 1).bell = ∑ i <= n, choose n i * (n - i).bell := by
  rw [Nat.bell]

/--
theorem `bell_succ'` / 定理 `bell_succ'`

English:
theorem bell_succ'
  given: (n : Nat)
  proof: by
  rw [Nat.bell_succ]; rw [← Nat.range_succ_eq_Iic]; rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => choose n x * y.bell) n]

@[simp]

中文:
定理 bell_succ'
  条件: (n : 自然数)
  证明: by
  rw [Nat.bell_succ]; rw [← Nat.range_succ_eq_Iic]; rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => choose n x * y.bell) n]

@[simp]

Depends on / 依赖: Finset, Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Nat.bell_succ, Nat.range_succ_eq_Iic, bell_succ, range_succ_eq_Iic, sum_antidiagonal_eq_sum_range_succ, y.bell
-/
theorem bell_succ' (n : Nat) :
    (n + 1).bell = ∑ ij in Finset.antidiagonal n, choose n ij.1 * ij.2.bell := by
  rw [Nat.bell_succ]; rw [← Nat.range_succ_eq_Iic]; rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => choose n x * y.bell) n]

@[simp]
/--
theorem `bell_zero` / 定理 `bell_zero`

English:
theorem bell_zero
  statement: Nat.bell 0 = 1
  proof: by
  simp [Nat.bell]

@[simp]

中文:
定理 bell_zero
  结论: 自然数.bell 0 = 1
  证明: by
  simp [Nat.bell]

@[simp]

Depends on / 依赖: Nat.bell
-/
theorem bell_zero : Nat.bell 0 = 1 := by
  simp [Nat.bell]

@[simp]
/--
theorem `bell_one` / 定理 `bell_one`

English:
theorem bell_one
  statement: Nat.bell 1 = 1
  proof: by
  have : Finset.Iic 0 = {0} := Eq.symm (Finset.eq_of_veq rfl)
  simp [Nat.bell, this]

@[simp]

中文:
定理 bell_one
  结论: 自然数.bell 1 = 1
  证明: by
  have : Finset.Iic 0 = {0} := Eq.symm (Finset.eq_of_veq rfl)
  simp [Nat.bell, this]

@[simp]

Depends on / 依赖: Eq.symm, Finset, Finset.Iic, Finset.eq_of_veq, Nat.bell, eq_of_veq
-/
theorem bell_one : Nat.bell 1 = 1 := by
  have : Finset.Iic 0 = {0} := Eq.symm (Finset.eq_of_veq rfl)
  simp [Nat.bell, this]

@[simp]
/--
theorem `bell_two` / 定理 `bell_two`

English:
theorem bell_two
  statement: Nat.bell 2 = 2
  proof: by
  have : Finset.Iic 1 = {0, 1} := Finset.eq_of_veq rfl
  simp [Nat.bell, this]

中文:
定理 bell_two
  结论: 自然数.bell 2 = 2
  证明: by
  have : Finset.Iic 1 = {0, 1} := Finset.eq_of_veq rfl
  simp [Nat.bell, this]

Depends on / 依赖: Finset, Finset.Iic, Finset.eq_of_veq, Nat.bell, eq_of_veq
-/
theorem bell_two : Nat.bell 2 = 2 := by
  have : Finset.Iic 1 = {0, 1} := Finset.eq_of_veq rfl
  simp [Nat.bell, this]

/--
theorem `bell_eq_sum_erase` / 定理 `bell_eq_sum_erase`

English:
theorem bell_eq_sum_erase
  given: {n : Nat} (p : (n + 1).Partition)
  proof: by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
  _ = (∑ a in p.parts.toFinset, p.parts.count a * a) * p.parts.bell := by
    rw [succ_eq_add_one]; rw [mul_eq_mul_right_iff]
    left
    simpa [smul_eq_mul, p.parts_sum] using Finset.sum_multiset_count p.parts
  _ = ∑ a in p.parts.toFinset, a * (p.parts.count a * p.parts.bell) := by grind [Finset.sum_mul]
  _ = ∑ a in p.parts.toFinset, (n + 1) * (n.choose (a - 1) * (p.parts.erase a).bell) := by
    congr! 1 with a ha
    have ha0 : a != 0 := by grind
    have hsum : (p.parts.erase a).sum + a = n + 1 := by
      simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (cons_erase (mem_dedup.mp ha))
    grind [Nat.add_one_mul_choose_eq, cons_erase, bell_cons_mul_count]
  _ = _ := by rw [Finset.mul_sum]

中文:
定理 bell_eq_sum_erase
  条件: {n : 自然数} (p : (n + 1).分拆)
  证明: by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
  _ = (∑ a in p.parts.toFinset, p.parts.count a * a) * p.parts.bell := by
    rw [succ_eq_add_one]; rw [mul_eq_mul_right_iff]
    left
    simpa [smul_eq_mul, p.parts_sum] using Finset.sum_multiset_count p.parts
  _ = ∑ a in p.parts.toFinset, a * (p.parts.count a * p.parts.bell) := by grind [Finset.sum_mul]
  _ = ∑ a in p.parts.toFinset, (n + 1) * (n.choose (a - 1) * (p.parts.erase a).bell) := by
    congr! 1 with a ha
    have ha0 : a != 0 := by grind
    have hsum : (p.parts.erase a).sum + a = n + 1 := by
      simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (cons_erase (mem_dedup.mp ha))
    grind [Nat.add_one_mul_choose_eq, cons_erase, bell_cons_mul_count]
  _ = _ := by rw [Finset.mul_sum]

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sum_multiset_count, Nat.eq_of_mul_eq_mul_left, eq_of_mul_eq_mul_left, mul_eq_mul_right_iff, n.choose, n.succ_pos, p.par, p.parts, p.parts.bell, p.parts.count, p.parts.erase, p.parts.toFinset, p.parts_sum, parts_sum, smul_eq_mul, succ_eq_add_one, succ_pos, sum_mul
-/
theorem bell_eq_sum_erase {n : Nat} (p : (n + 1).Partition) :
    p.parts.bell = ∑ a in p.parts.toFinset, n.choose (a - 1) * (p.parts.erase a).bell := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
  _ = (∑ a in p.parts.toFinset, p.parts.count a * a) * p.parts.bell := by
    rw [succ_eq_add_one]; rw [mul_eq_mul_right_iff]
    left
    simpa [smul_eq_mul, p.parts_sum] using Finset.sum_multiset_count p.parts
  _ = ∑ a in p.parts.toFinset, a * (p.parts.count a * p.parts.bell) := by grind [Finset.sum_mul]
  _ = ∑ a in p.parts.toFinset, (n + 1) * (n.choose (a - 1) * (p.parts.erase a).bell) := by
    congr! 1 with a ha
    have ha0 : a != 0 := by grind
    have hsum : (p.parts.erase a).sum + a = n + 1 := by
      simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (cons_erase (mem_dedup.mp ha))
    grind [Nat.add_one_mul_choose_eq, cons_erase, bell_cons_mul_count]
  _ = _ := by rw [Finset.mul_sum]

/--
Definition of `sigmaPartitionWithPartEquiv` / `sigmaPartitionWithPartEquiv` 的定义

English:
definition sigmaPartitionWithPartEquiv
  signature: (n : Nat)
  body: ⟨x.2.1, ⟨(x.1 + 1 : Nat), by simpa using x.2.2⟩⟩
  invFun x := ⟨⟨x.2.1 - 1, by grind⟩, ⟨x.1, by grind⟩⟩
  left_inv x := by simp
  right_inv x := by grind

中文:
定义 sigmaPartitionWithPartEquiv
  签名: (n : 自然数)
  定义体: ⟨x.2.1, ⟨(x.1 + 1 : Nat), by simpa using x.2.2⟩⟩
  invFun x := ⟨⟨x.2.1 - 1, by grind⟩, ⟨x.1, by grind⟩⟩
  left_inv x := by simp
  right_inv x := by grind
-/
private def sigmaPartitionWithPartEquiv (n : Nat) :
    (Σ i : Fin n.succ, {p : (n + 1).Partition // (i + 1 : Nat) in p.parts}) ≃
    Σ p : (n + 1).Partition, {a : Nat // a in p.parts.toFinset} where
  toFun x := ⟨x.2.1, ⟨(x.1 + 1 : Nat), by simpa using x.2.2⟩⟩
  invFun x := ⟨⟨x.2.1 - 1, by grind⟩, ⟨x.1, by grind⟩⟩
  left_inv x := by simp
  right_inv x := by grind

/--
theorem `bell_eq_sum_partition` / 定理 `bell_eq_sum_partition`

English:
theorem bell_eq_sum_partition
  given: (n : Nat)
  statement: n.bell = ∑ p : n.Partition, p.parts.bell
  proof: by
  refine Nat.strong_induction_on n ?_
  rintro (_ | n) ih
  · simp
  rw [Nat.bell_succ]
  calc
  _ = ∑ i <= n, ∑ q : (n - i).Partition, n.choose i * q.parts.bell := by
    congr! with i
    simp [ih (n - i) _, Finset.mul_sum]
  _ = ∑ i <= n, ∑ p : {p : (n + 1).Partition // (i + 1 : Nat) in p.parts},
      choose n i * (p.1.parts.erase (i + 1)).bell := by
    congr! with i hi
    have : i <= n := Finset.mem_Iic.mp hi
    have h1 : 1 <= (i + 1 : Nat) := by lia
    have h2 : (i + 1 : Nat) <= n + 1 := by lia
    have hsub : n + 1 - (i + 1 : Nat) = n - i := by lia
    exact hsub ▸ (Fintype.sum_equiv (Partition.partitionWithPartEquiv h1 h2) _ _ (fun _ => rfl)).symm
  _ = ∑ x : Σ p : (n + 1).Partition, p.parts.toFinset,
      choose n (x.2.1 - 1) * (x.1.parts.erase x.2.1).bell := by
    rw [← Nat.range_succ_eq_Iic]; rw [Finset.sum_range]; rw [← Fintype.sum_sigma']
    refine Fintype.sum_equiv (sigmaPartitionWithPartEquiv n) _ _ ?_
    simp [sigmaPartitionWithPartEquiv]
  _ = ∑ p : (n + 1).Partition, ∑ a : p.parts.toFinset, choose n (a - 1) * (p.parts.erase a).bell :=
    Fintype.sum_sigma' fun (p : (n + 1).Partition) (a : p.parts.toFinset) =>
      choose n (a - 1) * (p.parts.erase a.1).bell
  _ = _ := by
    congr! with p
    rw [bell_eq_sum_erase p]
    exact p.parts.toFinset.sum_coe_sort (fun a => choose n (a - 1) * (p.parts.erase a).bell)

中文:
定理 bell_eq_sum_partition
  条件: (n : 自然数)
  结论: n.bell = ∑ p : n.分拆, p.parts.bell
  证明: by
  refine Nat.strong_induction_on n ?_
  rintro (_ | n) ih
  · simp
  rw [Nat.bell_succ]
  calc
  _ = ∑ i <= n, ∑ q : (n - i).Partition, n.choose i * q.parts.bell := by
    congr! with i
    simp [ih (n - i) _, Finset.mul_sum]
  _ = ∑ i <= n, ∑ p : {p : (n + 1).Partition // (i + 1 : Nat) in p.parts},
      choose n i * (p.1.parts.erase (i + 1)).bell := by
    congr! with i hi
    have : i <= n := Finset.mem_Iic.mp hi
    have h1 : 1 <= (i + 1 : Nat) := by lia
    have h2 : (i + 1 : Nat) <= n + 1 := by lia
    have hsub : n + 1 - (i + 1 : Nat) = n - i := by lia
    exact hsub ▸ (Fintype.sum_equiv (Partition.partitionWithPartEquiv h1 h2) _ _ (fun _ => rfl)).symm
  _ = ∑ x : Σ p : (n + 1).Partition, p.parts.toFinset,
      choose n (x.2.1 - 1) * (x.1.parts.erase x.2.1).bell := by
    rw [← Nat.range_succ_eq_Iic]; rw [Finset.sum_range]; rw [← Fintype.sum_sigma']
    refine Fintype.sum_equiv (sigmaPartitionWithPartEquiv n) _ _ ?_
    simp [sigmaPartitionWithPartEquiv]
  _ = ∑ p : (n + 1).Partition, ∑ a : p.parts.toFinset, choose n (a - 1) * (p.parts.erase a).bell :=
    Fintype.sum_sigma' fun (p : (n + 1).Partition) (a : p.parts.toFinset) =>
      choose n (a - 1) * (p.parts.erase a.1).bell
  _ = _ := by
    congr! with p
    rw [bell_eq_sum_erase p]
    exact p.parts.toFinset.sum_coe_sort (fun a => choose n (a - 1) * (p.parts.erase a).bell)

Depends on / 依赖: Finset, Finset.mem_Iic.mp, Finset.mul_sum, Nat.bell_succ, Nat.strong_induction_on, Partition, bell_succ, mem_Iic, mul_sum, n.choose, p.parts, parts.erase, q.parts.bell, strong_induction_on
-/
theorem bell_eq_sum_partition (n : Nat) : n.bell = ∑ p : n.Partition, p.parts.bell := by
  refine Nat.strong_induction_on n ?_
  rintro (_ | n) ih
  · simp
  rw [Nat.bell_succ]
  calc
  _ = ∑ i <= n, ∑ q : (n - i).Partition, n.choose i * q.parts.bell := by
    congr! with i
    simp [ih (n - i) _, Finset.mul_sum]
  _ = ∑ i <= n, ∑ p : {p : (n + 1).Partition // (i + 1 : Nat) in p.parts},
      choose n i * (p.1.parts.erase (i + 1)).bell := by
    congr! with i hi
    have : i <= n := Finset.mem_Iic.mp hi
    have h1 : 1 <= (i + 1 : Nat) := by lia
    have h2 : (i + 1 : Nat) <= n + 1 := by lia
    have hsub : n + 1 - (i + 1 : Nat) = n - i := by lia
    exact hsub ▸ (Fintype.sum_equiv (Partition.partitionWithPartEquiv h1 h2) _ _ (fun _ => rfl)).symm
  _ = ∑ x : Σ p : (n + 1).Partition, p.parts.toFinset,
      choose n (x.2.1 - 1) * (x.1.parts.erase x.2.1).bell := by
    rw [← Nat.range_succ_eq_Iic]; rw [Finset.sum_range]; rw [← Fintype.sum_sigma']
    refine Fintype.sum_equiv (sigmaPartitionWithPartEquiv n) _ _ ?_
    simp [sigmaPartitionWithPartEquiv]
  _ = ∑ p : (n + 1).Partition, ∑ a : p.parts.toFinset, choose n (a - 1) * (p.parts.erase a).bell :=
    Fintype.sum_sigma' fun (p : (n + 1).Partition) (a : p.parts.toFinset) =>
      choose n (a - 1) * (p.parts.erase a.1).bell
  _ = _ := by
    congr! with p
    rw [bell_eq_sum_erase p]
    exact p.parts.toFinset.sum_coe_sort (fun a => choose n (a - 1) * (p.parts.erase a).bell)

end Nat
