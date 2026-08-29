/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/

@[expose] public section


namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

/--
Definition of `mirror` / `mirror` 的定义

English:
definition mirror
  body: p.reverse * X ^ p.natTrailingDegree

@[simp]

中文:
定义 mirror
  定义体: p.reverse * X ^ p.natTrailingDegree

@[simp]

Depends on / 依赖: natTrailingDegree, p.natTrailingDegree, p.reverse, reverse
-/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree

@[simp]
/--
theorem `mirror_zero` / 定理 `mirror_zero`

English:
theorem mirror_zero
  statement: (0 : R[X]).mirror = 0
  proof: by simp [mirror]

中文:
定理 mirror_zero
  结论: (0 : R[X]).mirror = 0
  证明: by simp [mirror]

Depends on / 依赖: mirror
-/
theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [mirror]

/--
theorem `mirror_monomial` / 定理 `mirror_monomial`

English:
theorem mirror_monomial
  given: (n : Nat) (a : R)
  statement: (monomial n a).mirror = monomial n a
  proof: by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

中文:
定理 mirror_monomial
  条件: (n : 自然数) (a : R)
  结论: (monomial n a).mirror = monomial n a
  证明: by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

Depends on / 依赖: C_mul_X_pow_eq_monomial, classical, if_neg, le_refl, mirror, mirror_zero, monomial_zero_right, mul_one, natDegree_monomial, natTrailingDegree_monomial, pow_zero, reflect_C_mul_X_pow, revAt_le, reverse, tsub_self
-/
theorem mirror_monomial (n : Nat) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

/--
theorem `mirror_C` / 定理 `mirror_C`

English:
theorem mirror_C
  given: (a : R)
  statement: (C a).mirror = C a
  proof: mirror_monomial 0 a

中文:
定理 mirror_C
  条件: (a : R)
  结论: (C a).mirror = C a
  证明: mirror_monomial 0 a

Depends on / 依赖: mirror_monomial
-/
theorem mirror_C (a : R) : (C a).mirror = C a :=
  mirror_monomial 0 a

/--
theorem `mirror_X` / 定理 `mirror_X`

English:
theorem mirror_X
  statement: X.mirror = (X : R[X])
  proof: mirror_monomial 1 (1 : R)

中文:
定理 mirror_X
  结论: X.mirror = (X : R[X])
  证明: mirror_monomial 1 (1 : R)

Depends on / 依赖: mirror_monomial
-/
theorem mirror_X : X.mirror = (X : R[X]) :=
  mirror_monomial 1 (1 : R)

/--
theorem `mirror_natDegree` / 定理 `mirror_natDegree`

English:
theorem mirror_natDegree
  statement: p.mirror.natDegree = p.natDegree
  proof: by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror]; rw [natDegree_mul']; rw [reverse_natDegree]; rw [natDegree_X_pow]; rw [tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]

中文:
定理 mirror_natDegree
  结论: p.mirror.natDegree = p.natDegree
  证明: by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror]; rw [natDegree_mul']; rw [reverse_natDegree]; rw [natDegree_X_pow]; rw [tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]

Depends on / 依赖: leadingCoeff_X_pow, mirror, mirror_zero, mul_one, natDegree_X_pow, natDegree_mul, natTrailingDegree_le_natDegree, nontriviality, p.natTrailingDegree_le_natDegree, reverse_leadingCoeff, reverse_natDegree, trailingCoeff_eq_zero, tsub_add_cancel_of_le
-/
theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror]; rw [natDegree_mul']; rw [reverse_natDegree]; rw [natDegree_X_pow]; rw [tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]

/--
theorem `mirror_natTrailingDegree` / 定理 `mirror_natTrailingDegree`

English:
theorem mirror_natTrailingDegree
  statement: p.mirror.natTrailingDegree = p.natTrailingDegree
  proof: by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]

中文:
定理 mirror_natTrailingDegree
  结论: p.mirror.natTrailingDegree = p.natTrailingDegree
  证明: by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]

Depends on / 依赖: mirror, mirror_zero, natTrailingDegree_mul_X_pow, natTrailingDegree_reverse, reverse_eq_zero, reverse_eq_zero.mp, zero_add
-/
theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]

/--
theorem `coeff_mirror` / 定理 `coeff_mirror`

English:
theorem coeff_mirror
  given: (n : Nat)
  proof: by
  by_cases h2 : p.natDegree < n
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [mirror_natDegree])]
    by_cases h1 : n <= p.natDegree + p.natTrailingDegree
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      grw [h2, add_tsub_cancel_left]
    · rw [← revAtFun_eq, revAtFun, if_neg 

中文:
定理 coeff_mirror
  条件: (n : 自然数)
  证明: by
  by_cases h2 : p.natDegree < n
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [mirror_natDegree])]
    by_cases h1 : n <= p.natDegree + p.natTrailingDegree
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      grw [h2, add_tsub_cancel_left]
    · rw [← revAtFun_eq, revAtFun, if_neg 

Depends on / 依赖: Nat.le_add_right, add_tsub_cancel_left, coeff_eq_zero_of_lt_natTrailingDegree, coeff_eq_zero_of_natDegree_lt, coeff_mul_X_p, h2.trans, if_neg, le_add_right, mirror, mirror_natDegree, natDegree, natTrailingDegree, not_lt, p.natDegree, p.natTrailingDegree, revAtFun, revAtFun_eq, revAt_le, tsub_add_eq_add_tsub, tsub_tsub_assoc
-/
theorem coeff_mirror (n : Nat) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  by_cases h2 : p.natDegree < n
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [mirror_natDegree])]
    by_cases h1 : n <= p.natDegree + p.natTrailingDegree
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      grw [h2, add_tsub_cancel_left]
    · rw [← revAtFun_eq, revAtFun, if_neg h1, coeff_eq_zero_of_natDegree_lt h2]
  rw [not_lt] at h2
  rw [revAt_le (h2.trans (Nat.le_add_right _ _))]
  by_cases h3 : p.natTrailingDegree <= n
  · rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3,
      coeff_reverse, revAt_le (tsub_le_self.trans h2)]
  rw [not_le] at h3
  rw [coeff_eq_zero_of_natDegree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_left h3 _))]
  exact coeff_eq_zero_of_lt_natTrailingDegree (by rwa [mirror_natTrailingDegree])

--TODO: Extract `Finset.sum_range_rev_at` lemma.
/--
theorem `mirror_eval_one` / 定理 `mirror_eval_one`

English:
theorem mirror_eval_one
  statement: p.mirror.eval 1 = p.eval 1
  proof: by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_natDegree]
  refine Finset.sum_bij_ne_zero ?_ ?_ ?_ ?_ ?_
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    rw 

中文:
定理 mirror_eval_one
  结论: p.mirror.eval 1 = p.eval 1
  证明: by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_natDegree]
  refine Finset.sum_bij_ne_zero ?_ ?_ ?_ ?_ ?_
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    rw 

Depends on / 依赖: Finset, Finset.mem_range_succ_iff, Finset.sum_bij_ne_zero, Nat.le_add_right, add_comm, add_tsub_cancel_right, eval_eq_sum_range, hn.trans, le_add_right, mem_range_succ_iff, mirror_natDegree, mirror_natTrailingDegree, mul_one, natDegree, natTrailingDegree, natTrailingDegree_le_of_ne_zero, one_pow, p.natDegree, p.natTrailingDegree, revAt_invol
-/
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_natDegree]
  refine Finset.sum_bij_ne_zero ?_ ?_ ?_ ?_ ?_
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    rw [tsub_le_iff_tsub_le]; rw [add_comm]; rw [add_tsub_cancel_right]; rw [← mirror_natTrailingDegree]
    exact natTrailingDegree_le_of_ne_zero hp
  · exact fun n₁ _ _ _ _ _ h => by rw [← @revAt_invol _ n₁, h, revAt_invol]
  · intro n hn hp
    use revAt (p.natDegree + p.natTrailingDegree) n
    refine ⟨?_, ?_, revAt_invol⟩
    · rw [Finset.mem_range_succ_iff] at *
      rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
      rw [tsub_le_iff_tsub_le]; rw [add_comm]; rw [add_tsub_cancel_right]
      exact natTrailingDegree_le_of_ne_zero hp
    · change p.mirror.coeff _ != 0
      rwa [coeff_mirror, revAt_invol]
  · exact fun n _ _ => p.coeff_mirror n

/--
theorem `mirror_mirror` / 定理 `mirror_mirror`

English:
theorem mirror_mirror
  statement: p.mirror.mirror = p
  proof: Polynomial.ext fun n => by
    rw [coeff_mirror]; rw [coeff_mirror]; rw [mirror_natDegree]; rw [mirror_natTrailingDegree]; rw [revAt_invol]

中文:
定理 mirror_mirror
  结论: p.mirror.mirror = p
  证明: Polynomial.ext fun n => by
    rw [coeff_mirror]; rw [coeff_mirror]; rw [mirror_natDegree]; rw [mirror_natTrailingDegree]; rw [revAt_invol]

Depends on / 依赖: Polynomial, Polynomial.ext, coeff_mirror, mirror_natDegree, mirror_natTrailingDegree, revAt_invol
-/
theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    rw [coeff_mirror]; rw [coeff_mirror]; rw [mirror_natDegree]; rw [mirror_natTrailingDegree]; rw [revAt_invol]

variable {p q}

/--
theorem `mirror_involutive` / 定理 `mirror_involutive`

English:
theorem mirror_involutive
  statement: Function.Involutive (mirror : R[X] -> R[X])
  proof: mirror_mirror

中文:
定理 mirror_involutive
  结论: Function.Involutive (mirror : R[X] -> R[X])
  证明: mirror_mirror

Depends on / 依赖: mirror_mirror
-/
theorem mirror_involutive : Function.Involutive (mirror : R[X] -> R[X]) :=
  mirror_mirror

/--
theorem `mirror_eq_iff` / 定理 `mirror_eq_iff`

English:
theorem mirror_eq_iff
  statement: p.mirror = q ↔ p = q.mirror
  proof: mirror_involutive.eq_iff

@[simp]

中文:
定理 mirror_eq_iff
  结论: p.mirror = q ↔ p = q.mirror
  证明: mirror_involutive.eq_iff

@[simp]

Depends on / 依赖: eq_iff, mirror_involutive, mirror_involutive.eq_iff
-/
theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  mirror_involutive.eq_iff

@[simp]
/--
theorem `mirror_inj` / 定理 `mirror_inj`

English:
theorem mirror_inj
  statement: p.mirror = q.mirror ↔ p = q
  proof: mirror_involutive.injective.eq_iff

@[simp]

中文:
定理 mirror_inj
  结论: p.mirror = q.mirror ↔ p = q
  证明: mirror_involutive.injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, injective, mirror_involutive, mirror_involutive.injective.eq_iff
-/
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.injective.eq_iff

@[simp]
/--
theorem `mirror_eq_zero` / 定理 `mirror_eq_zero`

English:
theorem mirror_eq_zero
  statement: p.mirror = 0 ↔ p = 0
  proof: ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩

中文:
定理 mirror_eq_zero
  结论: p.mirror = 0 ↔ p = 0
  证明: ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩

Depends on / 依赖: mirror_mirror, mirror_zero, p.mirror_mirror
-/
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩

variable (p q)

@[simp]
/--
theorem `mirror_trailingCoeff` / 定理 `mirror_trailingCoeff`

English:
theorem mirror_trailingCoeff
  statement: p.mirror.trailingCoeff = p.leadingCoeff
  proof: by
  rw [leadingCoeff]; rw [trailingCoeff]; rw [mirror_natTrailingDegree]; rw [coeff_mirror]; rw [revAt_le (Nat.le_add_left _ _)]; rw [add_tsub_cancel_right]

@[simp]

中文:
定理 mirror_trailingCoeff
  结论: p.mirror.trailingCoeff = p.leadingCoeff
  证明: by
  rw [leadingCoeff]; rw [trailingCoeff]; rw [mirror_natTrailingDegree]; rw [coeff_mirror]; rw [revAt_le (Nat.le_add_left _ _)]; rw [add_tsub_cancel_right]

@[simp]

Depends on / 依赖: Nat.le_add_left, add_tsub_cancel_right, coeff_mirror, le_add_left, leadingCoeff, mirror_natTrailingDegree, revAt_le, trailingCoeff
-/
theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leadingCoeff]; rw [trailingCoeff]; rw [mirror_natTrailingDegree]; rw [coeff_mirror]; rw [revAt_le (Nat.le_add_left _ _)]; rw [add_tsub_cancel_right]

@[simp]
/--
theorem `mirror_leadingCoeff` / 定理 `mirror_leadingCoeff`

English:
theorem mirror_leadingCoeff
  statement: p.mirror.leadingCoeff = p.trailingCoeff
  proof: by
  rw [← p.mirror_mirror]; rw [mirror_trailingCoeff]; rw [p.mirror_mirror]

中文:
定理 mirror_leadingCoeff
  结论: p.mirror.leadingCoeff = p.trailingCoeff
  证明: by
  rw [← p.mirror_mirror]; rw [mirror_trailingCoeff]; rw [p.mirror_mirror]

Depends on / 依赖: mirror_mirror, mirror_trailingCoeff, p.mirror_mirror
-/
theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror]; rw [mirror_trailingCoeff]; rw [p.mirror_mirror]

/--
theorem `coeff_mul_mirror` / 定理 `coeff_mul_mirror`

English:
theorem coeff_mul_mirror
  proof: by
  rw [coeff_mul]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ => (· ^ 2)) (fun _ => zero_pow two_ne_zero) fun n hn =>
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp 

中文:
定理 coeff_mul_mirror
  证明: by
  rw [coeff_mul]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ => (· ^ 2)) (fun _ => zero_pow two_ne_zero) fun n hn =>
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp 

Depends on / 依赖: Finset, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mem_range_succ_iff.mp, Finset.mem_range_succ_iff.mpr, Finset.sum_congr, Nat.le_add_right, coeff_mirror, coeff_mul, le_add_right, le_natDegree_of_mem_supp, mem_range_succ_iff, p.sum_eq_of_subset, revAt_invol, revAt_le, sum_antidiagonal_eq_sum_range_succ_mk, sum_congr, sum_eq_of_subset, two_ne_zero, zero_pow
-/
theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2) := by
  rw [coeff_mul]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ => (· ^ 2)) (fun _ => zero_pow two_ne_zero) fun n hn =>
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [coeff_mirror]; rw [← revAt_le (Finset.mem_range_succ_iff.mp hn)]; rw [revAt_invol]; rw [← sq]

variable [NoZeroDivisors R]

/--
theorem `natDegree_mul_mirror` / 定理 `natDegree_mul_mirror`

English:
theorem natDegree_mul_mirror
  statement: (p * p.mirror).natDegree = 2 * p.natDegree
  proof: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
  rw [natDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natDegree]; rw [two_mul]

中文:
定理 natDegree_mul_mirror
  结论: (p * p.mirror).natDegree = 2 * p.natDegree
  证明: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
  rw [natDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natDegree]; rw [two_mul]

Depends on / 依赖: mirror_eq_zero, mirror_eq_zero.mp, mirror_natDegree, mul_zero, natDegree_mul, natDegree_zero, two_mul, zero_mul
-/
theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
  rw [natDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natDegree]; rw [two_mul]

/--
theorem `natTrailingDegree_mul_mirror` / 定理 `natTrailingDegree_mul_mirror`

English:
theorem natTrailingDegree_mul_mirror
  proof: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
  rw [natTrailingDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natTrailingDegree]; rw [two_mul]

中文:
定理 natTrailingDegree_mul_mirror
  证明: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
  rw [natTrailingDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natTrailingDegree]; rw [two_mul]

Depends on / 依赖: mirror_eq_zero, mirror_eq_zero.mp, mirror_natTrailingDegree, mul_zero, natTrailingDegree_mul, natTrailingDegree_zero, two_mul, zero_mul
-/
theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
  rw [natTrailingDegree_mul hp (mt mirror_eq_zero.mp hp)]; rw [mirror_natTrailingDegree]; rw [two_mul]

/--
theorem `mirror_mul_of_domain` / 定理 `mirror_mul_of_domain`

English:
theorem mirror_mul_of_domain
  statement: (p * q).mirror = p.mirror * q.mirror
  proof: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, mirror_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, mirror_zero, mul_zero]
  rw [mirror]; rw [mirror]; rw [mirror]; rw [reverse_mul_of_domain]; rw [natTrailingDegree_mul hp hq]; rw [pow_add]
  rw [mul_assoc]; rw [← mul_assoc q.reverse]; r

中文:
定理 mirror_mul_of_domain
  结论: (p * q).mirror = p.mirror * q.mirror
  证明: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, mirror_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, mirror_zero, mul_zero]
  rw [mirror]; rw [mirror]; rw [mirror]; rw [reverse_mul_of_domain]; rw [natTrailingDegree_mul hp hq]; rw [pow_add]
  rw [mul_assoc]; rw [← mul_assoc q.reverse]; r

Depends on / 依赖: X_pow_mul, mirror, mirror_zero, mul_assoc, mul_zero, natTrailingDegree_mul, pow_add, q.reverse, repeat, reverse, reverse_mul_of_domain, zero_mul
-/
theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, mirror_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, mirror_zero, mul_zero]
  rw [mirror]; rw [mirror]; rw [mirror]; rw [reverse_mul_of_domain]; rw [natTrailingDegree_mul hp hq]; rw [pow_add]
  rw [mul_assoc]; rw [← mul_assoc q.reverse]; rw [← X_pow_mul (p := reverse q)]
  repeat' rw [mul_assoc]

/--
theorem `mirror_smul` / 定理 `mirror_smul`

English:
theorem mirror_smul
  given: (a : R)
  statement: (a • p).mirror = a • p.mirror
  proof: by
  rw [← C_mul']; rw [← C_mul']; rw [mirror_mul_of_domain]; rw [mirror_C]

中文:
定理 mirror_smul
  条件: (a : R)
  结论: (a • p).mirror = a • p.mirror
  证明: by
  rw [← C_mul']; rw [← C_mul']; rw [mirror_mul_of_domain]; rw [mirror_C]

Depends on / 依赖: C_mul, mirror_C, mirror_mul_of_domain
-/
theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul']; rw [← C_mul']; rw [mirror_mul_of_domain]; rw [mirror_C]

end Semiring

section Ring

variable {R : Type*} [Ring R] (p q : R[X])

/--
theorem `mirror_neg` / 定理 `mirror_neg`

English:
theorem mirror_neg
  statement: (-p).mirror = -p.mirror
  proof: by
  rw [mirror]; rw [mirror]; rw [reverse_neg]; rw [natTrailingDegree_neg]; rw [neg_mul_eq_neg_mul]

中文:
定理 mirror_neg
  结论: (-p).mirror = -p.mirror
  证明: by
  rw [mirror]; rw [mirror]; rw [reverse_neg]; rw [natTrailingDegree_neg]; rw [neg_mul_eq_neg_mul]

Depends on / 依赖: mirror, natTrailingDegree_neg, neg_mul_eq_neg_mul, reverse_neg
-/
theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror]; rw [mirror]; rw [reverse_neg]; rw [natTrailingDegree_neg]; rw [neg_mul_eq_neg_mul]

end Ring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

/--
theorem `irreducible_of_mirror` / 定理 `irreducible_of_mirror`

English:
theorem irreducible_of_mirror
  statement: (h1 : ¬IsUnit f)
  proof: by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh]; rw [mirror_mul_of_domain]; rw [mirror_mul_of_domain]; rw [mirror_mirror]; rw [mul_assoc]; rw [mul_comm h]; rw [mul_comm g.mirror]; rw [mul_assoc]; rw [← mul_asso

中文:
定理 irreducible_of_mirror
  结论: (h1 : ¬IsUnit f)
  证明: by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh]; rw [mirror_mul_of_domain]; rw [mirror_mul_of_domain]; rw [mirror_mirror]; rw [mul_assoc]; rw [mul_comm h]; rw [mul_comm g.mirror]; rw [mul_assoc]; rw [← mul_asso

Depends on / 依赖: dvd_mul_left, dvd_mul_right, f.mirror, g.mirror, g_dvd_f, g_dvd_k, h.mirror, h_dvd_f, h_dvd_k_rev, k.mirror, mirror, mirror_, mirror_mirror, mirror_mul_of_domain, mul_assoc, mul_comm
-/
theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : forall k, f * f.mirror = k * k.mirror -> k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : IsRelPrime f f.mirror) : Irreducible f := by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh]; rw [mirror_mul_of_domain]; rw [mirror_mul_of_domain]; rw [mirror_mirror]; rw [mul_assoc]; rw [mul_comm h]; rw [mul_comm g.mirror]; rw [mul_assoc]; rw [← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    have h_dvd_k_rev : h ∣ k.mirror := by
      rw [mirror_mul_of_domain]; rw [mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    rcases hk with (hk | hk | hk | hk)
    · exact Or.inr (h3 h_dvd_f (by rwa [← hk]))
    · exact Or.inr (h3 h_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, mirror_neg, dvd_neg]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← hk]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, dvd_neg]))

end CommRing

end Polynomial
