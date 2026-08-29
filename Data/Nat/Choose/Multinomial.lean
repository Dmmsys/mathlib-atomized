/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
/-!
# Multinomial

This file defines the multinomial coefficients and several small lemmas for manipulating them.

- `Nat.multinomial`: the multinomial coefficient,
  Given a function `f : α → ℕ` and `s : Finset α`, this is the number of strings
  consisting of symbols from `s`, where `c ∈ s` appears with multiplicity `f c`.

  It is defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.

- `Multiset.countPerms`: multinomial coefficient associated with the `Multiset.count` function
  of a multiset. This is the number of lists that induce the given multiset.

- `Finset.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

- `Multiset.multinomial`.
  Given a multiset `m` of natural numbers, `m.multinomial` is the
  multinomial coefficient defined by `(m.sum) ! / ∏ i ∈ m, m i !`.

This should not be confused with `m.countPerms` which
is defined as `m.toFinsupp.multinomial`.

As an example, one has `Multiset.multinomial {1, 2, 2} = 30`,
while `Multiset.countPerms {1, 2, 2} = 3`.

- `Multiset.multinomial_cons` proves that
  `(x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial`
- `Multiset.multinomial_add` proves that
  `(m + m').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial`

## Implementation note for `Multiset.multinomial`.

To avoid the definition of `Multiset.multinomial` as a quotient given above,
we define it in terms of `Finsupp.multinomial`, via lists:
If `m : Multiset ℕ` is the multiset associated with a list `l : List ℕ`,
then `m.multinomial = l.toFinsupp.multinomial`.
Then we prove its invariance under permutation.

-/

@[expose] public section

open Finset
open scoped Nat

namespace Nat

variable {α : Type*} (s : Finset α) (f : α -> Nat) {a b : α} (n : Nat)

/--
Definition of `multinomial` / `multinomial` 的定义

English:
definition multinomial
  signature: : Nat
  body: (∑ i in s, f i)! / ∏ i in s, (f i)!

中文:
定义 multinomial
  签名: : 自然数
  定义体: (∑ i in s, f i)! / ∏ i in s, (f i)!
-/
def multinomial : Nat :=
  (∑ i in s, f i)! / ∏ i in s, (f i)!

/--
theorem `multinomial_pos` / 定理 `multinomial_pos`

English:
theorem multinomial_pos
  statement: 0 < multinomial s f
  proof: Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)

中文:
定理 multinomial_pos
  结论: 0 < multinomial s f
  证明: Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)

Depends on / 依赖: Nat.div_pos, div_pos, factorial_pos, le_of_dvd, prod_factorial_dvd_factorial_sum, prod_factorial_pos
-/
theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)

/--
theorem `multinomial_spec` / 定理 `multinomial_spec`

English:
theorem multinomial_spec
  statement: (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)!
  proof: Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

中文:
定理 multinomial_spec
  结论: (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)!
  证明: Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

Depends on / 依赖: Nat.mul_div_cancel, mul_div_cancel, prod_factorial_dvd_factorial_sum
-/
theorem multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

/--
lemma `multinomial_empty` / 引理 `multinomial_empty`

English:
lemma multinomial_empty
  statement: multinomial ∅ f = 1
  proof: by simp [multinomial]

中文:
引理 multinomial_empty
  结论: multinomial ∅ f = 1
  证明: by simp [multinomial]
-/
@[simp] lemma multinomial_empty : multinomial ∅ f = 1 := by simp [multinomial]

variable {s f}

/--
lemma `multinomial_cons` / 引理 `multinomial_cons`

English:
lemma multinomial_cons
  given: (ha : a ∉ s) (f : α -> Nat)
  proof: by
  rw [multinomial]; rw [Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _)]; rw [prod_cons]; rw [multinomial]; rw [mul_assoc]; rw [mul_left_comm _ (f a)!]; rw [Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _)]; rw [← mul_assoc]; rw [Nat.choose_symm_add]; rw [Nat.add_choo

中文:
引理 multinomial_cons
  条件: (ha : a ∉ s) (f : α -> 自然数)
  证明: by
  rw [multinomial]; rw [Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _)]; rw [prod_cons]; rw [multinomial]; rw [mul_assoc]; rw [mul_left_comm _ (f a)!]; rw [Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _)]; rw [← mul_assoc]; rw [Nat.choose_symm_add]; rw [Nat.add_choo

Depends on / 依赖: Finset, Finset.sum_cons, Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add, Nat.div_eq_iff_eq_mul_left, Nat.div_mul_cancel, add_choose_mul_factorial_mul_factorial, choose_symm_add, div_eq_iff_eq_mul_left, div_mul_cancel, mul_assoc, mul_left_comm, multinomial, prod_cons, prod_factorial_dvd_factorial_sum, sum_cons
-/
lemma multinomial_cons (ha : a ∉ s) (f : α -> Nat) :
    multinomial (s.cons a ha) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f := by
  rw [multinomial]; rw [Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _)]; rw [prod_cons]; rw [multinomial]; rw [mul_assoc]; rw [mul_left_comm _ (f a)!]; rw [Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _)]; rw [← mul_assoc]; rw [Nat.choose_symm_add]; rw [Nat.add_choose_mul_factorial_mul_factorial]; rw [Finset.sum_cons]
  positivity

/--
lemma `multinomial_insert` / 引理 `multinomial_insert`

English:
lemma multinomial_insert
  given: [DecidableEq α] (ha : a ∉ s) (f : α -> Nat)
  proof: by
  rw [← cons_eq_insert _ _ ha]; rw [multinomial_cons]

中文:
引理 multinomial_insert
  条件: [DecidableEq α] (ha : a ∉ s) (f : α -> 自然数)
  证明: by
  rw [← cons_eq_insert _ _ ha]; rw [multinomial_cons]

Depends on / 依赖: cons_eq_insert, multinomial_cons
-/
lemma multinomial_insert [DecidableEq α] (ha : a ∉ s) (f : α -> Nat) :
    multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f := by
  rw [← cons_eq_insert _ _ ha]; rw [multinomial_cons]

/--
lemma `multinomial_singleton` / 引理 `multinomial_singleton`

English:
lemma multinomial_singleton
  given: (a : α) (f : α -> Nat)
  statement: multinomial {a} f = 1
  proof: by
  rw [← cons_empty]; rw [multinomial_cons]; simp

@[simp]

中文:
引理 multinomial_singleton
  条件: (a : α) (f : α -> 自然数)
  结论: multinomial {a} f = 1
  证明: by
  rw [← cons_empty]; rw [multinomial_cons]; simp

@[simp]
-/
@[simp] lemma multinomial_singleton (a : α) (f : α -> Nat) : multinomial {a} f = 1 := by
  rw [← cons_empty]; rw [multinomial_cons]; simp

@[simp]
/--
theorem `multinomial_insert_one` / 定理 `multinomial_insert_one`

English:
theorem multinomial_insert_one
  given: [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1)
  proof: by
  simp only [multinomial]
  rw [Finset.sum_insert h]; rw [Finset.prod_insert h]; rw [h₁]; rw [add_comm]; rw [← succ_eq_add_one]; rw [factorial_succ]
  simp only [factorial, succ_eq_add_one, zero_add, mul_one, one_mul]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]

中文:
定理 multinomial_insert_one
  条件: [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1)
  证明: by
  simp only [multinomial]
  rw [Finset.sum_insert h]; rw [Finset.prod_insert h]; rw [h₁]; rw [add_comm]; rw [← succ_eq_add_one]; rw [factorial_succ]
  simp only [factorial, succ_eq_add_one, zero_add, mul_one, one_mul]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]

Depends on / 依赖: Finset, Finset.prod_insert, Finset.sum_insert, Nat.mul_div_assoc, add_comm, factorial, factorial_succ, mul_div_assoc, mul_one, multinomial, one_mul, prod_factorial_dvd_factorial_sum, prod_insert, succ_eq_add_one, sum_insert, zero_add
-/
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.sum f).succ * multinomial s f := by
  simp only [multinomial]
  rw [Finset.sum_insert h]; rw [Finset.prod_insert h]; rw [h₁]; rw [add_comm]; rw [← succ_eq_add_one]; rw [factorial_succ]
  simp only [factorial, succ_eq_add_one, zero_add, mul_one, one_mul]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]

/--
theorem `multinomial_congr` / 定理 `multinomial_congr`

English:
theorem multinomial_congr
  given: {f g : α -> Nat} (h : forall a in s, f a = g a)
  proof: by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]

中文:
定理 multinomial_congr
  条件: {f g : α -> 自然数} (h : 对任意 a in s, f a = g a)
  证明: by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]

Depends on / 依赖: Finset, Finset.prod_congr, Finset.sum_congr, multinomial, prod_congr, sum_congr
-/
theorem multinomial_congr {f g : α -> Nat} (h : forall a in s, f a = g a) :
    multinomial s f = multinomial s g := by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]

/--
theorem `multinomial_congr_of_eq_on_inter` / 定理 `multinomial_congr_of_eq_on_inter`

English:
theorem multinomial_congr_of_eq_on_inter
  statement: [DecidableEq α] {f g : α -> Nat} {s t : Finset α}
  proof: by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun x _ => factorial_ne_zero (g x)))]; rw [multinomial_spec]; rw [prod_congr_of_eq_on_inter (g := fun a => (f a)!) (s₂ := s) (by aesop)
    (by aesop) (by aesop)]; rw [multinomial_spec s f]
  congr 1
  exact sum_congr_of_eq_on_inter (by grind) (by 

中文:
定理 multinomial_congr_of_eq_on_inter
  结论: [DecidableEq α] {f g : α -> 自然数} {s t : 有限集 α}
  证明: by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun x _ => factorial_ne_zero (g x)))]; rw [multinomial_spec]; rw [prod_congr_of_eq_on_inter (g := fun a => (f a)!) (s₂ := s) (by aesop)
    (by aesop) (by aesop)]; rw [multinomial_spec s f]
  congr 1
  exact sum_congr_of_eq_on_inter (by grind) (by 

Depends on / 依赖: Nat.mul_right_inj, factorial_ne_zero, mul_right_inj, multinomial_spec, prod_congr_of_eq_on_inter, prod_ne_zero_iff, prod_ne_zero_iff.mpr, sum_congr_of_eq_on_inter
-/
theorem multinomial_congr_of_eq_on_inter [DecidableEq α] {f g : α -> Nat} {s t : Finset α}
    (hf : forall a in s \ t, f a = 0) (hg : forall a in t \ s, g a = 0) (hfg : forall a in s inter t, f a = g a) :
    multinomial s f = multinomial t g := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun x _ => factorial_ne_zero (g x)))]; rw [multinomial_spec]; rw [prod_congr_of_eq_on_inter (g := fun a => (f a)!) (s₂ := s) (by aesop)
    (by aesop) (by aesop)]; rw [multinomial_spec s f]
  congr 1
  exact sum_congr_of_eq_on_inter (by grind) (by grind) (by grind)

/--
theorem `multinomial_congr_of_sdiff` / 定理 `multinomial_congr_of_sdiff`

English:
theorem multinomial_congr_of_sdiff
  statement: [DecidableEq α] {f g : α -> Nat} {s t : Finset α}
  proof: multinomial_congr_of_eq_on_inter (by grind) hg (by grind)

中文:
定理 multinomial_congr_of_sdiff
  结论: [DecidableEq α] {f g : α -> 自然数} {s t : 有限集 α}
  证明: multinomial_congr_of_eq_on_inter (by grind) hg (by grind)

Depends on / 依赖: multinomial_congr_of_eq_on_inter
-/
theorem multinomial_congr_of_sdiff [DecidableEq α] {f g : α -> Nat} {s t : Finset α}
    (hst : s subseteq t) (hg : forall a in t \ s, g a = 0) (hfg : forall a in s, f a = g a) :
    multinomial s f = multinomial t g :=
  multinomial_congr_of_eq_on_inter (by grind) hg (by grind)

variable (s a) in
/--
theorem `multinomial_single` / 定理 `multinomial_single`

English:
theorem multinomial_single
  given: [DecidableEq α]
  proof: by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun _ _ => factorial_ne_zero _))]; rw [mul_one]; rw [multinomial_spec]; rw [sum_pi_single']
  split_ifs with ha
  · rw [Finset.prod_eq_single a (by simp_all) (by simp_all), Pi.single_eq_same]
  · rw [eq_comm, factorial_zero]
    apply Finset.prod_e

中文:
定理 multinomial_single
  条件: [DecidableEq α]
  证明: by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun _ _ => factorial_ne_zero _))]; rw [mul_one]; rw [multinomial_spec]; rw [sum_pi_single']
  split_ifs with ha
  · rw [Finset.prod_eq_single a (by simp_all) (by simp_all), Pi.single_eq_same]
  · rw [eq_comm, factorial_zero]
    apply Finset.prod_e

Depends on / 依赖: Finset, Finset.prod_eq_one, Finset.prod_eq_single, Nat.mul_right_inj, Pi.single_apply, Pi.single_eq_same, eq_comm, factorial_ne_zero, factorial_zero, if_neg, mul_one, mul_right_inj, multinomial_spec, ne_of_mem_of_not_mem, prod_eq_one, prod_eq_single, prod_ne_zero_iff, prod_ne_zero_iff.mpr, single_apply, single_eq_same
-/
theorem multinomial_single [DecidableEq α] :
    multinomial s (Pi.single a n) = 1 := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun _ _ => factorial_ne_zero _))]; rw [mul_one]; rw [multinomial_spec]; rw [sum_pi_single']
  split_ifs with ha
  · rw [Finset.prod_eq_single a (by simp_all) (by simp_all), Pi.single_eq_same]
  · rw [eq_comm, factorial_zero]
    apply Finset.prod_eq_one
    intro _ hb
    rw [Pi.single_apply]; rw [if_neg (ne_of_mem_of_not_mem hb ha)]; rw [factorial_zero]


/--
theorem `binomial_eq` / 定理 `binomial_eq`

English:
theorem binomial_eq
  given: [DecidableEq α] (h : a != b)
  proof: by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]

中文:
定理 binomial_eq
  条件: [DecidableEq α] (h : a != b)
  证明: by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]

Depends on / 依赖: Finset, Finset.prod_pair, Finset.sum_pair, multinomial, prod_pair, sum_pair
-/
theorem binomial_eq [DecidableEq α] (h : a != b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]

/--
theorem `binomial_eq_choose` / 定理 `binomial_eq_choose`

English:
theorem binomial_eq_choose
  given: [DecidableEq α] (h : a != b)
  proof: by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]

中文:
定理 binomial_eq_choose
  条件: [DecidableEq α] (h : a != b)
  证明: by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]

Depends on / 依赖: Nat.le_add_right, binomial_eq, choose_eq_factorial_div_factorial, le_add_right
-/
theorem binomial_eq_choose [DecidableEq α] (h : a != b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]

/--
theorem `binomial_spec` / 定理 `binomial_spec`

English:
theorem binomial_spec
  given: [DecidableEq α] (hab : a != b)
  proof: by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f

中文:
定理 binomial_spec
  条件: [DecidableEq α] (hab : a != b)
  证明: by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f

Depends on / 依赖: Finset, Finset.prod_pair, Finset.sum_pair, multinomial_spec, prod_pair, sum_pair
-/
theorem binomial_spec [DecidableEq α] (hab : a != b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f

/--
theorem `binomial_one` / 定理 `binomial_one`

English:
theorem binomial_one
  given: [DecidableEq α] (h : a != b) (h₁ : f a = 1)
  proof: by
  simp [h, h₁]

中文:
定理 binomial_one
  条件: [DecidableEq α] (h : a != b) (h₁ : f a = 1)
  证明: by
  simp [h, h₁]
-/
theorem binomial_one [DecidableEq α] (h : a != b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [h, h₁]

/--
theorem `binomial_succ_succ` / 定理 `binomial_succ_succ`

English:
theorem binomial_succ_succ
  given: [DecidableEq α] (h : a != b)
  proof: by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ]; rw [choose_succ_succ]; rw [succ_add_eq_add_succ]
  ring

中文:
定理 binomial_succ_succ
  条件: [DecidableEq α] (h : a != b)
  证明: by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ]; rw [choose_succ_succ]; rw [succ_add_eq_add_succ]
  ring

Depends on / 依赖: Function, Function.update_apply, add_succ, binomial_eq_choose, choose_succ_succ, h.symm, if_neg, ite_false, ite_true, not_false_eq_true, succ_add_eq_add_succ, update_apply
-/
theorem binomial_succ_succ [DecidableEq α] (h : a != b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) +
      multinomial {a, b} (Function.update f b (f b).succ) := by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ]; rw [choose_succ_succ]; rw [succ_add_eq_add_succ]
  ring

/--
theorem `succ_mul_binomial` / 定理 `succ_mul_binomial`

English:
theorem succ_mul_binomial
  given: [DecidableEq α] (h : a != b)
  proof: by
  rw [binomial_eq_choose h]; rw [binomial_eq_choose h]; rw [mul_comm (f a).succ]; rw [Function.update_self]; rw [Function.update_of_ne h.symm]
  rw [succ_eq_add_one]; rw [add_one_mul_choose_eq (f a + f b) (f a)]; rw [succ_add (f a) (f b)]

中文:
定理 succ_mul_binomial
  条件: [DecidableEq α] (h : a != b)
  证明: by
  rw [binomial_eq_choose h]; rw [binomial_eq_choose h]; rw [mul_comm (f a).succ]; rw [Function.update_self]; rw [Function.update_of_ne h.symm]
  rw [succ_eq_add_one]; rw [add_one_mul_choose_eq (f a + f b) (f a)]; rw [succ_add (f a) (f b)]

Depends on / 依赖: Function, Function.update_of_ne, Function.update_self, add_one_mul_choose_eq, binomial_eq_choose, h.symm, mul_comm, succ_add, succ_eq_add_one, update_of_ne, update_self
-/
theorem succ_mul_binomial [DecidableEq α] (h : a != b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose h]; rw [binomial_eq_choose h]; rw [mul_comm (f a).succ]; rw [Function.update_self]; rw [Function.update_of_ne h.symm]
  rw [succ_eq_add_one]; rw [add_one_mul_choose_eq (f a + f b) (f a)]; rw [succ_add (f a) (f b)]



/--
theorem `multinomial_univ_two` / 定理 `multinomial_univ_two`

English:
theorem multinomial_univ_two
  given: (a b : Nat)
  proof: by
  rw [multinomial]; rw [Fin.sum_univ_two]; rw [Fin.prod_univ_two]
  dsimp only [Matrix.cons_val]

中文:
定理 multinomial_univ_two
  条件: (a b : 自然数)
  证明: by
  rw [multinomial]; rw [Fin.sum_univ_two]; rw [Fin.prod_univ_two]
  dsimp only [Matrix.cons_val]

Depends on / 依赖: Fin.prod_univ_two, Fin.sum_univ_two, Matrix, Matrix.cons_val, cons_val, multinomial, prod_univ_two, sum_univ_two
-/
theorem multinomial_univ_two (a b : Nat) :
    multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) := by
  rw [multinomial]; rw [Fin.sum_univ_two]; rw [Fin.prod_univ_two]
  dsimp only [Matrix.cons_val]

/--
theorem `multinomial_univ_three` / 定理 `multinomial_univ_three`

English:
theorem multinomial_univ_three
  given: (a b c : Nat)
  proof: by
  rw [multinomial]; rw [Fin.sum_univ_three]; rw [Fin.prod_univ_three]
  rfl

中文:
定理 multinomial_univ_three
  条件: (a b c : 自然数)
  证明: by
  rw [multinomial]; rw [Fin.sum_univ_three]; rw [Fin.prod_univ_three]
  rfl

Depends on / 依赖: Fin.prod_univ_three, Fin.sum_univ_three, multinomial, prod_univ_three, sum_univ_three
-/
theorem multinomial_univ_three (a b c : Nat) :
    multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  rw [multinomial]; rw [Fin.sum_univ_three]; rw [Fin.prod_univ_three]
  rfl

end Nat

/-! ### Alternative definitions -/

namespace Finsupp

variable {α : Type*}

/--
Definition of `multinomial` / `multinomial` 的定义

English:
definition multinomial
  signature: (f : α ->₀ Nat)
  body: (f.sum fun _ => id)! / f.prod fun _ n => n !

中文:
定义 multinomial
  签名: (f : α ->₀ 自然数)
  定义体: (f.sum fun _ => id)! / f.prod fun _ n => n !

Depends on / 依赖: f.prod, f.sum
-/
def multinomial (f : α ->₀ Nat) : Nat :=
  (f.sum fun _ => id)! / f.prod fun _ n => n !

/--
theorem `multinomial_eq` / 定理 `multinomial_eq`

English:
theorem multinomial_eq
  given: (f : α ->₀ Nat)
  statement: f.multinomial = Nat.multinomial f.support f
  proof: rfl

中文:
定理 multinomial_eq
  条件: (f : α ->₀ 自然数)
  结论: f.multinomial = 自然数.multinomial f.support f
  证明: rfl
-/
theorem multinomial_eq (f : α ->₀ Nat) : f.multinomial = Nat.multinomial f.support f :=
  rfl

/--
theorem `multinomial_eq_of_support_subset` / 定理 `multinomial_eq_of_support_subset`

English:
theorem multinomial_eq_of_support_subset
  given: {f : α ->₀ Nat} {s : Finset α} (h : f.support subseteq s)
  proof: by
  simp only [Finsupp.multinomial_eq, Nat.multinomial]
  congr 1
  · simp [Finset.sum_subset h]
  · rw [Finset.prod_subset h]
    grind [Nat.factorial_eq_one]

中文:
定理 multinomial_eq_of_support_subset
  条件: {f : α ->₀ 自然数} {s : 有限集 α} (h : f.support subseteq s)
  证明: by
  simp only [Finsupp.multinomial_eq, Nat.multinomial]
  congr 1
  · simp [Finset.sum_subset h]
  · rw [Finset.prod_subset h]
    grind [Nat.factorial_eq_one]

Depends on / 依赖: Finset, Finset.prod_subset, Finset.sum_subset, Finsupp, Finsupp.multinomial_eq, Nat.factorial_eq_one, Nat.multinomial, factorial_eq_one, multinomial, multinomial_eq, prod_subset, sum_subset
-/
theorem multinomial_eq_of_support_subset {f : α ->₀ Nat} {s : Finset α} (h : f.support subseteq s) :
    f.multinomial = Nat.multinomial s f := by
  simp only [Finsupp.multinomial_eq, Nat.multinomial]
  congr 1
  · simp [Finset.sum_subset h]
  · rw [Finset.prod_subset h]
    grind [Nat.factorial_eq_one]

/--
theorem `multinomial_update` / 定理 `multinomial_update`

English:
theorem multinomial_update
  given: (a : α) (f : α ->₀ Nat)
  proof: by
  simp only [multinomial_eq]
  classical
    by_cases h : a in f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.notMem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h => (Function.update_of_ne 

中文:
定理 multinomial_update
  条件: (a : α) (f : α ->₀ 自然数)
  证明: by
  simp only [multinomial_eq]
  classical
    by_cases h : a in f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.notMem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h => (Function.update_of_ne 

Depends on / 依赖: Finset, Finset.add_sum_erase, Finset.insert_erase, Finset.notMem_erase, Function, Function.update_of_ne, Nat.choose_zero_right, Nat.multinomial_congr, Nat.multinomial_insert, add_sum_erase, choose_zero_right, classical, f.support, insert_erase, mem_erase, multinomial_congr, multinomial_eq, multinomial_insert, notMem_erase, notMem_support_iff
-/
theorem multinomial_update (a : α) (f : α ->₀ Nat) :
    f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial := by
  simp only [multinomial_eq]
  classical
    by_cases h : a in f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.notMem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h => (Function.update_of_ne (mem_erase.1 h).1 0 f).symm
    rw [notMem_support_iff] at h
    rw [h]; rw [Nat.choose_zero_right]; rw [one_mul]; rw [← h]; rw [update_self]

end Finsupp

namespace Multiset

variable {α : Type*}

/--
Definition of `countPerms` / `countPerms` 的定义

English:
definition countPerms
  signature: [DecidableEq α] (m : Multiset α)
  body: m.toFinsupp.multinomial

中文:
定义 countPerms
  签名: [DecidableEq α] (m : Multiset α)
  定义体: m.toFinsupp.multinomial

Depends on / 依赖: m.toFinsupp.multinomial, multinomial, toFinsupp
-/
noncomputable def countPerms [DecidableEq α] (m : Multiset α) : Nat :=
  m.toFinsupp.multinomial

/--
theorem `countPerms_filter_ne` / 定理 `countPerms_filter_ne`

English:
theorem countPerms_filter_ne
  given: [DecidableEq α] (a : α) (m : Multiset α)
  proof: by
  dsimp only [countPerms]
  convert! Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply]; rw [count_filter]; rw [Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_of_ne h.symm, toFinsupp_apply]
    · rw [no

中文:
定理 countPerms_filter_ne
  条件: [DecidableEq α] (a : α) (m : Multiset α)
  证明: by
  dsimp only [countPerms]
  convert! Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply]; rw [count_filter]; rw [Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_of_ne h.symm, toFinsupp_apply]
    · rw [no

Depends on / 依赖: Finsupp, Finsupp.card_toMultiset, Finsupp.coe_update, Finsupp.multinomial_update, Function, Function.update_of_ne, Function.update_self, card_toMultiset, coe_update, convert, countPerms, count_filter, h.symm, m.toFinsupp_toMultiset, multinomial_update, not_ne_iff, split_ifs, toFinsupp_apply, toFinsupp_toMultiset, update_of_ne
-/
theorem countPerms_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.countPerms = m.card.choose (m.count a) * (m.filter (a != ·)).countPerms := by
  dsimp only [countPerms]
  convert! Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply]; rw [count_filter]; rw [Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_of_ne h.symm, toFinsupp_apply]
    · rw [not_ne_iff.1 h, Function.update_self]

@[simp]
/--
theorem `countPerms_zero` / 定理 `countPerms_zero`

English:
theorem countPerms_zero
  given: [DecidableEq α]
  statement: countPerms (0 : Multiset α) = 1
  proof: by
  simp [countPerms, Finsupp.multinomial]

中文:
定理 countPerms_zero
  条件: [DecidableEq α]
  结论: countPerms (0 : Multiset α) = 1
  证明: by
  simp [countPerms, Finsupp.multinomial]

Depends on / 依赖: Finsupp, Finsupp.multinomial, countPerms, multinomial
-/
theorem countPerms_zero [DecidableEq α] : countPerms (0 : Multiset α) = 1 := by
  simp [countPerms, Finsupp.multinomial]

end Multiset

namespace Finset
open _root_.Nat

/-! ### Multinomial theorem -/

variable {α R : Type*} [DecidableEq α]

section Semiring
variable [Semiring R]

open scoped Function -- required for scoped `on` notation

set_option backward.isDefEq.respectTransparency false in
-- TODO: Can we prove one of the following two from the other one?
/--
lemma `sum_pow_eq_sum_piAntidiag_of_commute` / 引理 `sum_pow_eq_sum_piAntidiag_of_commute`

English:
lemma sum_pow_eq_sum_piAntidiag_of_commute
  statement: (s : Finset α) (f : α -> R)
  proof: by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih => ?_
  rw [Finset.sum_cons]; rw [piAntidiag_cons]; rw [sum_disjiUnion]
  simp only [sum_map, Pi.add_apply, multinomial_cons,
    Pi.add_apply, if_true, Nat.cast_mul, noncommProd_cons,


中文:
引理 sum_pow_eq_sum_piAntidiag_of_commute
  结论: (s : 有限集 α) (f : α -> R)
  证明: by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih => ?_
  rw [Finset.sum_cons]; rw [piAntidiag_cons]; rw [sum_disjiUnion]
  simp only [sum_map, Pi.add_apply, multinomial_cons,
    Pi.add_apply, if_true, Nat.cast_mul, noncommProd_cons,


Depends on / 依赖: Finset, Finset.cons_induction, Finset.sum_cons, Nat.cast_mul, Pi.add_apply, addRightEmbedding_apply, add_apply, add_zero, antidiagonal, cast_mul, cons_induction, generalizing, if_false, if_true, multinomial_cons, noncommProd_cons, piAntidiag, piAntidiag_cons, s.sum, sum_add_distrib
-/
lemma sum_pow_eq_sum_piAntidiag_of_commute (s : Finset α) (f : α -> R)
    (hc : (s : Set α).Pairwise (Commute on f)) (n : Nat) :
    (∑ i in s, f i) ^ n = ∑ k in piAntidiag s n, multinomial s k *
      s.noncommProd (fun i => f i ^ k i) (hc.mono' fun _ _ h => h.pow_pow ..) := by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih => ?_
  rw [Finset.sum_cons]; rw [piAntidiag_cons]; rw [sum_disjiUnion]
  simp only [sum_map, Pi.add_apply, multinomial_cons,
    Pi.add_apply, if_true, Nat.cast_mul, noncommProd_cons,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero,
    addRightEmbedding_apply]
  suffices forall p : Nat × Nat, p in antidiagonal n ->
    ∑ g in piAntidiag s p.2, ((g a + p.1 + s.sum g).choose (g a + p.1) : R) *
      multinomial s (g + fun i => ite (i = a) p.1 0) *
        (f a ^ (g a + p.1) * s.noncommProd (fun i => f i ^ (g i + ite (i = a) p.1 0))
          ((hc.mono (by simp)).mono' fun i j h => h.pow_pow ..)) =
      ∑ g in piAntidiag s p.2, n.choose p.1 * multinomial s g * (f a ^ p.1 *
        s.noncommProd (fun i => f i ^ g i) ((hc.mono (by simp)).mono' fun i j h => h.pow_pow ..)) by
    rw [sum_congr rfl this]
    simp only [Nat.antidiagonal_eq_map, sum_map, Function.Embedding.coeFn_mk]
    rw [(Commute.sum_right _ _ _ fun i hi => hc (by simp) (by simp [hi])
      (by simpa [eq_comm] using ne_of_mem_of_not_mem hi has)).add_pow]
    simp only [ih (hc.mono (by simp)), sum_mul, mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun g _ => ?_
    rw [← Nat.cast_comm]; rw [(Nat.commute_cast (f a ^ i) _).left_comm]; rw [mul_assoc]
  refine fun p hp => sum_congr rfl fun f hf => ?_
  rw [mem_piAntidiag] at hf
  rw [not_imp_comm.1 (hf.2 _) has]; rw [zero_add]; rw [hf.1]
  congr 2
  · rw [mem_antidiagonal.1 hp]
  · rw [multinomial_congr]
    intro t ht
    rw [Pi.add_apply]; rw [if_neg]; rw [add_zero]
    exact ne_of_mem_of_not_mem ht has
  refine noncommProd_congr rfl (fun t ht => ?_) _
  rw [if_neg]; rw [add_zero]
  exact ne_of_mem_of_not_mem ht has

/--
theorem `sum_pow_of_commute` / 定理 `sum_pow_of_commute`

English:
theorem sum_pow_of_commute
  statement: (x : α -> R) (s : Finset α)
  proof: by
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty]
    rintro (_ | n)
    · rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert! (@one_mul R _ _).symm
      convert! @Nat.cast_one R _
      simp
  

中文:
定理 sum_pow_of_commute
  结论: (x : α -> R) (s : 有限集 α)
  证明: by
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty]
    rintro (_ | n)
    · rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert! (@one_mul R _ _).symm
      convert! @Nat.cast_one R _
      simp
  

Depends on / 依赖: Commut, Finset, Finset.induction, Finset.instIsEmpty, Finset.sym, Fintype, Fintype.sum_empty, Fintype.sum_subsingleton, IsEmpty, Nat.cast_one, _root_, _root_.pow_succ, _root_.pow_zero, cast_one, convert, eq_iff_true_of_subsingleton, hc.mono, insert, instIsEmpty, mul_zero
-/
theorem sum_pow_of_commute (x : α -> R) (s : Finset α)
    (hc : (s : Set α).Pairwise (Commute on x)) :
    forall n,
      s.sum x ^ n =
        ∑ k : s.sym n,
          k.1.1.countPerms *
            (k.1.1.map <| x).noncommProd
              (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 k.2) := by
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty]
    rintro (_ | n)
    · rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert! (@one_mul R _ _).symm
      convert! @Nat.cast_one R _
      simp
    · rw [_root_.pow_succ, mul_zero]
      have : IsEmpty (Finset.sym (∅ : Finset α) n.succ) := Finset.instIsEmpty
      apply (Fintype.sum_empty _).symm
  | insert a s ha ih => ?_
  intro n; specialize ih (hc.mono <| s.subset_insert a)
  rw [sum_insert ha]; rw [(Commute.sum_right s _ _ _).add_pow]; rw [sum_range]; swap
  · exact fun _ hb => hc (mem_insert_self a s) (mem_insert_of_mem hb)
      (ne_of_mem_of_not_mem hb ha).symm
  · simp_rw [ih, mul_sum, sum_mul, sum_sigma', univ_sigma_univ]
    refine (Fintype.sum_equiv (symInsertEquiv ha) _ _ fun m => ?_).symm
    rw [m.1.1.countPerms_filter_ne a]
    conv in m.1.1.map _ => rw [← m.1.1.filter_add_not (a = ·), Multiset.map_add]
    simp_rw [Multiset.noncommProd_add, m.1.1.filter_eq, Multiset.map_replicate, m.1.2]
    rw [Multiset.noncommProd_eq_pow_card _ _ _ fun _ => Multiset.eq_of_mem_replicate]
    rw [Multiset.card_replicate]; rw [Nat.cast_mul]; rw [mul_assoc]; rw [Nat.cast_comm]
    congr 1; simp_rw [← mul_assoc, Nat.cast_comm]; rfl

end Semiring

section CommSemiring
variable [CommSemiring R] {f : α -> R} {s : Finset α}

/--
lemma `sum_pow_eq_sum_piAntidiag` / 引理 `sum_pow_eq_sum_piAntidiag`

English:
lemma sum_pow_eq_sum_piAntidiag
  given: (s : Finset α) (f : α -> R) (n : Nat)
  proof: by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ => Commute.all ..]

中文:
引理 sum_pow_eq_sum_piAntidiag
  条件: (s : 有限集 α) (f : α -> R) (n : 自然数)
  证明: by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ => Commute.all ..]

Depends on / 依赖: Commute, Commute.all, noncommProd_eq_prod, simp_rw, sum_pow_eq_sum_piAntidiag_of_commute
-/
lemma sum_pow_eq_sum_piAntidiag (s : Finset α) (f : α -> R) (n : Nat) :
    (∑ i in s, f i) ^ n = ∑ k in piAntidiag s n, multinomial s k * ∏ i in s, f i ^ k i := by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ => Commute.all ..]

/--
theorem `sum_pow` / 定理 `sum_pow`

English:
theorem sum_pow
  given: (x : α -> R) (n : Nat)
  proof: by
  conv_rhs => rw [← sum_coe_sort]
  convert! sum_pow_of_commute x s (fun _ _ _ _ _ => Commute.all ..) n
  rw [Multiset.noncommProd_eq_prod]

中文:
定理 sum_pow
  条件: (x : α -> R) (n : 自然数)
  证明: by
  conv_rhs => rw [← sum_coe_sort]
  convert! sum_pow_of_commute x s (fun _ _ _ _ _ => Commute.all ..) n
  rw [Multiset.noncommProd_eq_prod]

Depends on / 依赖: Commute, Commute.all, Multiset, Multiset.noncommProd_eq_prod, conv_rhs, convert, noncommProd_eq_prod, sum_coe_sort, sum_pow_of_commute
-/
theorem sum_pow (x : α -> R) (n : Nat) :
    s.sum x ^ n = ∑ k in s.sym n, k.val.countPerms * (k.val.map x).prod := by
  conv_rhs => rw [← sum_coe_sort]
  convert! sum_pow_of_commute x s (fun _ _ _ _ _ => Commute.all ..) n
  rw [Multiset.noncommProd_eq_prod]

end CommSemiring
end Finset

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι -> Nat}

/--
lemma `multinomial_two_mul_le_mul_multinomial` / 引理 `multinomial_two_mul_le_mul_multinomial`

English:
lemma multinomial_two_mul_le_mul_multinomial
  proof: by
  rw [multinomial]; rw [multinomial]; rw [← mul_sum]; rw [← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum ..)]
  refine Nat.div_le_div_of_mul_le_mul (by positivity)
    ((prod_factorial_dvd_factorial_sum ..).trans (Nat.dvd_mul_left ..)) ?_
  calc
    (2 * ∑ i in s, f i)! * ∏ i in s, (f i)

中文:
引理 multinomial_two_mul_le_mul_multinomial
  证明: by
  rw [multinomial]; rw [multinomial]; rw [← mul_sum]; rw [← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum ..)]
  refine Nat.div_le_div_of_mul_le_mul (by positivity)
    ((prod_factorial_dvd_factorial_sum ..).trans (Nat.dvd_mul_left ..)) ?_
  calc
    (2 * ∑ i in s, f i)! * ∏ i in s, (f i)

Depends on / 依赖: Nat.div_le_div_of_mul_le_mul, Nat.dvd_mul_left, Nat.factorial_two_mul_le, Nat.mul_div_assoc, div_le_div_of_mul_le_mul, dvd_mul_left, factorial_two_mul_le, mul_div_assoc, mul_sum, multinomial, prod_factorial_dvd_factorial_sum
-/
lemma multinomial_two_mul_le_mul_multinomial :
    multinomial s (fun i => 2 * f i) <= ((∑ i in s, f i) ^ ∑ i in s, f i) * multinomial s f := by
  rw [multinomial]; rw [multinomial]; rw [← mul_sum]; rw [← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum ..)]
  refine Nat.div_le_div_of_mul_le_mul (by positivity)
    ((prod_factorial_dvd_factorial_sum ..).trans (Nat.dvd_mul_left ..)) ?_
  calc
    (2 * ∑ i in s, f i)! * ∏ i in s, (f i)!
      <= ((2 * ∑ i in s, f i) ^ (∑ i in s, f i) * (∑ i in s, f i)!) * ∏ i in s, (f i)! := by
      gcongr; exact Nat.factorial_two_mul_le _
    _ = ((∑ i in s, f i) ^ ∑ i in s, f i) * (∑ i in s, f i)! * ∏ i in s, 2 ^ f i * (f i)! := by
      rw [mul_pow]; rw [← prod_pow_eq_pow_sum]; rw [prod_mul_distrib]; ring
    _ <= ((∑ i in s, f i) ^ ∑ i in s, f i) * (∑ i in s, f i)! * ∏ i in s, (2 * f i)! := by
      gcongr
      rw [← doubleFactorial_two_mul]
      exact doubleFactorial_le_factorial _

end Nat

namespace Sym

variable {n : Nat} {α : Type*} [DecidableEq α]

/--
theorem `countPerms_coe_fill_of_notMem` / 定理 `countPerms_coe_fill_of_notMem`

English:
theorem countPerms_coe_fill_of_notMem
  given: {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s)
  proof: by
  rw [Multiset.countPerms_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_notMem hx]
  · refine congrArg _ ?_
    rw [coe_fill]; rw [coe_replicate]; rw [Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_eq_left]
      r

中文:
定理 countPerms_coe_fill_of_notMem
  条件: {m : 有限集 (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s)
  证明: by
  rw [Multiset.countPerms_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_notMem hx]
  · refine congrArg _ ?_
    rw [coe_fill]; rw [coe_replicate]; rw [Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_eq_left]
      r

Depends on / 依赖: Multiset, Multiset.countPerms_filter_ne, Multiset.filter_add, Multiset.filter_eq_nil, Multiset.filter_eq_self.mpr, Multiset.mem_replicate.mp, add_eq_left, card_coe, coe_fill, coe_replicate, countPerms_filter_ne, count_coe_fill_self_of_notMem, filter_add, filter_eq_nil, filter_eq_self, mem_coe, mem_replicate
-/
theorem countPerms_coe_fill_of_notMem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s) :
    (fill x m s : Multiset α).countPerms = n.choose m * (s : Multiset α).countPerms := by
  rw [Multiset.countPerms_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_notMem hx]
  · refine congrArg _ ?_
    rw [coe_fill]; rw [coe_replicate]; rw [Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_eq_left]
      rw [Multiset.filter_eq_nil]
      exact fun j hj => by simp [Multiset.mem_replicate.mp hj]
· exact fun j hj h => hx by simpa [h] using hj

end Sym

/--
theorem `Finsupp.multinomial_of_support_subset` / 定理 `Finsupp.multinomial_of_support_subset`

English:
theorem Finsupp.multinomial_of_support_subset
  statement: {σ : Type*} {d : σ ->₀ Nat} {s : Finset σ}
  proof: by
  rw [Nat.multinomial]; rw [Finsupp.multinomial]; rw [sum_of_support_subset _ h _ (by simp)]; rw [prod_of_support_subset _ h _ (by simp)]
  simp

中文:
定理 有限支撑.multinomial_of_support_subset
  结论: {σ : 类型} {d : σ ->₀ 自然数} {s : 有限集 σ}
  证明: by
  rw [Nat.multinomial]; rw [Finsupp.multinomial]; rw [sum_of_support_subset _ h _ (by simp)]; rw [prod_of_support_subset _ h _ (by simp)]
  simp

Depends on / 依赖: Finsupp, Finsupp.multinomial, Nat.multinomial, multinomial, prod_of_support_subset, sum_of_support_subset
-/
theorem Finsupp.multinomial_of_support_subset {σ : Type*} {d : σ ->₀ Nat} {s : Finset σ}
    (h : d.support subseteq s) : Nat.multinomial s d = d.multinomial := by
  rw [Nat.multinomial]; rw [Finsupp.multinomial]; rw [sum_of_support_subset _ h _ (by simp)]; rw [prod_of_support_subset _ h _ (by simp)]
  simp

namespace List


/--
lemma `toFinsupp_sum` / 引理 `toFinsupp_sum`

English:
lemma toFinsupp_sum
  given: {α : Type*} [AddCommMonoid α] [DecidableEq α] (l : List α)
  proof: by
  match l with
  | nil => simp
  | x :: l =>
    simp only [toFinsupp_cons_eq_single_add_embDomain, sum_cons]
    rw [Finsupp.sum_add_index (by simp) (by simp)]
    simp [Finsupp.sum_embDomain, l.toFinsupp_sum]

中文:
引理 toFinsupp_sum
  条件: {α : 类型} [加法交换幺半群 α] [DecidableEq α] (l : 列表 α)
  证明: by
  match l with
  | nil => simp
  | x :: l =>
    simp only [toFinsupp_cons_eq_single_add_embDomain, sum_cons]
    rw [Finsupp.sum_add_index (by simp) (by simp)]
    simp [Finsupp.sum_embDomain, l.toFinsupp_sum]

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, Finsupp.sum_embDomain, l.toFinsupp_sum, sum_add_index, sum_cons, sum_embDomain, toFinsupp_cons_eq_single_add_embDomain, toFinsupp_sum
-/
lemma toFinsupp_sum {α : Type*} [AddCommMonoid α] [DecidableEq α] (l : List α) :
    l.toFinsupp.sum (fun _ a => a) = l.sum := by
  match l with
  | nil => simp
  | x :: l =>
    simp only [toFinsupp_cons_eq_single_add_embDomain, sum_cons]
    rw [Finsupp.sum_add_index (by simp) (by simp)]
    simp [Finsupp.sum_embDomain, l.toFinsupp_sum]

/--
Definition of `multinomial` / `multinomial` 的定义

English:
abbreviation multinomial
  signature: (l : List Nat)
  body: l.toFinsupp.multinomial

中文:
缩写 multinomial
  签名: (l : 列表 自然数)
  定义体: l.toFinsupp.multinomial

Depends on / 依赖: l.toFinsupp.multinomial, multinomial, toFinsupp
-/
abbrev multinomial (l : List Nat) : Nat := l.toFinsupp.multinomial

/--
theorem `multinomial_cons` / 定理 `multinomial_cons`

English:
theorem multinomial_cons
  given: (x : Nat) (l : List Nat)
  proof: by
  simp only [multinomial]
  rw [Finsupp.multinomial_update 0 (x :: l).toFinsupp]
  congr 1
  · congr
    exact List.toFinsupp_sum (x :: l)
  let succEmb : Nat ↪ Nat := addRightEmbedding 1
  have : (Finsupp.single 0 x + l.toFinsupp.embDomain succEmb).update 0 0 =
    (l.toFinsupp.embDomain succEmb

中文:
定理 multinomial_cons
  条件: (x : 自然数) (l : 列表 自然数)
  证明: by
  simp only [multinomial]
  rw [Finsupp.multinomial_update 0 (x :: l).toFinsupp]
  congr 1
  · congr
    exact List.toFinsupp_sum (x :: l)
  let succEmb : Nat ↪ Nat := addRightEmbedding 1
  have : (Finsupp.single 0 x + l.toFinsupp.embDomain succEmb).update 0 0 =
    (l.toFinsupp.embDomain succEmb

Depends on / 依赖: Finsupp, Finsupp.embDomai, Finsupp.multinomial_update, Finsupp.single, Finsupp.single_eq_of_ne, Finsupp.update_apply, List.toFinsupp_sum, addRightEmbedding, embDomai, embDomain, if_neg, l.toFinsupp.embDomain, multinomial, multinomial_update, single, single_eq_of_ne, succEmb, toFinsupp, toFinsupp_sum, update
-/
theorem multinomial_cons (x : Nat) (l : List Nat) :
    (x :: l).multinomial = Nat.choose (x + l.sum) x * l.multinomial := by
  simp only [multinomial]
  rw [Finsupp.multinomial_update 0 (x :: l).toFinsupp]
  congr 1
  · congr
    exact List.toFinsupp_sum (x :: l)
  let succEmb : Nat ↪ Nat := addRightEmbedding 1
  have : (Finsupp.single 0 x + l.toFinsupp.embDomain succEmb).update 0 0 =
    (l.toFinsupp.embDomain succEmb).update 0 0 := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [Finsupp.update_apply, if_neg hi, Finsupp.single_eq_of_ne hi]
  have h (x) : (l.toFinsupp.embDomain succEmb) (x + 1) = l[x]?.getD 0 := by
    rw [Finsupp.embDomain_apply]; rw [dif_pos ⟨x]; rw [by simp [succEmb]⟩]
    simp [succEmb]
  simp [toFinsupp_cons_eq_single_add_embDomain, Finsupp.multinomial_eq,
    succEmb, this, Nat.multinomial, h]

end List

namespace Multiset

/--
Definition of `multinomial` / `multinomial` 的定义

English:
definition multinomial
  signature: (m : Multiset Nat)
  body: Quot.liftOn m List.multinomial fun l l' h => by
  induction h with
  | nil => simp
  | @cons x l l' hl hl' => simp [List.multinomial_cons, hl', hl.sum_nat]
  | @swap x y l =>
    simp only [List.multinomial_cons, ← mul_assoc, List.sum_cons]
    rw [← Nat.choose_symm (Nat.le_add_right y _)]; rw [add_

中文:
定义 multinomial
  签名: (m : Multiset 自然数)
  定义体: Quot.liftOn m List.multinomial fun l l' h => by
  induction h with
  | nil => simp
  | @cons x l l' hl hl' => simp [List.multinomial_cons, hl', hl.sum_nat]
  | @swap x y l =>
    simp only [List.multinomial_cons, ← mul_assoc, List.sum_cons]
    rw [← Nat.choose_symm (Nat.le_add_right y _)]; rw [add_

Depends on / 依赖: List.multinomial, List.multinomial_cons, List.sum_cons, Nat.choose_mul, Nat.choose_symm, Nat.le_add_right, Quot.liftOn, add_left_comm, add_tsub_cancel_left, choose_mul, choose_symm, hl.sum_nat, le_add_right, liftOn, mul_assoc, multinomial, multinomial_cons, sum_cons, sum_nat
-/
def multinomial (m : Multiset Nat) : Nat := Quot.liftOn m List.multinomial fun l l' h => by
  induction h with
  | nil => simp
  | @cons x l l' hl hl' => simp [List.multinomial_cons, hl', hl.sum_nat]
  | @swap x y l =>
    simp only [List.multinomial_cons, ← mul_assoc, List.sum_cons]
    rw [← Nat.choose_symm (Nat.le_add_right y _)]; rw [add_tsub_cancel_left]
    rw [add_left_comm]; rw [Nat.choose_mul (Nat.le_add_right _ _)]; rw [add_tsub_cancel_left]
    simp [← Nat.choose_symm (Nat.le_add_right _ _), add_tsub_cancel_left]
  | @trans l l' l'' h h' ih ih' => rw [ih, ih']

/--
theorem `multinomial_cons` / 定理 `multinomial_cons`

English:
theorem multinomial_cons
  given: (x : Nat) (m : Multiset Nat)
  proof: by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact List.multinomial_cons x l

@[simp]

中文:
定理 multinomial_cons
  条件: (x : 自然数) (m : Multiset 自然数)
  证明: by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact List.multinomial_cons x l

@[simp]

Depends on / 依赖: List.multinomial_cons, Quotient, Quotient.exists_rep, exists_rep, multinomial_cons
-/
theorem multinomial_cons (x : Nat) (m : Multiset Nat) :
    (x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact List.multinomial_cons x l

@[simp]
/--
theorem `multinomial_zero` / 定理 `multinomial_zero`

English:
theorem multinomial_zero
  statement: Multiset.multinomial 0 = 1
  proof: rfl

@[simp]

中文:
定理 multinomial_zero
  结论: Multiset.multinomial 0 = 1
  证明: rfl

@[simp]
-/
theorem multinomial_zero : Multiset.multinomial 0 = 1 := rfl

@[simp]
/--
theorem `multinomial_singleton` / 定理 `multinomial_singleton`

English:
theorem multinomial_singleton
  given: (n : Nat)
  proof: by
  simp [← cons_zero, multinomial_cons]

中文:
定理 multinomial_singleton
  条件: (n : 自然数)
  证明: by
  simp [← cons_zero, multinomial_cons]

Depends on / 依赖: cons_zero, multinomial_cons
-/
theorem multinomial_singleton (n : Nat) :
    Multiset.multinomial {n} = 1 := by
  simp [← cons_zero, multinomial_cons]

/--
theorem `multinomial_add` / 定理 `multinomial_add`

English:
theorem multinomial_add
  given: (m m' : Multiset Nat)
  proof: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m hind =>
    simp only [cons_add, sum_cons, sum_add, multinomial_cons, hind, ← mul_assoc]
    congr 2
    rw [← Nat.choose_symm (Nat.le_add_right _ _)]; rw [add_tsub_cancel_left]; rw [eq_comm]; rw [Nat.choose_mul (Nat.le

中文:
定理 multinomial_add
  条件: (m m' : Multiset 自然数)
  证明: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m hind =>
    simp only [cons_add, sum_cons, sum_add, multinomial_cons, hind, ← mul_assoc]
    congr 2
    rw [← Nat.choose_symm (Nat.le_add_right _ _)]; rw [add_tsub_cancel_left]; rw [eq_comm]; rw [Nat.choose_mul (Nat.le

Depends on / 依赖: Multiset, Multiset.induction_on, Nat.choose_mul, Nat.choose_symm, Nat.le_add_right, add_tsub_cancel_left, choose_mul, choose_symm, cons_add, eq_comm, induction_on, le_add_right, mul_assoc, multinomial_cons, sum_add, sum_cons
-/
theorem multinomial_add (m m' : Multiset Nat) :
    (m + m').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m hind =>
    simp only [cons_add, sum_cons, sum_add, multinomial_cons, hind, ← mul_assoc]
    congr 2
    rw [← Nat.choose_symm (Nat.le_add_right _ _)]; rw [add_tsub_cancel_left]; rw [eq_comm]; rw [Nat.choose_mul (Nat.le_add_right _ _)]; rw [← Nat.choose_symm (Nat.le_add_right x _)]
    simp [add_tsub_cancel_left]

/--
theorem `multinomial_nsmul` / 定理 `multinomial_nsmul`

English:
theorem multinomial_nsmul
  given: (k : Nat) (m : Multiset Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [succ_nsmul']; rw [multinomial_add]; rw [hk]; rw [Finset.range_add_one]; rw [Nat.multinomial_insert (by simp)]; rw [sum_add]; rw [sum_nsmul]; rw [pow_succ']
    simp [smul_eq_mul, Finset.sum_const, Finset.card_range]
    ring

中文:
定理 multinomial_nsmul
  条件: (k : 自然数) (m : Multiset 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [succ_nsmul']; rw [multinomial_add]; rw [hk]; rw [Finset.range_add_one]; rw [Nat.multinomial_insert (by simp)]; rw [sum_add]; rw [sum_nsmul]; rw [pow_succ']
    simp [smul_eq_mul, Finset.sum_const, Finset.card_range]
    ring

Depends on / 依赖: Finset, Finset.card_range, Finset.range_add_one, Finset.sum_const, Nat.multinomial_insert, card_range, multinomial_add, multinomial_insert, pow_succ, range_add_one, smul_eq_mul, succ_nsmul, sum_add, sum_const, sum_nsmul
-/
theorem multinomial_nsmul (k : Nat) (m : Multiset Nat) :
    (k • m).multinomial = Nat.multinomial (Finset.range k) (fun _ => m.sum) * m.multinomial ^ k := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [succ_nsmul']; rw [multinomial_add]; rw [hk]; rw [Finset.range_add_one]; rw [Nat.multinomial_insert (by simp)]; rw [sum_add]; rw [sum_nsmul]; rw [pow_succ']
    simp [smul_eq_mul, Finset.sum_const, Finset.card_range]
    ring

/--
theorem `multinomial_nsmul_singleton` / 定理 `multinomial_nsmul_singleton`

English:
theorem multinomial_nsmul_singleton
  given: (k n : Nat)
  proof: by
  simp [multinomial_nsmul]

中文:
定理 multinomial_nsmul_singleton
  条件: (k n : 自然数)
  证明: by
  simp [multinomial_nsmul]

Depends on / 依赖: multinomial_nsmul
-/
theorem multinomial_nsmul_singleton (k n : Nat) :
    (k • {n} : Multiset Nat).multinomial = Nat.multinomial (Finset.range k) (fun _ => n) := by
  simp [multinomial_nsmul]

/--
theorem `multinomial_pos` / 定理 `multinomial_pos`

English:
theorem multinomial_pos
  given: (m : Multiset Nat)
  statement: 0 < m.multinomial
  proof: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m h =>
    simp only [multinomial_cons, h, mul_pos_iff_of_pos_right]
    exact Nat.choose_pos (Nat.le_add_right x m.sum)

中文:
定理 multinomial_pos
  条件: (m : Multiset 自然数)
  结论: 0 < m.multinomial
  证明: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m h =>
    simp only [multinomial_cons, h, mul_pos_iff_of_pos_right]
    exact Nat.choose_pos (Nat.le_add_right x m.sum)

Depends on / 依赖: Multiset, Multiset.induction_on, Nat.choose_pos, Nat.le_add_right, choose_pos, induction_on, le_add_right, m.sum, mul_pos_iff_of_pos_right, multinomial_cons
-/
theorem multinomial_pos (m : Multiset Nat) : 0 < m.multinomial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m h =>
    simp only [multinomial_cons, h, mul_pos_iff_of_pos_right]
    exact Nat.choose_pos (Nat.le_add_right x m.sum)

section PositivityExtension

open Mathlib.Meta.Positivity Qq in
/--
Positivity extension for `Multiset.multinomial`.
-/
@[positivity multinomial (_ : Multiset Nat)]
meta def evalMultinomial : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => throwError "not PartialOrder Nat" | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(multinomial $a) =>
    assertInstancesCommute
    return .positive q(multinomial_pos $a)
  | _, _, _ => throwError "not multinomial"

end PositivityExtension

end Multiset
