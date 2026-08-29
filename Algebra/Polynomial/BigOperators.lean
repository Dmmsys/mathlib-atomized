/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `Finset.sum` and `Finset.prod` respectively.

## Main results

- `Polynomial.natDegree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[CommSemiring R]`,
  but it ought to be true for `[Semiring R]` and `List.prod`.
- `Polynomial.natDegree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `Polynomial.leadingCoeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `Polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/

public section


open Finset

open Multiset

open Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type*} [Semiring S]

/--
theorem `natDegree_list_sum_le` / 定理 `natDegree_list_sum_le`

English:
theorem natDegree_list_sum_le
  given: (l : List S[X])
  proof: by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le

中文:
定理 natDegree_list_sum_le
  条件: (l : 列表 S[X])
  证明: by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le

Depends on / 依赖: List.sum_le_foldr_max, natDegree, natDegree_add_le, sum_le_foldr_max
-/
theorem natDegree_list_sum_le (l : List S[X]) :
    natDegree l.sum <= (l.map natDegree).foldr max 0 := by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le

/--
theorem `natDegree_multiset_sum_le` / 定理 `natDegree_multiset_sum_le`

English:
theorem natDegree_multiset_sum_le
  given: (l : Multiset S[X])
  proof: Quotient.inductionOn l (by simpa using natDegree_list_sum_le)

中文:
定理 natDegree_multiset_sum_le
  条件: (l : Multiset S[X])
  证明: Quotient.inductionOn l (by simpa using natDegree_list_sum_le)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, natDegree_list_sum_le
-/
theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum <= (l.map natDegree).foldr max 0 :=
  Quotient.inductionOn l (by simpa using natDegree_list_sum_le)

/--
theorem `natDegree_sum_le` / 定理 `natDegree_sum_le`

English:
theorem natDegree_sum_le
  given: (f : ι -> S[X])
  proof: by
  simpa using! natDegree_multiset_sum_le (s.val.map f)

中文:
定理 natDegree_sum_le
  条件: (f : ι -> S[X])
  证明: by
  simpa using! natDegree_multiset_sum_le (s.val.map f)

Depends on / 依赖: natDegree_multiset_sum_le, s.val.map
-/
theorem natDegree_sum_le (f : ι -> S[X]) :
    natDegree (∑ i in s, f i) <= s.fold max 0 (natDegree ∘ f) := by
  simpa using! natDegree_multiset_sum_le (s.val.map f)

/--
lemma `natDegree_sum_le_of_forall_le` / 引理 `natDegree_sum_le_of_forall_le`

English:
lemma natDegree_sum_le_of_forall_le
  given: {n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n)
  proof: le_trans (natDegree_sum_le s f) (Finset.fold_max_le n).mpr by simpa

中文:
引理 natDegree_sum_le_of_对任意_le
  条件: {n : 自然数} (f : ι -> S[X]) (h : 对任意 i in s, natDegree (f i) <= n)
  证明: le_trans (natDegree_sum_le s f) (Finset.fold_max_le n).mpr by simpa

Depends on / 依赖: Finset, Finset.fold_max_le, fold_max_le, le_trans, natDegree_sum_le
-/
lemma natDegree_sum_le_of_forall_le {n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n) :
    natDegree (∑ i in s, f i) <= n :=
le_trans (natDegree_sum_le s f) (Finset.fold_max_le n).mpr by simpa

set_option backward.isDefEq.respectTransparency false in
/--
theorem `leadingCoeff_sum_of_degree_eq` / 定理 `leadingCoeff_sum_of_degree_eq`

English:
theorem leadingCoeff_sum_of_degree_eq
  statement: {f : ι -> S[X]} {s : Finset ι} {d}
  proof: by
  obtain _ | d := d
  · simp_all [WithBot.none_eq_bot]
· replace hd k (hk : k in s) : (f k).natDegree = d := natDegree_eq_of_degree_eq_some hd k hk
    suffices (∑ k in s, f k).natDegree = d by simp_all [leadingCoeff]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · aesop (add safe natDegree_s

中文:
定理 leadingCoeff_sum_of_degree_eq
  结论: {f : ι -> S[X]} {s : 有限集 ι} {d}
  证明: by
  obtain _ | d := d
  · simp_all [WithBot.none_eq_bot]
· replace hd k (hk : k in s) : (f k).natDegree = d := natDegree_eq_of_degree_eq_some hd k hk
    suffices (∑ k in s, f k).natDegree = d by simp_all [leadingCoeff]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · aesop (add safe natDegree_s

Depends on / 依赖: WithBot, WithBot.none_eq_bot, leadingCoeff, natDegree, natDegree_eq_of_degree_eq_some, natDegree_eq_of_le_of_coeff_ne_zero, natDegree_sum_le_of_forall_le, none_eq_bot, replace
-/
theorem leadingCoeff_sum_of_degree_eq {f : ι -> S[X]} {s : Finset ι} {d}
    (hd : forall k in s, (f k).degree = d) (hf : ∑ k in s, (f k).leadingCoeff != 0) :
    (∑ k in s, f k).leadingCoeff = ∑ k in s, (f k).leadingCoeff := by
  obtain _ | d := d
  · simp_all [WithBot.none_eq_bot]
· replace hd k (hk : k in s) : (f k).natDegree = d := natDegree_eq_of_degree_eq_some hd k hk
    suffices (∑ k in s, f k).natDegree = d by simp_all [leadingCoeff]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · aesop (add safe natDegree_sum_le_of_forall_le)
    · simp_all [leadingCoeff]

/--
theorem `degree_list_sum_le_of_forall_degree_le` / 定理 `degree_list_sum_le_of_forall_degree_le`

English:
theorem degree_list_sum_le_of_forall_degree_le
  statement: (l : List S[X])
  proof: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))

中文:
定理 degree_list_sum_le_of_对任意_degree_le
  结论: (l : 列表 S[X])
  证明: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))

Depends on / 依赖: List.mem_cons, List.sum_cons, degree_add_le, forall_eq_or_imp, le_trans, max_le, mem_cons, sum_cons, tl.sum
-/
theorem degree_list_sum_le_of_forall_degree_le (l : List S[X])
    (n : WithBot Nat) (hl : forall p in l, degree p <= n) :
    degree l.sum <= n := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))

/--
theorem `degree_list_sum_le` / 定理 `degree_list_sum_le`

English:
theorem degree_list_sum_le
  given: (l : List S[X])
  statement: degree l.sum <= (l.map natDegree).maximum
  proof: by
  apply degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]

中文:
定理 degree_list_sum_le
  条件: (l : 列表 S[X])
  结论: degree l.求和 <= (l.map natDegree).maximum
  证明: by
  apply degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]

Depends on / 依赖: List.le_maximum_of_mem, List.mem_map, degree_eq_natDegree, degree_list_sum_le_of_forall_degree_le, le_maximum_of_mem, mem_map
-/
theorem degree_list_sum_le (l : List S[X]) : degree l.sum <= (l.map natDegree).maximum := by
  apply degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]

/--
theorem `natDegree_list_prod_le` / 定理 `natDegree_list_prod_le`

English:
theorem natDegree_list_prod_le
  given: (l : List S[X])
  statement: natDegree l.prod <= (l.map natDegree).sum
  proof: l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le

中文:
定理 natDegree_list_prod_le
  条件: (l : 列表 S[X])
  结论: natDegree l.乘积 <= (l.map natDegree).求和
  证明: l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le

Depends on / 依赖: apply_prod_le_sum_map, l.apply_prod_le_sum_map, natDegree_mul_le, natDegree_one, natDegree_one.le
-/
theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod <= (l.map natDegree).sum :=
  l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le

/--
theorem `degree_list_prod_le` / 定理 `degree_list_prod_le`

English:
theorem degree_list_prod_le
  given: (l : List S[X])
  statement: degree l.prod <= (l.map degree).sum
  proof: l.apply_prod_le_sum_map _ degree_one_le degree_mul_le

中文:
定理 degree_list_prod_le
  条件: (l : 列表 S[X])
  结论: degree l.乘积 <= (l.map degree).求和
  证明: l.apply_prod_le_sum_map _ degree_one_le degree_mul_le

Depends on / 依赖: apply_prod_le_sum_map, degree_mul_le, degree_one_le, l.apply_prod_le_sum_map
-/
theorem degree_list_prod_le (l : List S[X]) : degree l.prod <= (l.map degree).sum :=
  l.apply_prod_le_sum_map _ degree_one_le degree_mul_le

/--
theorem `coeff_list_prod_of_natDegree_le` / 定理 `coeff_list_prod_of_natDegree_le`

English:
theorem coeff_list_prod_of_natDegree_le
  given: (l : List S[X]) (n : Nat) (hl : forall p in l, natDegree p <= n)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : forall p in tl, natDegree p <= n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul]; rw [one_mul]; rw [add_comm]; rw [← IH hl']; rw [mul_comm tl.length]
    h

中文:
定理 coeff_list_prod_of_natDegree_le
  条件: (l : 列表 S[X]) (n : 自然数) (hl : 对任意 p in l, natDegree p <= n)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : forall p in tl, natDegree p <= n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul]; rw [one_mul]; rw [add_comm]; rw [← IH hl']; rw [mul_comm tl.length]
    h

Depends on / 依赖: List.length, List.map, List.mem_cons_of_mem, List.prod_cons, List.sum_le_card_nsmul, add_comm, add_mul, coeff_mul_add_eq_of_natDe, length, length_map, mem_cons_of_mem, mul_comm, natDegree, natDegree_list_prod_le, one_mul, prod_cons, sum_le_card_nsmul, tl.length, tl.length_map, tl.prod
-/
theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : Nat) (hl : forall p in l, natDegree p <= n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : forall p in tl, natDegree p <= n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul]; rw [one_mul]; rw [add_comm]; rw [← IH hl']; rw [mul_comm tl.length]
    have h : natDegree tl.prod <= n * tl.length := by
      refine (natDegree_list_prod_le _).trans ?_
      rw [← tl.length_map natDegree]; rw [mul_comm]
      refine List.sum_le_card_nsmul _ _ ?_
      simpa using hl'
    exact coeff_mul_add_eq_of_natDegree_le (hl _ List.mem_cons_self) h

end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι -> R[X]) (t : Multiset R[X])

/--
theorem `natDegree_multiset_prod_le` / 定理 `natDegree_multiset_prod_le`

English:
theorem natDegree_multiset_prod_le
  statement: t.prod.natDegree <= (t.map natDegree).sum
  proof: Quotient.inductionOn t (by simpa using natDegree_list_prod_le)

中文:
定理 natDegree_multiset_prod_le
  结论: t.乘积.natDegree <= (t.map natDegree).求和
  证明: Quotient.inductionOn t (by simpa using natDegree_list_prod_le)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, natDegree_list_prod_le
-/
theorem natDegree_multiset_prod_le : t.prod.natDegree <= (t.map natDegree).sum :=
  Quotient.inductionOn t (by simpa using natDegree_list_prod_le)

/--
theorem `natDegree_prod_le` / 定理 `natDegree_prod_le`

English:
theorem natDegree_prod_le
  statement: (∏ i in s, f i).natDegree <= ∑ i in s, (f i).natDegree
  proof: by
  simpa using natDegree_multiset_prod_le (s.1.map f)

中文:
定理 natDegree_prod_le
  结论: (∏ i in s, f i).natDegree <= ∑ i in s, (f i).natDegree
  证明: by
  simpa using natDegree_multiset_prod_le (s.1.map f)

Depends on / 依赖: natDegree_multiset_prod_le
-/
theorem natDegree_prod_le : (∏ i in s, f i).natDegree <= ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_le (s.1.map f)

/--
theorem `degree_multiset_prod_le` / 定理 `degree_multiset_prod_le`

English:
theorem degree_multiset_prod_le
  statement: t.prod.degree <= (t.map Polynomial.degree).sum
  proof: Quotient.inductionOn t (by simpa using degree_list_prod_le)

中文:
定理 degree_multiset_prod_le
  结论: t.乘积.degree <= (t.map 多项式.degree).求和
  证明: Quotient.inductionOn t (by simpa using degree_list_prod_le)

Depends on / 依赖: Quotient, Quotient.inductionOn, degree_list_prod_le, inductionOn
-/
theorem degree_multiset_prod_le : t.prod.degree <= (t.map Polynomial.degree).sum :=
  Quotient.inductionOn t (by simpa using degree_list_prod_le)

/--
theorem `degree_prod_le` / 定理 `degree_prod_le`

English:
theorem degree_prod_le
  statement: (∏ i in s, f i).degree <= ∑ i in s, (f i).degree
  proof: by
  simpa only [Multiset.map_map] using! degree_multiset_prod_le (s.1.map f)

中文:
定理 degree_prod_le
  结论: (∏ i in s, f i).degree <= ∑ i in s, (f i).degree
  证明: by
  simpa only [Multiset.map_map] using! degree_multiset_prod_le (s.1.map f)

Depends on / 依赖: Multiset, Multiset.map_map, degree_multiset_prod_le, map_map
-/
theorem degree_prod_le : (∏ i in s, f i).degree <= ∑ i in s, (f i).degree := by
  simpa only [Multiset.map_map] using! degree_multiset_prod_le (s.1.map f)

/--
theorem `leadingCoeff_multiset_prod'` / 定理 `leadingCoeff_multiset_prod'`

English:
theorem leadingCoeff_multiset_prod'
  given: (h : (t.map leadingCoeff).prod != 0)
  proof: by
  induction t using Multiset.induction_on with | empty => simp | cons a t ih => ?_
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  rw [Polynomial.leadingCoeff_mul']
  · rw [ih]
    simp only [ne_eq]
    apply right_ne_zero_of_mul h
  · rw [ih]
    · exact h
    simp only [ne_eq]
    

中文:
定理 leadingCoeff_multiset_prod'
  条件: (h : (t.map leadingCoeff).乘积 != 0)
  证明: by
  induction t using Multiset.induction_on with | empty => simp | cons a t ih => ?_
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  rw [Polynomial.leadingCoeff_mul']
  · rw [ih]
    simp only [ne_eq]
    apply right_ne_zero_of_mul h
  · rw [ih]
    · exact h
    simp only [ne_eq]
    

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Polynomial, Polynomial.leadingCoeff_mul, induction_on, leadingCoeff_mul, map_cons, ne_eq, prod_cons, right_ne_zero_of_mul
-/
theorem leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).prod != 0) :
    t.prod.leadingCoeff = (t.map leadingCoeff).prod := by
  induction t using Multiset.induction_on with | empty => simp | cons a t ih => ?_
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  rw [Polynomial.leadingCoeff_mul']
  · rw [ih]
    simp only [ne_eq]
    apply right_ne_zero_of_mul h
  · rw [ih]
    · exact h
    simp only [ne_eq]
    apply right_ne_zero_of_mul h

/--
theorem `leadingCoeff_prod'` / 定理 `leadingCoeff_prod'`

English:
theorem leadingCoeff_prod'
  given: (h : (∏ i in s, (f i).leadingCoeff) != 0)
  proof: by
  simpa using leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)

中文:
定理 leadingCoeff_prod'
  条件: (h : (∏ i in s, (f i).leadingCoeff) != 0)
  证明: by
  simpa using leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)

Depends on / 依赖: leadingCoeff_multiset_prod
-/
theorem leadingCoeff_prod' (h : (∏ i in s, (f i).leadingCoeff) != 0) :
    (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)

/--
theorem `natDegree_multiset_prod'` / 定理 `natDegree_multiset_prod'`

English:
theorem natDegree_multiset_prod'
  given: (h : (t.map fun f => leadingCoeff f).prod != 0)
  proof: by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_; · simp
  rw [Multiset.map_cons]; rw [Multiset.prod_cons] at ht ⊢
  rw [Multiset.sum_cons]; rw [Polynomial.natDegree_mul']; rw [ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right

中文:
定理 natDegree_multiset_prod'
  条件: (h : (t.map fun f => leadingCoeff f).乘积 != 0)
  证明: by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_; · simp
  rw [Multiset.map_cons]; rw [Multiset.prod_cons] at ht ⊢
  rw [Multiset.sum_cons]; rw [Polynomial.natDegree_mul']; rw [ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Polynomial, Polynomial.leadingCoeff_multiset_prod, Polynomial.natDegree_mul, induction_on, leadingCoeff_multiset_prod, map_cons, natDegree_mul, prod_cons, revert, right_ne_zero_of_mul, sum_cons
-/
theorem natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).prod != 0) :
    t.prod.natDegree = (t.map fun f => natDegree f).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_; · simp
  rw [Multiset.map_cons]; rw [Multiset.prod_cons] at ht ⊢
  rw [Multiset.sum_cons]; rw [Polynomial.natDegree_mul']; rw [ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right_ne_zero_of_mul ht

/--
theorem `natDegree_prod'` / 定理 `natDegree_prod'`

English:
theorem natDegree_prod'
  given: (h : (∏ i in s, (f i).leadingCoeff) != 0)
  proof: by
  simpa using natDegree_multiset_prod' (s.1.map f) (by simpa using h)

中文:
定理 natDegree_prod'
  条件: (h : (∏ i in s, (f i).leadingCoeff) != 0)
  证明: by
  simpa using natDegree_multiset_prod' (s.1.map f) (by simpa using h)

Depends on / 依赖: natDegree_multiset_prod
-/
theorem natDegree_prod' (h : (∏ i in s, (f i).leadingCoeff) != 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod' (s.1.map f) (by simpa using h)

/--
theorem `natDegree_multiset_prod_of_monic` / 定理 `natDegree_multiset_prod_of_monic`

English:
theorem natDegree_multiset_prod_of_monic
  given: (h : forall f in t, Monic f)
  proof: by
  nontriviality R
  apply natDegree_multiset_prod'
  simp_all

中文:
定理 natDegree_multiset_prod_of_monic
  条件: (h : 对任意 f in t, Monic f)
  证明: by
  nontriviality R
  apply natDegree_multiset_prod'
  simp_all

Depends on / 依赖: natDegree_multiset_prod, nontriviality
-/
theorem natDegree_multiset_prod_of_monic (h : forall f in t, Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  nontriviality R
  apply natDegree_multiset_prod'
  simp_all

/--
theorem `degree_multiset_prod_of_monic` / 定理 `degree_multiset_prod_of_monic`

English:
theorem degree_multiset_prod_of_monic
  given: [Nontrivial R] (h : forall f in t, Monic f)
  proof: by
have : t.prod != 0 := Monic.ne_zero by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this]; rw [natDegree_multiset_prod_of_monic _ h]; rw [Nat.cast_multiset_sum]; rw [Multiset.map_map]; rw [Function.comp_def]; rw [Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree

中文:
定理 degree_multiset_prod_of_monic
  条件: [非平凡 R] (h : 对任意 f in t, Monic f)
  证明: by
have : t.prod != 0 := Monic.ne_zero by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this]; rw [natDegree_multiset_prod_of_monic _ h]; rw [Nat.cast_multiset_sum]; rw [Multiset.map_map]; rw [Function.comp_def]; rw [Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree

Depends on / 依赖: Function, Function.comp_def, Monic.ne_zero, Multiset, Multiset.map_congr, Multiset.map_map, Nat.cast_multiset_sum, cast_multiset_sum, comp_def, degree_eq_natDegree, e.symm, map_congr, map_map, monic_multiset_prod_of_monic, natDegree_multiset_prod_of_monic, ne_zero, t.prod
-/
theorem degree_multiset_prod_of_monic [Nontrivial R] (h : forall f in t, Monic f) :
    t.prod.degree = (t.map degree).sum := by
have : t.prod != 0 := Monic.ne_zero by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this]; rw [natDegree_multiset_prod_of_monic _ h]; rw [Nat.cast_multiset_sum]; rw [Multiset.map_map]; rw [Function.comp_def]; rw [Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree (h f hf).ne_zero).symm)]

/--
theorem `natDegree_prod_of_monic` / 定理 `natDegree_prod_of_monic`

English:
theorem natDegree_prod_of_monic
  given: (h : forall i in s, (f i).Monic)
  proof: by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

中文:
定理 natDegree_prod_of_monic
  条件: (h : 对任意 i in s, (f i).Monic)
  证明: by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

Depends on / 依赖: natDegree_multiset_prod_of_monic
-/
theorem natDegree_prod_of_monic (h : forall i in s, (f i).Monic) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

/--
theorem `degree_prod_of_monic` / 定理 `degree_prod_of_monic`

English:
theorem degree_prod_of_monic
  given: [Nontrivial R] (h : forall i in s, (f i).Monic)
  proof: by
  simpa using degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

中文:
定理 degree_prod_of_monic
  条件: [非平凡 R] (h : 对任意 i in s, (f i).Monic)
  证明: by
  simpa using degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

Depends on / 依赖: degree_multiset_prod_of_monic
-/
theorem degree_prod_of_monic [Nontrivial R] (h : forall i in s, (f i).Monic) :
    (∏ i in s, f i).degree = ∑ i in s, (f i).degree := by
  simpa using degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

/--
theorem `coeff_multiset_prod_of_natDegree_le` / 定理 `coeff_multiset_prod_of_natDegree_le`

English:
theorem coeff_multiset_prod_of_natDegree_le
  given: (n : Nat) (hl : forall p in t, natDegree p <= n)
  proof: by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl

中文:
定理 coeff_multiset_prod_of_natDegree_le
  条件: (n : 自然数) (hl : 对任意 p in t, natDegree p <= n)
  证明: by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl

Depends on / 依赖: Quotient, Quotient.inductionOn, coeff_list_prod_of_natDegree_le, inductionOn
-/
theorem coeff_multiset_prod_of_natDegree_le (n : Nat) (hl : forall p in t, natDegree p <= n) :
    coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).prod := by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl

/--
theorem `coeff_prod_of_natDegree_le` / 定理 `coeff_prod_of_natDegree_le`

English:
theorem coeff_prod_of_natDegree_le
  given: (f : ι -> R[X]) (n : Nat) (h : forall p in s, natDegree (f p) <= n)
  proof: by
  obtain ⟨l, hl⟩ := s
  convert! coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h

中文:
定理 coeff_prod_of_natDegree_le
  条件: (f : ι -> R[X]) (n : 自然数) (h : 对任意 p in s, natDegree (f p) <= n)
  证明: by
  obtain ⟨l, hl⟩ := s
  convert! coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h

Depends on / 依赖: coeff_multiset_prod_of_natDegree_le, convert, l.map
-/
theorem coeff_prod_of_natDegree_le (f : ι -> R[X]) (n : Nat) (h : forall p in s, natDegree (f p) <= n) :
    coeff (∏ i in s, f i) (#s * n) = ∏ i in s, coeff (f i) n := by
  obtain ⟨l, hl⟩ := s
  convert! coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h

/--
theorem `coeff_zero_multiset_prod` / 定理 `coeff_zero_multiset_prod`

English:
theorem coeff_zero_multiset_prod
  statement: t.prod.coeff 0 = (t.map fun f => coeff f 0).prod
  proof: by
  refine Multiset.induction_on t ?_ fun a t ht => ?_; · simp
  rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Polynomial.mul_coeff_zero]; rw [ht]

中文:
定理 coeff_zero_multiset_prod
  结论: t.乘积.coeff 0 = (t.map fun f => coeff f 0).乘积
  证明: by
  refine Multiset.induction_on t ?_ fun a t ht => ?_; · simp
  rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Polynomial.mul_coeff_zero]; rw [ht]

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Polynomial, Polynomial.mul_coeff_zero, induction_on, map_cons, mul_coeff_zero, prod_cons
-/
theorem coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).prod := by
  refine Multiset.induction_on t ?_ fun a t ht => ?_; · simp
  rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Polynomial.mul_coeff_zero]; rw [ht]

/--
theorem `coeff_zero_prod` / 定理 `coeff_zero_prod`

English:
theorem coeff_zero_prod
  statement: (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0
  proof: by
  simpa using coeff_zero_multiset_prod (s.1.map f)

中文:
定理 coeff_zero_prod
  结论: (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0
  证明: by
  simpa using coeff_zero_multiset_prod (s.1.map f)

Depends on / 依赖: coeff_zero_multiset_prod
-/
theorem coeff_zero_prod : (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
/--
theorem `multiset_prod_X_sub_C_nextCoeff` / 定理 `multiset_prod_X_sub_C_nextCoeff`

English:
theorem multiset_prod_X_sub_C_nextCoeff
  given: (t : Multiset R)
  proof: by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C

中文:
定理 multiset_prod_X_sub_C_nextCoeff
  条件: (t : Multiset R)
  证明: by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, intros, monic_X_sub_C, nextCoeff_X_sub_C, nextCoeff_multiset_prod, sum_hom, t.sum_hom
-/
theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).prod = -t.sum := by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C

/--
theorem `prod_X_sub_C_nextCoeff` / 定理 `prod_X_sub_C_nextCoeff`

English:
theorem prod_X_sub_C_nextCoeff
  given: {s : Finset ι} (f : ι -> R)
  proof: by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)

中文:
定理 prod_X_sub_C_nextCoeff
  条件: {s : 有限集 ι} (f : ι -> R)
  证明: by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)

Depends on / 依赖: multiset_prod_X_sub_C_nextCoeff, ofUnique
-/
theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι -> R) :
    nextCoeff (∏ i in s, (X - C (f i))) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)

/--
theorem `multiset_prod_X_sub_C_coeff_card_pred` / 定理 `multiset_prod_X_sub_C_coeff_card_pred`

English:
theorem multiset_prod_X_sub_C_coeff_card_pred
  given: (t : Multiset R) (ht : 0 < Multiset.card t)
  proof: by
  nontriviality R
  convert! multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff]; rw [if_neg]
  swap
  · rw [natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multi

中文:
定理 multiset_prod_X_sub_C_coeff_card_pred
  条件: (t : Multiset R) (ht : 0 < Multiset.card t)
  证明: by
  nontriviality R
  convert! multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff]; rw [if_neg]
  swap
  · rw [natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multi

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.sum_eq_zero_iff, card_pos_iff_exists_mem, card_pos_iff_exists_mem.mp, convert, if_neg, mem_map, monic_X_sub_C, multiset_prod_X_sub_C_nextCoeff, natDegree_X_sub_C, natDegree_multiset_prod_of_monic, nextCoeff, nontriviality, one_ne_zero, simp_rw, sum_eq_zero_iff
-/
theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  nontriviality R
  convert! multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff]; rw [if_neg]
  swap
  · rw [natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map]
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
exact fun h => one_ne_zero h 1 ⟨_, ⟨x, hx, rfl⟩, natDegree_X_sub_C _⟩
  congr; rw [natDegree_multiset_prod_of_monic] <;> · simp [monic_X_sub_C]

/--
theorem `prod_X_sub_C_coeff_card_pred` / 定理 `prod_X_sub_C_coeff_card_pred`

English:
theorem prod_X_sub_C_coeff_card_pred
  given: (s : Finset ι) (f : ι -> R) (hs : 0 < #s)
  proof: by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)

中文:
定理 prod_X_sub_C_coeff_card_pred
  条件: (s : 有限集 ι) (f : ι -> R) (hs : 0 < #s)
  证明: by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)

Depends on / 依赖: multiset_prod_X_sub_C_coeff_card_pred
-/
theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι -> R) (hs : 0 < #s) :
    (∏ i in s, (X - C (f i))).coeff (#s - 1) = -∑ i in s, f i := by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)

/--
lemma `degree_sum_eq_of_linearIndepOn` / 引理 `degree_sum_eq_of_linearIndepOn`

English:
lemma degree_sum_eq_of_linearIndepOn
  statement: {A : Type*} [CommRing A] [Algebra R A] {f : ι -> R[X]}
  proof: by
  apply le_antisymm
· exact (degree_sum_le s _).trans Finset.sup_le fun i hi => (degree_smul_le _ _).trans
degree_map_le.trans Finset.le_sup (f := fun i => (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply l

中文:
引理 degree_sum_eq_of_linearIndepOn
  结论: {A : 类型} [交换环 A] [代数 R A] {f : ι -> R[X]}
  证明: by
  apply le_antisymm
· exact (degree_sum_le s _).trans Finset.sup_le fun i hi => (degree_smul_le _ _).trans
degree_map_le.trans Finset.le_sup (f := fun i => (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply l

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.le_sup, Finset.sup_le, coeff_map, coeff_smul, degree, degree_eq_natDegree, degree_map_le, degree_map_le.trans, degree_smul_le, degree_sum_le, finsetSum_coeff, le_antisymm, le_degree_of_ne_zero, le_sup, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, linearIndepOn_finset_i
-/
lemma degree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι -> R[X]}
    {v : ι -> A} (h : LinearIndepOn R v s) :
    (∑ i in s, v i • (f i).map (algebraMap R A)).degree = s.sup (fun i => (f i).degree) := by
  apply le_antisymm
· exact (degree_sum_le s _).trans Finset.sup_le fun i hi => (degree_smul_le _ _).trans
degree_map_le.trans Finset.le_sup (f := fun i => (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply le_degree_of_ne_zero
    rw [finsetSum_coeff]
    conv in (fun _ => _) =>
      ext
      rw [coeff_smul]; rw [smul_eq_mul]; rw [coeff_map]; rw [mul_comm]; rw [← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

-- Note: Proof duplicated from the `degree` version, since the statements don't
-- trivially follow from each other.
/--
lemma `natDegree_sum_eq_of_linearIndepOn` / 引理 `natDegree_sum_eq_of_linearIndepOn`

English:
lemma natDegree_sum_eq_of_linearIndepOn
  statement: {A : Type*} [CommRing A] [Algebra R A] {f : ι -> R[X]}
  proof: by
  apply le_antisymm
· exact natDegree_sum_le_of_forall_le _ _ fun i hi => (natDegree_smul_le _ _).trans
natDegree_map_le.trans Finset.le_sup (f := fun i => (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw

中文:
引理 natDegree_sum_eq_of_linearIndepOn
  结论: {A : 类型} [交换环 A] [代数 R A] {f : ι -> R[X]}
  证明: by
  apply le_antisymm
· exact natDegree_sum_le_of_forall_le _ _ fun i hi => (natDegree_smul_le _ _).trans
natDegree_map_le.trans Finset.le_sup (f := fun i => (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.le_sup, Finset.sup_le, coeff_map, coeff_smul, finsetSum_coeff, le_antisymm, le_natDegree_of_ne_zero, le_sup, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, linearIndepOn_finset_iff, linearIndepOn_finset_iff.mp, mul_comm, natDegree, natDegree_map_le, natDegree_map_le.trans, natDegree_smul_le
-/
lemma natDegree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι -> R[X]}
    {v : ι -> A} (h : LinearIndepOn R v s) :
    (∑ i in s, v i • (f i).map (algebraMap R A)).natDegree = s.sup (fun i => (f i).natDegree) := by
  apply le_antisymm
· exact natDegree_sum_le_of_forall_le _ _ fun i hi => (natDegree_smul_le _ _).trans
natDegree_map_le.trans Finset.le_sup (f := fun i => (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw [finsetSum_coeff]
    conv in (fun _ => _) =>
      ext
      rw [coeff_smul]; rw [smul_eq_mul]; rw [coeff_map]; rw [mul_comm]; rw [← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

variable [Nontrivial R]

@[simp]
/--
lemma `natDegree_multiset_prod_X_sub_C_eq_card` / 引理 `natDegree_multiset_prod_X_sub_C_eq_card`

English:
lemma natDegree_multiset_prod_X_sub_C_eq_card
  given: (s : Multiset R)
  proof: by
  rw [natDegree_multiset_prod_of_monic]; rw [Multiset.map_map]
  · simp
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a

中文:
引理 natDegree_multiset_prod_X_sub_C_eq_card
  条件: (s : Multiset R)
  证明: by
  rw [natDegree_multiset_prod_of_monic]; rw [Multiset.map_map]
  · simp
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a

Depends on / 依赖: Multiset, Multiset.forall_mem_map_iff, Multiset.map_map, forall_mem_map_iff, map_map, monic_X_sub_C, natDegree_multiset_prod_of_monic
-/
lemma natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map (X - C ·)).prod.natDegree = Multiset.card s := by
  rw [natDegree_multiset_prod_of_monic]; rw [Multiset.map_map]
  · simp
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a

/--
lemma `natDegree_finsetProd_X_sub_C_eq_card` / 引理 `natDegree_finsetProd_X_sub_C_eq_card`

English:
lemma natDegree_finsetProd_X_sub_C_eq_card
  given: {α} (s : Finset α) (f : α -> R)
  proof: by
  rw [Finset.prod]; rw [← (X - C ·).comp_def f]; rw [← Multiset.map_map]; rw [natDegree_multiset_prod_X_sub_C_eq_card]; rw [Multiset.card_map]; rw [Finset.card]

@[deprecated (since := "2026-04-08")]
alias natDegree_finset_prod_X_sub_C_eq_card := natDegree_finsetProd_X_sub_C_eq_card

中文:
引理 natDegree_finsetProd_X_sub_C_eq_card
  条件: {α} (s : 有限集 α) (f : α -> R)
  证明: by
  rw [Finset.prod]; rw [← (X - C ·).comp_def f]; rw [← Multiset.map_map]; rw [natDegree_multiset_prod_X_sub_C_eq_card]; rw [Multiset.card_map]; rw [Finset.card]

@[deprecated (since := "2026-04-08")]
alias natDegree_finset_prod_X_sub_C_eq_card := natDegree_finsetProd_X_sub_C_eq_card
-/
@[simp] lemma natDegree_finsetProd_X_sub_C_eq_card {α} (s : Finset α) (f : α -> R) :
    (∏ a in s, (X - C (f a))).natDegree = s.card := by
  rw [Finset.prod]; rw [← (X - C ·).comp_def f]; rw [← Multiset.map_map]; rw [natDegree_multiset_prod_X_sub_C_eq_card]; rw [Multiset.card_map]; rw [Finset.card]

@[deprecated (since := "2026-04-08")]
alias natDegree_finset_prod_X_sub_C_eq_card := natDegree_finsetProd_X_sub_C_eq_card

end CommRing

section NoZeroDivisors

section Semiring

variable [Semiring R] [NoZeroDivisors R]

/--
theorem `degree_list_prod` / 定理 `degree_list_prod`

English:
theorem degree_list_prod
  given: [Nontrivial R] (l : List R[X])
  statement: l.prod.degree = (l.map degree).sum
  proof: map_list_prod (@degreeMonoidHom R _ _ _) l

中文:
定理 degree_list_prod
  条件: [非平凡 R] (l : 列表 R[X])
  结论: l.乘积.degree = (l.map degree).求和
  证明: map_list_prod (@degreeMonoidHom R _ _ _) l

Depends on / 依赖: degreeMonoidHom, map_list_prod
-/
theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map degree).sum :=
  map_list_prod (@degreeMonoidHom R _ _ _) l

end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] (f : ι -> R[X]) (t : Multiset R[X])

/--
theorem `natDegree_prod` / 定理 `natDegree_prod`

English:
theorem natDegree_prod
  given: (h : forall i in s, f i != 0)
  proof: by
  nontriviality R
  apply natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]

中文:
定理 natDegree_prod
  条件: (h : 对任意 i in s, f i != 0)
  证明: by
  nontriviality R
  apply natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]

Depends on / 依赖: natDegree_prod, nontriviality, prod_ne_zero_iff
-/
theorem natDegree_prod (h : forall i in s, f i != 0) :
    (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree := by
  nontriviality R
  apply natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]

/--
theorem `natDegree_multiset_prod` / 定理 `natDegree_multiset_prod`

English:
theorem natDegree_multiset_prod
  given: (h : (0 : R[X]) ∉ t)
  proof: by
  nontriviality R
  rw [natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

中文:
定理 natDegree_multiset_prod
  条件: (h : (0 : R[X]) ∉ t)
  证明: by
  nontriviality R
  rw [natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.prod_eq_zero_iff, leadingCoeff_eq_zero, mem_map, natDegree_multiset_prod, nontriviality, prod_eq_zero_iff, simp_rw
-/
theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
  rw [natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

/--
theorem `degree_multiset_prod` / 定理 `degree_multiset_prod`

English:
theorem degree_multiset_prod
  given: [Nontrivial R]
  statement: t.prod.degree = (t.map fun f => degree f).sum
  proof: map_multiset_prod (@degreeMonoidHom R _ _ _) _

中文:
定理 degree_multiset_prod
  条件: [非平凡 R]
  结论: t.乘积.degree = (t.map fun f => degree f).求和
  证明: map_multiset_prod (@degreeMonoidHom R _ _ _) _

Depends on / 依赖: degreeMonoidHom, map_multiset_prod
-/
theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).sum :=
  map_multiset_prod (@degreeMonoidHom R _ _ _) _

/--
theorem `degree_prod` / 定理 `degree_prod`

English:
theorem degree_prod
  given: [Nontrivial R]
  statement: (∏ i in s, f i).degree = ∑ i in s, (f i).degree
  proof: map_prod (@degreeMonoidHom R _ _ _) _ _

中文:
定理 degree_prod
  条件: [非平凡 R]
  结论: (∏ i in s, f i).degree = ∑ i in s, (f i).degree
  证明: map_prod (@degreeMonoidHom R _ _ _) _ _

Depends on / 依赖: degreeMonoidHom, map_prod
-/
theorem degree_prod [Nontrivial R] : (∏ i in s, f i).degree = ∑ i in s, (f i).degree :=
  map_prod (@degreeMonoidHom R _ _ _) _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `leadingCoeff_multiset_prod` / 定理 `leadingCoeff_multiset_prod`

English:
theorem leadingCoeff_multiset_prod
  proof: by
  rw [← leadingCoeffHom_apply]; rw [MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

中文:
定理 leadingCoeff_multiset_prod
  证明: by
  rw [← leadingCoeffHom_apply]; rw [MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

Depends on / 依赖: MonoidHom, MonoidHom.map_multiset_prod, leadingCoeffHom_apply, map_multiset_prod
-/
theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  rw [← leadingCoeffHom_apply]; rw [MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

/--
theorem `leadingCoeff_prod` / 定理 `leadingCoeff_prod`

English:
theorem leadingCoeff_prod
  statement: (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff
  proof: by
  simpa using leadingCoeff_multiset_prod (s.1.map f)

中文:
定理 leadingCoeff_prod
  结论: (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff
  证明: by
  simpa using leadingCoeff_multiset_prod (s.1.map f)

Depends on / 依赖: leadingCoeff_multiset_prod
-/
theorem leadingCoeff_prod : (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod (s.1.map f)

end CommSemiring

end NoZeroDivisors

end Polynomial
