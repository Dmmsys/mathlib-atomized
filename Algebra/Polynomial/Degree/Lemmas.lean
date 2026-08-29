/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Prime.Lemmas

/-!
# Theory of degrees of polynomials

Some of the main results include
- `natDegree_comp_le` : The degree of the composition is at most the product of degrees

-/

public section


noncomputable section

open Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

/--
theorem `natDegree_comp_le` / 定理 `natDegree_comp_le`

English:
theorem natDegree_comp_le
  statement: natDegree (p.comp q) <= natDegree p * natDegree q
  proof: letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
WithBot.coe_le_coe.1
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ <= _ := degre

中文:
定理 natDegree_comp_le
  结论: natDegree (p.comp q) <= natDegree p * natDegree q
  证明: letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
WithBot.coe_le_coe.1
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ <= _ := degre

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.sup_le, Nat.zero_le, WithBot, WithBot.coe_le_coe, add_le_add, coe_le_coe, comp_eq_sum_left, congr_arg, degree, degree_eq_natDegree, degree_le_natDegree, degree_mul_le, degree_sum_le, natDegree, natDegree_zero, p.comp, sup_le
-/
theorem natDegree_comp_le : natDegree (p.comp q) <= natDegree p * natDegree q :=
  letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
WithBot.coe_le_coe.1
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ <= _ := degree_sum_le _ _
        _ <= _ :=
          Finset.sup_le fun n hn =>
            calc
              degree (C (coeff p n) * q ^ n) <= degree (C (coeff p n)) + degree (q ^ n) :=
                degree_mul_le _ _
              _ <= natDegree (C (coeff p n)) + n • degree q :=
                (add_le_add degree_le_natDegree (degree_pow_le _ _))
              _ <= natDegree (C (coeff p n)) + n • ↑(natDegree q) := by grw [degree_le_natDegree]
              _ = (n * natDegree q : Nat) := by
                rw [natDegree_C]; rw [Nat.cast_zero]; rw [zero_add]; rw [nsmul_eq_mul]
                simp
              _ <= (natDegree p * natDegree q : Nat) :=
WithBot.coe_le_coe.2
                  by gcongr; exact le_natDegree_of_ne_zero (mem_support_iff.1 hn)

/--
theorem `natDegree_comp_eq_of_mul_ne_zero` / 定理 `natDegree_comp_eq_of_mul_ne_zero`

English:
theorem natDegree_comp_eq_of_mul_ne_zero
  given: (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0)
  proof: by
  by_cases hq : natDegree q = 0
  · exact le_antisymm natDegree_comp_le (by simp [hq])
  apply natDegree_eq_of_le_of_coeff_ne_zero natDegree_comp_le
  rwa [coeff_comp_degree_mul_degree hq]

中文:
定理 natDegree_comp_eq_of_mul_ne_zero
  条件: (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0)
  证明: by
  by_cases hq : natDegree q = 0
  · exact le_antisymm natDegree_comp_le (by simp [hq])
  apply natDegree_eq_of_le_of_coeff_ne_zero natDegree_comp_le
  rwa [coeff_comp_degree_mul_degree hq]

Depends on / 依赖: coeff_comp_degree_mul_degree, le_antisymm, natDegree, natDegree_comp_le, natDegree_eq_of_le_of_coeff_ne_zero
-/
theorem natDegree_comp_eq_of_mul_ne_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0) :
    natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases hq : natDegree q = 0
  · exact le_antisymm natDegree_comp_le (by simp [hq])
  apply natDegree_eq_of_le_of_coeff_ne_zero natDegree_comp_le
  rwa [coeff_comp_degree_mul_degree hq]

/--
theorem `degree_pos_of_root` / 定理 `degree_pos_of_root`

English:
theorem degree_pos_of_root
  given: {p : R[X]} (hp : p != 0) (h : IsRoot p a)
  statement: 0 < degree p
  proof: lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot]; rw [this]; rw [eval_C] at h
    simp only [h, map_zero] at this
    exact hp this

中文:
定理 degree_pos_of_root
  条件: {p : R[X]} (hp : p != 0) (h : IsRoot p a)
  结论: 0 < degree p
  证明: lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot]; rw [this]; rw [eval_C] at h
    simp only [h, map_zero] at this
    exact hp this

Depends on / 依赖: IsRoot, eq_C_of_degree_le_zero, eval_C, lt_of_not_ge, map_zero
-/
theorem degree_pos_of_root {p : R[X]} (hp : p != 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot]; rw [this]; rw [eval_C] at h
    simp only [h, map_zero] at this
    exact hp this

/--
theorem `natDegree_le_iff_coeff_eq_zero` / 定理 `natDegree_le_iff_coeff_eq_zero`

English:
theorem natDegree_le_iff_coeff_eq_zero
  statement: p.natDegree <= n ↔ forall N : Nat, n < N -> p.coeff N = 0
  proof: by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]

中文:
定理 natDegree_le_iff_coeff_eq_zero
  结论: p.natDegree <= n ↔ 对任意 N : 自然数, n < N -> p.coeff N = 0
  证明: by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]

Depends on / 依赖: Nat.cast_lt, cast_lt, degree_le_iff_coeff_zero, natDegree_le_iff_degree_le, simp_rw
-/
theorem natDegree_le_iff_coeff_eq_zero : p.natDegree <= n ↔ forall N : Nat, n < N -> p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]

/--
theorem `natDegree_add_le_iff_left` / 定理 `natDegree_add_le_iff_left`

English:
theorem natDegree_add_le_iff_left
  given: {n : Nat} (p q : R[X]) (qn : q.natDegree <= n)
  proof: by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert! natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add]; rw [natDegree_le_iff_coeff_eq_zero.mp qn _ hm]; rw [add_zero]

中文:
定理 natDegree_add_le_iff_left
  条件: {n : 自然数} (p q : R[X]) (qn : q.natDegree <= n)
  证明: by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert! natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add]; rw [natDegree_le_iff_coeff_eq_zero.mp qn _ hm]; rw [add_zero]

Depends on / 依赖: add_zero, coeff_add, convert, natDegree_add_le_of_degree_le, natDegree_le_iff_coeff_eq_zero, natDegree_le_iff_coeff_eq_zero.mp, natDegree_le_iff_coeff_eq_zero.mpr
-/
theorem natDegree_add_le_iff_left {n : Nat} (p q : R[X]) (qn : q.natDegree <= n) :
    (p + q).natDegree <= n ↔ p.natDegree <= n := by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert! natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add]; rw [natDegree_le_iff_coeff_eq_zero.mp qn _ hm]; rw [add_zero]

/--
theorem `natDegree_add_le_iff_right` / 定理 `natDegree_add_le_iff_right`

English:
theorem natDegree_add_le_iff_right
  given: {n : Nat} (p q : R[X]) (pn : p.natDegree <= n)
  proof: by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn

中文:
定理 natDegree_add_le_iff_right
  条件: {n : 自然数} (p q : R[X]) (pn : p.natDegree <= n)
  证明: by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn

Depends on / 依赖: add_comm, natDegree_add_le_iff_left
-/
theorem natDegree_add_le_iff_right {n : Nat} (p q : R[X]) (pn : p.natDegree <= n) :
    (p + q).natDegree <= n ↔ q.natDegree <= n := by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn

-- TODO: Do we really want the following two lemmas? They are straightforward consequences of a
-- more atomic lemma
/--
theorem `natDegree_C_mul_le` / 定理 `natDegree_C_mul_le`

English:
theorem natDegree_C_mul_le
  given: (a : R) (f : R[X])
  statement: (C a * f).natDegree <= f.natDegree
  proof: by
  simpa using natDegree_mul_le (p := C a)

中文:
定理 natDegree_C_mul_le
  条件: (a : R) (f : R[X])
  结论: (C a * f).natDegree <= f.natDegree
  证明: by
  simpa using natDegree_mul_le (p := C a)

Depends on / 依赖: natDegree_mul_le
-/
theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree <= f.natDegree := by
  simpa using natDegree_mul_le (p := C a)

/--
theorem `natDegree_mul_C_le` / 定理 `natDegree_mul_C_le`

English:
theorem natDegree_mul_C_le
  given: (f : R[X]) (a : R)
  statement: (f * C a).natDegree <= f.natDegree
  proof: by
  simpa using natDegree_mul_le (q := C a)

中文:
定理 natDegree_mul_C_le
  条件: (f : R[X]) (a : R)
  结论: (f * C a).natDegree <= f.natDegree
  证明: by
  simpa using natDegree_mul_le (q := C a)

Depends on / 依赖: natDegree_mul_le
-/
theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree <= f.natDegree := by
  simpa using natDegree_mul_le (q := C a)

/--
theorem `eq_natDegree_of_le_mem_support` / 定理 `eq_natDegree_of_le_mem_support`

English:
theorem eq_natDegree_of_le_mem_support
  given: (pn : p.natDegree <= n) (ns : n in p.support)
  proof: le_antisymm pn (le_natDegree_of_mem_supp _ ns)

中文:
定理 eq_natDegree_of_le_mem_support
  条件: (pn : p.natDegree <= n) (ns : n in p.support)
  证明: le_antisymm pn (le_natDegree_of_mem_supp _ ns)

Depends on / 依赖: le_antisymm, le_natDegree_of_mem_supp
-/
theorem eq_natDegree_of_le_mem_support (pn : p.natDegree <= n) (ns : n in p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)

/--
theorem `natDegree_C_mul_eq_of_mul_eq_one` / 定理 `natDegree_C_mul_eq_of_mul_eq_one`

English:
theorem natDegree_C_mul_eq_of_mul_eq_one
  given: {ai : R} (au : ai * a = 1)
  proof: le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))

中文:
定理 natDegree_C_mul_eq_of_mul_eq_one
  条件: {ai : R} (au : ai * a = 1)
  证明: le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))

Depends on / 依赖: le_antisymm, map_mul, mul_assoc, natDegree, natDegree_C_mul_le, nth_rw, one_mul, p.natDegree
-/
theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))

/--
theorem `natDegree_mul_C_eq_of_mul_eq_one` / 定理 `natDegree_mul_C_eq_of_mul_eq_one`

English:
theorem natDegree_mul_C_eq_of_mul_eq_one
  given: {ai : R} (au : a * ai = 1)
  proof: le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

中文:
定理 natDegree_mul_C_eq_of_mul_eq_one
  条件: {ai : R} (au : a * ai = 1)
  证明: le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

Depends on / 依赖: le_antisymm, map_mul, mul_assoc, mul_one, natDegree, natDegree_mul_C_le, nth_rw, p.natDegree
-/
theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ <= (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

/--
theorem `natDegree_mul_C_eq_of_mul_ne_zero` / 定理 `natDegree_mul_C_eq_of_mul_ne_zero`

English:
theorem natDegree_mul_C_eq_of_mul_ne_zero
  given: (h : p.leadingCoeff * a != 0)
  proof: by
  refine eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_mul_C]

中文:
定理 natDegree_mul_C_eq_of_mul_ne_zero
  条件: (h : p.leadingCoeff * a != 0)
  证明: by
  refine eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_mul_C]

Depends on / 依赖: coeff_mul_C, eq_natDegree_of_le_mem_support, mem_support_iff, mem_support_iff.mpr, natDegree_mul_C_le
-/
theorem natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a != 0) :
    (p * C a).natDegree = p.natDegree := by
  refine eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_mul_C]

/--
theorem `natDegree_C_mul_of_mul_ne_zero` / 定理 `natDegree_C_mul_of_mul_ne_zero`

English:
theorem natDegree_C_mul_of_mul_ne_zero
  given: (h : a * p.leadingCoeff != 0)
  proof: by
  refine eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_C_mul]

中文:
定理 natDegree_C_mul_of_mul_ne_zero
  条件: (h : a * p.leadingCoeff != 0)
  证明: by
  refine eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_C_mul]

Depends on / 依赖: coeff_C_mul, eq_natDegree_of_le_mem_support, mem_support_iff, mem_support_iff.mpr, natDegree_C_mul_le
-/
theorem natDegree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff != 0) :
    (C a * p).natDegree = p.natDegree := by
  refine eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_C_mul]

/--
lemma `degree_C_mul_of_mul_ne_zero` / 引理 `degree_C_mul_of_mul_ne_zero`

English:
lemma degree_C_mul_of_mul_ne_zero
  given: (h : a * p.leadingCoeff != 0)
  statement: (C a * p).degree = p.degree
  proof: by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]

中文:
引理 degree_C_mul_of_mul_ne_zero
  条件: (h : a * p.leadingCoeff != 0)
  结论: (C a * p).degree = p.degree
  证明: by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]

Depends on / 依赖: degree_mul, left_ne_zero_of_mul
-/
lemma degree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff != 0) : (C a * p).degree = p.degree := by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]

/--
theorem `natDegree_add_coeff_mul` / 定理 `natDegree_add_coeff_mul`

English:
theorem natDegree_add_coeff_mul
  given: (f g : R[X])
  proof: by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]

中文:
定理 natDegree_add_coeff_mul
  条件: (f g : R[X])
  证明: by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]

Depends on / 依赖: coeff_mul_degree_add_degree, coeff_natDegree
-/
theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]

/--
theorem `natDegree_lt_coeff_mul` / 定理 `natDegree_lt_coeff_mul`

English:
theorem natDegree_lt_coeff_mul
  given: (h : p.natDegree + q.natDegree < m + n)
  proof: coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)

中文:
定理 natDegree_lt_coeff_mul
  条件: (h : p.natDegree + q.natDegree < m + n)
  证明: coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, natDegree_mul_le, natDegree_mul_le.trans_lt, trans_lt
-/
theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)

/--
theorem `coeff_pow_of_natDegree_le` / 定理 `coeff_pow_of_natDegree_le`

English:
theorem coeff_pow_of_natDegree_le
  given: (pn : p.natDegree <= n)
  proof: by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ]; rw [pow_succ]; rw [← hm]; rw [Nat.succ_mul]; rw [coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    gcongr

中文:
定理 coeff_pow_of_natDegree_le
  条件: (pn : p.natDegree <= n)
  证明: by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ]; rw [pow_succ]; rw [← hm]; rw [Nat.succ_mul]; rw [coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    gcongr

Depends on / 依赖: Nat.succ_mul, coeff_mul_add_eq_of_natDegree_le, le_refl, le_trans, natDegree_pow_le, natDegree_pow_le.trans, pow_succ, succ_mul
-/
theorem coeff_pow_of_natDegree_le (pn : p.natDegree <= n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ]; rw [pow_succ]; rw [← hm]; rw [Nat.succ_mul]; rw [coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    gcongr

/--
theorem `coeff_pow_eq_ite_of_natDegree_le_of_le` / 定理 `coeff_pow_eq_ite_of_natDegree_le_of_le`

English:
theorem coeff_pow_eq_ite_of_natDegree_le_of_le
  statement: {o : Nat}
  proof: by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
· simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

中文:
定理 coeff_pow_eq_ite_of_natDegree_le_of_le
  结论: {o : 自然数}
  证明: by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
· simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, coeff_pow_of_natDegree_le, eq_or_ne, h.symm, ite_false, ite_true, lt_of_le_of_lt, lt_of_le_of_ne, natDegree_pow_le_of_le
-/
theorem coeff_pow_eq_ite_of_natDegree_le_of_le {o : Nat}
    (pn : natDegree p <= n) (mno : m * n <= o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
· simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

/--
theorem `coeff_add_eq_left_of_lt` / 定理 `coeff_add_eq_left_of_lt`

English:
theorem coeff_add_eq_left_of_lt
  given: (qn : q.natDegree < n)
  statement: (p + q).coeff n = p.coeff n
  proof: (coeff_add _ _ _).trans
(congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans add_zero _

中文:
定理 coeff_add_eq_left_of_lt
  条件: (qn : q.natDegree < n)
  结论: (p + q).coeff n = p.coeff n
  证明: (coeff_add _ _ _).trans
(congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans add_zero _

Depends on / 依赖: add_zero, coeff_add, coeff_eq_zero_of_natDegree_lt, congr_arg
-/
theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
(coeff_add _ _ _).trans
(congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans add_zero _

/--
theorem `coeff_add_eq_right_of_lt` / 定理 `coeff_add_eq_right_of_lt`

English:
theorem coeff_add_eq_right_of_lt
  given: (pn : p.natDegree < n)
  statement: (p + q).coeff n = q.coeff n
  proof: by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn

中文:
定理 coeff_add_eq_right_of_lt
  条件: (pn : p.natDegree < n)
  结论: (p + q).coeff n = q.coeff n
  证明: by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn

Depends on / 依赖: add_comm, coeff_add_eq_left_of_lt
-/
theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn

open scoped Function -- required for scoped `on` notation

/--
theorem `degree_sum_eq_of_disjoint` / 定理 `degree_sum_eq_of_disjoint`

English:
theorem degree_sum_eq_of_disjoint
  statement: (f : S -> R[X]) (s : Finset S)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx IH =>
    simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize IH (h.mono fun _ => by simp +contextual)
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H

中文:
定理 degree_sum_eq_of_disjoint
  结论: (f : S -> R[X]) (s : Finset S)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx IH =>
    simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize IH (h.mono fun _ => by simp +contextual)
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, Finset.induction_on, Finset.sum_insert, Finset.sup_insert, H.le, classical, contextual, degree, degree_add_eq_right_of_degree_lt, eq_empty_or_nonempty, exists_mem_eq_sup, h.mono, induction_on, insert, lt_trichotomy, not_false_iff, s.eq_empty_or_nonempty, s.sum, specialize
-/
theorem degree_sum_eq_of_disjoint (f : S -> R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on degree ∘ f)) :
    degree (s.sum f) = s.sup fun i => degree (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx IH =>
    simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize IH (h.mono fun _ => by simp +contextual)
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simp
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      rw [IH]; rw [hy'] at H
      by_cases hx0 : f x = 0
      · simp [hx0, IH]
      have hy0 : f y != 0 := by
        contrapose! H
        simpa [H, degree_eq_bot] using hx0
      refine absurd H (h ?_ ?_ fun H => hx ?_)
      · simp [hx0]
      · simp [hy, hy0]
      · exact H.symm ▸ hy
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]

/--
theorem `natDegree_sum_eq_of_disjoint` / 定理 `natDegree_sum_eq_of_disjoint`

English:
theorem natDegree_sum_eq_of_disjoint
  statement: (f : S -> R[X]) (s : Finset S)
  proof: by
  by_cases! H : exists x in s, f x != 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
    

中文:
定理 natDegree_sum_eq_of_disjoint
  结论: (f : S -> R[X]) (s : Finset S)
  证明: by
  by_cases! H : exists x in s, f x != 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
    

Depends on / 依赖: Finset, Finset.coe_sup, Finset.le_sup, Finset.sup, Nat.cast_withBot, Nonempty, _eq_sup, _le_iff, cast_withBot, coe_sup, degree_eq_natDegree, degree_sum_eq_of_disjoint, le_antisymm, le_sup, natDegree, natDegree_eq_of_degree_eq_some, s.Nonempty
-/
theorem natDegree_sum_eq_of_disjoint (f : S -> R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on natDegree ∘ f)) :
    natDegree (s.sum f) = s.sup fun i => natDegree (f i) := by
  by_cases! H : exists x in s, f x != 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
        Finset.sup'_eq_sup hs]
      refine le_antisymm ?_ ?_
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases hb' : f b = 0
        · simpa [hb'] using! hs
        rw [degree_eq_natDegree hb']; rw [Nat.cast_withBot]
        exact Finset.le_sup' (fun i : S => (natDegree (f i) : WithBot Nat)) hb
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, Function.comp_apply]
        by_cases hb' : f b = 0
        · refine ⟨x, hx, ?_⟩
          contrapose! hx'
          simpa [← Nat.cast_withBot, hb', degree_eq_bot] using! hx'
        exact ⟨b, hb, (degree_eq_natDegree hb').ge⟩
    · exact h.imp fun x y hxy hxy' => hxy (natDegree_eq_of_degree_eq hxy')
  · rw [Finset.sum_eq_zero H, natDegree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]

variable [Semiring S]

/--
theorem `natDegree_pos_of_eval₂_root` / 定理 `natDegree_pos_of_eval₂_root`

English:
theorem natDegree_pos_of_eval₂_root
  statement: {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
  proof: lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A]; rw [eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, map_zero] at A
    exact hp A

中文:
定理 natDegree_pos_of_eval₂_root
  结论: {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
  证明: lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A]; rw [eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, map_zero] at A
    exact hp A

Depends on / 依赖: eq_C_of_natDegree_le_zero, lt_of_not_ge, map_zero, p.coeff
-/
theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : forall x : R, f x = 0 -> x = 0) : 0 < natDegree p :=
  lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A]; rw [eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, map_zero] at A
    exact hp A

/--
theorem `degree_pos_of_eval₂_root` / 定理 `degree_pos_of_eval₂_root`

English:
theorem degree_pos_of_eval₂_root
  statement: {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
  proof: natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)

@[simp]

中文:
定理 degree_pos_of_eval₂_root
  结论: {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
  证明: natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)

@[simp]

Depends on / 依赖: natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mp
-/
theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p != 0) (f : R ->+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : forall x : R, f x = 0 -> x = 0) : 0 < degree p :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)

@[simp]
/--
theorem `coe_lt_degree` / 定理 `coe_lt_degree`

English:
theorem coe_lt_degree
  given: {p : R[X]} {n : Nat}
  statement: (n : WithBot Nat) < degree p ↔ n < natDegree p
  proof: by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

@[simp]

中文:
定理 coe_lt_degree
  条件: {p : R[X]} {n : 自然数}
  结论: (n : WithBot 自然数) < degree p ↔ n < natDegree p
  证明: by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

@[simp]

Depends on / 依赖: Nat.cast_lt, cast_lt, degree_eq_natDegree
-/
theorem coe_lt_degree {p : R[X]} {n : Nat} : (n : WithBot Nat) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

@[simp]
/--
theorem `degree_map_eq_iff` / 定理 `degree_map_eq_iff`

English:
theorem degree_map_eq_iff
  given: {f : R ->+* S} {p : Polynomial R}
  proof: by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 => ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p != 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
 

中文:
定理 degree_map_eq_iff
  条件: {f : R ->+* S} {p : Polynomial R}
  证明: by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 => ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p != 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
 

Depends on / 依赖: coeff_map, coeff_natDegree, degree_eq_bot, degree_map_eq_of_leadingCoeff_ne_zero, eq_or_ne, leadingCoeff_eq_zero, natDegree, ne_eq, or_false, simp_rw
-/
theorem degree_map_eq_iff {f : R ->+* S} {p : Polynomial R} :
    degree (map f p) = degree p ↔ f (leadingCoeff p) != 0 ∨ p = 0 := by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 => ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p != 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
  rwa [← coeff_natDegree, ← coeff_map, ← h3, coeff_natDegree, ne_eq, leadingCoeff_eq_zero]

@[simp]
/--
theorem `natDegree_map_eq_iff` / 定理 `natDegree_map_eq_iff`

English:
theorem natDegree_map_eq_iff
  given: {f : R ->+* S} {p : Polynomial R}
  proof: by
  rcases eq_or_ne (natDegree p) 0 with h | h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le]
  simp_all [natDegree, WithBot.unbotD_eq_unbotD_iff]

中文:
定理 natDegree_map_eq_iff
  条件: {f : R ->+* S} {p : Polynomial R}
  证明: by
  rcases eq_or_ne (natDegree p) 0 with h | h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le]
  simp_all [natDegree, WithBot.unbotD_eq_unbotD_iff]

Depends on / 依赖: Nat.le_zero, WithBot, WithBot.unbotD_eq_unbotD_iff, eq_or_ne, iff_true, le_zero, natDegree, natDegree_map_le, ne_eq, or_true, simp_rw, unbotD_eq_unbotD_iff
-/
theorem natDegree_map_eq_iff {f : R ->+* S} {p : Polynomial R} :
    natDegree (map f p) = natDegree p ↔ f (p.leadingCoeff) != 0 ∨ natDegree p = 0 := by
  rcases eq_or_ne (natDegree p) 0 with h | h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le]
  simp_all [natDegree, WithBot.unbotD_eq_unbotD_iff]

/--
theorem `degree_map_eq_of_isUnit_leadingCoeff` / 定理 `degree_map_eq_of_isUnit_leadingCoeff`

English:
theorem degree_map_eq_of_isUnit_leadingCoeff
  statement: [Nontrivial S] (f : R ->+* S)
  proof: degree_map_eq_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

中文:
定理 degree_map_eq_of_isUnit_leadingCoeff
  结论: [Nontrivial S] (f : R ->+* S)
  证明: degree_map_eq_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

Depends on / 依赖: degree_map_eq_of_leadingCoeff_ne_zero, f.isUnit_map, isUnit_map, ne_zero
-/
theorem degree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).degree = p.degree :=
degree_map_eq_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

/--
theorem `natDegree_map_eq_of_isUnit_leadingCoeff` / 定理 `natDegree_map_eq_of_isUnit_leadingCoeff`

English:
theorem natDegree_map_eq_of_isUnit_leadingCoeff
  statement: [Nontrivial S] (f : R ->+* S)
  proof: natDegree_eq_natDegree degree_map_eq_of_isUnit_leadingCoeff _ hp

中文:
定理 natDegree_map_eq_of_isUnit_leadingCoeff
  结论: [Nontrivial S] (f : R ->+* S)
  证明: natDegree_eq_natDegree degree_map_eq_of_isUnit_leadingCoeff _ hp

Depends on / 依赖: degree_map_eq_of_isUnit_leadingCoeff, natDegree_eq_natDegree
-/
theorem natDegree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).natDegree = p.natDegree :=
natDegree_eq_natDegree degree_map_eq_of_isUnit_leadingCoeff _ hp

/--
theorem `leadingCoeff_map_eq_of_isUnit_leadingCoeff` / 定理 `leadingCoeff_map_eq_of_isUnit_leadingCoeff`

English:
theorem leadingCoeff_map_eq_of_isUnit_leadingCoeff
  statement: [Nontrivial S] (f : R ->+* S)
  proof: leadingCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

中文:
定理 leadingCoeff_map_eq_of_isUnit_leadingCoeff
  结论: [Nontrivial S] (f : R ->+* S)
  证明: leadingCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

Depends on / 依赖: f.isUnit_map, isUnit_map, leadingCoeff_map_of_leadingCoeff_ne_zero, ne_zero
-/
theorem leadingCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).leadingCoeff = f p.leadingCoeff :=
leadingCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

/--
theorem `nextCoeff_map_eq_of_isUnit_leadingCoeff` / 定理 `nextCoeff_map_eq_of_isUnit_leadingCoeff`

English:
theorem nextCoeff_map_eq_of_isUnit_leadingCoeff
  statement: [Nontrivial S] (f : R ->+* S)
  proof: nextCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

中文:
定理 nextCoeff_map_eq_of_isUnit_leadingCoeff
  结论: [Nontrivial S] (f : R ->+* S)
  证明: nextCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

Depends on / 依赖: f.isUnit_map, isUnit_map, ne_zero, nextCoeff_map_of_leadingCoeff_ne_zero
-/
theorem nextCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).nextCoeff = f p.nextCoeff :=
nextCoeff_map_of_leadingCoeff_ne_zero _ .ne_zero f.isUnit_map hp

/--
theorem `degree_map_eq_of_injective` / 定理 `degree_map_eq_of_injective`

English:
theorem degree_map_eq_of_injective
  given: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  proof: by
  simp [hf, map_ne_zero_iff, ne_or_eq]

中文:
定理 degree_map_eq_of_injective
  条件: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  证明: by
  simp [hf, map_ne_zero_iff, ne_or_eq]

Depends on / 依赖: map_ne_zero_iff, ne_or_eq
-/
theorem degree_map_eq_of_injective {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).degree = p.degree := by
  simp [hf, map_ne_zero_iff, ne_or_eq]

/--
theorem `natDegree_map_eq_of_injective` / 定理 `natDegree_map_eq_of_injective`

English:
theorem natDegree_map_eq_of_injective
  given: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  proof: natDegree_eq_of_degree_eq degree_map_eq_of_injective hf _

中文:
定理 natDegree_map_eq_of_injective
  条件: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  证明: natDegree_eq_of_degree_eq degree_map_eq_of_injective hf _

Depends on / 依赖: degree_map_eq_of_injective, natDegree_eq_of_degree_eq
-/
theorem natDegree_map_eq_of_injective {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).natDegree = p.natDegree :=
natDegree_eq_of_degree_eq degree_map_eq_of_injective hf _

/--
theorem `leadingCoeff_map_of_injective` / 定理 `leadingCoeff_map_of_injective`

English:
theorem leadingCoeff_map_of_injective
  statement: {f : R ->+* S} (hf : Function.Injective f)
  proof: by
  simp only [leadingCoeff, natDegree_map_eq_of_injective hf, coeff_map]

中文:
定理 leadingCoeff_map_of_injective
  结论: {f : R ->+* S} (hf : Function.Injective f)
  证明: by
  simp only [leadingCoeff, natDegree_map_eq_of_injective hf, coeff_map]

Depends on / 依赖: coeff_map, leadingCoeff, natDegree_map_eq_of_injective
-/
theorem leadingCoeff_map_of_injective {f : R ->+* S} (hf : Function.Injective f)
    (p : Polynomial R) : (p.map f).leadingCoeff = f p.leadingCoeff := by
  simp only [leadingCoeff, natDegree_map_eq_of_injective hf, coeff_map]

/--
theorem `nextCoeff_map` / 定理 `nextCoeff_map`

English:
theorem nextCoeff_map
  given: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  proof: by
  simp only [hf, nextCoeff, natDegree_map_eq_of_injective]
  split_ifs <;> simp

中文:
定理 nextCoeff_map
  条件: {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R)
  证明: by
  simp only [hf, nextCoeff, natDegree_map_eq_of_injective]
  split_ifs <;> simp

Depends on / 依赖: natDegree_map_eq_of_injective, nextCoeff, split_ifs
-/
theorem nextCoeff_map {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  simp only [hf, nextCoeff, natDegree_map_eq_of_injective]
  split_ifs <;> simp

/--
theorem `natDegree_pos_of_nextCoeff_ne_zero` / 定理 `natDegree_pos_of_nextCoeff_ne_zero`

English:
theorem natDegree_pos_of_nextCoeff_ne_zero
  given: (h : p.nextCoeff != 0)
  statement: 0 < p.natDegree
  proof: by
  grind [nextCoeff]

中文:
定理 natDegree_pos_of_nextCoeff_ne_zero
  条件: (h : p.nextCoeff != 0)
  结论: 0 < p.natDegree
  证明: by
  grind [nextCoeff]

Depends on / 依赖: nextCoeff
-/
theorem natDegree_pos_of_nextCoeff_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegree := by
  grind [nextCoeff]

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

/--
theorem `natDegree_sub` / 定理 `natDegree_sub`

English:
theorem natDegree_sub
  statement: (p - q).natDegree = (q - p).natDegree
  proof: by rw [← natDegree_neg, neg_sub]

中文:
定理 natDegree_sub
  结论: (p - q).natDegree = (q - p).natDegree
  证明: by rw [← natDegree_neg, neg_sub]

Depends on / 依赖: natDegree_neg, neg_sub
-/
theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]

/--
theorem `natDegree_sub_le_iff_left` / 定理 `natDegree_sub_le_iff_left`

English:
theorem natDegree_sub_le_iff_left
  given: (qn : q.natDegree <= n)
  proof: by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg]; rw [natDegree_add_le_iff_left _ _ qn]

中文:
定理 natDegree_sub_le_iff_left
  条件: (qn : q.natDegree <= n)
  证明: by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg]; rw [natDegree_add_le_iff_left _ _ qn]

Depends on / 依赖: natDegree_add_le_iff_left, natDegree_neg, sub_eq_add_neg
-/
theorem natDegree_sub_le_iff_left (qn : q.natDegree <= n) :
    (p - q).natDegree <= n ↔ p.natDegree <= n := by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg]; rw [natDegree_add_le_iff_left _ _ qn]

/--
theorem `natDegree_sub_le_iff_right` / 定理 `natDegree_sub_le_iff_right`

English:
theorem natDegree_sub_le_iff_right
  given: (pn : p.natDegree <= n)
  proof: by rwa [natDegree_sub, natDegree_sub_le_iff_left]

中文:
定理 natDegree_sub_le_iff_right
  条件: (pn : p.natDegree <= n)
  证明: by rwa [natDegree_sub, natDegree_sub_le_iff_left]

Depends on / 依赖: natDegree_sub, natDegree_sub_le_iff_left
-/
theorem natDegree_sub_le_iff_right (pn : p.natDegree <= n) :
    (p - q).natDegree <= n ↔ q.natDegree <= n := by rwa [natDegree_sub, natDegree_sub_le_iff_left]

/--
theorem `coeff_sub_eq_left_of_lt` / 定理 `coeff_sub_eq_left_of_lt`

English:
theorem coeff_sub_eq_left_of_lt
  given: (dg : q.natDegree < n)
  statement: (p - q).coeff n = p.coeff n
  proof: by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg]; rw [coeff_add_eq_left_of_lt dg]

中文:
定理 coeff_sub_eq_left_of_lt
  条件: (dg : q.natDegree < n)
  结论: (p - q).coeff n = p.coeff n
  证明: by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg]; rw [coeff_add_eq_left_of_lt dg]

Depends on / 依赖: coeff_add_eq_left_of_lt, natDegree_neg, sub_eq_add_neg
-/
theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg]; rw [coeff_add_eq_left_of_lt dg]

/--
theorem `coeff_sub_eq_neg_right_of_lt` / 定理 `coeff_sub_eq_neg_right_of_lt`

English:
theorem coeff_sub_eq_neg_right_of_lt
  given: (df : p.natDegree < n)
  statement: (p - q).coeff n = -q.coeff n
  proof: by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]

中文:
定理 coeff_sub_eq_neg_right_of_lt
  条件: (df : p.natDegree < n)
  结论: (p - q).coeff n = -q.coeff n
  证明: by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]

Depends on / 依赖: coeff_add_eq_right_of_lt, coeff_neg, sub_eq_add_neg
-/
theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]

end Ring

section NoZeroDivisors

variable [Semiring R] {p q : R[X]} {a : R}

@[simp]
/--
lemma `nextCoeff_C_mul_X_add_C` / 引理 `nextCoeff_C_mul_X_add_C`

English:
lemma nextCoeff_C_mul_X_add_C
  given: (ha : a != 0) (c : R)
  statement: nextCoeff (C a * X + C c) = c
  proof: by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]

中文:
引理 nextCoeff_C_mul_X_add_C
  条件: (ha : a != 0) (c : R)
  结论: nextCoeff (C a * X + C c) = c
  证明: by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]

Depends on / 依赖: nextCoeff_of_natDegree_pos
-/
lemma nextCoeff_C_mul_X_add_C (ha : a != 0) (c : R) : nextCoeff (C a * X + C c) = c := by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]

/--
lemma `natDegree_eq_one` / 引理 `natDegree_eq_one`

English:
lemma natDegree_eq_one
  statement: p.natDegree = 1 ↔ exists a != 0, exists b, C a * X + C b = p
  proof: by
  refine ⟨fun hp => ⟨p.coeff 1, fun h => ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    simp_all
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_l

中文:
引理 natDegree_eq_one
  结论: p.natDegree = 1 ↔ 存在 a != 0, 存在 b, C a * X + C b = p
  证明: by
  refine ⟨fun hp => ⟨p.coeff 1, fun h => ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    simp_all
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_l

Depends on / 依赖: add_zero, coeff_C_succ, coeff_add, coeff_eq_zero_of_natDegree_lt, coeff_mul_X, coeff_natDegree, leadingCoeff_eq_zero, p.coeff
-/
lemma natDegree_eq_one : p.natDegree = 1 ↔ exists a != 0, exists b, C a * X + C b = p := by
  refine ⟨fun hp => ⟨p.coeff 1, fun h => ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    simp_all
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_lt]
      simp [hp]
  · rintro ⟨a, ha, b, rfl⟩
    simp [ha]

/--
theorem `subsingleton_isRoot_of_natDegree_eq_one` / 定理 `subsingleton_isRoot_of_natDegree_eq_one`

English:
theorem subsingleton_isRoot_of_natDegree_eq_one
  statement: [IsLeftCancelMulZero R]
  proof: by
  intro r₁
  obtain ⟨r₂, hr₂, r₃, rfl⟩ : exists a, a != 0 ∧ exists b, C a * X + C b = p := by rwa [natDegree_eq_one] at h
  have (x y : R) := mul_left_cancel₀ hr₂ (b := x) (c := y)
  grind [IsRoot, eval_add, eval_mul_X, eval_C]

中文:
定理 subsingleton_isRoot_of_natDegree_eq_one
  结论: [IsLeftCancelMulZero R]
  证明: by
  intro r₁
  obtain ⟨r₂, hr₂, r₃, rfl⟩ : exists a, a != 0 ∧ exists b, C a * X + C b = p := by rwa [natDegree_eq_one] at h
  have (x y : R) := mul_left_cancel₀ hr₂ (b := x) (c := y)
  grind [IsRoot, eval_add, eval_mul_X, eval_C]

Depends on / 依赖: IsRoot, eval_C, eval_add, eval_mul_X, natDegree_eq_one
-/
theorem subsingleton_isRoot_of_natDegree_eq_one [IsLeftCancelMulZero R]
    (h : p.natDegree = 1) : { x | IsRoot p x }.Subsingleton := by
  intro r₁
  obtain ⟨r₂, hr₂, r₃, rfl⟩ : exists a, a != 0 ∧ exists b, C a * X + C b = p := by rwa [natDegree_eq_one] at h
  have (x y : R) := mul_left_cancel₀ hr₂ (b := x) (c := y)
  grind [IsRoot, eval_add, eval_mul_X, eval_C]

variable [NoZeroDivisors R]

/--
theorem `degree_mul_C` / 定理 `degree_mul_C`

English:
theorem degree_mul_C
  given: (a0 : a != 0)
  statement: (p * C a).degree = p.degree
  proof: by
  rw [degree_mul]; rw [degree_C a0]; rw [add_zero]

中文:
定理 degree_mul_C
  条件: (a0 : a != 0)
  结论: (p * C a).degree = p.degree
  证明: by
  rw [degree_mul]; rw [degree_C a0]; rw [add_zero]

Depends on / 依赖: add_zero, degree_C, degree_mul
-/
theorem degree_mul_C (a0 : a != 0) : (p * C a).degree = p.degree := by
  rw [degree_mul]; rw [degree_C a0]; rw [add_zero]

/--
theorem `degree_C_mul` / 定理 `degree_C_mul`

English:
theorem degree_C_mul
  given: (a0 : a != 0)
  statement: (C a * p).degree = p.degree
  proof: by
  rw [degree_mul]; rw [degree_C a0]; rw [zero_add]

中文:
定理 degree_C_mul
  条件: (a0 : a != 0)
  结论: (C a * p).degree = p.degree
  证明: by
  rw [degree_mul]; rw [degree_C a0]; rw [zero_add]

Depends on / 依赖: degree_C, degree_mul, zero_add
-/
theorem degree_C_mul (a0 : a != 0) : (C a * p).degree = p.degree := by
  rw [degree_mul]; rw [degree_C a0]; rw [zero_add]

/--
theorem `natDegree_mul_C` / 定理 `natDegree_mul_C`

English:
theorem natDegree_mul_C
  given: (a0 : a != 0)
  statement: (p * C a).natDegree = p.natDegree
  proof: by
  simp only [natDegree, degree_mul_C a0]

中文:
定理 natDegree_mul_C
  条件: (a0 : a != 0)
  结论: (p * C a).natDegree = p.natDegree
  证明: by
  simp only [natDegree, degree_mul_C a0]

Depends on / 依赖: degree_mul_C, natDegree
-/
theorem natDegree_mul_C (a0 : a != 0) : (p * C a).natDegree = p.natDegree := by
  simp only [natDegree, degree_mul_C a0]

/--
theorem `natDegree_C_mul` / 定理 `natDegree_C_mul`

English:
theorem natDegree_C_mul
  given: (a0 : a != 0)
  statement: (C a * p).natDegree = p.natDegree
  proof: by
  simp only [natDegree, degree_C_mul a0]

中文:
定理 natDegree_C_mul
  条件: (a0 : a != 0)
  结论: (C a * p).natDegree = p.natDegree
  证明: by
  simp only [natDegree, degree_C_mul a0]

Depends on / 依赖: degree_C_mul, natDegree
-/
theorem natDegree_C_mul (a0 : a != 0) : (C a * p).natDegree = p.natDegree := by
  simp only [natDegree, degree_C_mul a0]

/--
theorem `natDegree_comp` / 定理 `natDegree_comp`

English:
theorem natDegree_comp
  statement: natDegree (p.comp q) = natDegree p * natDegree q
  proof: by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p

中文:
定理 natDegree_comp
  结论: natDegree (p.comp q) = natDegree p * natDegree q
  证明: by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p

Depends on / 依赖: Nat.pos_of_ne_zero, comp_C, degree_le_zero_iff, degree_le_zero_iff.mp, leadingCoeff_eq_zero, mul_eq_zero, mul_zero, natDegree, natDegree_C, natDegree_comp_eq_of_mul_ne_zero, natDegree_eq_zero_iff_degree_le_zero, natDegree_eq_zero_iff_degree_le_zero.mp, natDegree_zero, ne_zero_of_natDegree_gt, not_false_eq_true, or_self, pos_of_ne_zero, pow_ne_zero, q.natDegree, zero_comp
-/
theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p0, natDegree_comp_eq_of_mul_ne_zero,
        ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), not_false_eq_true, pow_ne_zero, or_self]

@[simp]
/--
theorem `natDegree_iterate_comp` / 定理 `natDegree_iterate_comp`

English:
theorem natDegree_iterate_comp
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]

中文:
定理 natDegree_iterate_comp
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply, mul_assoc, natDegree_comp, pow_succ
-/
theorem natDegree_iterate_comp (k : Nat) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]

/--
theorem `leadingCoeff_comp` / 定理 `leadingCoeff_comp`

English:
theorem leadingCoeff_comp
  given: (hq : natDegree q != 0)
  proof: by
  rw [← coeff_comp_degree_mul_degree hq]; rw [← natDegree_comp]; rw [coeff_natDegree]

@[simp]

中文:
定理 leadingCoeff_comp
  条件: (hq : natDegree q != 0)
  证明: by
  rw [← coeff_comp_degree_mul_degree hq]; rw [← natDegree_comp]; rw [coeff_natDegree]

@[simp]

Depends on / 依赖: coeff_comp_degree_mul_degree, coeff_natDegree, natDegree_comp
-/
theorem leadingCoeff_comp (hq : natDegree q != 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq]; rw [← natDegree_comp]; rw [coeff_natDegree]

@[simp]
/--
theorem `nextCoeff_C_mul` / 定理 `nextCoeff_C_mul`

English:
theorem nextCoeff_C_mul
  statement: (C a * p).nextCoeff = a * p.nextCoeff
  proof: by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_C_mul]

@[simp]

中文:
定理 nextCoeff_C_mul
  结论: (C a * p).nextCoeff = a * p.nextCoeff
  证明: by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_C_mul]

@[simp]

Depends on / 依赖: natDegree_C_mul, nextCoeff
-/
theorem nextCoeff_C_mul : (C a * p).nextCoeff = a * p.nextCoeff := by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_C_mul]

@[simp]
/--
theorem `nextCoeff_mul_C` / 定理 `nextCoeff_mul_C`

English:
theorem nextCoeff_mul_C
  statement: (p * C a).nextCoeff = p.nextCoeff * a
  proof: by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_mul_C]

中文:
定理 nextCoeff_mul_C
  结论: (p * C a).nextCoeff = p.nextCoeff * a
  证明: by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_mul_C]

Depends on / 依赖: natDegree_mul_C, nextCoeff
-/
theorem nextCoeff_mul_C : (p * C a).nextCoeff = p.nextCoeff * a := by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_mul_C]

end NoZeroDivisors

/--
lemma `comp_neg_X_leadingCoeff_eq` / 引理 `comp_neg_X_leadingCoeff_eq`

English:
lemma comp_neg_X_leadingCoeff_eq
  given: [Ring R] (p : R[X])
  proof: by
  nontriviality R
  by_cases h : p = 0
  · simp [h]
  rw [Polynomial.leadingCoeff]; rw [natDegree_comp_eq_of_mul_ne_zero]; rw [coeff_comp_degree_mul_degree] <;>
  simp [((Commute.neg_one_left _).pow_left _).eq, h]

@[simp]

中文:
引理 comp_neg_X_leadingCoeff_eq
  条件: [Ring R] (p : R[X])
  证明: by
  nontriviality R
  by_cases h : p = 0
  · simp [h]
  rw [Polynomial.leadingCoeff]; rw [natDegree_comp_eq_of_mul_ne_zero]; rw [coeff_comp_degree_mul_degree] <;>
  simp [((Commute.neg_one_left _).pow_left _).eq, h]

@[simp]
-/
@[simp] lemma comp_neg_X_leadingCoeff_eq [Ring R] (p : R[X]) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  nontriviality R
  by_cases h : p = 0
  · simp [h]
  rw [Polynomial.leadingCoeff]; rw [natDegree_comp_eq_of_mul_ne_zero]; rw [coeff_comp_degree_mul_degree] <;>
  simp [((Commute.neg_one_left _).pow_left _).eq, h]

@[simp]
/--
theorem `comp_neg_X_eq_zero_iff` / 定理 `comp_neg_X_eq_zero_iff`

English:
theorem comp_neg_X_eq_zero_iff
  given: [Ring R] {p : R[X]}
  statement: p.comp (-X) = 0 ↔ p = 0
  proof: by
  simp [← leadingCoeff_eq_zero]

中文:
定理 comp_neg_X_eq_zero_iff
  条件: [Ring R] {p : R[X]}
  结论: p.comp (-X) = 0 ↔ p = 0
  证明: by
  simp [← leadingCoeff_eq_zero]

Depends on / 依赖: leadingCoeff_eq_zero
-/
theorem comp_neg_X_eq_zero_iff [Ring R] {p : R[X]} : p.comp (-X) = 0 ↔ p = 0 := by
  simp [← leadingCoeff_eq_zero]

/--
lemma `comp_eq_zero_iff` / 引理 `comp_eq_zero_iff`

English:
lemma comp_eq_zero_iff
  given: [Semiring R] [NoZeroDivisors R] {p q : R[X]}
  proof: by
  refine ⟨fun h => ?_, Or.rec (fun h => by simp [h]) fun h => by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero]; rw [← natDegree_comp]; rw [h]; rw [natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_

中文:
引理 comp_eq_zero_iff
  条件: [Semiring R] [NoZeroDivisors R] {p q : R[X]}
  证明: by
  refine ⟨fun h => ?_, Or.rec (fun h => by simp [h]) fun h => by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero]; rw [← natDegree_comp]; rw [h]; rw [natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_

Depends on / 依赖: C_comp, C_eq_zero, Or.imp, Or.inl, Or.inr, Or.rec, comp_C, eq_C_of_natDegree_eq_zero, key.trans, mul_eq_zero, natDegree, natDegree_comp, natDegree_zero, p.natDegree, q.natDegree
-/
lemma comp_eq_zero_iff [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  refine ⟨fun h => ?_, Or.rec (fun h => by simp [h]) fun h => by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero]; rw [← natDegree_comp]; rw [h]; rw [natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
  · rw [key, C_comp] at h
    exact Or.inl (key.trans h)
  · rw [key, comp_C, C_eq_zero] at h
    exact Or.inr ⟨h, key⟩

/--
lemma `degree_comp` / 引理 `degree_comp`

English:
lemma degree_comp
  given: [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degree)
  proof: by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, degree_zero, WithBot.bot_mul']
    simp [hq.ne']
  rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree (ne_zero_of_degree_gt hq)]; rw [← Nat.cast_mul]; rw [← natDegree_comp]
  apply degree_eq_natDegree
  simp_rw [Ne, comp_eq_zero_iff, hp, fa

中文:
引理 degree_comp
  条件: [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degree)
  证明: by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, degree_zero, WithBot.bot_mul']
    simp [hq.ne']
  rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree (ne_zero_of_degree_gt hq)]; rw [← Nat.cast_mul]; rw [← natDegree_comp]
  apply degree_eq_natDegree
  simp_rw [Ne, comp_eq_zero_iff, hp, fa

Depends on / 依赖: Nat.cast_mul, WithBot, WithBot.bot_mul, bot_mul, cast_mul, comp_eq_zero_iff, degree_eq_natDegree, degree_le_zero_iff, degree_zero, eq_or_ne, false_or, hq.ne, natDegree_comp, ne_zero_of_degree_gt, not_and_or, simp_rw, zero_comp
-/
lemma degree_comp [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degree) :
    (p.comp q).degree = p.degree * q.degree := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, degree_zero, WithBot.bot_mul']
    simp [hq.ne']
  rw [degree_eq_natDegree hp]; rw [degree_eq_natDegree (ne_zero_of_degree_gt hq)]; rw [← Nat.cast_mul]; rw [← natDegree_comp]
  apply degree_eq_natDegree
  simp_rw [Ne, comp_eq_zero_iff, hp, false_or, not_and_or, ← degree_le_zero_iff]
  simp [hq]

/--
lemma `degree_comp_neg_X` / 引理 `degree_comp_neg_X`

English:
lemma degree_comp_neg_X
  given: [Ring R] {p : R[X]}
  statement: (p.comp (-X)).degree = p.degree
  proof: by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp]
  rw [degree_eq_natDegree (by simp [hp]), degree_eq_natDegree hp, Nat.cast_inj,
    natDegree_comp_eq_of_mul_ne_zero (by simp [hp]), natDegree_neg, natDegree_X, mul_one]

中文:
引理 degree_comp_neg_X
  条件: [Ring R] {p : R[X]}
  结论: (p.comp (-X)).degree = p.degree
  证明: by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp]
  rw [degree_eq_natDegree (by simp [hp]), degree_eq_natDegree hp, Nat.cast_inj,
    natDegree_comp_eq_of_mul_ne_zero (by simp [hp]), natDegree_neg, natDegree_X, mul_one]
-/
@[simp] lemma degree_comp_neg_X [Ring R] {p : R[X]} : (p.comp (-X)).degree = p.degree := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp]
  rw [degree_eq_natDegree (by simp [hp]), degree_eq_natDegree hp, Nat.cast_inj,
    natDegree_comp_eq_of_mul_ne_zero (by simp [hp]), natDegree_neg, natDegree_X, mul_one]

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-! Useful lemmas for the "monicization" of a nonzero polynomial `p`. -/
@[simp]
/--
theorem `irreducible_mul_leadingCoeff_inv` / 定理 `irreducible_mul_leadingCoeff_inv`

English:
theorem irreducible_mul_leadingCoeff_inv
  given: {p : K[X]}
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

中文:
定理 irreducible_mul_leadingCoeff_inv
  条件: {p : K[X]}
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

Depends on / 依赖: IsUnit, IsUnit.mk0, inv_ne_zero, irreducible_mul_isUnit, isUnit_C, isUnit_C.mpr, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr
-/
theorem irreducible_mul_leadingCoeff_inv {p : K[X]} :
    Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

/--
lemma `dvd_mul_leadingCoeff_inv` / 引理 `dvd_mul_leadingCoeff_inv`

English:
lemma dvd_mul_leadingCoeff_inv
  given: {p q : K[X]} (hp0 : p != 0)
  proof: by
  simp [hp0]

中文:
引理 dvd_mul_leadingCoeff_inv
  条件: {p q : K[X]} (hp0 : p != 0)
  证明: by
  simp [hp0]
-/
lemma dvd_mul_leadingCoeff_inv {p q : K[X]} (hp0 : p != 0) :
    q ∣ p * C (leadingCoeff p)⁻¹ ↔ q ∣ p := by
  simp [hp0]

/--
theorem `monic_mul_leadingCoeff_inv` / 定理 `monic_mul_leadingCoeff_inv`

English:
theorem monic_mul_leadingCoeff_inv
  given: {p : K[X]} (h : p != 0)
  statement: Monic (p * C (leadingCoeff p)⁻¹)
  proof: by
  rw [Monic]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [mul_inv_cancel₀ (show leadingCoeff p != 0 from mt leadingCoeff_eq_zero.1 h)]

中文:
定理 monic_mul_leadingCoeff_inv
  条件: {p : K[X]} (h : p != 0)
  结论: Monic (p * C (leadingCoeff p)⁻¹)
  证明: by
  rw [Monic]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [mul_inv_cancel₀ (show leadingCoeff p != 0 from mt leadingCoeff_eq_zero.1 h)]

Depends on / 依赖: leadingCoeff, leadingCoeff_C, leadingCoeff_eq_zero, leadingCoeff_mul
-/
theorem monic_mul_leadingCoeff_inv {p : K[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹) := by
  rw [Monic]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [mul_inv_cancel₀ (show leadingCoeff p != 0 from mt leadingCoeff_eq_zero.1 h)]

-- `simp` normal form of `degree_mul_leadingCoeff_inv`
/--
lemma `degree_leadingCoeff_inv` / 引理 `degree_leadingCoeff_inv`

English:
lemma degree_leadingCoeff_inv
  given: {p : K[X]} (hp0 : p != 0)
  proof: by
  simp [hp0]

中文:
引理 degree_leadingCoeff_inv
  条件: {p : K[X]} (hp0 : p != 0)
  证明: by
  simp [hp0]
-/
lemma degree_leadingCoeff_inv {p : K[X]} (hp0 : p != 0) :
    degree (C (leadingCoeff p)⁻¹) = 0 := by
  simp [hp0]

/--
theorem `degree_mul_leadingCoeff_inv` / 定理 `degree_mul_leadingCoeff_inv`

English:
theorem degree_mul_leadingCoeff_inv
  given: (p : K[X]) {q : K[X]} (h : q != 0)
  proof: by
  have h₁ : (leadingCoeff q)⁻¹ != 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [degree_mul_C h₁]

中文:
定理 degree_mul_leadingCoeff_inv
  条件: (p : K[X]) {q : K[X]} (h : q != 0)
  证明: by
  have h₁ : (leadingCoeff q)⁻¹ != 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [degree_mul_C h₁]

Depends on / 依赖: degree_mul_C, inv_ne_zero, leadingCoeff, leadingCoeff_eq_zero
-/
theorem degree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q != 0) :
    degree (p * C (leadingCoeff q)⁻¹) = degree p := by
  have h₁ : (leadingCoeff q)⁻¹ != 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [degree_mul_C h₁]

/--
theorem `natDegree_mul_leadingCoeff_inv` / 定理 `natDegree_mul_leadingCoeff_inv`

English:
theorem natDegree_mul_leadingCoeff_inv
  given: (p : K[X]) {q : K[X]} (h : q != 0)
  proof: natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv _ h)

中文:
定理 natDegree_mul_leadingCoeff_inv
  条件: (p : K[X]) {q : K[X]} (h : q != 0)
  证明: natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv _ h)

Depends on / 依赖: degree_mul_leadingCoeff_inv, natDegree_eq_of_degree_eq
-/
theorem natDegree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q != 0) :
    natDegree (p * C (leadingCoeff q)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv _ h)

/--
theorem `degree_mul_leadingCoeff_self_inv` / 定理 `degree_mul_leadingCoeff_self_inv`

English:
theorem degree_mul_leadingCoeff_self_inv
  given: (p : K[X])
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp

中文:
定理 degree_mul_leadingCoeff_self_inv
  条件: (p : K[X])
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp

Depends on / 依赖: degree_mul_leadingCoeff_inv
-/
theorem degree_mul_leadingCoeff_self_inv (p : K[X]) :
    degree (p * C (leadingCoeff p)⁻¹) = degree p := by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp

/--
theorem `natDegree_mul_leadingCoeff_self_inv` / 定理 `natDegree_mul_leadingCoeff_self_inv`

English:
theorem natDegree_mul_leadingCoeff_self_inv
  given: (p : K[X])
  proof: natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

中文:
定理 natDegree_mul_leadingCoeff_self_inv
  条件: (p : K[X])
  证明: natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

Depends on / 依赖: degree_mul_leadingCoeff_self_inv, natDegree_eq_of_degree_eq
-/
theorem natDegree_mul_leadingCoeff_self_inv (p : K[X]) :
    natDegree (p * C (leadingCoeff p)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

-- `simp` normal form of `degree_mul_leadingCoeff_self_inv`
/--
lemma `degree_add_degree_leadingCoeff_inv` / 引理 `degree_add_degree_leadingCoeff_inv`

English:
lemma degree_add_degree_leadingCoeff_inv
  given: (p : K[X])
  proof: by
  rw [← degree_mul]; rw [degree_mul_leadingCoeff_self_inv]

中文:
引理 degree_add_degree_leadingCoeff_inv
  条件: (p : K[X])
  证明: by
  rw [← degree_mul]; rw [degree_mul_leadingCoeff_self_inv]
-/
@[simp] lemma degree_add_degree_leadingCoeff_inv (p : K[X]) :
    degree p + degree (C (leadingCoeff p)⁻¹) = degree p := by
  rw [← degree_mul]; rw [degree_mul_leadingCoeff_self_inv]

end DivisionRing

end Polynomial
