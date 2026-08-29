/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic.ComputeDegree

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancelLeads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancelLeads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/

@[expose] public section


namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type*}

section Ring

variable [Ring R] (p q : R[X])

/--
Definition of `cancelLeads` / `cancelLeads` 的定义

English:
definition cancelLeads
  signature: : R[X]
  body: C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

中文:
定义 cancelLeads
  签名: : R[X]
  定义体: C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

Depends on / 依赖: leadingCoeff, natDegree, p.leadingCoeff, p.natDegree, q.leadingCoeff, q.natDegree
-/
def cancelLeads : R[X] :=
  C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

variable {p q}

@[simp]
/--
theorem `neg_cancelLeads` / 定理 `neg_cancelLeads`

English:
theorem neg_cancelLeads
  statement: -p.cancelLeads q = q.cancelLeads p
  proof: neg_sub _ _

中文:
定理 neg_cancelLeads
  结论: -p.cancelLeads q = q.cancelLeads p
  证明: neg_sub _ _

Depends on / 依赖: neg_sub
-/
theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _

/--
theorem `natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm` / 定理 `natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm`

English:
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
  proof: by
  by_cases hp : p = 0
  · convert! hq
    simp [hp, cancelLeads]
  rw [cancelLeads]; rw [sub_eq_add_neg]; rw [tsub_eq_zero_iff_le.mpr h]; rw [pow_zero]; rw [mul_one]
  by_cases h0 :
    C p.leadingCoeff * q + -(C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by si

中文:
定理 natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
  证明: by
  by_cases hp : p = 0
  · convert! hq
    simp [hp, cancelLeads]
  rw [cancelLeads]; rw [sub_eq_add_neg]; rw [tsub_eq_zero_iff_le.mpr h]; rw [pow_zero]; rw [mul_one]
  by_cases h0 :
    C p.leadingCoeff * q + -(C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by si

Depends on / 依赖: Nat.sub_add_cancel, X_pow_mul, cancelLeads, compute_degree, contrapose, convert, le_of_eq, leadingCoeff, leadingCoeff_eq_zero, lt_of_le_of_ne, mul_assoc, mul_one, natDegree, natDegree_zero, p.leadingCoeff, p.natDegree, pow_zero, q.leadingCoeff, q.natDegree, sub_add_cancel
-/
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree <= q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree := by
  by_cases hp : p = 0
  · convert! hq
    simp [hp, cancelLeads]
  rw [cancelLeads]; rw [sub_eq_add_neg]; rw [tsub_eq_zero_iff_le.mpr h]; rw [pow_zero]; rw [mul_one]
  by_cases h0 :
    C p.leadingCoeff * q + -(C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by simp only [h0, natDegree_zero])).trans_lt hq
  apply lt_of_le_of_ne
  · compute_degree!
    rwa [Nat.sub_add_cancel]
  · contrapose h0
    rw [← leadingCoeff_eq_zero]; rw [leadingCoeff]; rw [h0]; rw [mul_assoc]; rw [X_pow_mul]; rw [← tsub_add_cancel_of_le h]; rw [add_comm _ p.natDegree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_comm p.natDegree]; rw [tsub_add_cancel_of_le h]; rw [← leadingCoeff]; rw [← leadingCoeff]; rw [comm]; rw [add_neg_cancel]

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

/--
theorem `dvd_cancelLeads_of_dvd_of_dvd` / 定理 `dvd_cancelLeads_of_dvd_of_dvd`

English:
theorem dvd_cancelLeads_of_dvd_of_dvd
  given: {r : R[X]} (pq : p ∣ q) (pr : p ∣ r)
  statement: p ∣ q.cancelLeads r
  proof: dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

中文:
定理 dvd_cancelLeads_of_dvd_of_dvd
  条件: {r : R[X]} (pq : p ∣ q) (pr : p ∣ r)
  结论: p ∣ q.cancelLeads r
  证明: dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

Depends on / 依赖: Dvd.intro_left, dvd_sub, intro_left, pq.trans, pr.trans
-/
theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

/--
theorem `natDegree_cancelLeads_lt_of_natDegree_le_natDegree` / 定理 `natDegree_cancelLeads_lt_of_natDegree_le_natDegree`

English:
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree
  statement: (h : p.natDegree <= q.natDegree)
  proof: natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq

中文:
定理 natDegree_cancelLeads_lt_of_natDegree_le_natDegree
  结论: (h : p.natDegree <= q.natDegree)
  证明: natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq

Depends on / 依赖: mul_comm, natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
-/
theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree <= q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree :=
  natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq

end CommRing

end

end Polynomial
