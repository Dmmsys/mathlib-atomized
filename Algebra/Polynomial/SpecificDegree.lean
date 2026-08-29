/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

public section

namespace Polynomial

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/--
theorem `Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` / 定理 `Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`

English:
theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
  statement: {p : R[X]} (hp : p.Monic)
  proof: by
  have hp0 : p != 0 := hp.ne_zero
  have hp1 : p != 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    s

中文:
定理 Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
  结论: {p : R[X]} (hp : p.Monic)
  证明: by
  have hp0 : p != 0 := hp.ne_zero
  have hp1 : p != 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    s

Depends on / 依赖: Finset, Finset.Ioc, Finset.mem_singleton, Multiset, Multiset.eq_zero_iff_forall_notMem, Nat.div_le_div_right, antisymm, div_le_div_right, dvd_iff_isRoot, eq_X_ad, eq_zero_iff_forall_notMem, hp.irreducible_iff_lt_natDegree_lt, hp.ne_zero, hq.eq_X_ad, irreducible_iff_lt_natDegree_lt, mem_roots, mem_singleton, monic_X_sub_C, natDegree, natDegree_X_sub_C
-/
theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three {p : R[X]} (hp : p.Monic)
    (hp2 : 2 <= p.natDegree) (hp3 : p.natDegree <= 3) : Irreducible p ↔ p.roots = 0 := by
  have hp0 : p != 0 := hp.ne_zero
  have hp1 : p != 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_notMem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r => h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 => ?_⟩
  rw [hq.eq_X_add_C hq1]; rw [← sub_neg_eq_add]; rw [← C_neg]
  apply h

end IsDomain

section Field

variable {K : Type*} [Field K] {p : K[X]}

/--
theorem `irreducible_iff_roots_eq_zero_of_degree_le_three` / 定理 `irreducible_iff_roots_eq_zero_of_degree_le_three`

English:
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
  proof: by
  have hp0 : p != 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three]; rw [mul_comm]; rw [roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · r

中文:
定理 irreducible_iff_roots_eq_zero_of_degree_le_three
  证明: by
  have hp0 : p != 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three]; rw [mul_comm]; rw [roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · r

Depends on / 依赖: inv_ne_zero, irreducible_iff_roots_eq_zero_of_degree_le_three, irreducible_mul_leadingCoeff_inv, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, monic_mul_leadingCoeff_inv, mul_comm, natDegree_mul_leadingCoeff_inv, natDegree_zero, roots_C_mul
-/
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    (hp2 : 2 <= p.natDegree) (hp3 : p.natDegree <= 3) :
    Irreducible p ↔ p.roots = 0 := by
  have hp0 : p != 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three]; rw [mul_comm]; rw [roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]

/--
lemma `irreducible_of_degree_le_three_of_not_isRoot` / 引理 `irreducible_of_degree_le_three_of_not_isRoot`

English:
lemma irreducible_of_degree_le_three_of_not_isRoot
  proof: by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 <= p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one]; rw [Polynomial.de

中文:
引理 irreducible_of_degree_le_three_of_not_isRoot
  证明: by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 <= p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one]; rw [Polynomial.de

Depends on / 依赖: Finset, Finset.mem_Icc, Multiset, Multiset.eq_zero_of_forall_notMem, Nat.cast_one, Nat.lt_succ_iff, Polynomial, Polynomial.degree_eq_iff_natDegree_eq_of_pos, Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three, Polynomial.irreducible_of_degree_eq_one, cast_one, degree_eq_iff_natDegree_eq_of_pos, eq_zero_of_forall_notMem, irreducible_iff_roots_eq_zero_of_degree_le_three, irreducible_of_degree_eq_one, le_antisymm, lt_succ_iff, mem_Icc, natDegree, not_le
-/
lemma irreducible_of_degree_le_three_of_not_isRoot
    (hdeg : p.natDegree in Finset.Icc 1 3) (hnot : forall x, ¬ IsRoot p x) :
    Irreducible p := by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 <= p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one]; rw [Polynomial.degree_eq_iff_natDegree_eq_of_pos (by simp)]
    exact le_antisymm (by rwa [not_le, Nat.lt_succ_iff] at hdeg2) hdeg.1

end Field

end Polynomial
