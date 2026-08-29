/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.signVariations`: The number of sign changes in a polynomial's coefficients,
  where `0` coefficients are ignored.

## Main theorem

- `Polynomial.roots_countP_pos_le_signVariations`. States that
  `P.roots.countP (0 < ·) ≤ P.signVariations`, so that positive roots are counted with multiplicity.
  It's currently proved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
  statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
  commutative rings.

## Reference

[Wikipedia: Descartes' Rule of Signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs)
-/

@[expose] public section

namespace Polynomial

section Semiring
variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

/--
Definition of `signVariations` / `signVariations` 的定义

English:
definition signVariations
  signature: : Nat
  body: letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· != 0)
  (nonzero_signs.destutter (· != ·)).length - 1

中文:
定义 signVariations
  签名: : 自然数
  定义体: letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· != 0)
  (nonzero_signs.destutter (· != ·)).length - 1

Depends on / 依赖: SignType, SignType.sign, coeffList, coeff_signs, coeff_signs.filter, destutter, filter, length, nonzero_signs, nonzero_signs.destutter
-/
def signVariations : Nat :=
  letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· != 0)
  (nonzero_signs.destutter (· != ·)).length - 1

variable (R) in
@[simp]
/--
theorem `signVariations_zero` / 定理 `signVariations_zero`

English:
theorem signVariations_zero
  statement: signVariations (0 : R[X]) = 0
  proof: by
  simp [signVariations]

中文:
定理 signVariations_zero
  结论: signVariations (0 : R[X]) = 0
  证明: by
  simp [signVariations]

Depends on / 依赖: signVariations
-/
theorem signVariations_zero : signVariations (0 : R[X]) = 0 := by
  simp [signVariations]

/-- Sign variations of a monomial are always zero. -/
@[simp]
/--
theorem `signVariations_monomial` / 定理 `signVariations_monomial`

English:
theorem signVariations_monomial
  given: (d : Nat) (c : R)
  statement: signVariations (monomial d c) = 0
  proof: by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

中文:
定理 signVariations_monomial
  条件: (d : 自然数) (c : R)
  结论: signVariations (monomial d c) = 0
  证明: by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

Depends on / 依赖: coeffList_eraseLead, monomial_eq_zero_iff, signVariations
-/
theorem signVariations_monomial (d : Nat) (c : R) : signVariations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

/--
theorem `signVariations_eraseLead` / 定理 `signVariations_eraseLead`

English:
theorem signVariations_eraseLead
  given: (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff)
  proof: by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P != 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

中文:
定理 signVariations_eraseLead
  条件: (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff)
  证明: by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P != 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

Depends on / 依赖: List.destutter, coeffList_eq_cons_leadingCoeff, coeffList_eraseLead, destutter, leadingCoeff_eraseLead_eq_nextCoeff, nextCoeff, nextCoeff_eq_zero_of_eraseLead_eq_zero, signVariations
-/
theorem signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
    signVariations P.eraseLead = signVariations P := by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P != 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

/--
theorem `signVariations_eq_eraseLead_add_ite` / 定理 `signVariations_eq_eraseLead_add_ite`

English:
theorem signVariations_eq_eraseLead_add_ite
  given: {P : Polynomial R} (h : P != 0)
  proof: by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) != 0 := by simp_all
  rw [signVariations]; rw [signVariations]; rw [coeffList_eraseLead hpz]
  rw [List.map_cons]; rw [List.map_append]; rw [List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c != 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P != 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄]; rw [if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

中文:
定理 signVariations_eq_eraseLead_add_ite
  条件: {P : 多项式 R} (h : P != 0)
  证明: by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) != 0 := by simp_all
  rw [signVariations]; rw [signVariations]; rw [coeffList_eraseLead hpz]
  rw [List.map_cons]; rw [List.map_append]; rw [List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c != 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P != 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄]; rw [if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

Depends on / 依赖: List.filter, List.filter_append, List.filter_replicate, List.map_append, List.map_cons, List.map_replicate, P.eraseLead.coeffList, SignType, SignType.sign, coeffList, coeffList_eq_nil, coeffList_eq_nil.mp, coeffList_eraseLead, eraseLead, filter, filter_append, filter_replicate, h_eL, leadingCoeff, map_append
-/
theorem signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P != 0) :
    signVariations P = signVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) != 0 := by simp_all
  rw [signVariations]; rw [signVariations]; rw [coeffList_eraseLead hpz]
  rw [List.map_cons]; rw [List.map_append]; rw [List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c != 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P != 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄]; rw [if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

/--
theorem `signVariations_eraseLead_le` / 定理 `signVariations_eraseLead_le`

English:
theorem signVariations_eraseLead_le
  statement: signVariations P.eraseLead <= signVariations P
  proof: by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

中文:
定理 signVariations_eraseLead_le
  结论: signVariations P.eraseLead <= signVariations P
  证明: by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

Depends on / 依赖: signVariations_eq_eraseLead_add_ite
-/
theorem signVariations_eraseLead_le : signVariations P.eraseLead <= signVariations P := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

/--
theorem `signVariations_le_eraseLead_succ` / 定理 `signVariations_le_eraseLead_succ`

English:
theorem signVariations_le_eraseLead_succ
  statement: signVariations P <= signVariations P.eraseLead + 1
  proof: by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

中文:
定理 signVariations_le_eraseLead_succ
  结论: signVariations P <= signVariations P.eraseLead + 1
  证明: by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

Depends on / 依赖: signVariations_eq_eraseLead_add_ite
-/
theorem signVariations_le_eraseLead_succ : signVariations P <= signVariations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

/-- The number of sign changes does not change if we negate. -/
@[simp]
/--
theorem `signVariations_neg` / 定理 `signVariations_neg`

English:
theorem signVariations_neg
  statement: signVariations (-P) = signVariations P
  proof: by
  rw [signVariations]; rw [signVariations]; rw [coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x : R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·) := by
    grind [List.map_destutter, neg_inj]
  rw [hsc]; rw [List.comp_map]; rw [← h_neg_destutter]; rw [List.length_map]
  congr 5
  funext
  simp [SignType.sign]

中文:
定理 signVariations_neg
  结论: signVariations (-P) = signVariations P
  证明: by
  rw [signVariations]; rw [signVariations]; rw [coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x : R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·) := by
    grind [List.map_destutter, neg_inj]
  rw [hsc]; rw [List.comp_map]; rw [← h_neg_destutter]; rw [List.length_map]
  congr 5
  funext
  simp [SignType.sign]

Depends on / 依赖: Left.sign_neg, List.comp_map, List.filter_map, List.length_map, List.map_destutter, List.map_map, SignType, SignType.sign, coeffList_neg, comp_map, destutter, filter_map, h_neg_destutter, l.destutter, l.map, length_map, map_destutter, map_map, neg_inj, signVariations
-/
theorem signVariations_neg : signVariations (-P) = signVariations P := by
  rw [signVariations]; rw [signVariations]; rw [coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x : R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·) := by
    grind [List.map_destutter, neg_inj]
  rw [hsc]; rw [List.comp_map]; rw [← h_neg_destutter]; rw [List.length_map]
  congr 5
  funext
  simp [SignType.sign]

end OrderedRing

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

/-- The number of sign changes does not change if we multiply by any nonzero scalar. -/
@[simp]
/--
theorem `signVariations_C_mul` / 定理 `signVariations_C_mul`

English:
theorem signVariations_C_mul
  given: (P : Polynomial R) (hx : η != 0)
  proof: by
  wlog! hx2 : 0 < η
  · simpa [lt_of_le_of_ne hx2, hx] using this (η := -η) (P := -P)
  rw [signVariations]; rw [signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2))]; rw [← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

中文:
定理 signVariations_C_mul
  条件: (P : 多项式 R) (hx : η != 0)
  证明: by
  wlog! hx2 : 0 < η
  · simpa [lt_of_le_of_ne hx2, hx] using this (η := -η) (P := -P)
  rw [signVariations]; rw [signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2))]; rw [← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

Depends on / 依赖: List.comp_map, coeffList_C_mul, comp_map, lt_of_le_of_ne, lt_or_lt_iff_ne, lt_or_lt_iff_ne.mp, signVariations, sign_mul
-/
theorem signVariations_C_mul (P : Polynomial R) (hx : η != 0) :
    signVariations (C η * P) = signVariations P := by
  wlog! hx2 : 0 < η
  · simpa [lt_of_le_of_ne hx2, hx] using this (η := -η) (P := -P)
  rw [signVariations]; rw [signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2))]; rw [← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

/--
lemma `signVariations_eraseLead_mul_X_sub_C` / 引理 `signVariations_eraseLead_mul_X_sub_C`

English:
lemma signVariations_eraseLead_mul_X_sub_C
  statement: (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
  proof: by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P != 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0]; rw [natDegree_X_sub_C]; rw [add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead != 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0]; rw [natDegree_X_sub_C]; rw [add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ]; rw [sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP]; rw [natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [signVariations]; rw [signVariations]; rw [this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by lia
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0]; rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP]; rw [hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne]; rw [← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ]; rw [mul_sub]; rw [sub_mul]; rw [sub_mul]; rw [X_mul_monomial]; rw [C_mul_monomial]; rw [monomial_sub]
  rw [leadingCoeff]; rw [nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos)]; rw [hd]; rw [Nat.add_sub_cancel]
  abel

中文:
引理 signVariations_eraseLead_mul_X_sub_C
  结论: (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
  证明: by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P != 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0]; rw [natDegree_X_sub_C]; rw [add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead != 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0]; rw [natDegree_X_sub_C]; rw [add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ]; rw [sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP]; rw [natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [signVariations]; rw [signVariations]; rw [this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by lia
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0]; rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP]; rw [hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne]; rw [← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ]; rw [mul_sub]; rw [sub_mul]; rw [sub_mul]; rw [X_mul_monomial]; rw [C_mul_monomial]; rw [monomial_sub]
  rw [leadingCoeff]; rw [nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos)]; rw [hd]; rw [Nat.add_sub_cancel]
  abel

Depends on / 依赖: Nat.exists_eq_add_one.mpr, P.eraseLead, P.natDegree, X_sub_C_ne_zero, add_comm, eraseLead, exists_eq_add_one, hc.ne, hndxeP, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mp, natDegree, natDegree_X_sub_C, natDegree_mul, natDegree_pos_of_nextCoeff_ne_zero, nextCoeff_eq_zero_of_eraseLead_eq_zero
-/
lemma signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.signVariations = ((X - C η) * P.eraseLead).signVariations := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P != 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0]; rw [natDegree_X_sub_C]; rw [add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead != 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0]; rw [natDegree_X_sub_C]; rw [add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ]; rw [sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP]; rw [natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [signVariations]; rw [signVariations]; rw [this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by lia
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0]; rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP]; rw [hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne]; rw [← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ]; rw [mul_sub]; rw [sub_mul]; rw [sub_mul]; rw [X_mul_monomial]; rw [C_mul_monomial]; rw [monomial_sub]
  rw [leadingCoeff]; rw [nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos)]; rw [hd]; rw [Nat.add_sub_cancel]
  abel

/--
lemma `succ_signVariations_X_sub_C_mul_monomial` / 引理 `succ_signVariations_X_sub_C_mul_monomial`

English:
lemma succ_signVariations_X_sub_C_mul_monomial
  given: {d c} (hc : c != 0) (hη : 0 < η)
  proof: by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) != 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c != SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using! List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

中文:
引理 succ_signVariations_X_sub_C_mul_monomial
  条件: {d c} (hc : c != 0) (hη : 0 < η)
  证明: by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) != 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c != SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using! List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

Depends on / 依赖: Left.sign_neg, List.destutter_cons_cons, SignType, SignType.sign, X_sub_C_ne_zero, coeff_mul_monomial, convert, destutter_cons_cons, eraseLead, leadingCoeff_cons_erase, monomial, natDegree_mul, nextCoeff, nextCoeff_eq_zero_of_eraseLead_eq_zero, signVariations, sign_mul, sign_neg
-/
lemma succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c != 0) (hη : 0 < η) :
    (monomial d c).signVariations + 1 <= ((X - C η) * monomial d c).signVariations := by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) != 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c != SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using! List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

/--
lemma `exists_cons_of_leadingCoeff_pos` / 引理 `exists_cons_of_leadingCoeff_pos`

English:
lemma exists_cons_of_leadingCoeff_pos
  given: (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff != 0)
  proof: by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) != 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead != 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃]; rw [natDegree_X_sub_C]; rw [add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

中文:
引理 存在_cons_of_leadingCoeff_pos
  条件: (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff != 0)
  证明: by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) != 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead != 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃]; rw [natDegree_X_sub_C]; rw [add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]
-/
private lemma exists_cons_of_leadingCoeff_pos (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff != 0) :
    exists c₀ cs, ((X - C η) * P).coeffList = P.leadingCoeff :: c₀ :: cs ∧
      ((X - C η) * P.eraseLead).coeffList = P.nextCoeff :: cs := by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) != 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead != 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃]; rw [natDegree_X_sub_C]; rw [add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

/--
lemma `signVariations_X_sub_C_mul_eraseLead_le` / 引理 `signVariations_X_sub_C_mul_eraseLead_le`

English:
lemma signVariations_X_sub_C_mul_eraseLead_le
  given: (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff)
  proof: by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x => decide (x != 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

中文:
引理 signVariations_X_sub_C_mul_eraseLead_le
  条件: (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff)
  证明: by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x => decide (x != 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

Depends on / 依赖: List.destutter, List.filter_cons, List.filter_cons_of_pos, List.length_pos_of_ne_nil, List.map_cons, Nat.sub_add_cancel, SignType, SignType.sign, _cons, _ne_nil, coefficient, destutter, exists_cons_of_leadingCoeff_pos, filter_cons, filter_cons_of_pos, identical, length_pos_of_ne_nil, map_cons, nonzero, signVariations
-/
lemma signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff) :
    signVariations ((X - C η) * P.eraseLead) <= signVariations ((X - C η) * P) := by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x => decide (x != 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

-- TODO: fix non-terminal simp below; simp followed by rfl
set_option linter.flexible false in
/--
theorem `succ_signVariations_le_X_sub_C_mul` / 定理 `succ_signVariations_le_X_sub_C_mul`

English:
theorem succ_signVariations_le_X_sub_C_mul
  given: (hη : 0 < η) (hP : P != 0)
  proof: by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with | _ d ih =>
  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])
  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P != 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP]; rw [natDegree_X_sub_C]; rw [add_comm]
  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      simp_all [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt]
    dsimp [signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP]; rw [withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]
  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul
  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]
  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]
  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]
    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : signVariations ((X - C η) * P).eraseLead + 1 =
          signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations <=
          ((X - C η) * P).eraseLead.signVariations := by
        have := signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [signVariations_le_eraseLead_succ]
  all_goals (
    have h₁ : nextCoeff P != 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl)
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]

中文:
定理 succ_signVariations_le_X_sub_C_mul
  条件: (hη : 0 < η) (hP : P != 0)
  证明: by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with | _ d ih =>
  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])
  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P != 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP]; rw [natDegree_X_sub_C]; rw [add_comm]
  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      simp_all [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt]
    dsimp [signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP]; rw [withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]
  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul
  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]
  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]
  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]
    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : signVariations ((X - C η) * P).eraseLead + 1 =
          signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations <=
          ((X - C η) * P).eraseLead.signVariations := by
        have := signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [signVariations_le_eraseLead_succ]
  all_goals (
    have h₁ : nextCoeff P != 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl)
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]
-/
theorem succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P != 0) :
    signVariations P + 1 <= signVariations ((X - C η) * P) := by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with | _ d ih =>
  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])
  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P != 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP]; rw [natDegree_X_sub_C]; rw [add_comm]
  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      simp_all [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt]
    dsimp [signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP]; rw [withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]
  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul
  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]
  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]
  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]
    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : signVariations ((X - C η) * P).eraseLead + 1 =
          signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations <=
          ((X - C η) * P).eraseLead.signVariations := by
        have := signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [signVariations_le_eraseLead_succ]
  all_goals (
    have h₁ : nextCoeff P != 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl)
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]

end StrictOrderedRing
section CommStrictOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

/--
theorem `roots_countP_pos_le_signVariations` / 定理 `roots_countP_pos_le_signVariations`

English:
theorem roots_countP_pos_le_signVariations
  statement: P.roots.countP (0 < ·) <= signVariations P
  proof: by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P -- Induct on number of roots.
  · exact zero_le
  rename_i ih
  have hp : P != 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : exists x, x in P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

中文:
定理 roots_countP_pos_le_signVariations
  结论: P.roots.countP (0 < ·) <= signVariations P
  证明: by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P -- Induct on number of roots.
  · exact zero_le
  rename_i ih
  have hp : P != 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : exists x, x in P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

Depends on / 依赖: Induct, Multiset, Multiset.countP_zero, P.roots.countP, countP, countP_zero, generalize, generalizing, num_pos_roots, number, rename_i, roots_zero, zero_le
-/
theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) <= signVariations P := by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P -- Induct on number of roots.
  · exact zero_le
  rename_i ih
  have hp : P != 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : exists x, x in P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

end CommStrictOrderedRing
end Polynomial
