/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Span

/-!
# Bounding the coefficients of the quotient and remainder of polynomials

This file proves that, for polynomials `p q : R[X]`, the coefficients of `p /ₘ q` and `p %ₘ q` can
be written as sums of products of coefficients of `p` and `q`.

Precisely, we show that each summand needs at most one coefficient of `p` and `deg p` coefficients
of `q`.
-/

public section

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

local notation3 "deg("p")" => natDegree p
local notation3 "coeffs("p")" => Set.range (coeff p)
local notation3 "spanCoeffs("p")" => 1 ⊔ Submodule.span R coeffs(p)

open Submodule Set in
/--
lemma `coeff_divModByMonicAux_mem_span_pow_mul_span` / 引理 `coeff_divModByMonicAux_mem_span_pow_mul_span`

English:
lemma coeff_divModByMonicAux_mem_span_pow_mul_span
  statement: forall (p q : S[X]) (hq : q.Monic) (i),
  proof: by
refine SetLike.le_def.mp ?_ subset_span mem_range_self i
      calc
        span R coeffs(p)
        _ = 1 ^ deg(p) * span R coeffs(p) := by simp
        _ <= spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, le_sup_right]
    split_ifs with hpq; swap
    · simpa using H₀ 

中文:
引理 coeff_divModByMonicAux_mem_span_pow_mul_span
  结论: 对任意 (p q : S[X]) (hq : q.Monic) (i),
  证明: by
refine SetLike.le_def.mp ?_ subset_span mem_range_self i
      calc
        span R coeffs(p)
        _ = 1 ^ deg(p) * span R coeffs(p) := by simp
        _ <= spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, le_sup_right]
    split_ifs with hpq; swap
    · simpa using H₀ 

Depends on / 依赖: SetLike, SetLike.le_def.mp, coeff_C_mul, coeff_X_pow, coeff_add, coeffs, degree_zero, divModByMonicAux, exacts, generalize, le_bot_iff, le_def, le_sup_left, le_sup_right, leadingCoeff, mem_range_self, mul_ite, mul_one, mul_zero, p.leadingCoeff
-/
lemma coeff_divModByMonicAux_mem_span_pow_mul_span : forall (p q : S[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i in spanCoeffs(q) ^ deg(p) * spanCoeffs(p) ∧
    (p.divModByMonicAux hq).2.coeff i in spanCoeffs(q) ^ deg(p) * spanCoeffs(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i in spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
refine SetLike.le_def.mp ?_ subset_span mem_range_self i
      calc
        span R coeffs(p)
        _ = 1 ^ deg(p) * span R coeffs(p) := by simp
        _ <= spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, le_sup_right]
    split_ifs with hpq; swap
    · simpa using H₀ _
    simp only [coeff_add, coeff_C_mul, coeff_X_pow]
    generalize hr : (p - q * (C p.leadingCoeff * X ^ (deg(p) - deg(q)))) = r
    by_cases hr' : r = 0
    · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero, le_bot_iff,
        degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, coeff_zero, add_zero,
        Submodule.zero_mem, and_true]
      split_ifs
      exacts [H₀ _, zero_mem _]
    have H : span R coeffs(r) <= span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p) := by
      rw [span_le]; rw [← hr]
      rintro _ ⟨i, rfl⟩
      rw [coeff_sub]; rw [← mul_assoc]; rw [coeff_mul_X_pow']; rw [coeff_mul_C]
      apply sub_mem
      · exact SetLike.le_def.mp le_sup_left (subset_span (mem_range_self _))
      · split_ifs
        · refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_) <;> exact subset_span ⟨_, rfl⟩
        · exact zero_mem _
    have deg_r_lt_deg_p : deg(r) < deg(p) := natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
    have H'' := calc
      spanCoeffs(q) ^ deg(r) * spanCoeffs(r)
      _ <= spanCoeffs(q) ^ deg(r) *
          (1 ⊔ (span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p))) := by gcongr
      _ <= spanCoeffs(q) ^ deg(r) * (spanCoeffs(q) * spanCoeffs(p)) := by
        gcongr
        simp only [sup_le_iff]
        refine ⟨one_le_mul le_sup_left le_sup_left, ?_, mul_le_mul' le_sup_right le_sup_right⟩
        rw [Submodule.sup_mul]; rw [one_mul]
        exact le_sup_of_le_left le_sup_right
      _ = spanCoeffs(q) ^ (deg(r) + 1) * spanCoeffs(p) := by rw [pow_succ, mul_assoc]
      _ <= spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, deg_r_lt_deg_p]
    refine ⟨add_mem ?_ ?_, ?_⟩
    · split_ifs <;> simp only [mul_one, mul_zero]
      exacts [H₀ _, zero_mem _]
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span r _ hq i).1
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span _ _ hq i).2
  termination_by p => deg(p)

/--
lemma `coeff_modByMonic_mem_pow_natDegree_mul` / 引理 `coeff_modByMonic_mem_pow_natDegree_mul`

English:
lemma coeff_modByMonic_mem_pow_natDegree_mul
  statement: (p q : S[X])
  proof: by
  delta modByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).2
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · rw [← one_mul (p.coeff i), ← one_pow p.natDegree]
    exact Submo

中文:
引理 coeff_modByMonic_mem_pow_natDegree_mul
  结论: (p q : S[X])
  证明: by
  delta modByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).2
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · rw [← one_mul (p.coeff i), ← one_pow p.natDegree]
    exact Submo

Depends on / 依赖: Set.range_subset_iff, SetLike, SetLike.le_def.mp, Submodule, Submodule.mul_mem_mul, Submodule.pow_mem_pow, Submodule.span_le, coeff_divModByMonicAux_mem_span_pow_mul_span, le_def, modByMonic, mul_mem_mul, natDegree, one_mul, one_pow, p.coeff, p.natDegree, pow_mem_pow, range_subset_iff, span_le, split_ifs
-/
lemma coeff_modByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : forall i, p.coeff i in Mp) (hp' : 1 in Mp)
    (Mq : Submodule R S) (hq : forall i, q.coeff i in Mq) (hq' : 1 in Mq) (i : Nat) :
    (p %ₘ q).coeff i in Mq ^ p.natDegree * Mp := by
  delta modByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).2
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · rw [← one_mul (p.coeff i), ← one_pow p.natDegree]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow Mq hq' _) (hp i)

/--
lemma `coeff_divByMonic_mem_pow_natDegree_mul` / 引理 `coeff_divByMonic_mem_pow_natDegree_mul`

English:
lemma coeff_divByMonic_mem_pow_natDegree_mul
  statement: (p q : S[X])
  proof: by
  delta divByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).1
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · simp

中文:
引理 coeff_divByMonic_mem_pow_natDegree_mul
  结论: (p q : S[X])
  证明: by
  delta divByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).1
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · simp

Depends on / 依赖: Set.range_subset_iff, SetLike, SetLike.le_def.mp, Submodule, Submodule.span_le, coeff_divModByMonicAux_mem_span_pow_mul_span, divByMonic, le_def, range_subset_iff, span_le, split_ifs, sup_le
-/
lemma coeff_divByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : forall i, p.coeff i in Mp) (hp' : 1 in Mp)
    (Mq : Submodule R S) (hq : forall i, q.coeff i in Mq) (hq' : 1 in Mq) (i : Nat) :
    (p /ₘ q).coeff i in Mq ^ p.natDegree * Mp := by
  delta divByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).1
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · simp

variable [DecidableEq ι] {i j : ι}

open Function Ideal in
/--
lemma `idealSpan_range_update_divByMonic` / 引理 `idealSpan_range_update_divByMonic`

English:
lemma idealSpan_range_update_divByMonic
  given: (hij : i != j) (v : ι -> R[X])
  proof: by
  rw [modByMonic_eq_sub_mul_div]; rw [mul_comm]; rw [← smul_eq_mul]; rw [Ideal.span]; rw [Ideal.span]; rw [Submodule.span_range_update_sub_smul hij]

中文:
引理 idealSpan_range_update_divByMonic
  条件: (hij : i != j) (v : ι -> R[X])
  证明: by
  rw [modByMonic_eq_sub_mul_div]; rw [mul_comm]; rw [← smul_eq_mul]; rw [Ideal.span]; rw [Ideal.span]; rw [Submodule.span_range_update_sub_smul hij]

Depends on / 依赖: Ideal.span, Submodule, Submodule.span_range_update_sub_smul, modByMonic_eq_sub_mul_div, mul_comm, smul_eq_mul, span_range_update_sub_smul
-/
lemma idealSpan_range_update_divByMonic (hij : i != j) (v : ι -> R[X]) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by
  rw [modByMonic_eq_sub_mul_div]; rw [mul_comm]; rw [← smul_eq_mul]; rw [Ideal.span]; rw [Ideal.span]; rw [Submodule.span_range_update_sub_smul hij]

end Polynomial
