/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
## Gauss's Lemma for Dedekind Domains

This file contains Gauss's Lemma for Dedekind Domains, which states that the content ideal of a
polynomial is the whole ring if and only if the `v`-adic Gauss norms of the polynomial are equal to
1 for all `v`.
-/

public section
namespace Polynomial

open IsDedekindDomain HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {b : NNReal}
  (hb : 1 < b) (p : R[X])

/--
theorem `gaussNorm_intAdicAbv_le_one` / 定理 `gaussNorm_intAdicAbv_le_one`

English:
theorem gaussNorm_intAdicAbv_le_one
  statement: p.gaussNorm (v.intAdicAbv hb) 1 <= 1
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  simp [gaussNorm, hp0, intAdicAbv_le_one]

中文:
定理 gaussNorm_intAdicAbv_le_one
  结论: p.gaussNorm (v.intAdicAbv hb) 1 <= 1
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  simp [gaussNorm, hp0, intAdicAbv_le_one]

Depends on / 依赖: gaussNorm, intAdicAbv_le_one
-/
theorem gaussNorm_intAdicAbv_le_one : p.gaussNorm (v.intAdicAbv hb) 1 <= 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  simp [gaussNorm, hp0, intAdicAbv_le_one]

/--
theorem `gaussNorm_lt_one_iff_contentIdeal_le` / 定理 `gaussNorm_lt_one_iff_contentIdeal_le`

English:
theorem gaussNorm_lt_one_iff_contentIdeal_le
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsupp_nonempty : p.support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, one_pow, mul_one, contentIdeal, Ideal.span_le,
    Set.subset_def, SetLike.mem_coe, ← v.intAdicAbv_lt_one_iff hb]
  constructor
  · 

中文:
定理 gaussNorm_lt_one_iff_contentIdeal_le
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsupp_nonempty : p.support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, one_pow, mul_one, contentIdeal, Ideal.span_le,
    Set.subset_def, SetLike.mem_coe, ← v.intAdicAbv_lt_one_iff hb]
  constructor
  · 

Depends on / 依赖: Finset, Finset.le_sup, Ideal.span_le, Nonempty, Set.subset_def, SetLike, SetLike.mem_coe, _of_le, and_imp, and_true, contentIdeal, contrapose, existsAndEq, forall_exists_index, gaussNorm, hsupp_nonempty, intAdicAbv, intAdicAbv_lt_one_iff, le_sup, mem_coe
-/
theorem gaussNorm_lt_one_iff_contentIdeal_le :
    p.gaussNorm (v.intAdicAbv hb) 1 < 1 ↔ p.contentIdeal <= v.asIdeal := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsupp_nonempty : p.support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, one_pow, mul_one, contentIdeal, Ideal.span_le,
    Set.subset_def, SetLike.mem_coe, ← v.intAdicAbv_lt_one_iff hb]
  constructor
  · contrapose!
    simp only [mem_coeffs_iff, mem_support_iff, ↓existsAndEq, and_true, forall_exists_index,
      and_imp]
    intro _ h1 h2
    exact Finset.le_sup'_of_le (fun n => (v.intAdicAbv hb) (p.coeff n)) (by simp [h1]) h2
  · intro h
    rw [Finset.sup'_lt_iff]
    intro n hn
    rw [mem_support_iff] at hn
exact h _ p.coeff_mem_coeffs hn

/--
theorem `contentIdeal_eq_top_iff_forall_gaussNorm_eq_one` / 定理 `contentIdeal_eq_top_iff_forall_gaussNorm_eq_one`

English:
theorem contentIdeal_eq_top_iff_forall_gaussNorm_eq_one
  given: (hR : ¬IsField R)
  proof: by
  convert_to _ ↔ forall (x : HeightOneSpectrum R), 1 <= gaussNorm (x.intAdicAbv hb) 1 p
  · grind [gaussNorm_intAdicAbv_le_one]
  simp [← not_iff_not, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

中文:
定理 contentIdeal_eq_top_iff_对任意_gaussNorm_eq_one
  条件: (hR : ¬是域 R)
  证明: by
  convert_to _ ↔ forall (x : HeightOneSpectrum R), 1 <= gaussNorm (x.intAdicAbv hb) 1 p
  · grind [gaussNorm_intAdicAbv_le_one]
  simp [← not_iff_not, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

Depends on / 依赖: HeightOneSpectrum, convert_to, gaussNorm, gaussNorm_intAdicAbv_le_one, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists, intAdicAbv, not_iff_not, x.intAdicAbv
-/
theorem contentIdeal_eq_top_iff_forall_gaussNorm_eq_one (hR : ¬IsField R) :
    p.contentIdeal = ⊤ ↔ forall v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  convert_to _ ↔ forall (x : HeightOneSpectrum R), 1 <= gaussNorm (x.intAdicAbv hb) 1 p
  · grind [gaussNorm_intAdicAbv_le_one]
  simp [← not_iff_not, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (hR : ¬IsField R)
  {b : NNReal} (hb : 1 < b) (p : R[X])

include hR in
/--
theorem `isPrimitive_iff_forall_gaussNorm_eq_one` / 定理 `isPrimitive_iff_forall_gaussNorm_eq_one`

English:
theorem isPrimitive_iff_forall_gaussNorm_eq_one
  proof: by
  rw [isPrimitive_iff_contentIdeal_eq_top]; rw [p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one hb hR]

中文:
定理 isPrimitive_iff_对任意_gaussNorm_eq_one
  证明: by
  rw [isPrimitive_iff_contentIdeal_eq_top]; rw [p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one hb hR]

Depends on / 依赖: contentIdeal_eq_top_iff_forall_gaussNorm_eq_one, isPrimitive_iff_contentIdeal_eq_top, p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one
-/
theorem isPrimitive_iff_forall_gaussNorm_eq_one :
    p.IsPrimitive ↔ forall v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  rw [isPrimitive_iff_contentIdeal_eq_top]; rw [p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one hb hR]

end Polynomial
