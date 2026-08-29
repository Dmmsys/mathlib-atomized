/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Spectrum mapping theorem

This file develops and proves the spectral mapping theorem for polynomials over algebraically closed
fields. In particular, if `a` is an element of a `𝕜`-algebra `A` where `𝕜` is a field, and
`p : 𝕜[X]` is a polynomial, then the spectrum of `Polynomial.aeval a p` contains the image of the
spectrum of `a` under `(fun k ↦ Polynomial.eval k p)`. When `𝕜` is algebraically closed,
these are in fact equal (assuming either that the spectrum of `a` is nonempty or the polynomial
has positive degree), which is the **spectral mapping theorem**.

In addition, this file contains the fact that every element of a finite-dimensional nontrivial
algebra over an algebraically closed field has nonempty spectrum. In particular, this is used in
`Module.End.exists_eigenvalue` to show that every linear map from a vector space to itself has an
eigenvalue.

## Main statements

* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the **spectral mapping theorem**.
* `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`: the spectrum is nonempty for any
  element of a nontrivial finite-dimensional algebra over an algebraically closed field.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

public section

namespace spectrum

open Set Polynomial

open scoped Pointwise Polynomial

universe u v

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R
local notation "↑ₐ" => algebraMap R A

/--
theorem `exists_mem_of_not_isUnit_aeval_prod` / 定理 `exists_mem_of_not_isUnit_aeval_prod`

English:
theorem exists_mem_of_not_isUnit_aeval_prod
  statement: [IsDomain R] {p : R[X]} {a : A}
  proof: by
  rw [← Multiset.prod_toList]; rw [map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩

中文:
定理 存在_mem_of_not_isUnit_aeval_prod
  结论: [是整环 R] {p : R[X]} {a : A}
  证明: by
  rw [← Multiset.prod_toList]; rw [map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩

Depends on / 依赖: IsUnit, IsUnit.sub_iff, List.mem_map, List.prod_isUnit, Multiset, Multiset.mem_map, Multiset.mem_toList, Multiset.prod_toList, aeval_C, aeval_X, exists_exists_and_eq_and, exists_prop, map_list_prod, map_sub, mem_iff, mem_map, mem_roots, mem_toList, not_forall, prod_isUnit
-/
theorem exists_mem_of_not_isUnit_aeval_prod [IsDomain R] {p : R[X]} {a : A}
    (h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)) :
    exists k : R, k in σ a ∧ eval k p = 0 := by
  rw [← Multiset.prod_toList]; rw [map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

open Polynomial

/--
theorem `subset_polynomial_aeval` / 定理 `subset_polynomial_aeval`

English:
theorem subset_polynomial_aeval
  given: (a : A) (p : 𝕜[X])
  statement: (eval · p) '' σ a subseteq σ (aeval a p)
  proof: by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : IsRoot q k := by simp only [q, eval_C, eval_sub, sub_self, IsRoot.def]
  rw [← mul_div_eq_iff_isRoot]; rw [← neg_mul_neg]; rw [neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [q, aeval_C, map_sub]
  rw [mem_iff]; rw [aeval_q_eq]; rw [← hroot]; rw [aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, map_sub] using! hk

中文:
定理 subset_polynomial_aeval
  条件: (a : A) (p : 𝕜[X])
  结论: (eval · p) '' σ a subseteq σ (aeval a p)
  证明: by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : IsRoot q k := by simp only [q, eval_C, eval_sub, sub_self, IsRoot.def]
  rw [← mul_div_eq_iff_isRoot]; rw [← neg_mul_neg]; rw [neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [q, aeval_C, map_sub]
  rw [mem_iff]; rw [aeval_q_eq]; rw [← hroot]; rw [aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, map_sub] using! hk

Depends on / 依赖: Commute, Commute.all, IsRoot, IsRoot.def, aeval_C, aeval_mul, aeval_q_eq, eval_C, eval_sub, hcomm.isUnit_mul_iff.mp, isUnit_mul_iff, map_sub, mem_iff, mul_div_eq_iff_isRoot, neg_mul_neg, neg_sub, sub_self
-/
theorem subset_polynomial_aeval (a : A) (p : 𝕜[X]) : (eval · p) '' σ a subseteq σ (aeval a p) := by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : IsRoot q k := by simp only [q, eval_C, eval_sub, sub_self, IsRoot.def]
  rw [← mul_div_eq_iff_isRoot]; rw [← neg_mul_neg]; rw [neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [q, aeval_C, map_sub]
  rw [mem_iff]; rw [aeval_q_eq]; rw [← hroot]; rw [aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, map_sub] using! hk

/--
theorem `map_polynomial_aeval_of_degree_pos` / 定理 `map_polynomial_aeval_of_degree_pos`

English:
theorem map_polynomial_aeval_of_degree_pos
  statement: [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
  proof: by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := (IsAlgClosed.splits (C k - p)).eq_prod_roots
have h_ne : C k - p != 0 := ne_zero_of_degree_gt by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, map_sub]
  rw [mem_iff]; rw [← p_a_eq]; rw [hprod]; rw [aeval_mul]; rw [((Commute.all _ _).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩

中文:
定理 map_polynomial_aeval_of_degree_pos
  结论: [是代数闭 𝕜] (a : A) (p : 𝕜[X])
  证明: by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := (IsAlgClosed.splits (C k - p)).eq_prod_roots
have h_ne : C k - p != 0 := ne_zero_of_degree_gt by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, map_sub]
  rw [mem_iff]; rw [← p_a_eq]; rw [hprod]; rw [aeval_mul]; rw [((Commute.all _ _).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩
-/
theorem map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hdeg : 0 < degree p) : σ (aeval a p) = (eval · p) '' σ a := by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := (IsAlgClosed.splits (C k - p)).eq_prod_roots
have h_ne : C k - p != 0 := ne_zero_of_degree_gt by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, map_sub]
  rw [mem_iff]; rw [← p_a_eq]; rw [hprod]; rw [aeval_mul]; rw [((Commute.all _ _).map (aeval a : 𝕜[X] ->ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩

/--
theorem `map_polynomial_aeval_of_nonempty` / 定理 `map_polynomial_aeval_of_nonempty`

English:
theorem map_polynomial_aeval_of_nonempty
  statement: [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
  proof: by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]

中文:
定理 map_polynomial_aeval_of_nonempty
  结论: [是代数闭 𝕜] (a : A) (p : 𝕜[X])
  证明: by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]

Depends on / 依赖: Nonempty, Or.elim, Set.Nonempty.image_const, aeval_C, degree, eq_C_of_degree_le_zero, eval_C, image_const, le_or_gt, map_polynomial_aeval_of_degree_pos, nontriviality, scalar_eq
-/
theorem map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hnon : (σ a).Nonempty) : σ (aeval a p) = (fun k => eval k p) '' σ a := by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]

/--
theorem `pow_image_subset` / 定理 `pow_image_subset`

English:
theorem pow_image_subset
  given: (a : A) (n : Nat)
  statement: (fun x => x ^ n) '' σ a subseteq σ (a ^ n)
  proof: by
  simpa only [eval_X_pow, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

中文:
定理 pow_image_subset
  条件: (a : A) (n : 自然数)
  结论: (fun x => x ^ n) '' σ a subseteq σ (a ^ n)
  证明: by
  simpa only [eval_X_pow, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

Depends on / 依赖: aeval_X_pow, eval_X_pow, subset_polynomial_aeval
-/
theorem pow_image_subset (a : A) (n : Nat) : (fun x => x ^ n) '' σ a subseteq σ (a ^ n) := by
  simpa only [eval_X_pow, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

/--
theorem `pow_mem_pow` / 定理 `pow_mem_pow`

English:
theorem pow_mem_pow
  given: (a : A) (n : Nat) {k : 𝕜} (hk : k in σ a)
  statement: k ^ n in σ (a ^ n)
  proof: pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩

中文:
定理 pow_mem_pow
  条件: (a : A) (n : 自然数) {k : 𝕜} (hk : k in σ a)
  结论: k ^ n in σ (a ^ n)
  证明: pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩

Depends on / 依赖: pow_image_subset
-/
theorem pow_mem_pow (a : A) (n : Nat) {k : 𝕜} (hk : k in σ a) : k ^ n in σ (a ^ n) :=
  pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩

/--
theorem `map_pow_of_pos` / 定理 `map_pow_of_pos`

English:
theorem map_pow_of_pos
  given: [IsAlgClosed 𝕜] (a : A) {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [aeval_X_pow, eval_X_pow]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])

中文:
定理 map_pow_of_pos
  条件: [是代数闭 𝕜] (a : A) {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [aeval_X_pow, eval_X_pow]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])

Depends on / 依赖: Nat.cast_pos, aeval_X_pow, cast_pos, degree_X_pow, eval_X_pow, map_polynomial_aeval_of_degree_pos
-/
theorem map_pow_of_pos [IsAlgClosed 𝕜] (a : A) {n : Nat} (hn : 0 < n) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])

/--
theorem `map_pow_of_nonempty` / 定理 `map_pow_of_nonempty`

English:
theorem map_pow_of_nonempty
  given: [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : Nat)
  proof: by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

中文:
定理 map_pow_of_nonempty
  条件: [是代数闭 𝕜] {a : A} (ha : (σ a).非空) (n : 自然数)
  证明: by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

Depends on / 依赖: aeval_X_pow, eval_X_pow, map_polynomial_aeval_of_nonempty
-/
theorem map_pow_of_nonempty [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : Nat) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

variable (𝕜)

-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
/--
theorem `nonempty_of_isAlgClosed_of_finiteDimensional` / 定理 `nonempty_of_isAlgClosed_of_finiteDimensional`

English:
theorem nonempty_of_isAlgClosed_of_finiteDimensional
  statement: [IsAlgClosed 𝕜] [Nontrivial A]
  proof: by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic h_mon] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩

中文:
定理 nonempty_of_isAlgClosed_of_finiteDimensional
  结论: [是代数闭 𝕜] [非平凡 A]
  证明: by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic h_mon] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, IsNoetherian, IsNoetherian.iff_fg, IsUnit, aeval_def, eq_prod_roots_of_monic, exists_mem_of_not_isUnit_aeval_prod, h_eval_p, h_mon, iff_fg, isIntegral_of_noetherian, splits
-/
theorem nonempty_of_isAlgClosed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A]
    [I : FiniteDimensional 𝕜 A] (a : A) : (σ a).Nonempty := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic h_mon] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩

end ScalarField

end spectrum

open Polynomial in
/--
theorem `IsIdempotentElem.spectrum_subset` / 定理 `IsIdempotentElem.spectrum_subset`

English:
theorem IsIdempotentElem.spectrum_subset
  statement: (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  proof: by
  nontriviality A
.trans apply Set.image_subset_iff.mp (spectrum.subset_polynomial_aeval p (X ^ 2 - X))
  refine fun a ha => eq_zero_or_one_of_sq_eq_self ?_
  simpa [pow_two p, hp.eq, sub_eq_zero] using ha

中文:
定理 IsIdempotentElem.spectrum_subset
  结论: (𝕜 : 类型) {A : 类型} [域 𝕜] [环 A] [代数 𝕜 A]
  证明: by
  nontriviality A
.trans apply Set.image_subset_iff.mp (spectrum.subset_polynomial_aeval p (X ^ 2 - X))
  refine fun a ha => eq_zero_or_one_of_sq_eq_self ?_
  simpa [pow_two p, hp.eq, sub_eq_zero] using ha

Depends on / 依赖: Set.image_subset_iff.mp, eq_zero_or_one_of_sq_eq_self, hp.eq, image_subset_iff, nontriviality, pow_two, spectrum, spectrum.subset_polynomial_aeval, sub_eq_zero, subset_polynomial_aeval
-/
theorem IsIdempotentElem.spectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : spectrum 𝕜 p subseteq {0, 1} := by
  nontriviality A
.trans apply Set.image_subset_iff.mp (spectrum.subset_polynomial_aeval p (X ^ 2 - X))
  refine fun a ha => eq_zero_or_one_of_sq_eq_self ?_
  simpa [pow_two p, hp.eq, sub_eq_zero] using ha

/--
lemma `IsIdempotentElem.finite_spectrum` / 引理 `IsIdempotentElem.finite_spectrum`

English:
lemma IsIdempotentElem.finite_spectrum
  statement: (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  proof: have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.spectrum_subset 𝕜))

中文:
引理 IsIdempotentElem.finite_spectrum
  结论: (𝕜 : 类型) {A : 类型} [域 𝕜] [环 A] [代数 𝕜 A]
  证明: have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.spectrum_subset 𝕜))

Depends on / 依赖: Set.encard_le_encard, Set.encard_pair, Set.finite_of_encard_le_coe, encard, encard_le_encard, encard_pair, finite_of_encard_le_coe, hp.spectrum_subset, spectrum_subset
-/
lemma IsIdempotentElem.finite_spectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : (spectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.spectrum_subset 𝕜))

open Unitization in
/--
theorem `IsIdempotentElem.quasispectrum_subset` / 定理 `IsIdempotentElem.quasispectrum_subset`

English:
theorem IsIdempotentElem.quasispectrum_subset
  statement: (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
  proof: quasispectrum_eq_spectrum_inr' 𝕜 𝕜 p ▸ (hp.inr _ |>.spectrum_subset _)

中文:
定理 IsIdempotentElem.quasispectrum_subset
  结论: (𝕜 : 类型) {A : 类型} [域 𝕜] [非幺环 A]
  证明: quasispectrum_eq_spectrum_inr' 𝕜 𝕜 p ▸ (hp.inr _ |>.spectrum_subset _)

Depends on / 依赖: hp.inr, quasispectrum_eq_spectrum_inr, spectrum_subset
-/
theorem IsIdempotentElem.quasispectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    quasispectrum 𝕜 p subseteq {0, 1} :=
  quasispectrum_eq_spectrum_inr' 𝕜 𝕜 p ▸ (hp.inr _ |>.spectrum_subset _)

/--
theorem `IsIdempotentElem.finite_quasispectrum` / 定理 `IsIdempotentElem.finite_quasispectrum`

English:
theorem IsIdempotentElem.finite_quasispectrum
  statement: (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
  proof: have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.quasispectrum_subset 𝕜))

中文:
定理 IsIdempotentElem.finite_quasispectrum
  结论: (𝕜 : 类型) {A : 类型} [域 𝕜] [非幺环 A]
  证明: have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.quasispectrum_subset 𝕜))

Depends on / 依赖: Set.encard_le_encard, Set.encard_pair, Set.finite_of_encard_le_coe, encard, encard_le_encard, encard_pair, finite_of_encard_le_coe, hp.quasispectrum_subset, quasispectrum_subset
-/
theorem IsIdempotentElem.finite_quasispectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    (quasispectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : Nat) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.quasispectrum_subset 𝕜))
