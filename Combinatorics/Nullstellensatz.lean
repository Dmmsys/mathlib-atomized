/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` :
  if `f` vanishes at any such point and `f.degreeOf s < #(S s)` for all `s`,
  then `f = 0`.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h`,
  for some `h : σ →₀ MvPolynomial σ R` such that
  `((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

- `combinatorial_nullstellensatz_exists_eval_nonzero`
  a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
  `f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
  there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

## TODO

- Applications
- relation with Schwartz–Zippel lemma, as in [Rote_2023]

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]

- [Rote, *The Generalized Combinatorial Lasoń-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

public section

open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

namespace MvPolynomial

open Finsupp Function

/--
theorem `eq_zero_of_eval_zero_at_prod_finset` / 定理 `eq_zero_of_eval_zero_at_prod_finset`

English:
theorem eq_zero_of_eval_zero_at_prod_finset
  statement: {σ : Type*} [Finite σ] [IsDomain R]
  proof: by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, th

中文:
定理 eq_zero_of_eval_zero_at_prod_finset
  结论: {σ : 类型} [Finite σ] [IsDomain R]
  证明: by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, th

Depends on / 依赖: Finite, Finite.induction_empty_option, MvPolynomial, MvPolynomial.eval_rename, MvPolynomial.rename, MvPolynomial.rename_injective, RingHom, RingHom.injective_iff_ker_eq_bot, RingHom.mem_ker, conv_lhs, convert, degreeOf_rename_of_injective, e.symm, e.symm.injective, e.symm_apply_apply, eval_rename, induction_empty_option, injective, injective_iff_ker_eq_bot, mem_ker
-/
theorem eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ -> Finset R)
    (Hdeg : forall i, P.degreeOf i < #(S i))
    (Heval : forall (x : σ -> R), (forall i, x i in S i) -> eval x P = 0) :
    P = 0 := by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, that] at this
    apply h _ (fun i => S (e i))
    · intro i
      convert! Hdeg (e i)
      conv_lhs => rw [← e.symm_apply_apply i, degreeOf_rename_of_injective e.symm.injective]
    · intro x hx
      simp only [MvPolynomial.eval_rename]
      apply Heval
      intro s
      simp only [Function.comp_apply]
      convert! hx (e.symm s)
      simp only [Equiv.apply_symm_apply]
  | h_empty =>
    suffices P = C (constantCoeff P) by
      specialize Heval default (fun i => PEmpty.elim i)
      rw [this]; rw [eval_C] at Heval
      rw [this]; rw [Heval]; rw [C_0]
    ext m
    suffices m = 0 by simp [this, ← constantCoeff_eq]
    ext d; exact PEmpty.elim d
  | @h_option σ _ h =>
    set Q := optionEquivLeft R σ P with hQ
    suffices Q = 0 by
      rw [← AlgEquiv.symm_apply_apply (optionEquivLeft R σ) P]; rw [← hQ]; rw [this]; rw [map_zero]
    have Heval' (x : σ -> R) (hx : forall i, x i in S (some i)) : Polynomial.map (eval x) Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S none)
      · intro y hy
        rw [← optionEquivLeft_elim_eval]
        apply Heval
        simp only [Option.forall, Option.elim_none, hy, Option.elim_some, hx, implies_true,
          and_self]
      · apply lt_of_le_of_lt _ (Hdeg none)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [hQ]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert! map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero]
        set n := (embDomain Function.Embedding.some m).update none d with hn
        rw [eq_option_embedding_update_none_iff] at hn
        rw [← hn.1]; rw [← hn.2]; rw [optionEquivLeft_coeff_some_coeff_none]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq]; rw [← MvPolynomial.mem_support_iff] at hm
        convert! Finset.le_sup hm
        exact hn.1.symm
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by simp only [this, coeff_zero]
    apply h _ (fun i => S (some i))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg (some i))
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      set n := (embDomain Function.Embedding.some e).update none m with hn
      rw [eq_option_embedding_update_none_iff] at hn
      rw [hQ]; rw [← hn.1]; rw [← hn.2]; rw [optionEquivLeft_coeff_some_coeff_none]; rw [← ne_eq]; rw [← MvPolynomial.mem_support_iff] at he
      convert! Finset.le_sup he
      rw [← hn.2]; rw [some_apply]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

open MonomialOrder

/- Here starts the actual proof of the combinatorial Nullstellensatz -/

variable {σ : Type*}

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Alon.P (S : Finset R) (i : σ)
  body: ∏ r in S, (X i - C r)

中文:
定义 noncomputable
  签名: def Alon.P (S : Finset R) (i : σ)
  定义体: ∏ r in S, (X i - C r)
-/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r in S, (X i - C r)

/--
theorem `Alon.degree_P` / 定理 `Alon.degree_P`

English:
theorem Alon.degree_P
  given: [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ)
  proof: by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ => m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

中文:
定理 Alon.degree_P
  条件: [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ)
  证明: by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ => m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one
-/
private theorem Alon.degree_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i #S := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ => m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

/--
theorem `Alon.monic_P` / 定理 `Alon.monic_P`

English:
theorem Alon.monic_P
  given: (m : MonomialOrder σ) (S : Finset R) (i : σ)
  proof: Monic.prod (fun r _ => m.monic_X_sub_C i r)

中文:
定理 Alon.monic_P
  条件: (m : MonomialOrder σ) (S : Finset R) (i : σ)
  证明: Monic.prod (fun r _ => m.monic_X_sub_C i r)
-/
private theorem Alon.monic_P (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.Monic (P S i) :=
  Monic.prod (fun r _ => m.monic_X_sub_C i r)

/--
lemma `Alon.of_mem_P_support` / 引理 `Alon.of_mem_P_support`

English:
lemma Alon.of_mem_P_support
  statement: {ι : Type*} (i : ι) (S : Finset R) (m : ι ->₀ Nat)
  proof: by
  classical
  have hP : Alon.P S i = .rename (fun _ => i) (Alon.P S ()) := by simp [Alon.P]
  rw [hP]; rw [support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  have : Nontrivial R := non

中文:
引理 Alon.of_mem_P_support
  结论: {ι : 类型} (i : ι) (S : Finset R) (m : ι ->₀ 自然数)
  证明: by
  classical
  have hP : Alon.P S i = .rename (fun _ => i) (Alon.P S ()) := by simp [Alon.P]
  rw [hP]; rw [support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  have : Nontrivial R := non
-/
private lemma Alon.of_mem_P_support {ι : Type*} (i : ι) (S : Finset R) (m : ι ->₀ Nat)
    (hm : m in (Alon.P S i).support) :
    exists e <= S.card, m = single i e := by
  classical
  have hP : Alon.P S i = .rename (fun _ => i) (Alon.P S ()) := by simp [Alon.P]
  rw [hP]; rw [support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  have : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () #S by
      simpa [MonomialOrder.lex_le_iff_of_unique] using this
    rw [← Alon.degree_P]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert! he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_of_notMem_range, single_eq_of_ne hj]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Finite σ]

/--
theorem `combinatorial_nullstellensatz_exists_linearCombination` / 定理 `combinatorial_nullstellensatz_exists_linearCombination`

English:
theorem combinatorial_nullstellensatz_exists_linearCombination
  proof: by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i => Alon.P (S i) i)
      (fun i => by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this]; rw [add_zero] at hf
    exact ⟨f

中文:
定理 combinatorial_nullstellensatz_exists_linearCombination
  证明: by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i => Alon.P (S i) i)
      (fun i => by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this]; rw [add_zero] at hf
    exact ⟨f

Depends on / 依赖: Alon.P, Alon.degree_P, Alon.monic_P, Finset, Finset.sup_lt_iff, Iff.s, LinearOrder, WellOrderingRel, WellOrderingRel.isWellOrder.linearOrder, add_zero, degLex, degLex.div, degLex_totalDegree_monotone, degreeOf_eq_sup, degree_P, eq_zero_of_eval_zero_at_prod_finset, isUnit_one, isWellOrder, leadingCoeff_eq_one, linearOrder
-/
theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] (S : σ -> Finset R) (Sne : forall i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : forall (x : σ -> R), (forall i, x i in S i) -> eval x f = 0) :
    exists (h : σ ->₀ MvPolynomial σ R),
      (forall i, ((∏ s in S i, (X i - C s)) * h i).totalDegree <= f.totalDegree) ∧
      f = linearCombination (MvPolynomial σ R) (fun i => ∏ r in S i, (X i - C r)) h := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i => Alon.P (S i) i)
      (fun i => by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this]; rw [add_zero] at hf
    exact ⟨fun i => degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod_finset r S
  · intro i
    rw [degreeOf_eq_sup]; rw [Finset.sup_lt_iff (by simp [Sne i])]
    aesop (add simp [Alon.degree_P])
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf]; rw [map_sub]; rw [Heval x hx]; rw [zero_sub]; rw [neg_eq_zero]; rw [linearCombination_apply]; rw [map_finsuppSum]; rw [Finsupp.sum]; rw [Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul]; rw [map_mul]
    convert! mul_zero _
    rw [Alon.P]; rw [_root_.map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp

/--
theorem `combinatorial_nullstellensatz_exists_eval_nonzero` / 定理 `combinatorial_nullstellensatz_exists_eval_nonzero`

English:
theorem combinatorial_nullstellensatz_exists_eval_nonzero
  statement: [IsDomain R]
  proof: by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  by_contra! Heval
  apply ht
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i => by rw [← Finset.card_pos]; exact Nat.zero_lt_of_lt (htS i)) f Heval
  rw [hf]
  rw [linearCombination_app

中文:
定理 combinatorial_nullstellensatz_exists_eval_nonzero
  结论: [IsDomain R]
  证明: by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  by_contra! Heval
  apply ht
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i => by rw [← Finset.card_pos]; exact Nat.zero_lt_of_lt (htS i)) f Heval
  rw [hf]
  rw [linearCombination_app

Depends on / 依赖: Alon.P, Finset, Finset.card_pos, Finset.sum_eq_zero, Finsupp, Finsupp.sum, LinearOrder, Nat.zero_lt_of_lt, WellOrderingRel, WellOrderingRel.isWellOrder.linearOrder, card_pos, coeff_sum, combinatorial_nullstellensatz_exists_linearCombination, f.totalDegree, g.totalDegree, isWellOrder, linearCombination_apply, linearOrder, mul_comm, sum_eq_zero
-/
theorem combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ ->₀ Nat) (ht : f.coeff t != 0) (ht' : f.totalDegree = t.degree)
    (S : σ -> Finset R) (htS : forall i, t i < #(S i)) :
    exists s : σ -> R, (forall i, s i in S i) ∧ eval s f != 0 := by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  by_contra! Heval
  apply ht
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i => by rw [← Finset.card_pos]; exact Nat.zero_lt_of_lt (htS i)) f Heval
  rw [hf]
  rw [linearCombination_apply]; rw [Finsupp.sum]; rw [coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * Alon.P (S i) i with hg
  by_cases hi : h i = 0
  · simp [hi]
  have : g.totalDegree <= f.totalDegree := by
    rw [hg]; rw [mul_comm]
    exact hh i
  -- one could simplify this by proving `totalDegree_mul_eq` (at least in a domain)
  rw [hg]; rw [← degree_degLexDegree]; rw [degree_mul_of_isRegular_right hi (by simp only [(Alon.monic_P ..).leadingCoeff_eq_one]; rw [isRegular_one]),
    Alon.degree_P, map_add, degree_degLexDegree, degree_single, ht'] at this
  rw [smul_eq_mul]; rw [coeff_mul]; rw [Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq]; rw [← mem_support_iff]
  intro hq
  obtain ⟨e, hq', hq⟩ := Alon.of_mem_P_support _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  rw [← Finsupp.degree_apply]
  apply lt_of_add_lt_add_right (lt_of_le_of_lt this _)
  rw [← hpq]; rw [map_add]; rw [add_lt_add_iff_left]; rw [hq]; rw [degree_single]
  apply lt_of_le_of_lt _ (htS i)
  simp [← hpq, hq]

end MvPolynomial
