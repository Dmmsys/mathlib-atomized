/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Johan Commelin, Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Irreducibility of linear and quadratic polynomials

* `MvPolynomial.irreducible_of_totalDegree_eq_one`:
  a multivariate polynomial of `totalDegree` one is irreducible
  if its coefficients are relatively prime.

* For `c : n →₀ R`, `MvPolynomial.sumSMulX c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sumSMulX` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sumSMulX c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sumXSMulY c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sumSMulXSMulY` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sumSMulXSMulY c` is irreducible.

## TODO

* Treat the case of diagonal quadratic polynomials,
  $ \sum c_i X_i ^ 2$. For irreducibility, one will need that
  there are at least 3 nonzero values of `c`,
  and that the only common divisors to all `c i` are units.

* Addition of quadratic polynomial of both kinds are relevant too.

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

open scoped Polynomial in
attribute [local simp] MvPolynomial.optionEquivLeft_X_none in -- tag simp globally?
/--
lemma `irreducible_mul_X_add` / 引理 `irreducible_mul_X_add`

English:
lemma irreducible_mul_X_add
  statement: {n : Type*} {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  classical
  let S := MvPolynomial { j // j != i } R
  let e : MvPolynomial n R ≃ₐ[R] S[X] :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)
  have he : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (↑) := by ext; simp [e, S]
  obtain ⟨f, rfl⟩ : f in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  obtain ⟨g, rfl⟩ : g in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  refine .of_map (f := e) ?_
  simpa [e, S] using Polynomial.irreducible_C_mul_X_add_C (by aesop)
    (IsRelPrime.of_map Polynomial.C (IsRelPrime.of_map e.symm h))

中文:
引理 irreducible_mul_X_add
  结论: {n : 类型} {R : 类型} [交换环 R] [是整环 R]
  证明: by
  classical
  let S := MvPolynomial { j // j != i } R
  let e : MvPolynomial n R ≃ₐ[R] S[X] :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)
  have he : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (↑) := by ext; simp [e, S]
  obtain ⟨f, rfl⟩ : f in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  obtain ⟨g, rfl⟩ : g in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  refine .of_map (f := e) ?_
  simpa [e, S] using Polynomial.irreducible_C_mul_X_add_C (by aesop)
    (IsRelPrime.of_map Polynomial.C (IsRelPrime.of_map e.symm h))

Depends on / 依赖: CAlgHom, Equiv.optionSubtypeNe, MvPolynomial, Polynomial, Polynomial.CAlgHom, Set.subset_def, Subtype, Subtype.val_injective, classical, e.symm.toAlgHom.comp, exists_rename_eq_of_vars_subset_range, optionEquivLeft, optionSubtypeNe, renameEquiv, subset_def, toAlgHom, val_injective
-/
lemma irreducible_mul_X_add {n : Type*} {R : Type*} [CommRing R] [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f != 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : IsRelPrime f g) :
    Irreducible (f * X i + g) := by
  classical
  let S := MvPolynomial { j // j != i } R
  let e : MvPolynomial n R ≃ₐ[R] S[X] :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)
  have he : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (↑) := by ext; simp [e, S]
  obtain ⟨f, rfl⟩ : f in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  obtain ⟨g, rfl⟩ : g in (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  refine .of_map (f := e) ?_
  simpa [e, S] using Polynomial.irreducible_C_mul_X_add_C (by aesop)
    (IsRelPrime.of_map Polynomial.C (IsRelPrime.of_map e.symm h))

/--
lemma `irreducible_of_disjoint_support` / 引理 `irreducible_of_disjoint_support`

English:
lemma irreducible_of_disjoint_support
  statement: [IsDomain R]
  proof: by
  classical
  have hfd : f.coeff d != 0 := by simpa using hd
  let d₀ := d.erase i
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hφ : φ * X i = monomial d (f.coeff d) := by
    nth_rw 1 [← Finsupp.erase_add_single i d]; simp [φ, monomial_add_single, hdi, d₀]
  have hdψ (k) : ψ.coeff k = if d = k then 0 else f.coeff k := by
    simp +contextual [ψ, hφ, sub_eq_iff_eq_add, ite_add_ite]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · suffices forall x, d != x -> x in f.support -> i ∉ x.support by
      simpa [mem_vars_iff_mem_support, hdψ] using this
    exact fun x hxd hx hix =>
      Finset.disjoint_iff_ne.mp (disjoint hd hx hxd) i (by simp [hdi]) _ hix rfl
  · rintro p hpφ ⟨q, hq⟩
    obtain ⟨m, b, hm, hb, rfl⟩ := (dvd_monomial_iff_exists hfd).mp hpφ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      have aux : coeff d₂ ψ != 0 := by simpa [hdψ, H.symm] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      simpa using disjoint hd₂ hd H (Finsupp.support_mono aux.1)
        ((Finsupp.support_mono hm).trans (d.support.erase_subset i))
    have hb' : IsUnit b := isPrimitive _ fun k =>
      if hk : k = d then hk ▸ hb else hf ▸ by simp [hq, hφ, Ne.symm hk]
    simpa

中文:
引理 irreducible_of_disjoint_support
  结论: [是整环 R]
  证明: by
  classical
  have hfd : f.coeff d != 0 := by simpa using hd
  let d₀ := d.erase i
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hφ : φ * X i = monomial d (f.coeff d) := by
    nth_rw 1 [← Finsupp.erase_add_single i d]; simp [φ, monomial_add_single, hdi, d₀]
  have hdψ (k) : ψ.coeff k = if d = k then 0 else f.coeff k := by
    simp +contextual [ψ, hφ, sub_eq_iff_eq_add, ite_add_ite]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · suffices forall x, d != x -> x in f.support -> i ∉ x.support by
      simpa [mem_vars_iff_mem_support, hdψ] using this
    exact fun x hxd hx hix =>
      Finset.disjoint_iff_ne.mp (disjoint hd hx hxd) i (by simp [hdi]) _ hix rfl
  · rintro p hpφ ⟨q, hq⟩
    obtain ⟨m, b, hm, hb, rfl⟩ := (dvd_monomial_iff_exists hfd).mp hpφ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      have aux : coeff d₂ ψ != 0 := by simpa [hdψ, H.symm] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      simpa using disjoint hd₂ hd H (Finsupp.support_mono aux.1)
        ((Finsupp.support_mono hm).trans (d.support.erase_subset i))
    have hb' : IsUnit b := isPrimitive _ fun k =>
      if hk : k = d then hk ▸ hb else hf ▸ by simp [hq, hφ, Ne.symm hk]
    simpa

Depends on / 依赖: Finsupp, Finsupp.erase_add_single, MvPolynomial, classical, contextual, d.erase, erase_add_single, f.coeff, irreducible_mul_X_a, ite_add_ite, monomial, monomial_add_single, nth_rw, sub_eq_iff_eq_add
-/
lemma irreducible_of_disjoint_support [IsDomain R]
    {f : MvPolynomial n R}
    (nontrivial : f.support.Nontrivial)
    {d : n ->₀ Nat} (hd : d in f.support) {i : n} (hdi : d i = 1)
    (disjoint : (f.support : Set (n ->₀ Nat)).PairwiseDisjoint Finsupp.support)
    (isPrimitive : forall r, (forall d, r ∣ f.coeff d) -> IsUnit r) :
    Irreducible f := by
  classical
  have hfd : f.coeff d != 0 := by simpa using hd
  let d₀ := d.erase i
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hφ : φ * X i = monomial d (f.coeff d) := by
    nth_rw 1 [← Finsupp.erase_add_single i d]; simp [φ, monomial_add_single, hdi, d₀]
  have hdψ (k) : ψ.coeff k = if d = k then 0 else f.coeff k := by
    simp +contextual [ψ, hφ, sub_eq_iff_eq_add, ite_add_ite]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · suffices forall x, d != x -> x in f.support -> i ∉ x.support by
      simpa [mem_vars_iff_mem_support, hdψ] using this
    exact fun x hxd hx hix =>
      Finset.disjoint_iff_ne.mp (disjoint hd hx hxd) i (by simp [hdi]) _ hix rfl
  · rintro p hpφ ⟨q, hq⟩
    obtain ⟨m, b, hm, hb, rfl⟩ := (dvd_monomial_iff_exists hfd).mp hpφ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      have aux : coeff d₂ ψ != 0 := by simpa [hdψ, H.symm] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      simpa using disjoint hd₂ hd H (Finsupp.support_mono aux.1)
        ((Finsupp.support_mono hm).trans (d.support.erase_subset i))
    have hb' : IsUnit b := isPrimitive _ fun k =>
      if hk : k = d then hk ▸ hb else hf ▸ by simp [hq, hφ, Ne.symm hk]
    simpa

end

section
/--
Instance `instModuleSelf` / 实例 `instModuleSelf`

English:
instance instModuleSelf
  signature: : Module R (MvPolynomial n R)
  body: inferInstanceAs Module R (AddMonoidAlgebra R (n ->₀ Nat))

中文:
实例 instModuleSelf
  签名: : 模 R (多元多项式 n R)
  定义体: inferInstanceAs Module R (AddMonoidAlgebra R (n ->₀ Nat))

Depends on / 依赖: AddMonoidAlgebra, Module
-/
noncomputable instance instModuleSelf : Module R (MvPolynomial n R) :=
inferInstanceAs Module R (AddMonoidAlgebra R (n ->₀ Nat))

/--
Definition of `sumSMulX` / `sumSMulX` 的定义

English:
definition sumSMulX
  signature: :
  body: Finsupp.linearCombination R X

中文:
定义 sumSMulX
  签名: :
  定义体: Finsupp.linearCombination R X

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination
-/
noncomputable def sumSMulX :
    (n ->₀ R) ->ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X

/--
theorem `coeff_sumSMulX` / 定理 `coeff_sumSMulX`

English:
theorem coeff_sumSMulX
  given: (i : n)
  proof: by
  classical
  rw [sumSMulX]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [coeff_sum]
  rw [Finset.sum_eq_single i _ (by simp)]
  · simp
  intro j hj hji
  rw [coeff_smul]; rw [coeff_X]; rw [if_neg]
  · simp
  · rwa [Finsupp.single_left_inj Nat.one_ne_zero]

中文:
定理 coeff_sumSMulX
  条件: (i : n)
  证明: by
  classical
  rw [sumSMulX]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [coeff_sum]
  rw [Finset.sum_eq_single i _ (by simp)]
  · simp
  intro j hj hji
  rw [coeff_smul]; rw [coeff_X]; rw [if_neg]
  · simp
  · rwa [Finsupp.single_left_inj Nat.one_ne_zero]

Depends on / 依赖: Finset, Finset.sum_eq_single, Finsupp, Finsupp.linearCombination_apply, Finsupp.single_left_inj, Finsupp.sum, Nat.one_ne_zero, classical, coeff_X, coeff_smul, coeff_sum, if_neg, linearCombination_apply, one_ne_zero, single_left_inj, sumSMulX, sum_eq_single
-/
theorem coeff_sumSMulX (i : n) :
    (sumSMulX c).coeff (Finsupp.single i 1) = c i := by
  classical
  rw [sumSMulX]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [coeff_sum]
  rw [Finset.sum_eq_single i _ (by simp)]
  · simp
  intro j hj hji
  rw [coeff_smul]; rw [coeff_X]; rw [if_neg]
  · simp
  · rwa [Finsupp.single_left_inj Nat.one_ne_zero]

/--
theorem `irreducible_sumSMulX` / 定理 `irreducible_sumSMulX`

English:
theorem irreducible_sumSMulX
  statement: [IsDomain R]
  proof: by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm
    · simp only [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
      apply totalDegree_finsetSum_le
      intros
      apply le_trans (totalDegree_smul_le ..)
      simp
    · rw [← not_lt, Nat.lt_one_iff, totalDegree_eq_zero_iff]
      intro h
      obtain ⟨i, hi⟩ := hc_nonempty
      simp only [Finsupp.mem_support_iff] at hi
      specialize h (Finsupp.single i 1) (by
        rwa [mem_support_iff, coeff_sumSMulX]) i
      simp only [Finsupp.single_eq_same, one_ne_zero] at h
  · intro r hr
    apply hc_gcd
    intro i
    simpa [coeff_sumSMulX] using hr (Finsupp.single i 1)

中文:
定理 irreducible_sumSMulX
  结论: [是整环 R]
  证明: by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm
    · simp only [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
      apply totalDegree_finsetSum_le
      intros
      apply le_trans (totalDegree_smul_le ..)
      simp
    · rw [← not_lt, Nat.lt_one_iff, totalDegree_eq_zero_iff]
      intro h
      obtain ⟨i, hi⟩ := hc_nonempty
      simp only [Finsupp.mem_support_iff] at hi
      specialize h (Finsupp.single i 1) (by
        rwa [mem_support_iff, coeff_sumSMulX]) i
      simp only [Finsupp.single_eq_same, one_ne_zero] at h
  · intro r hr
    apply hc_gcd
    intro i
    simpa [coeff_sumSMulX] using hr (Finsupp.single i 1)

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.mem_support_iff, Finsupp.single, Finsupp.single_eq_same, Finsupp.sum, Nat.lt_one_iff, coeff_sumSMulX, hc_nonempty, intros, irreducible_of_totalDegree_eq_one, le_antisymm, le_trans, linearCombination_apply, lt_one_iff, mem_support_iff, not_lt, one_ne_zero, single, single_eq_same
-/
theorem irreducible_sumSMulX [IsDomain R]
    (hc_nonempty : c.support.Nonempty)
    (hc_gcd : forall r, (forall i, r ∣ c i) -> IsUnit r) :
    Irreducible (sumSMulX c) := by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm
    · simp only [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
      apply totalDegree_finsetSum_le
      intros
      apply le_trans (totalDegree_smul_le ..)
      simp
    · rw [← not_lt, Nat.lt_one_iff, totalDegree_eq_zero_iff]
      intro h
      obtain ⟨i, hi⟩ := hc_nonempty
      simp only [Finsupp.mem_support_iff] at hi
      specialize h (Finsupp.single i 1) (by
        rwa [mem_support_iff, coeff_sumSMulX]) i
      simp only [Finsupp.single_eq_same, one_ne_zero] at h
  · intro r hr
    apply hc_gcd
    intro i
    simpa [coeff_sumSMulX] using hr (Finsupp.single i 1)

/--
Definition of `sumSMulXSMulY` / `sumSMulXSMulY` 的定义

English:
definition sumSMulXSMulY
  signature: :
  body: Finsupp.linearCombination R (fun i => X (.inl i) * X (.inr i))

中文:
定义 sumSMulXSMulY
  签名: :
  定义体: Finsupp.linearCombination R (fun i => X (.inl i) * X (.inr i))

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination
-/
noncomputable def sumSMulXSMulY :
    (n ->₀ R) ->ₗ[R] MvPolynomial (n oplus n) R :=
  Finsupp.linearCombination R (fun i => X (.inl i) * X (.inr i))

variable (c : n ->₀ R)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `irreducible_sumSMulXSMulY` / 定理 `irreducible_sumSMulXSMulY`

English:
theorem irreducible_sumSMulXSMulY
  statement: [IsDomain R]
  proof: by
  classical
  let ι : n ↪ ((n oplus n) ->₀ Nat) :=
    ⟨fun i => .single (.inl i) 1 + .single (.inr i) 1,
     fun i j => by simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  have aux : sumSMulXSMulY c = .ofCoeff (c.embDomain ι) := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sumSMulXSMulY, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sumSMulXSMulY c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sumSMulXSMulY c).support = c.support.map ι := by
    simp [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · rw [hsupp, Finset.coe_map, ι.injective.injOn.pairwiseDisjoint_image]
    suffices (c.support : Set n).PairwiseDisjoint fun x => {Sum.inl x, Sum.inr x} by
      simpa [ι, Function.comp_def, Finsupp.support_add_eq, Finsupp.support_single]
    simp [Set.PairwiseDisjoint, Set.Pairwise, ne_comm]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

中文:
定理 irreducible_sumSMulXSMulY
  结论: [是整环 R]
  证明: by
  classical
  let ι : n ↪ ((n oplus n) ->₀ Nat) :=
    ⟨fun i => .single (.inl i) 1 + .single (.inr i) 1,
     fun i j => by simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  have aux : sumSMulXSMulY c = .ofCoeff (c.embDomain ι) := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sumSMulXSMulY, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sumSMulXSMulY c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sumSMulXSMulY c).support = c.support.map ι := by
    simp [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · rw [hsupp, Finset.coe_map, ι.injective.injOn.pairwiseDisjoint_image]
    suffices (c.support : Set n).PairwiseDisjoint fun x => {Sum.inl x, Sum.inr x} by
      simpa [ι, Function.comp_def, Finsupp.support_add_eq, Finsupp.support_single]
    simp [Set.PairwiseDisjoint, Set.Pairwise, ne_comm]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

Depends on / 依赖: Finsup, Finsupp, Finsupp.embDomain, Finsupp.ext_iff, Finsupp.linearCombination_apply, Finsupp.single_apply, Finsupp.sum_embDomain, Finsupp.sum_single, c.embDomain, classical, contextual, embDomain, ext_iff, hcoeff, ite_eq_iff, linearCombination_apply, monomial_mul, ofCoeff, single, single_apply
-/
theorem irreducible_sumSMulXSMulY [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : forall r, (forall i, r ∣ c i) -> IsUnit r) :
    Irreducible (sumSMulXSMulY c) := by
  classical
  let ι : n ↪ ((n oplus n) ->₀ Nat) :=
    ⟨fun i => .single (.inl i) 1 + .single (.inr i) 1,
     fun i j => by simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  have aux : sumSMulXSMulY c = .ofCoeff (c.embDomain ι) := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sumSMulXSMulY, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sumSMulXSMulY c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sumSMulXSMulY c).support = c.support.map ι := by
    simp [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · rw [hsupp, Finset.coe_map, ι.injective.injOn.pairwiseDisjoint_image]
    suffices (c.support : Set n).PairwiseDisjoint fun x => {Sum.inl x, Sum.inr x} by
      simpa [ι, Function.comp_def, Finsupp.support_add_eq, Finsupp.support_single]
    simp [Set.PairwiseDisjoint, Set.Pairwise, ne_comm]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

end

end MvPolynomial
