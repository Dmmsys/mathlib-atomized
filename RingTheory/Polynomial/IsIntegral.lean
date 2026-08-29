/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!

# Results about coefficients of polynomials being integral

## Main results
- `Polynomial.isIntegral_coeff_of_dvd`: If a monic polynomial `p` divides another monic polynomial
  with integral coefficients, then the coefficients of `p` are themselves integral.
- `Polynomial.isIntegral_iff_isIntegral_coeff`:
  `p : S[X]` is integral over `R[X]` iff the coefficients of `p` are integral over `R`.
- `MvPolynomial.isIntegral_iff_isIntegral_coeff`: `p : MvPolynomial σ S` is integral over
  `MvPolynomial σ R` iff the coefficients of `p` are integral over `R`.
- We also provide the instance `[IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`.

-/

public section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

/--
lemma `isIntegral_coeff_prod` / 引理 `isIntegral_coeff_prod`

English:
lemma isIntegral_coeff_prod
  proof: by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has]; rw [coeff_mul]
    exact IsIntegral.sum _ fun i hi => .mul (H _ (by simp) _) (IH (fun _ _ => H _

中文:
引理 is整数egral_coeff_prod
  证明: by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has]; rw [coeff_mul]
    exact IsIntegral.sum _ fun i hi => .mul (H _ (by simp) _) (IH (fun _ _ => H _

Depends on / 依赖: Finset, Finset.induction, Finset.prod_insert, IsIntegral, IsIntegral.sum, apply_ite, classical, coeff_mul, coeff_one, generalizing, insert, isIntegral_one, isIntegral_zero, prod_insert
-/
lemma isIntegral_coeff_prod
    (s : Finset ι) (p : ι -> S[X]) (H : forall i in s, forall j, IsIntegral R ((p i).coeff j)) (j : Nat) :
    IsIntegral R ((s.prod p).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has]; rw [coeff_mul]
    exact IsIntegral.sum _ fun i hi => .mul (H _ (by simp) _) (IH (fun _ _ => H _ (by aesop)) _)

/--
lemma `isIntegral_coeff_of_factors` / 引理 `isIntegral_coeff_of_factors`

English:
lemma isIntegral_coeff_of_factors
  statement: (p : S[X])
  proof: by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm]; rw [Multiset.prod_eq_prod_coe]; rw [coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x in m) : p.IsRoot x := by
    rw [IsRoot]; rw [hm]; rw [eval_mul]; rw [eval_multiset_pro

中文:
引理 is整数egral_coeff_of_factors
  结论: (p : S[X])
  证明: by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm]; rw [Multiset.prod_eq_prod_coe]; rw [coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x in m) : p.IsRoot x := by
    rw [IsRoot]; rw [hm]; rw [eval_mul]; rw [eval_multiset_pro

Depends on / 依赖: IsIntegral, IsRoot, Multiset, Multiset.count_pos.mp, Multiset.mem_map.mp, Multiset.prod_eq_prod_coe, Multiset.prod_eq_zero, Polynomial, Polynomial.splits_iff_exists_multiset.mp, classical, coeff_C, coeff_C_mul, coeff_X, count_pos, eval_mul, eval_multiset_prod, i.zero_le.trans_lt, isIntegral_coeff_prod, mem_map, mul_zero
-/
lemma isIntegral_coeff_of_factors (p : S[X])
    (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits)
    (hpr : forall x, p.IsRoot x -> IsIntegral R x) (i : Nat) :
    IsIntegral R (p.coeff i) := by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm]; rw [Multiset.prod_eq_prod_coe]; rw [coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x in m) : p.IsRoot x := by
    rw [IsRoot]; rw [hm]; rw [eval_mul]; rw [eval_multiset_prod]; rw [Multiset.prod_eq_zero]; rw [mul_zero]
    simpa [sub_eq_zero]
  rintro ⟨a, ⟨i, hi⟩⟩ -
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (i.zero_le.trans_lt hi))
  simp [coeff_X, coeff_C, IsIntegral.sub, apply_ite (IsIntegral R),
    isIntegral_one, isIntegral_zero, hpr x (H hx)]

open scoped TensorProduct in
@[stacks 00H6 "(1)"]
/--
lemma `isIntegral_coeff_of_dvd` / 引理 `isIntegral_coeff_of_dvd`

English:
lemma isIntegral_coeff_of_dvd
  statement: (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
  proof: by
  nontriviality S
  obtain ⟨T, _, _, _, _, _, hqT⟩ := hq.exists_splits_map
  algebraize [(algebraMap S T).comp (algebraMap R S)]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S T)
    (FaithfulSMul.algebraMap_injective S _)).mp ?_
  rw [IsScalarTower.coe_toAlgHom']; rw [← coeff_map]
 

中文:
引理 is整数egral_coeff_of_dvd
  结论: (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
  证明: by
  nontriviality S
  obtain ⟨T, _, _, _, _, _, hqT⟩ := hq.exists_splits_map
  algebraize [(algebraMap S T).comp (algebraMap R S)]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S T)
    (FaithfulSMul.algebraMap_injective S _)).mp ?_
  rw [IsScalarTower.coe_toAlgHom']; rw [← coeff_map]
 

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, Polynomial, Polynomial.isIntegral_coeff_of_factors, aeval_eq_zero_of_dvd_aeval_eq_zero, algebraMap, algebraMap_injective, algebraize, coe_toAlgHom, coeff_map, exists_splits_map, hq.exists_splits_map, hq.map, isIntegral_algHom_iff, isIntegral_coeff_of_factors, isIntegral_one, nontriviality
-/
lemma isIntegral_coeff_of_dvd (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p.map (algebraMap R S)) (i : Nat) : IsIntegral R (q.coeff i) := by
  nontriviality S
  obtain ⟨T, _, _, _, _, _, hqT⟩ := hq.exists_splits_map
  algebraize [(algebraMap S T).comp (algebraMap R S)]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S T)
    (FaithfulSMul.algebraMap_injective S _)).mp ?_
  rw [IsScalarTower.coe_toAlgHom']; rw [← coeff_map]
  refine Polynomial.isIntegral_coeff_of_factors _ (by simp [hq.map, isIntegral_one]) hqT ?_ i
  intro x hx
  exact ⟨p, hp, by simpa using! aeval_eq_zero_of_dvd_aeval_eq_zero (x := x) H (by simp_all)⟩

end Polynomial

section

open scoped nonZeroDivisors

open Polynomial

attribute [local instance] Polynomial.algebra

@[stacks 00H0 "(1)"]
/--
lemma `IsAlmostIntegral.coeff` / 引理 `IsAlmostIntegral.coeff`

English:
lemma IsAlmostIntegral.coeff
  statement: [IsDomain R] [FaithfulSMul R S]
  proof: by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n => ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases 

中文:
引理 IsAlmost整数egral.coeff
  结论: [是整环 R] [忠实标量乘法 R S]
  证明: by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n => ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases 

Depends on / 依赖: Algebra, Algebra.smul_def, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsAlmostIntegral, algebraMap, algebraMap_def, algebraMap_injective, coe_mapRingHom, leadingCoeff, leadingCoeff_map_of_injective, p.leadingCoeff, q.leadingCoeff, r.leadingCoeff, smul_def
-/
lemma IsAlmostIntegral.coeff [IsDomain R] [FaithfulSMul R S]
    {p : S[X]} (hp : IsAlmostIntegral R[X] p) (i : Nat) :
    IsAlmostIntegral R (p.coeff i) := by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n => ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases h : algebraMap R S p.leadingCoeff * q.leadingCoeff ^ n = 0
    · simp [h]
    have h' : q.leadingCoeff ^ n != 0 := by aesop
    use r.leadingCoeff
    simp only [← leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective R S), hr] at h ⊢
    rw [← leadingCoeff_pow' h'] at h ⊢
    rw [leadingCoeff_mul' h]
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with | h n IH =>
  by_cases hp' : p.natDegree = 0
  · obtain ⟨p, rfl⟩ := natDegree_eq_zero.mp hp'
    simp only [coeff_C]
    split_ifs with h
    · simpa using H hp
    · exact (completeIntegralClosure R S).zero_mem
  by_cases hi : i = p.natDegree
  · simp [hi, H hp]
  have : IsAlmostIntegral R[X] p.eraseLead := by
    rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [← mem_completeIntegralClosure]; rw [← C_mul_X_pow_eq_monomial]; rw [← map_X (algebraMap R S)]; rw [← Polynomial.map_pow]
    refine sub_mem hp (mul_mem ?_ (algebraMap_mem (R := R[X]) _ _))
    obtain ⟨r, hr, hr'⟩ := H hp
    refine ⟨C r, by simpa using hr, fun n => ?_⟩
    obtain ⟨s, hs⟩ := hr' n
    exact ⟨C s, by simp [Algebra.smul_def, hs]⟩
  simpa [hi, eraseLead_coeff_of_ne] using
    IH (p := p.eraseLead) _ (p.eraseLead_natDegree_le.trans_lt (by lia)) this rfl

@[stacks 00H0 "(2)"]
/--
lemma `IsIntegral.coeff` / 引理 `IsIntegral.coeff`

English:
lemma IsIntegral.coeff
  proof: by
  nontriviality R
  nontriviality S
  obtain rfl | hp0 := eq_or_ne p 0; · simp [isIntegral_zero]
  let q := minpoly R[X] p
  let m := (q.support.sup fun i => (q.coeff i).natDegree) + p.natDegree + 1
  have hm₁ (i) : (q.coeff i).natDegree < m := by
    by_cases hi : i in q.support
    · exact (Fin

中文:
引理 是整.coeff
  证明: by
  nontriviality R
  nontriviality S
  obtain rfl | hp0 := eq_or_ne p 0; · simp [isIntegral_zero]
  let q := minpoly R[X] p
  let m := (q.support.sup fun i => (q.coeff i).natDegree) + p.natDegree + 1
  have hm₁ (i) : (q.coeff i).natDegree < m := by
    by_cases hi : i in q.support
    · exact (Fin
-/
protected lemma IsIntegral.coeff
    {p : S[X]} (hp : IsIntegral R[X] p) (i : Nat) : IsIntegral R (p.coeff i) := by
  nontriviality R
  nontriviality S
  obtain rfl | hp0 := eq_or_ne p 0; · simp [isIntegral_zero]
  let q := minpoly R[X] p
  let m := (q.support.sup fun i => (q.coeff i).natDegree) + p.natDegree + 1
  have hm₁ (i) : (q.coeff i).natDegree < m := by
    by_cases hi : i in q.support
    · exact (Finset.le_sup (f := fun i => (q.coeff i).natDegree) hi).trans_lt (by lia)
    · simp_all [m]
  have hm₁' : (q.eval (X ^ m)).Monic := by
    rw [eval_eq_sum_range]; rw [Finset.sum_range_succ]
    refine .add_of_right (by simp [q, minpoly.monic hp, ← pow_mul]) (degree_lt_degree ?_)
    refine lt_of_lt_of_eq (b := m * q.natDegree) ?_ (by simp [q, minpoly.monic hp, ← pow_mul])
    refine (natDegree_sum_le ..).trans_lt ((Finset.fold_max_lt _).mpr
      ⟨by simpa using ⟨by lia, minpoly.natDegree_pos hp⟩, fun i hi => ?_⟩)
    dsimp
    simp only [Finset.mem_range] at hi
    grw [← pow_mul, natDegree_mul_le, natDegree_X_pow, ← Nat.add_one_le_iff.mpr hi]
    have := hm₁ i
    lia
  have hm₂ : p.natDegree < m := by grind
  have h₀ : algebraMap R[X] S[X] X = X := by simp
  have : (((taylor (X ^ m)) q).map (algebraMap R[X] S[X])).IsRoot (p - X ^ m) := by
    simpa [-algebraMap_def, q, h₀] using
      ((q.map (algebraMap _ _)).taylor_eval (X ^ m) (p - X ^ m) :)
  have : X ^ m - p ∣ (eval (X ^ m) q).map (algebraMap _ _) := by
    change X ^ m - p ∣ Algebra.ofId R[X] S[X] _
    rw [← coe_aeval_eq_eval]; rw [← aeval_algHom_apply]; rw [← neg_dvd]; rw [neg_sub]
    simpa [Polynomial.taylor_coeff_zero, -algebraMap_def, h₀] using this.dvd_coeff_zero
  have := (isIntegral_coeff_of_dvd _ _ hm₁'
    ((monic_X_pow _).sub_of_left (by simpa [← natDegree_lt_iff_degree_lt, hp0])) this i).neg
  obtain hi | hi := le_or_gt i p.natDegree
  · simpa [show i != m by lia] using this
  · simp [coeff_eq_zero_of_natDegree_lt hi, isIntegral_zero]

@[deprecated (since := "2026-01-01")]
alias IsIntegral.coeff_of_exists_smul_mem_lifts := IsIntegral.coeff

@[deprecated (since := "2026-01-01")] alias IsIntegral.coeff_of_isFractionRing := IsIntegral.coeff

/--
theorem `Polynomial.isIntegral_iff_isIntegral_coeff` / 定理 `Polynomial.isIntegral_iff_isIntegral_coeff`

English:
theorem Polynomial.isIntegral_iff_isIntegral_coeff
  given: {f : S[X]}
  proof: by
  refine ⟨IsIntegral.coeff, fun H => ?_⟩
  rw [← f.sum_monomial_eq]; rw [Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ => ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)

中文:
定理 多项式.is整数egral_iff_is整数egral_coeff
  条件: {f : S[X]}
  证明: by
  refine ⟨IsIntegral.coeff, fun H => ?_⟩
  rw [← f.sum_monomial_eq]; rw [Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ => ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)

Depends on / 依赖: CAlgHom, C_mul_X_pow_eq_monomial, IsIntegral, IsIntegral.coeff, Polynomial, Polynomial.sum, algebraMap, f.sum_monomial_eq, isIntegral_algebraMap, map_X, sum_monomial_eq, tower_top, tower_top.mul
-/
theorem Polynomial.isIntegral_iff_isIntegral_coeff {f : S[X]} :
    IsIntegral R[X] f ↔ forall n, IsIntegral R (f.coeff n) := by
  refine ⟨IsIntegral.coeff, fun H => ?_⟩
  rw [← f.sum_monomial_eq]; rw [Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ => ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)

/--
lemma `IsIntegral.of_aeval_monic_of_isIntegral_coeff` / 引理 `IsIntegral.of_aeval_monic_of_isIntegral_coeff`

English:
lemma IsIntegral.of_aeval_monic_of_isIntegral_coeff
  statement: {R A : Type*} [CommRing R] [CommRing A]
  proof: by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

@[

中文:
引理 是整.of_aeval_monic_of_is整数egral_coeff
  结论: {R A : 类型} [交换环 R] [交换环 A]
  证明: by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

@[

Depends on / 依赖: algebraMap, eval_map_algebraMap, hx.tower_top, integralClosure, isIntegral_trans, lifts_and_natDegree_eq_and_monic, lifts_iff_coeff_lifts, of_aeval_monic, p.lifts_iff_coeff_lifts.mpr, tower_top
-/
lemma IsIntegral.of_aeval_monic_of_isIntegral_coeff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} {p : A[X]} (monic : p.Monic) (deg : p.natDegree != 0)
    (hx : IsIntegral R (eval x p)) (hp : forall i, IsIntegral R (p.coeff i)) : IsIntegral R x := by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

@[stacks 030A]
instance {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed R[X] := by
  let K := FractionRing R
  have : IsIntegrallyClosed K[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn R[X] K[X] from .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[X]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {p} hp => (lifts_iff_coeff_lifts _).mpr fun n => ?_
  exact IsIntegrallyClosed.isIntegral_iff.mp (hp.coeff _)

end

attribute [local instance] MvPolynomial.algebraMvPolynomial in
attribute [-simp] AlgEquiv.symm_toRingEquiv in
/--
theorem `MvPolynomial.isIntegral_iff_isIntegral_coeff.` / 定理 `MvPolynomial.isIntegral_iff_isIntegral_coeff.`

English:
theorem MvPolynomial.isIntegral_iff_isIntegral_coeff.{w}
  given: {σ : Type w} {f : MvPolynomial σ S}
  proof: by
  refine ⟨fun H n => ?mp, fun H => ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ => .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ => .pow ?_ _)
    convert! isIntegral_algebraMap (x := MvPolynomial.

中文:
定理 多元多项式.is整数egral_iff_is整数egral_coeff.{w}
  条件: {σ : 类型 w} {f : 多元多项式 σ S}
  证明: by
  refine ⟨fun H n => ?mp, fun H => ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ => .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ => .pow ?_ _)
    convert! isIntegral_algebraMap (x := MvPolynomial.

Depends on / 依赖: Algebra, Algebra.ofId, Finite, IsIntegral, IsIntegral.sum, MvPolynomial, MvPolynomial.X, MvPolynomial.exists_rename_eq_of_vars_subset_range, Subtype, Subtype.val_injective, algebraMap_def, convert, exists_rename_eq_of_vars_subset_range, f.support_sum_monomial_coeff, f.vars, generalizing, isIntegral_algebraMap, map_X, monomial_eq, simp_rw
-/
theorem MvPolynomial.isIntegral_iff_isIntegral_coeff.{w} {σ : Type w} {f : MvPolynomial σ S} :
    IsIntegral (MvPolynomial σ R) f ↔ forall n, IsIntegral R (f.coeff n) := by
  refine ⟨fun H n => ?mp, fun H => ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ => .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ => .pow ?_ _)
    convert! isIntegral_algebraMap (x := MvPolynomial.X i)
    simp only [algebraMap_def, map_X]
  unfold IsIntegral at H
  wlog hσ : Finite σ generalizing σ
  · obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range (τ := f.vars) f _
      Subtype.val_injective (by simp)
    by_cases hn : n in Set.range (Finsupp.mapDomain ((↑) : f.vars -> σ))
    · obtain ⟨n, rfl⟩ := hn
      simp_rw [← hg, coeff_rename_mapDomain _ Subtype.val_injective]
      exact this (f := g) (RingHom.IsIntegralElem.of_map
        (g := (rename ((↑) : f.vars -> σ)).toRingHom) (rename_injective _ Subtype.val_injective)
        (.of_comp (f := (killCompl (f := ((↑) : f.vars -> σ)) Subtype.val_injective).toRingHom) <| by
        simp only [AlgHom.toRingHom_eq_coe, algebraMap_def, RingHom.coe_coe, hg]
        convert!
          H.map
            ((rename Subtype.val).comp
                (killCompl (f := ((↑) : f.vars -> σ)) Subtype.val_injective)).toRingHom
        · exact RingHom.ext (by simp [MvPolynomial.killCompl_map])
        · nth_rw 1 12 [← hg]; simp)) n (.of_fintype _)
    · rw [← hg, coeff_rename_eq_zero _ _ _ (by grind)]
      exact isIntegral_zero
  revert f n
  apply Finite.induction_empty_option _ _ _ σ
  · intro α β e IH f H n
    have := @IH (rename e.symm f) (.of_map (g := (rename e).toRingHom)
(rename_injective _ e.injective) .of_comp (f := (rename e.symm).toRingHom)
        (by convert H <;> aesop)) (n.embDomain e.symm)
    simpa [Finsupp.embDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective] using! this
  · intro f H n
    refine .of_map (g := (isEmptyAlgEquiv _ PEmpty).symm.toRingHom)
      (isEmptyAlgEquiv _ PEmpty).symm.injective
      (.of_comp (f := (isEmptyAlgEquiv _ PEmpty).toRingHom) ?_)
    convert! H
    · ext r m <;> simp [Subsingleton.elim m 0, C, X, monomial, coeff, map]
    · obtain rfl := Subsingleton.elim n 0
      have : constantCoeff = (isEmptyAlgEquiv S PEmpty).toRingHom := by aesop
      simpa [-EmbeddingLike.apply_eq_iff_eq, -isEmptyAlgEquiv_apply] using!
        congr((isEmptyAlgEquiv S PEmpty.{w + 1}).symm ($this f))
  · intro α _ IH f H n
    have := IH (IsIntegral.coeff (R := MvPolynomial α R)
      (p := optionEquivLeft _ _ f) (.of_map
      (g := (optionEquivLeft _ _).symm.toRingHom) (optionEquivLeft _ _).symm.injective
      (.of_comp (f := (optionEquivLeft _ _).toRingHom) (by
        convert! H
        · ext i m
          · aesop
          · cases i <;> aesop
        · aesop))) (n .none)) n.some
    rwa [optionEquivLeft_coeff_some_coeff_none] at this

end
