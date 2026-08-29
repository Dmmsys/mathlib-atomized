/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also provide some specific results about the Galois groups of ℚ-polynomials with specific numbers
of non-real roots.

We also show that an irreducible real polynomial has degree at most two.
-/

public section

open Polynomial Bornology Complex

open scoped ComplexConjugate

namespace Complex

/--
theorem `exists_root` / 定理 `exists_root`

English:
theorem exists_root
  given: {f : Complex[X]} (hf : 0 < degree f)
  statement: exists z : Complex, IsRoot f z
  proof: by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : Complex) : (f.eval z)⁻¹ = 0 :=
(f.differentiable.inv hf').apply_eq_of_t

中文:
定理 存在_root
  条件: {f : 复形[X]} (hf : 0 < degree f)
  结论: 存在 z : 复形, IsRoot f z
  证明: by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : Complex) : (f.eval z)⁻¹ = 0 :=
(f.differentiable.inv hf').apply_eq_of_t
-/
theorem exists_root {f : Complex[X]} (hf : 0 < degree f) : exists z : Complex, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : Complex) : (f.eval z)⁻¹ = 0 :=
(f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z
      Metric.cobounded_eq_cocompact (α := Complex) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
obtain rfl : f = C 0 := Polynomial.funext fun z => inv_injective by simp [this]
  simp at hf

/-- **Fundamental theorem of algebra**: the field `ℂ` of complex numbers is algebraically closed. -/
@[wikidata Q192760]
/--
Instance `isAlgClosed` / 实例 `isAlgClosed`

English:
instance isAlgClosed
  signature: : IsAlgClosed Complex
  body: IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root degree_pos_of_irreducible hp

中文:
实例 isAlgClosed
  签名: : 是代数闭 复形
  定义体: IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root degree_pos_of_irreducible hp

Depends on / 依赖: Complex.exists_root, IsAlgClosed, IsAlgClosed.of_exists_root, degree_pos_of_irreducible, exists_root, of_exists_root
-/
instance isAlgClosed : IsAlgClosed Complex :=
IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root degree_pos_of_irreducible hp

end Complex

/--
theorem `Real.nonempty_algEquiv_or` / 定理 `Real.nonempty_algEquiv_or`

English:
theorem Real.nonempty_algEquiv_or
  given: (F : Type*) [Field F] [Algebra Real F] [Algebra.IsAlgebraic Real F]
  proof: IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

中文:
定理 实数.nonempty_algEquiv_or
  条件: (F : 类型) [域 F] [代数 实数 F] [代数.是代数 实数 F]
  证明: IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

Depends on / 依赖: Complex.finrank_real_complex, IsAlgClosed, IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two, finrank_real_complex, nonempty_algEquiv_or_of_finrank_eq_two
-/
theorem Real.nonempty_algEquiv_or (F : Type*) [Field F] [Algebra Real F] [Algebra.IsAlgebraic Real F] :
    Nonempty (F ≃ₐ[Real] Real) ∨ Nonempty (F ≃ₐ[Real] Complex) :=
  IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

namespace Polynomial.Gal

section Rationals

/--
theorem `splits_Rat_Complex` / 定理 `splits_Rat_Complex`

English:
theorem splits_Rat_Complex
  given: {p : Rat[X]}
  statement: Fact ((p.map (algebraMap Rat Complex)).Splits)
  proof: ⟨IsAlgClosed.splits _⟩

中文:
定理 splits_Rat_Complex
  条件: {p : 有理数[X]}
  结论: Fact ((p.map (algebraMap 有理数 复形)).Splits)
  证明: ⟨IsAlgClosed.splits _⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, splits
-/
theorem splits_Rat_Complex {p : Rat[X]} : Fact ((p.map (algebraMap Rat Complex)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

attribute [local instance] splits_Rat_Complex
attribute [local ext] Complex.ext

/--
theorem `card_complex_roots_eq_card_real_add_card_not_gal_inv` / 定理 `card_complex_roots_eq_card_real_add_card_not_gal_inv`

English:
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv
  given: (p : Rat[X])
  proof: by
  by_cases hp : p = 0
  · have : IsEmpty (p.rootSet Complex) := by rw [hp, rootSet_zero]; infer_instance
    simp_rw [(galActionHom p Complex _).support.eq_empty_of_isEmpty, hp, rootSet_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom Rat 

中文:
定理 card_complex_roots_eq_card_real_add_card_not_gal_inv
  条件: (p : 有理数[X])
  证明: by
  by_cases hp : p = 0
  · have : IsEmpty (p.rootSet Complex) := by rw [hp, rootSet_zero]; infer_instance
    simp_rw [(galActionHom p Complex _).support.eq_empty_of_isEmpty, hp, rootSet_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom Rat 

Depends on / 依赖: Finset, Finset.card_empty, Finset.card_image_of_injective, Function, Function.Injective, Injective, IsEmpty, IsScalarTower, IsScalarTower.toAlgHom, Set.toFinset_empty, Subtype, Subtype.coe_injective, algebraMap, card_empty, card_image_of_injective, coe_injective, eq_empty_of_isEmpty, galActionHom, infer_instance, injective
-/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : Rat[X]) :
    (p.rootSet Complex).toFinset.card =
      (p.rootSet Real).toFinset.card +
        (galActionHom p Complex (restrict p Complex
        (AlgEquiv.restrictScalars Rat Complex.conjAe))).support.card := by
  by_cases hp : p = 0
  · have : IsEmpty (p.rootSet Complex) := by rw [hp, rootSet_zero]; infer_instance
    simp_rw [(galActionHom p Complex _).support.eq_empty_of_isEmpty, hp, rootSet_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom Rat Real Complex) := (algebraMap Real Complex).injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective]; rw [←
    Finset.card_image_of_injective _ inj]
  let a : Finset Complex := ?_
  on_goal 1 => let b : Finset Complex := ?_
  on_goal 1 => let c : Finset Complex := ?_
  change a.card = b.card + c.card
  have ha : forall z : Complex, z in a ↔ aeval z p = 0 := by
    intro z; rw [Set.mem_toFinset, mem_rootSet_of_ne hp]
  have hb : forall z : Complex, z in b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [b, Finset.mem_image, Set.mem_toFinset, mem_rootSet_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [aeval_algHom_apply, hw, map_zero], rfl⟩
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom Rat Real Complex z.re = z := by
        ext
        · rfl
        · rw [hz2]; rfl
      exact ⟨z.re, inj (by rwa [← aeval_algHom_apply, key, map_zero]), key⟩
  have hc0 :
    forall w : p.rootSet Complex, galActionHom p Complex (restrict p Complex (Complex.conjAe.restrictScalars Rat)) w = w ↔
        w.val.im = 0 := by
    intro w
    rw [Subtype.ext_iff]; rw [galActionHom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : forall z : Complex, z in c ↔ aeval z p = 0 ∧ z.im != 0 := by
    intro z
    simp_rw [c, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_rootSet.mp w.2).2, mt (hc0 w).mpr (Equiv.Perm.mem_support.mp hw)⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, mem_rootSet.mpr ⟨hp, hz1⟩⟩, Equiv.Perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
  rw [← Finset.card_union_of_disjoint]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb]; rw [hc]
    tauto

/--
theorem `galActionHom_bijective_of_prime_degree` / 定理 `galActionHom_bijective_of_prime_degree`

English:
theorem galActionHom_bijective_of_prime_degree
  statement: {p : Rat[X]} (p_irr : Irreducible p)
  proof: by
  have h1 : Fintype.card (p.rootSet Complex) = p.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup]; rw [← Splits.natDegree_eq_card_roots]; rw [natDegree_map]
    · exact IsAlgClosed.splits _
    · exact nodup_roots ((separabl

中文:
定理 galActionHom_bijective_of_prime_degree
  结论: {p : 有理数[X]} (p_irr : 不可约 p)
  证明: by
  have h1 : Fintype.card (p.rootSet Complex) = p.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup]; rw [← Splits.natDegree_eq_card_roots]; rw [natDegree_map]
    · exact IsAlgClosed.splits _
    · exact nodup_roots ((separabl

Depends on / 依赖: Complex.conjAe.restrictScalars, Finset, Finset.coe_sort_coe, Fintype, Fintype.card, Fintype.card_coe, IsAlgClosed, IsAlgClosed.splits, Multiset, Multiset.toFinset_card_of_nodup, Splits, Splits.natDegree_eq_card_roots, algebraMap, card_coe, coe_sort_coe, congr_arg, conjAe, galActionHom, galActionHom_injective, natDegree
-/
theorem galActionHom_bijective_of_prime_degree {p : Rat[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet Complex) = Fintype.card (p.rootSet Real) + 2) :
    Function.Bijective (galActionHom p Complex) := by
  have h1 : Fintype.card (p.rootSet Complex) = p.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup]; rw [← Splits.natDegree_eq_card_roots]; rw [natDegree_map]
    · exact IsAlgClosed.splits _
    · exact nodup_roots ((separable_map (algebraMap Rat Complex)).mpr p_irr.separable)
  let conj' := restrict p Complex (Complex.conjAe.restrictScalars Rat)
  refine
    ⟨galActionHom_injective p Complex, fun x =>
      (congr_arg (x in ·) (show (galActionHom p Complex).range = ⊤ from ?_)).mpr
        (Subgroup.mem_top x)⟩
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
  · rw [h1]
    simpa only [Fintype.card_eq_nat_card,
      Nat.card_congr (MonoidHom.ofInjective (galActionHom_injective p Complex)).toEquiv.symm]
      using prime_degree_dvd_card p_irr p_deg
  · exact ⟨conj', rfl⟩
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots]; rw [← Set.toFinset_card (rootSet p Real)]; rw [← Set.toFinset_card (rootSet p Complex)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm

/--
theorem `galActionHom_bijective_of_prime_degree'` / 定理 `galActionHom_bijective_of_prime_degree'`

English:
theorem galActionHom_bijective_of_prime_degree'
  statement: {p : Rat[X]} (p_irr : Irreducible p)
  proof: by
  apply galActionHom_bijective_of_prime_degree p_irr p_deg
  let n := (galActionHom p Complex (restrict p Complex (Complex.conjAe.restrictScalars Rat))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
         rw [← map_pow]; rw [← map_pow]; rw [show AlgEquiv.restr

中文:
定理 galActionHom_bijective_of_prime_degree'
  结论: {p : 有理数[X]} (p_irr : 不可约 p)
  证明: by
  apply galActionHom_bijective_of_prime_degree p_irr p_deg
  let n := (galActionHom p Complex (restrict p Complex (Complex.conjAe.restrictScalars Rat))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
         rw [← map_pow]; rw [← map_pow]; rw [show AlgEquiv.restr

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.restrictScalars, Complex.conjAe, Complex.conjAe.restrictScalars, Complex.conj_conj, Equiv.Perm.two_dvd_card_support, Set.toFinset_card, card_complex_roots_eq_card_real_add_card_not_gal_inv, conjAe, conj_conj, galActionHom, galActionHom_bijective_of_prime_degree, map_one, map_pow, p_deg, p_irr, restrict, restrictScalars, simp_rw
-/
theorem galActionHom_bijective_of_prime_degree' {p : Rat[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.rootSet Real) + 1 <= Fintype.card (p.rootSet Complex))
    (p_roots2 : Fintype.card (p.rootSet Complex) <= Fintype.card (p.rootSet Real) + 3) :
    Function.Bijective (galActionHom p Complex) := by
  apply galActionHom_bijective_of_prime_degree p_irr p_deg
  let n := (galActionHom p Complex (restrict p Complex (Complex.conjAe.restrictScalars Rat))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
         rw [← map_pow]; rw [← map_pow]; rw [show AlgEquiv.restrictScalars Rat Complex.conjAe ^ 2 = 1 from
            AlgEquiv.ext Complex.conj_conj]; rw [map_one]; rw [map_one])
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  simp_rw [Set.toFinset_card] at key
  lia

end Rationals

end Polynomial.Gal

/--
lemma `Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero` / 引理 `Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero`

English:
lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero
  statement: (p : Real[X]) {z : Complex} (h0 : aeval z p = 0)
  proof: by
  apply IsCoprime.mul_dvd
· exact isCoprime_X_sub_C_of_isUnit_sub .mk0 _ sub_ne_zero.2 mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

中文:
引理 多项式.mul_star_dvd_of_aeval_eq_zero_im_ne_zero
  结论: (p : 实数[X]) {z : 复形} (h0 : aeval z p = 0)
  证明: by
  apply IsCoprime.mul_dvd
· exact isCoprime_X_sub_C_of_isUnit_sub .mk0 _ sub_ne_zero.2 mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

Depends on / 依赖: IsCoprime, IsCoprime.mul_dvd, aeval_conj, conj_eq_iff_im, dvd_iff_isRoot, isCoprime_X_sub_C_of_isUnit_sub, mul_dvd, sub_ne_zero
-/
lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : Real[X]) {z : Complex} (h0 : aeval z p = 0)
    (hz : z.im != 0) : (X - C ((starRingEnd Complex) z)) * (X - C z) ∣ map (algebraMap Real Complex) p := by
  apply IsCoprime.mul_dvd
· exact isCoprime_X_sub_C_of_isUnit_sub .mk0 _ sub_ne_zero.2 mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

/--
lemma `Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero` / 引理 `Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`

English:
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero
  statement: (p : Real[X]) {z : Complex} (h0 : aeval z p = 0)
  proof: by
  rw [← map_dvd_map' (algebraMap Real Complex)]
  convert! p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap Real Complex) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : Complex) * X + C (‖z‖ ^ 2 : Complex) := by simp
    _ = (X - C (conj z)) *

中文:
引理 多项式.quadratic_dvd_of_aeval_eq_zero_im_ne_zero
  结论: (p : 实数[X]) {z : 复形} (h0 : aeval z p = 0)
  证明: by
  rw [← map_dvd_map' (algebraMap Real Complex)]
  convert! p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap Real Complex) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : Complex) * X + C (‖z‖ ^ 2 : Complex) := by simp
    _ = (X - C (conj z)) *

Depends on / 依赖: add_conj, algebraMap, convert, map_add, map_dvd_map, map_mul, mul_conj, mul_star_dvd_of_aeval_eq_zero_im_ne_zero, p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero, z.re
-/
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : Real[X]) {z : Complex} (h0 : aeval z p = 0)
    (hz : z.im != 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p := by
  rw [← map_dvd_map' (algebraMap Real Complex)]
  convert! p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap Real Complex) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : Complex) * X + C (‖z‖ ^ 2 : Complex) := by simp
    _ = (X - C (conj z)) * (X - C z) := by
      rw [← add_conj]; rw [map_add]; rw [← mul_conj']; rw [map_mul]
      ring

/--
lemma `Irreducible.natDegree_le_two` / 引理 `Irreducible.natDegree_le_two`

English:
lemma Irreducible.natDegree_le_two
  given: {p : Real[X]} (hp : Irreducible p)
  statement: natDegree p <= 2
  proof: by
  obtain ⟨z, hz⟩ : exists z : Complex, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  rw [← finrank_real_complex]
  suffices p.natDegree = (minpoly Real z).natDegree from this ▸ minpoly.natDegree_le (A := Real) z
  rw [← minpoly.eq_of_irreducible hp

中文:
引理 不可约.natDegree_le_two
  条件: {p : 实数[X]} (hp : 不可约 p)
  结论: natDegree p <= 2
  证明: by
  obtain ⟨z, hz⟩ : exists z : Complex, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  rw [← finrank_real_complex]
  suffices p.natDegree = (minpoly Real z).natDegree from this ▸ minpoly.natDegree_le (A := Real) z
  rw [← minpoly.eq_of_irreducible hp

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_aeval_eq_zero, add_zero, degree_pos_of_irreducible, eq_of_irreducible, exists_aeval_eq_zero, finrank_real_complex, hp.ne_zero, minpoly, minpoly.eq_of_irreducible, minpoly.natDegree_le, natDegree, natDegree_C, natDegree_le, natDegree_mul, ne_zero, p.natDegree
-/
lemma Irreducible.natDegree_le_two {p : Real[X]} (hp : Irreducible p) : natDegree p <= 2 := by
  obtain ⟨z, hz⟩ : exists z : Complex, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  rw [← finrank_real_complex]
  suffices p.natDegree = (minpoly Real z).natDegree from this ▸ minpoly.natDegree_le (A := Real) z
  rw [← minpoly.eq_of_irreducible hp hz]; rw [natDegree_mul hp.ne_zero (by simpa using hp.ne_zero)]; rw [natDegree_C]; rw [add_zero]

/--
lemma `Irreducible.degree_le_two` / 引理 `Irreducible.degree_le_two`

English:
lemma Irreducible.degree_le_two
  given: {p : Real[X]} (hp : Irreducible p)
  statement: degree p <= 2
  proof: natDegree_le_iff_degree_le.1 hp.natDegree_le_two

中文:
引理 不可约.degree_le_two
  条件: {p : 实数[X]} (hp : 不可约 p)
  结论: degree p <= 2
  证明: natDegree_le_iff_degree_le.1 hp.natDegree_le_two

Depends on / 依赖: hp.natDegree_le_two, natDegree_le_iff_degree_le, natDegree_le_two
-/
lemma Irreducible.degree_le_two {p : Real[X]} (hp : Irreducible p) : degree p <= 2 :=
  natDegree_le_iff_degree_le.1 hp.natDegree_le_two
