/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Division algorithm with respect to monomial orders

We provide a division algorithm with respect to monomial orders in polynomial rings.
Let `R` be a commutative ring, `σ` a type of indeterminates and `m : MonomialOrder σ`
a monomial ordering on `σ →₀ ℕ`.

Consider a family of polynomials `b : ι → MvPolynomial σ R` with invertible leading coefficients
(with respect to `m`): we assume `hb : ∀ i, IsUnit (m.leadingCoeff (b i))`.

* `MonomialOrder.div hb f` furnishes
  - a finitely supported family `g : ι →₀ MvPolynomial σ R`
  - and a “remainder” `r : MvPolynomial σ R`
    such that the three properties hold:
    1. One has `f = ∑ (g i) * (b i) + r`
    2. For every `i`, `m.degree ((g i) * (b i)` is less than or equal to that of `f`
    3. For every `i`, every monomial in the support of `r` is strictly smaller
       than the leading term of `b i`,

The proof is done by induction, using two standard constructions

* `MonomialOrder.subLTerm f` deletes the leading term of a polynomial `f`

* `MonomialOrder.reduce hb f` subtracts from `f` the appropriate multiple of `b : MvPolynomial σ R`,
  provided `IsUnit (m.leadingCoeff b)`.

* `MonomialOrder.div_set` is the variant of `MonomialOrder.div` for a set of polynomials.

* `MonomialOrder.div_single` is the variant of `MonomialOrder.div` for a single polynomial.


## Reference : [Becker-Weispfenning1993]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

variable (m) in
/--
Definition of `subLTerm` / `subLTerm` 的定义

English:
definition subLTerm
  signature: (f : MvPolynomial σ R)
  body: f - monomial (m.degree f) (m.leadingCoeff f)

中文:
定义 subLTerm
  签名: (f : MvPolynomial σ R)
  定义体: f - monomial (m.degree f) (m.leadingCoeff f)

Depends on / 依赖: degree, leadingCoeff, m.degree, m.leadingCoeff, monomial
-/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.leadingCoeff f)

/--
theorem `degree_sub_LTerm_le` / 定理 `degree_sub_LTerm_le`

English:
theorem degree_sub_LTerm_le
  given: (f : MvPolynomial σ R)
  proof: by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

中文:
定理 degree_sub_LTerm_le
  条件: (f : MvPolynomial σ R)
  证明: by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

Depends on / 依赖: degree_monomial_le, degree_sub_le, le_refl, le_trans, sup_le_iff, true_and
-/
theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

/--
theorem `degree_sub_LTerm_lt` / 定理 `degree_sub_LTerm_lt`

English:
theorem degree_sub_LTerm_lt
  given: {f : MvPolynomial σ R} (hf : m.degree f != 0)
  proof: by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f != 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m)]; rw [hf'] at 

中文:
定理 degree_sub_LTerm_lt
  条件: {f : MvPolynomial σ R} (hf : m.degree f != 0)
  证明: by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f != 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m)]; rw [hf'] at 

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, classical, coeff_degree_ne_zero_iff, coeff_monomial, degree_sub_LTerm_le, degree_zero, leadingCoeff, lt_iff_le_and_ne, m.subLTerm, subLTerm
-/
theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f != 0) :
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f != 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m)]; rw [hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, leadingCoeff]

variable (m) in
/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable
/--
Definition of `reduce` / `reduce` 的定义

English:
definition reduce
  signature: {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R)
  body: f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b

中文:
定义 reduce
  签名: {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R)
  定义体: f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b

Depends on / 依赖: degree, hb.unit, leadingCoeff, m.degree, m.leadingCoeff, monomial
-/
def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b

/--
theorem `degree_reduce_lt` / 定理 `degree_reduce_lt`

English:
theorem degree_reduce_lt
  statement: {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
  proof: by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial]; rw [if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_ze

中文:
定理 degree_reduce_lt
  结论: {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
  证明: by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial]; rw [if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_ze

Depends on / 依赖: Units.mul_right_eq_zero, classical, coeff_mul_of_degree_add, coeff_sub, degree, degree_monomial, hb.unit, if_neg, leadingCoeff, leadingCoeff_eq_zero_iff, leadingCoeff_monomial, m.degree, m.leadingCoeff, m.reduce, monomial, mul_comm, mul_right_eq_zero, nth_rewrite, sub_eq_zero, tsub_add_cancel_of_le
-/
theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbf : m.degree b <= m.degree f) (hf : m.degree f != 0) :
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial]; rw [if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [coeff_mul_of_degree_add (m := m)]; rw [leadingCoeff_monomial]; rw [mul_comm]; rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]; rw [← leadingCoeff]
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    rw [← leadingCoeff]; rw [leadingCoeff_eq_zero_iff] at H'
    rw [H']; rw [degree_zero] at K
    exact hf K.symm

/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: {ι : Type*} {b : ι -> MvPolynomial σ R}
  proof: by
  by_cases! hb' : exists i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      

中文:
定理 div
  结论: {ι : 类型} {b : ι -> MvPolynomial σ R}
  证明: by
  by_cases! hb' : exists i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      

Depends on / 依赖: Finsupp, Finsupp.linearCombination_single, Finsupp.single, Finsupp.single_eq_same, Units.smul_isUnit, add_zero, degree, degree_mul_le, eq_C_of_degree_eq_zero, le_of_eq, le_trans, linearCombination_single, m.degree, mul_comm, nth_rewrite, single, single_eq_same, smul_eq_C_mul, smul_eq_iff_eq_inv_smul, smul_eq_mul
-/
theorem div {ι : Type*} {b : ι -> MvPolynomial σ R}
    (hb : forall i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) :
    exists (g : ι ->₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (forall i, m.degree (b i * (g i)) ≼[m] m.degree f) ∧
        (forall c in r.support, forall i, ¬ (m.degree (b i) <= c)) := by
  by_cases! hb' : exists i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm]; rw [smul_eq_C_mul]
    constructor
    · intro j
      by_cases hj : j = i
      · apply le_trans degree_mul_le
        simp only [hj, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul_of_isRegular (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne hj, mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases! hf : exists i, m.degree (b i) <= m.degree f
  · obtain ⟨i, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hb i) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hb i) hf
      intro hf0'
      apply hb' i
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := div hb (m.reduce (hb i) f)
    use g' +
      Finsupp.single i (monomial (m.degree f - m.degree (b i)) ((hb i).unit⁻¹ * m.leadingCoeff f))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro j
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · subst j
          grw [degree_mul_le, map_add, degree_monomial_le, ← map_add, add_tsub_cancel_of_le hf]
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · suffices exists (g' : ι ->₀ MvPolynomial σ R), exists r',
        (m.subLTerm f = Finsupp.linearCombination (MvPolynomial σ R) b g' + r') ∧
        (forall i, m.degree ((b i) * (g' i)) ≼[m] m.degree (m.subLTerm f)) ∧
        (forall c in r'.support, forall i, ¬ m.degree (b i) <= c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' + monomial (m.degree f) (m.leadingCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b => le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc i
        by_cases hc' : c in r'.support
        · exact H'.2.2 c hc' i
        · convert! hf i
          classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union]; rw [Classical.or_iff_not_imp_left] at this
          simpa only [Finset.mem_singleton] using support_monomial_subset (this hc')
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · exact (div hb) (m.subLTerm f)
termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 => x < x_1).mp m.wellFoundedLT_syn) (m.toSyn (m.degree f))
decreasing_by
  · exact deg_reduce
  · apply degree_sub_LTerm_lt
    intro hf0
    apply hf'0
    simp only [subLTerm, sub_eq_zero]
    nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
    simp

/-!
Module doc as workaround for a parser error that prevents using `set_option`
after a `decreasing_by` block with focus dots.

See https://github.com/leanprover/lean4/issues/12573
-/

/--
theorem `div_set` / 定理 `div_set`

English:
theorem div_set
  statement: {B : Set (MvPolynomial σ R)}
  proof: by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) => p) (fun b => hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb => H.2.2 c hc ⟨b, hb⟩⟩

中文:
定理 div_set
  结论: {B : Set (MvPolynomial σ R)}
  证明: by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) => p) (fun b => hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb => H.2.2 c hc ⟨b, hb⟩⟩

Depends on / 依赖: G.toProfinite, b.prop, m.div, toProfinite
-/
theorem div_set {B : Set (MvPolynomial σ R)}
    (hB : forall b in B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    exists (g : B ->₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) => (b : MvPolynomial σ R)) g + r ∧
        (forall (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (forall c in r.support, forall b in B, ¬ (m.degree b <= c)) := by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) => p) (fun b => hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb => H.2.2 c hc ⟨b, hb⟩⟩

/--
theorem `div_single` / 定理 `div_single`

English:
theorem div_single
  statement: {b : MvPolynomial σ R}
  proof: by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsu

中文:
定理 div_single
  结论: {b : MvPolynomial σ R}
  证明: by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsu

Depends on / 依赖: Finsupp, Finsupp.coe_lsum, Finsupp.linearCombination, Finsupp.sum_eq_single, LinearMap, LinearMap.coe_smulRight, LinearMap.id_coe, Set.mem_singleton_iff, add_left_inj, coe_lsum, coe_smulRight, contextual, div_set, forall_eq, id_coe, id_eq, linearCombination, mem_singleton_iff, smul_eq_mul, specialize
-/
theorem div_single {b : MvPolynomial σ R}
    (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    exists (g : MvPolynomial σ R) (r : MvPolynomial σ R),
      f = g * b + r ∧
        (m.degree (b * g) ≼[m] m.degree f) ∧
        (forall c in r.support, ¬ (m.degree b <= c)) := by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id_eq, smul_eq_mul, add_left_inj]
  rw [Finsupp.sum_eq_single ⟨b]; rw [by simp⟩ _ (by simp)]
  simp +contextual

end MonomialOrder
