/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.MvPowerSeries.Order

/-! # ZeroDivisors in a MvPowerSeries ring

- `mem_nonZeroDivisors_of_constantCoeff` proves that
  a multivariate power series whose constant coefficient is not a zero divisor
  is itself not a zero divisor


- `MvPowerSeries.order_mul` : multiplicativity of `MvPowerSeries.order`
  if the semiring `R` has no zero divisors

## Instance

If `R` has `NoZeroDivisors`, then so does `MvPowerSeries σ R`.


## TODO

* Transfer/adapt these results to `HahnSeries`.

## Remark

The analogue of `Polynomial.notMem_nonZeroDivisors_iff`
(McCoy theorem) holds for power series over a Noetherian ring,
but not in general. See [Fields1971]
-/

public section

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp nonZeroDivisors

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/--
theorem `mem_nonZeroDivisorsRight_of_constantCoeff` / 定理 `mem_nonZeroDivisorsRight_of_constantCoeff`

English:
theorem mem_nonZeroDivisorsRight_of_constantCoeff
  statement: {φ : MvPowerSeries σ R}
  proof: by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e]; rw [0)]; rw [coeff_zero_eq_constan

中文:
定理 mem_nonZeroDivisorsRight_of_constantCoeff
  结论: {φ : MvPowerSeries σ R}
  证明: by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e]; rw [0)]; rw [coeff_zero_eq_constan

Depends on / 依赖: Finset, Finset.sum_eq_single, WellFoundedLT, WellFoundedLT.induction, classical, coeff_mul, coeff_zero_eq_constantCoeff, convert, le_add_iff_nonneg_right, lt_of_le_of_ne, map_zero, mem_antidiagonal, mem_antidiagonal.mp, mul_right_mem_nonZeroDivisorsRight_eq_zero_iff, sum_eq_single, zero_le, zero_mul
-/
theorem mem_nonZeroDivisorsRight_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ in nonZeroDivisorsRight R) :
    φ in nonZeroDivisorsRight (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e]; rw [0)]; rw [coeff_zero_eq_constantCoeff]
  · rintro ⟨u, _⟩ huv _
    suffices u < e by simp only [he u this, zero_mul, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_right, zero_le]
    · rintro rfl
      simp_all
  · simp

-- TODO: derive from `mem_nonZeroDivisorsRight_of_constantCoeff` using `MulOpposite`
/--
theorem `mem_nonZeroDivisorsLeft_of_constantCoeff` / 定理 `mem_nonZeroDivisorsLeft_of_constantCoeff`

English:
theorem mem_nonZeroDivisorsLeft_of_constantCoeff
  statement: {φ : MvPowerSeries σ R}
  proof: by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e φ x).symm
  rw [Finset.sum_eq_single (0]; rw [e)]; rw [coeff_zero_eq_constantC

中文:
定理 mem_nonZeroDivisorsLeft_of_constantCoeff
  结论: {φ : MvPowerSeries σ R}
  证明: by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e φ x).symm
  rw [Finset.sum_eq_single (0]; rw [e)]; rw [coeff_zero_eq_constantC

Depends on / 依赖: Finset, Finset.sum_eq_single, WellFoundedLT, WellFoundedLT.induction, classical, coeff_mul, coeff_zero_eq_constantCoeff, convert, le_add_iff_nonneg_left, lt_of_le_of_ne, map_zero, mem_antidiagonal, mem_antidiagonal.mp, mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff, mul_zero, sum_eq_single, zero_le
-/
theorem mem_nonZeroDivisorsLeft_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ in nonZeroDivisorsLeft R) :
    φ in nonZeroDivisorsLeft (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero]; rw [← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hφ]; rw [← map_zero (f := coeff e)]; rw [← hx]
  convert! (coeff_mul e φ x).symm
  rw [Finset.sum_eq_single (0]; rw [e)]; rw [coeff_zero_eq_constantCoeff]
  · rintro ⟨_, u⟩ huv _
    suffices u < e by simp only [he u this, mul_zero, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_left, zero_le]
    · rintro rfl
      simp_all
  · simp only [mem_antidiagonal, zero_add, not_true_eq_false, coeff_zero_eq_constantCoeff,
      false_implies]

/--
theorem `mem_nonZeroDivisors_of_constantCoeff` / 定理 `mem_nonZeroDivisors_of_constantCoeff`

English:
theorem mem_nonZeroDivisors_of_constantCoeff
  statement: {φ : MvPowerSeries σ R}
  proof: ⟨mem_nonZeroDivisorsLeft_of_constantCoeff hφ.1, mem_nonZeroDivisorsRight_of_constantCoeff hφ.2⟩

中文:
定理 mem_nonZeroDivisors_of_constantCoeff
  结论: {φ : MvPowerSeries σ R}
  证明: ⟨mem_nonZeroDivisorsLeft_of_constantCoeff hφ.1, mem_nonZeroDivisorsRight_of_constantCoeff hφ.2⟩

Depends on / 依赖: mem_nonZeroDivisorsLeft_of_constantCoeff, mem_nonZeroDivisorsRight_of_constantCoeff
-/
theorem mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ in R⁰) :
    φ in (MvPowerSeries σ R)⁰ :=
  ⟨mem_nonZeroDivisorsLeft_of_constantCoeff hφ.1, mem_nonZeroDivisorsRight_of_constantCoeff hφ.2⟩

/--
lemma `monomial_mem_nonzeroDivisorsLeft` / 引理 `monomial_mem_nonzeroDivisorsLeft`

English:
lemma monomial_mem_nonzeroDivisorsLeft
  given: {n : σ ->₀ Nat} {r}
  proof: by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_monomial_mul]; rw [if_pos le_add_self]; rw [add_tsub_ca

中文:
引理 monomial_mem_nonzeroDivisorsLeft
  条件: {n : σ ->₀ 自然数} {r}
  证明: by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_monomial_mul]; rw [if_pos le_add_self]; rw [add_tsub_ca

Depends on / 依赖: add_tsub_cancel_right, coeff_monomial_mul, if_pos, le_add_self, monomial_mul_monomial, monomial_zero_eq_C
-/
lemma monomial_mem_nonzeroDivisorsLeft {n : σ ->₀ Nat} {r} :
    monomial n r in nonZeroDivisorsLeft (MvPowerSeries σ R) ↔ r in nonZeroDivisorsLeft R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_monomial_mul]; rw [if_pos le_add_self]; rw [add_tsub_cancel_right] at this
    simpa using H _ this

-- TODO: reduce duplication
/--
lemma `monomial_mem_nonzeroDivisorsRight` / 引理 `monomial_mem_nonzeroDivisorsRight`

English:
lemma monomial_mem_nonzeroDivisorsRight
  given: {n : σ ->₀ Nat} {r}
  proof: by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_mul_monomial]; rw [if_pos le_add_self]; rw [add_tsub_ca

中文:
引理 monomial_mem_nonzeroDivisorsRight
  条件: {n : σ ->₀ 自然数} {r}
  证明: by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_mul_monomial]; rw [if_pos le_add_self]; rw [add_tsub_ca

Depends on / 依赖: add_tsub_cancel_right, coeff_mul_monomial, if_pos, le_add_self, monomial_mul_monomial, monomial_zero_eq_C
-/
lemma monomial_mem_nonzeroDivisorsRight {n : σ ->₀ Nat} {r} :
    monomial n r in nonZeroDivisorsRight (MvPowerSeries σ R) ↔ r in nonZeroDivisorsRight R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_mul_monomial]; rw [if_pos le_add_self]; rw [add_tsub_cancel_right] at this
    simpa using H _ this

/--
lemma `monomial_mem_nonzeroDivisors` / 引理 `monomial_mem_nonzeroDivisors`

English:
lemma monomial_mem_nonzeroDivisors
  given: {n : σ ->₀ Nat} {r}
  proof: monomial_mem_nonzeroDivisorsLeft.and monomial_mem_nonzeroDivisorsRight

中文:
引理 monomial_mem_nonzeroDivisors
  条件: {n : σ ->₀ 自然数} {r}
  证明: monomial_mem_nonzeroDivisorsLeft.and monomial_mem_nonzeroDivisorsRight

Depends on / 依赖: monomial_mem_nonzeroDivisorsLeft, monomial_mem_nonzeroDivisorsLeft.and, monomial_mem_nonzeroDivisorsRight
-/
lemma monomial_mem_nonzeroDivisors {n : σ ->₀ Nat} {r} :
    monomial n r in (MvPowerSeries σ R)⁰ ↔ r in R⁰ :=
  monomial_mem_nonzeroDivisorsLeft.and monomial_mem_nonzeroDivisorsRight

/--
lemma `X_mem_nonzeroDivisors` / 引理 `X_mem_nonzeroDivisors`

English:
lemma X_mem_nonzeroDivisors
  given: {i : σ}
  proof: by
  rw [X]; rw [monomial_mem_nonzeroDivisors]
  exact Submonoid.one_mem R⁰

中文:
引理 X_mem_nonzeroDivisors
  条件: {i : σ}
  证明: by
  rw [X]; rw [monomial_mem_nonzeroDivisors]
  exact Submonoid.one_mem R⁰

Depends on / 依赖: Submonoid, Submonoid.one_mem, monomial_mem_nonzeroDivisors, one_mem
-/
lemma X_mem_nonzeroDivisors {i : σ} :
    X i in (MvPowerSeries σ R)⁰ := by
  rw [X]; rw [monomial_mem_nonzeroDivisors]
  exact Submonoid.one_mem R⁰

end Semiring

variable [Semiring R] [NoZeroDivisors R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors (MvPowerSeries σ R)
  body: by
    rcases exists_wellFoundedGT σ
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h

中文:
实例 :
  签名: 无零因子 (MvPowerSeries σ R)
  定义体: by
    rcases exists_wellFoundedGT σ
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h

Depends on / 依赖: WithTop, WithTop.add_eq_top, add_eq_top, exists_wellFoundedGT, lexOrder_eq_top_iff_eq_zero, lexOrder_mul
-/
instance : NoZeroDivisors (MvPowerSeries σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    rcases exists_wellFoundedGT σ
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h

/--
theorem `weightedOrder_mul` / 定理 `weightedOrder_mul`

English:
theorem weightedOrder_mul
  given: (w : σ -> Nat) (f g : MvPowerSeries σ R)
  proof: by
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let p := (f.weightedOrder w).toNat
      have hp : p = f.weightedOrder w := by
        simpa only [p, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      let q := 

中文:
定理 weightedOrder_mul
  条件: (w : σ -> 自然数) (f g : MvPowerSeries σ R)
  证明: by
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let p := (f.weightedOrder w).toNat
      have hp : p = f.weightedOrder w := by
        simpa only [p, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      let q := 

Depends on / 依赖: ENat.natCast_toNat_eq_self, f.weightedHomogeneousComponent, f.weightedOrder, g.weightedHomogeneousComponent, g.weightedOrder, le_antisymm, le_weightedOrder_mul, lt_top_iff_ne_top, natCast_toNat_eq_self, weightedHomogeneousComponent, weightedOrder
-/
theorem weightedOrder_mul (w : σ -> Nat) (f g : MvPowerSeries σ R) :
    (f * g).weightedOrder w = f.weightedOrder w + g.weightedOrder w := by
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let p := (f.weightedOrder w).toNat
      have hp : p = f.weightedOrder w := by
        simpa only [p, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      let q := (g.weightedOrder w).toNat
      have hq : q = g.weightedOrder w := by
        simpa only [q, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      have : f.weightedHomogeneousComponent w p * g.weightedHomogeneousComponent w q != 0 := by
        simp only [ne_eq, mul_eq_zero]
        intro H
        rcases H with H | H <;>
        · refine weightedHomogeneousComponent_of_weightedOrder ?_ H
          simp only [ENat.natCast_toNat_eq_self, ne_eq, weightedOrder_eq_top_iff, p, q]
          rw [← ne_eq]; rw [ne_zero_iff_weightedOrder_finite w]
          exact ENat.natCast_toNat (ne_top_of_lt (by simpa))
      rw [← weightedHomogeneousComponent_mul_of_le_weightedOrder
          (le_of_eq hp) (le_of_eq hq)] at this
      rw [← hp]; rw [← hq]; rw [← Nat.cast_add]; rw [← not_lt]
      intro H
      apply this
      apply weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero H
    · rw [not_lt_top_iff] at hg
      simp [hg]
  · rw [not_lt_top_iff] at hf
    simp [hf]

/--
theorem `weightedOrder_prod` / 定理 `weightedOrder_prod`

English:
theorem weightedOrder_prod
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons ha, Finset.prod_cons ha, weightedOrder_mul, ih]

中文:
定理 weightedOrder_prod
  结论: {R : 类型} [交换半环 R] [无零因子 R] [非平凡 R]
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons ha, Finset.prod_cons ha, weightedOrder_mul, ih]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_cons, Finset.sum_cons, cons_induction, prod_cons, sum_cons, weightedOrder_mul
-/
theorem weightedOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {ι : Type*} (w : σ -> Nat) (f : ι -> MvPowerSeries σ R) (s : Finset ι) :
    (∏ i in s, f i).weightedOrder w = ∑ i in s, (f i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons ha, Finset.prod_cons ha, weightedOrder_mul, ih]

/--
theorem `order_mul` / 定理 `order_mul`

English:
theorem order_mul
  given: (f g : MvPowerSeries σ R)
  proof: weightedOrder_mul _ f g

中文:
定理 order_mul
  条件: (f g : MvPowerSeries σ R)
  证明: weightedOrder_mul _ f g

Depends on / 依赖: weightedOrder_mul
-/
theorem order_mul (f g : MvPowerSeries σ R) :
    (f * g).order = f.order + g.order :=
  weightedOrder_mul _ f g

/--
theorem `order_prod` / 定理 `order_prod`

English:
theorem order_prod
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
  proof: weightedOrder_prod _ _ _

中文:
定理 order_prod
  结论: {R : 类型} [交换半环 R] [无零因子 R] [非平凡 R]
  证明: weightedOrder_prod _ _ _

Depends on / 依赖: weightedOrder_prod
-/
theorem order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {ι : Type*} (f : ι -> MvPowerSeries σ R) (s : Finset ι) :
    (∏ i in s, f i).order = ∑ i in s, (f i).order := weightedOrder_prod _ _ _

end MvPowerSeries

end
