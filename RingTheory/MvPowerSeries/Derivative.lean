/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Formal partial derivatives of multivariate power series

This file defines `MvPowerSeries.pderiv R i`, the formal partial derivative of a multivariate
power series with respect to variable `i`, as a
`Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)`.

See also `PowerSeries.derivative` for the univariate setting.

## Main definitions

- `MvPowerSeries.pderiv R i`: the formal partial derivative with respect to `i`, as a derivation.

## Main results

- `MvPowerSeries.coeff_pderiv`: coefficient formula
  `coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)`.
- `MvPowerSeries.pderiv_coe`: compatibility with `MvPolynomial.pderiv`.
- `MvPowerSeries.trunc_pderiv`: truncation commutes with partial differentiation.
- `MvPowerSeries.pderiv.ext`: a power series is determined by its constant term and its partial
  derivatives.
- `MvPowerSeries.pderiv_pow`: power rule.
- `MvPowerSeries.pderiv_inv`, `MvPowerSeries.pderiv_inv'`: derivative of an inverse.

-/

@[expose] public section

namespace MvPowerSeries

open MvPolynomial Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/--
Definition of `pderivFun` / `pderivFun` 的定义

English:
definition pderivFun
  signature: (i : σ) (f : MvPowerSeries σ R)
  body: fun d => coeff (d + single i 1) f * (d i + 1)

中文:
定义 pderivFun
  签名: (i : σ) (f : MvPowerSeries σ R)
  定义体: fun d => coeff (d + single i 1) f * (d i + 1)

Depends on / 依赖: single
-/
noncomputable def pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d => coeff (d + single i 1) f * (d i + 1)

/--
theorem `coeff_pderivFun` / 定理 `coeff_pderivFun`

English:
theorem coeff_pderivFun
  given: {i : σ} (f : MvPowerSeries σ R) (d : σ ->₀ Nat)
  proof: by
  rfl

中文:
定理 coeff_pderivFun
  条件: {i : σ} (f : MvPowerSeries σ R) (d : σ ->₀ 自然数)
  证明: by
  rfl
-/
theorem coeff_pderivFun {i : σ} (f : MvPowerSeries σ R) (d : σ ->₀ Nat) :
    coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d i + 1) := by
  rfl

/--
theorem `pderivFun_add` / 定理 `pderivFun_add`

English:
theorem pderivFun_add
  given: {i : σ} (f g : MvPowerSeries σ R)
  proof: by
  ext
  rw [coeff_pderivFun]; rw [map_add]; rw [map_add]; rw [coeff_pderivFun]; rw [coeff_pderivFun]; rw [add_mul]

中文:
定理 pderivFun_add
  条件: {i : σ} (f g : MvPowerSeries σ R)
  证明: by
  ext
  rw [coeff_pderivFun]; rw [map_add]; rw [map_add]; rw [coeff_pderivFun]; rw [coeff_pderivFun]; rw [add_mul]

Depends on / 依赖: add_mul, coeff_pderivFun, map_add
-/
theorem pderivFun_add {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f + g) = pderivFun i f + pderivFun i g := by
  ext
  rw [coeff_pderivFun]; rw [map_add]; rw [map_add]; rw [coeff_pderivFun]; rw [coeff_pderivFun]; rw [add_mul]

/--
theorem `pderivFun_C` / 定理 `pderivFun_C`

English:
theorem pderivFun_C
  given: {i : σ} (r : R)
  statement: pderivFun i (C r) = 0
  proof: by
  ext n
  rw [coeff_pderivFun]; rw [coeff_add_single_C]; rw [zero_mul]; rw [(coeff n).map_zero]

中文:
定理 pderivFun_C
  条件: {i : σ} (r : R)
  结论: pderivFun i (C r) = 0
  证明: by
  ext n
  rw [coeff_pderivFun]; rw [coeff_add_single_C]; rw [zero_mul]; rw [(coeff n).map_zero]

Depends on / 依赖: coeff_add_single_C, coeff_pderivFun, map_zero, zero_mul
-/
theorem pderivFun_C {i : σ} (r : R) : pderivFun i (C r) = 0 := by
  ext n
  rw [coeff_pderivFun]; rw [coeff_add_single_C]; rw [zero_mul]; rw [(coeff n).map_zero]

/--
theorem `pderivFun_one` / 定理 `pderivFun_one`

English:
theorem pderivFun_one
  given: {i : σ}
  statement: pderivFun i (1 : MvPowerSeries σ R) = 0
  proof: by
  rw [← map_one C]; rw [pderivFun_C (1 : R)]

中文:
定理 pderivFun_one
  条件: {i : σ}
  结论: pderivFun i (1 : MvPowerSeries σ R) = 0
  证明: by
  rw [← map_one C]; rw [pderivFun_C (1 : R)]

Depends on / 依赖: map_one, pderivFun_C
-/
theorem pderivFun_one {i : σ} : pderivFun i (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one C]; rw [pderivFun_C (1 : R)]

end Semiring

section CommSemiring

variable [CommSemiring R]

/--
theorem `pderivFun_coe` / 定理 `pderivFun_coe`

English:
theorem pderivFun_coe
  given: {i : σ} (f : MvPolynomial σ R)
  proof: by
  ext
  rw [coeff_pderivFun]; rw [coeff_coe]; rw [coeff_coe]; rw [coeff_pderiv]

中文:
定理 pderivFun_coe
  条件: {i : σ} (f : 多元多项式 σ R)
  证明: by
  ext
  rw [coeff_pderivFun]; rw [coeff_coe]; rw [coeff_coe]; rw [coeff_pderiv]
-/
private theorem pderivFun_coe {i : σ} (f : MvPolynomial σ R) :
    (f : MvPowerSeries σ R).pderivFun i = f.pderiv i := by
  ext
  rw [coeff_pderivFun]; rw [coeff_coe]; rw [coeff_coe]; rw [coeff_pderiv]

/--
theorem `trunc_pderivFun` / 定理 `trunc_pderivFun`

English:
theorem trunc_pderivFun
  given: [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat)
  proof: by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, if_pos (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, if_neg ((add_lt_add_iff_right _).not.mpr h), zero_mul]

中文:
定理 trunc_pderivFun
  条件: [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ 自然数)
  证明: by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, if_pos (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, if_neg ((add_lt_add_iff_right _).not.mpr h), zero_mul]
-/
private theorem trunc_pderivFun [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat) :
    trunc R n (pderivFun i f) = pderiv i (trunc R (n + single i 1) f) := by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, if_pos (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, if_neg ((add_lt_add_iff_right _).not.mpr h), zero_mul]

-- A special case of `pderivFun_mul`, used in its proof.
/--
theorem `pderivFun_coe_mul_coe` / 定理 `pderivFun_coe_mul_coe`

English:
theorem pderivFun_coe_mul_coe
  given: {i : σ} (f g : MvPolynomial σ R)
  proof: by
  rw [← coe_mul]; rw [pderivFun_coe]; rw [pderiv_mul]; rw [add_comm]; rw [mul_comm _ g]; rw [← coe_mul]; rw [← coe_mul]; rw [MvPolynomial.coe_add]

中文:
定理 pderivFun_coe_mul_coe
  条件: {i : σ} (f g : 多元多项式 σ R)
  证明: by
  rw [← coe_mul]; rw [pderivFun_coe]; rw [pderiv_mul]; rw [add_comm]; rw [mul_comm _ g]; rw [← coe_mul]; rw [← coe_mul]; rw [MvPolynomial.coe_add]
-/
private theorem pderivFun_coe_mul_coe {i : σ} (f g : MvPolynomial σ R) :
    pderivFun i (f * g : MvPowerSeries σ R) = f * pderiv i g + g * pderiv i f := by
  rw [← coe_mul]; rw [pderivFun_coe]; rw [pderiv_mul]; rw [add_comm]; rw [mul_comm _ g]; rw [← coe_mul]; rw [← coe_mul]; rw [MvPolynomial.coe_add]

/--
theorem `pderivFun_mul` / 定理 `pderivFun_mul`

English:
theorem pderivFun_mul
  given: {i : σ} (f g : MvPowerSeries σ R)
  proof: by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun]; rw [map_add]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁]; rw [trunc_pderivFun]; rw [trunc_pderivFun]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← map_add]; rw [coe_mul]; rw [coe_mul]; rw [coe_mul]; rw [← pderivFun_coe_mul_coe]; rw [coeff_pderivFun]

中文:
定理 pderivFun_mul
  条件: {i : σ} (f g : MvPowerSeries σ R)
  证明: by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun]; rw [map_add]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁]; rw [trunc_pderivFun]; rw [trunc_pderivFun]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← map_add]; rw [coe_mul]; rw [coe_mul]; rw [coe_mul]; rw [← pderivFun_coe_mul_coe]; rw [coeff_pderivFun]
-/
private theorem pderivFun_mul {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f * g) = f • g.pderivFun i + g • f.pderivFun i := by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun]; rw [map_add]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁]; rw [← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁]; rw [trunc_pderivFun]; rw [trunc_pderivFun]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← coeff_coe]; rw [← map_add]; rw [coe_mul]; rw [coe_mul]; rw [coe_mul]; rw [← pderivFun_coe_mul_coe]; rw [coeff_pderivFun]

/--
theorem `pderivFun_smul` / 定理 `pderivFun_smul`

English:
theorem pderivFun_smul
  given: {i : σ} (r : R) (f : MvPowerSeries σ R)
  proof: by
  rw [smul_eq_C_mul]; rw [smul_eq_C_mul]; rw [pderivFun_mul]; rw [pderivFun_C]; rw [smul_zero]; rw [add_zero]; rw [smul_eq_mul]

中文:
定理 pderivFun_smul
  条件: {i : σ} (r : R) (f : MvPowerSeries σ R)
  证明: by
  rw [smul_eq_C_mul]; rw [smul_eq_C_mul]; rw [pderivFun_mul]; rw [pderivFun_C]; rw [smul_zero]; rw [add_zero]; rw [smul_eq_mul]
-/
private theorem pderivFun_smul {i : σ} (r : R) (f : MvPowerSeries σ R) :
    pderivFun i (r • f) = r • pderivFun i f := by
  rw [smul_eq_C_mul]; rw [smul_eq_C_mul]; rw [pderivFun_mul]; rw [pderivFun_C]; rw [smul_zero]; rw [add_zero]; rw [smul_eq_mul]

variable (R) in
/-- The formal partial derivative of a multivariate formal power series with respect to
variable `i`, as an `R`-derivation on `MvPowerSeries σ R`. -/
@[no_expose]
/--
Definition of `pderiv` / `pderiv` 的定义

English:
definition pderiv
  signature: (i : σ)
  body: pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul

中文:
定义 pderiv
  签名: (i : σ)
  定义体: pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul

Depends on / 依赖: pderivFun
-/
noncomputable def pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul

/--
theorem `pderiv_C` / 定理 `pderiv_C`

English:
theorem pderiv_C
  given: {i : σ} {r : R}
  statement: pderiv R i (C r) = 0
  proof: pderivFun_C r

中文:
定理 pderiv_C
  条件: {i : σ} {r : R}
  结论: pderiv R i (C r) = 0
  证明: pderivFun_C r
-/
@[simp] theorem pderiv_C {i : σ} {r : R} : pderiv R i (C r) = 0 := pderivFun_C r

/--
theorem `pderiv_one` / 定理 `pderiv_one`

English:
theorem pderiv_one
  given: {i : σ}
  statement: pderiv R i 1 = 0
  proof: pderiv_C

中文:
定理 pderiv_one
  条件: {i : σ}
  结论: pderiv R i 1 = 0
  证明: pderiv_C

Depends on / 依赖: pderiv_C
-/
theorem pderiv_one {i : σ} : pderiv R i 1 = 0 := pderiv_C

/--
theorem `coeff_pderiv` / 定理 `coeff_pderiv`

English:
theorem coeff_pderiv
  given: {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat)
  proof: coeff_pderivFun f n

中文:
定理 coeff_pderiv
  条件: {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ 自然数)
  证明: coeff_pderivFun f n

Depends on / 依赖: coeff_pderivFun
-/
theorem coeff_pderiv {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat) :
    coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1) :=
  coeff_pderivFun f n

/--
theorem `pderiv_coe` / 定理 `pderiv_coe`

English:
theorem pderiv_coe
  given: {i : σ} (f : MvPolynomial σ R)
  proof: pderivFun_coe f

@[simp]

中文:
定理 pderiv_coe
  条件: {i : σ} (f : 多元多项式 σ R)
  证明: pderivFun_coe f

@[simp]

Depends on / 依赖: pderivFun_coe
-/
theorem pderiv_coe {i : σ} (f : MvPolynomial σ R) :
    pderiv R i f = MvPolynomial.pderiv i f := pderivFun_coe f

@[simp]
/--
theorem `pderiv_X_self` / 定理 `pderiv_X_self`

English:
theorem pderiv_X_self
  given: {i : σ}
  statement: pderiv R i (X i) = 1
  proof: by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]

中文:
定理 pderiv_X_self
  条件: {i : σ}
  结论: pderiv R i (X i) = 1
  证明: by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: add_eq_right, boole_mul, classical, coeff_X, coeff_one, coeff_pderiv, split_ifs
-/
theorem pderiv_X_self {i : σ} : pderiv R i (X i) = 1 := by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]
/--
theorem `pderiv_X_of_ne` / 定理 `pderiv_X_of_ne`

English:
theorem pderiv_X_of_ne
  given: {i j : σ} (h : j != i)
  statement: pderiv R i (X j) = 0
  proof: by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    if_neg (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)

中文:
定理 pderiv_X_of_ne
  条件: {i j : σ} (h : j != i)
  结论: pderiv R i (X j) = 0
  证明: by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    if_neg (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)

Depends on / 依赖: Finsupp, Finsupp.add_apply, add_apply, boole_mul, classical, coeff_X, coeff_pderiv, coeff_zero, if_neg, ne_iff, ne_iff.mpr
-/
theorem pderiv_X_of_ne {i j : σ} (h : j != i) : pderiv R i (X j) = 0 := by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    if_neg (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)

/--
theorem `pderiv_X` / 定理 `pderiv_X`

English:
theorem pderiv_X
  given: [DecidableEq σ] (i j : σ)
  proof: by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]

中文:
定理 pderiv_X
  条件: [DecidableEq σ] (i j : σ)
  证明: by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]

Depends on / 依赖: MvPowerSeries, Pi.single_eq_same, pderiv_X_of_ne, pderiv_X_self, single_eq_same
-/
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv R i (X j) = Pi.single (M := fun _ => MvPowerSeries σ R) i 1 j := by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]

/--
theorem `trunc_pderiv` / 定理 `trunc_pderiv`

English:
theorem trunc_pderiv
  given: [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat)
  proof: trunc_pderivFun ..

中文:
定理 trunc_pderiv
  条件: [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ 自然数)
  证明: trunc_pderivFun ..

Depends on / 依赖: trunc_pderivFun
-/
theorem trunc_pderiv [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ ->₀ Nat) :
    trunc R n (pderiv R i f) = MvPolynomial.pderiv i (trunc R (n + single i 1) f) :=
  trunc_pderivFun ..

/--
theorem `pderiv_pow` / 定理 `pderiv_pow`

English:
theorem pderiv_pow
  given: {i : σ} (g : MvPowerSeries σ R) (n : Nat)
  proof: by
  rw [Derivation.leibniz_pow]; rw [smul_eq_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]

中文:
定理 pderiv_pow
  条件: {i : σ} (g : MvPowerSeries σ R) (n : 自然数)
  证明: by
  rw [Derivation.leibniz_pow]; rw [smul_eq_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]

Depends on / 依赖: Derivation, Derivation.leibniz_pow, leibniz_pow, mul_assoc, nsmul_eq_mul, smul_eq_mul
-/
theorem pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n : Nat) :
    pderiv R i (g ^ n) = n * g ^ (n - 1) * pderiv R i g := by
  rw [Derivation.leibniz_pow]; rw [smul_eq_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]

end CommSemiring

/--
theorem `pderiv.ext` / 定理 `pderiv.ext`

English:
theorem pderiv.ext
  statement: [CommRing R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R}
  proof: by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i != 0⟩ := ne_iff.mp h
  have : single i 1 <= n := fun j => by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]

中文:
定理 pderiv.ext
  结论: [交换环 R] [是加法无挠 R] {f g : MvPowerSeries σ R}
  证明: by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i != 0⟩ := ne_iff.mp h
  have : single i 1 <= n := fun j => by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]

Depends on / 依赖: Nat.cast_one, Nat.cast_sub, Nat.one_le_iff_ne_zero.mpr, Pi.sub_apply, cast_one, cast_sub, coe_tsub, coeff_pderiv, coeff_zero_eq_constantCoeff, mul_comm, ne_iff, ne_iff.mp, nsmul_eq_mul, one_le_iff_ne_zero, single, single_eq_of_ne, single_eq_same, smul_right, sub_add_cancel, sub_apply
-/
theorem pderiv.ext [CommRing R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R}
    (hD : forall i, pderiv R i f = pderiv R i g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i != 0⟩ := ne_iff.mp h
  have : single i 1 <= n := fun j => by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]
/--
theorem `pderiv_inv` / 定理 `pderiv_inv`

English:
theorem pderiv_inv
  given: {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ)
  proof: (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]

中文:
定理 pderiv_inv
  条件: {i : σ} [交换环 R] (f : (MvPowerSeries σ R)ˣ)
  证明: (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]

Depends on / 依赖: f.inv_mul, inv_mul, leibniz_of_mul_eq_one, pderiv
-/
theorem pderiv_inv {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ) :
    pderiv R i ↑f⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]
/--
theorem `pderiv_invOf` / 定理 `pderiv_invOf`

English:
theorem pderiv_invOf
  given: {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f]
  proof: (pderiv R i).leibniz_invOf f

中文:
定理 pderiv_invOf
  条件: {i : σ} [交换环 R] (f : MvPowerSeries σ R) [可逆 f]
  证明: (pderiv R i).leibniz_invOf f

Depends on / 依赖: leibniz_invOf, pderiv
-/
theorem pderiv_invOf {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f] :
    pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv (MvPowerSeries σ R)` for more general base rings `R`.
-/

@[simp]
/--
theorem `pderiv_inv'` / 定理 `pderiv_inv'`

English:
theorem pderiv_inv'
  given: {i : σ} [Field R] (f : MvPowerSeries σ R)
  proof: by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this]; rw [pow_two]; rw [zero_mul]; rw [neg_zero]; rw [zero_mul]; rw [map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

中文:
定理 pderiv_inv'
  条件: {i : σ} [域 R] (f : MvPowerSeries σ R)
  证明: by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this]; rw [pow_two]; rw [zero_mul]; rw [neg_zero]; rw [zero_mul]; rw [map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

Depends on / 依赖: Derivation, Derivation.leibniz_of_mul_eq_one, MvPowerSeries, MvPowerSeries.inv_eq_zero, MvPowerSeries.inv_mul_cancel, constantCoeff, inv_eq_zero, inv_mul_cancel, leibniz_of_mul_eq_one, map_zero, neg_zero, pow_two, zero_mul
-/
theorem pderiv_inv' {i : σ} [Field R] (f : MvPowerSeries σ R) :
    pderiv R i f⁻¹ = -f⁻¹ ^ 2 * pderiv R i f := by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this]; rw [pow_two]; rw [zero_mul]; rw [neg_zero]; rw [zero_mul]; rw [map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

end MvPowerSeries
