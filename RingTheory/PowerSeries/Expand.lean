/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
## Expand power series

Given a power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `PowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `PowerSeries.expand`: expand a power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace PowerSeries

variable {τ R S : Type*} [CommRing R] [CommRing S] (p : Nat) (hp : p != 0)

/--
Definition of `expand` / `expand` 的定义

English:
definition expand
  signature: : PowerSeries R ->ₐ[R] PowerSeries R
  body: MvPowerSeries.expand p hp

中文:
定义 expand
  签名: : PowerSeries R ->ₐ[R] PowerSeries R
  定义体: MvPowerSeries.expand p hp

Depends on / 依赖: MvPowerSeries, MvPowerSeries.expand, expand
-/
noncomputable def expand : PowerSeries R ->ₐ[R] PowerSeries R :=
  MvPowerSeries.expand p hp

/--
theorem `expand_apply` / 定理 `expand_apply`

English:
theorem expand_apply
  given: (f : PowerSeries R)
  statement: expand p hp f = subst (X ^ p) f
  proof: by
  simp [expand, MvPowerSeries.expand, subst, X]

中文:
定理 expand_apply
  条件: (f : PowerSeries R)
  结论: expand p hp f = subst (X ^ p) f
  证明: by
  simp [expand, MvPowerSeries.expand, subst, X]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.expand, expand
-/
theorem expand_apply (f : PowerSeries R) : expand p hp f = subst (X ^ p) f := by
  simp [expand, MvPowerSeries.expand, subst, X]

/--
theorem `expand_C` / 定理 `expand_C`

English:
theorem expand_C
  given: (r : R)
  statement: expand p hp (C r : PowerSeries R) = C r
  proof: by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

中文:
定理 expand_C
  条件: (r : R)
  结论: expand p hp (C r : PowerSeries R) = C r
  证明: by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

Depends on / 依赖: AlgHom, AlgHom.map_smul_of_tower, conv_lhs, expand, map_one, map_smul_of_tower, mul_one, smul_eq_C_mul
-/
theorem expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

/--
theorem `expand_mul_eq_comp` / 定理 `expand_mul_eq_comp`

English:
theorem expand_mul_eq_comp
  given: (q : Nat) (hq : q != 0)
  proof: by
  ext1 i
  simp [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]

中文:
定理 expand_mul_eq_comp
  条件: (q : 自然数) (hq : q != 0)
  证明: by
  ext1 i
  simp [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.expand_mul_eq_comp, expand, expand_mul_eq_comp
-/
theorem expand_mul_eq_comp (q : Nat) (hq : q != 0) :
    expand (p * q) (p.mul_ne_zero hp hq) = (expand p hp (R := R)).comp (expand q hq) := by
  ext1 i
  simp [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]

/--
theorem `expand_mul` / 定理 `expand_mul`

English:
theorem expand_mul
  given: (q : Nat) (hq : q != 0) (φ : PowerSeries R)
  proof: DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

中文:
定理 expand_mul
  条件: (q : 自然数) (hq : q != 0) (φ : PowerSeries R)
  证明: DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, expand_mul_eq_comp
-/
theorem expand_mul (q : Nat) (hq : q != 0) (φ : PowerSeries R) :
    φ.expand (p * q) (p.mul_ne_zero hp hq) = (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

/--
theorem `expand_smul` / 定理 `expand_smul`

English:
theorem expand_smul
  given: (a : R) (φ : PowerSeries R)
  proof: AlgHom.map_smul_of_tower _ _ _

@[simp]

中文:
定理 expand_smul
  条件: (a : R) (φ : PowerSeries R)
  证明: AlgHom.map_smul_of_tower _ _ _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.map_smul_of_tower, map_smul_of_tower
-/
theorem expand_smul (a : R) (φ : PowerSeries R) :
    expand p hp (a • φ) = a • φ.expand p hp := AlgHom.map_smul_of_tower _ _ _

@[simp]
/--
theorem `expand_X` / 定理 `expand_X`

English:
theorem expand_X
  statement: expand p hp (X (R := R)) = X ^ p
  proof: substAlgHom_X (HasSubst.X_pow hp)

@[simp]

中文:
定理 expand_X
  结论: expand p hp (X (R := R)) = X ^ p
  证明: substAlgHom_X (HasSubst.X_pow hp)

@[simp]
-/
theorem expand_X : expand p hp (X (R := R)) = X ^ p :=
  substAlgHom_X (HasSubst.X_pow hp)

@[simp]
/--
theorem `expand_monomial` / 定理 `expand_monomial`

English:
theorem expand_monomial
  given: (d : Nat) (r : R)
  proof: by
  simp [expand, monomial, MvPowerSeries.expand_monomial]

@[simp]

中文:
定理 expand_monomial
  条件: (d : 自然数) (r : R)
  证明: by
  simp [expand, monomial, MvPowerSeries.expand_monomial]

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.expand_monomial, expand, expand_monomial, monomial
-/
theorem expand_monomial (d : Nat) (r : R) :
    expand p hp (monomial d r) = monomial (p * d) r := by
  simp [expand, monomial, MvPowerSeries.expand_monomial]

@[simp]
/--
theorem `expand_one` / 定理 `expand_one`

English:
theorem expand_one
  statement: expand 1 one_ne_zero = AlgHom.id R (PowerSeries R)
  proof: by
  simp [expand]

中文:
定理 expand_one
  结论: expand 1 one_ne_zero = AlgHom.id R (PowerSeries R)
  证明: by
  simp [expand]

Depends on / 依赖: expand
-/
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (PowerSeries R) := by
  simp [expand]

/--
theorem `expand_one_apply` / 定理 `expand_one_apply`

English:
theorem expand_one_apply
  given: (f : PowerSeries R)
  statement: expand 1 one_ne_zero f = f
  proof: by simp

@[simp]

中文:
定理 expand_one_apply
  条件: (f : PowerSeries R)
  结论: expand 1 one_ne_zero f = f
  证明: by simp

@[simp]
-/
theorem expand_one_apply (f : PowerSeries R) : expand 1 one_ne_zero f = f := by simp

@[simp]
/--
theorem `map_expand` / 定理 `map_expand`

English:
theorem map_expand
  given: (f : R ->+* S) (φ : PowerSeries R)
  proof: by
  simp [map, expand, MvPowerSeries.map_expand]

中文:
定理 map_expand
  条件: (f : R ->+* S) (φ : PowerSeries R)
  证明: by
  simp [map, expand, MvPowerSeries.map_expand]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map_expand, expand, map_expand
-/
theorem map_expand (f : R ->+* S) (φ : PowerSeries R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [map, expand, MvPowerSeries.map_expand]

/--
theorem `expand_subst` / 定理 `expand_subst`

English:
theorem expand_subst
  given: {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S)
  proof: by
  rw [PowerSeries.subst]; rw [MvPowerSeries.expand_subst _ hp (HasSubst.const hf) (φ := φ)]; rw [PowerSeries.subst]

中文:
定理 expand_subst
  条件: {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S)
  证明: by
  rw [PowerSeries.subst]; rw [MvPowerSeries.expand_subst _ hp (HasSubst.const hf) (φ := φ)]; rw [PowerSeries.subst]

Depends on / 依赖: HasSubst, HasSubst.const, MvPowerSeries, MvPowerSeries.expand_subst, PowerSeries, PowerSeries.subst, expand_subst
-/
theorem expand_subst {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S) :
    (subst f φ).expand p hp = subst (f.expand p hp) φ := by
  rw [PowerSeries.subst]; rw [MvPowerSeries.expand_subst _ hp (HasSubst.const hf) (φ := φ)]; rw [PowerSeries.subst]

/- TODO : In the original file of multivariate polynomial, there are two theorems about rename
here, but we don't have rename for multivariate power series. And for `eval₂Hom`, `eval₂`
and `aeval`, the expression does not look good. -/

variable (φ : PowerSeries R) (q : Nat) (hq : 0 < q)

@[simp]
/--
theorem `coeff_expand_mul` / 定理 `coeff_expand_mul`

English:
theorem coeff_expand_mul
  given: (m : Nat)
  proof: by
  rw [coeff]; rw [coeff]; rw [expand]; rw [← smul_eq_mul]; rw [← Finsupp.smul_single]; rw [MvPowerSeries.coeff_expand_smul]

@[simp]

中文:
定理 coeff_expand_mul
  条件: (m : 自然数)
  证明: by
  rw [coeff]; rw [coeff]; rw [expand]; rw [← smul_eq_mul]; rw [← Finsupp.smul_single]; rw [MvPowerSeries.coeff_expand_smul]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.smul_single, MvPowerSeries, MvPowerSeries.coeff_expand_smul, coeff_expand_smul, expand, smul_eq_mul, smul_single
-/
theorem coeff_expand_mul (m : Nat) :
    (expand p hp φ).coeff (p * m) = φ.coeff m := by
  rw [coeff]; rw [coeff]; rw [expand]; rw [← smul_eq_mul]; rw [← Finsupp.smul_single]; rw [MvPowerSeries.coeff_expand_smul]

@[simp]
/--
theorem `constantCoeff_expand` / 定理 `constantCoeff_expand`

English:
theorem constantCoeff_expand
  given: (φ : PowerSeries R)
  proof: by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
  simp

中文:
定理 constantCoeff_expand
  条件: (φ : PowerSeries R)
  证明: by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
  simp

Depends on / 依赖: coeff_expand_mul, coeff_zero_eq_constantCoeff, conv_lhs, mul_zero
-/
theorem constantCoeff_expand (φ : PowerSeries R) :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
  simp

/--
theorem `coeff_expand_of_not_dvd` / 定理 `coeff_expand_of_not_dvd`

English:
theorem coeff_expand_of_not_dvd
  given: {m : Nat} (h : ¬ p ∣ m)
  proof: by
  rw [coeff]; rw [expand]; rw [MvPowerSeries.coeff_expand_of_not_dvd (i := ())]
  simpa

中文:
定理 coeff_expand_of_not_dvd
  条件: {m : 自然数} (h : ¬ p ∣ m)
  证明: by
  rw [coeff]; rw [expand]; rw [MvPowerSeries.coeff_expand_of_not_dvd (i := ())]
  simpa

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_expand_of_not_dvd, coeff_expand_of_not_dvd, expand
-/
theorem coeff_expand_of_not_dvd {m : Nat} (h : ¬ p ∣ m) :
    (expand p hp φ).coeff m = 0 := by
  rw [coeff]; rw [expand]; rw [MvPowerSeries.coeff_expand_of_not_dvd (i := ())]
  simpa

/--
theorem `support_expand_subset` / 定理 `support_expand_subset`

English:
theorem support_expand_subset
  proof: by
  rw [expand]; rw [MvPowerSeries.support_expand]

中文:
定理 support_expand_subset
  证明: by
  rw [expand]; rw [MvPowerSeries.support_expand]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.support_expand, expand, f.val, support_expand
-/
theorem support_expand_subset :
    (expand p hp φ).support subseteq φ.support.image (p • ·) := by
  rw [expand]; rw [MvPowerSeries.support_expand]

/--
theorem `support_expand` / 定理 `support_expand`

English:
theorem support_expand
  proof: by
  rw [expand]; rw [MvPowerSeries.support_expand]

中文:
定理 support_expand
  证明: by
  rw [expand]; rw [MvPowerSeries.support_expand]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.support_expand, expand, support_expand
-/
theorem support_expand :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  rw [expand]; rw [MvPowerSeries.support_expand]

/--
theorem `coeff_expand` / 定理 `coeff_expand`

English:
theorem coeff_expand
  given: {n : Nat}
  proof: by
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    rw [hq]; rw [coeff_expand_mul]; rw [Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
  exact coeff_expand_of_not_dvd p hp _ h

@[simp]

中文:
定理 coeff_expand
  条件: {n : 自然数}
  证明: by
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    rw [hq]; rw [coeff_expand_mul]; rw [Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
  exact coeff_expand_of_not_dvd p hp _ h

@[simp]

Depends on / 依赖: Nat.mul_div_cancel_left, coeff_expand_mul, coeff_expand_of_not_dvd, mul_div_cancel_left, p.pos_of_ne_zero, pos_of_ne_zero, split_ifs
-/
theorem coeff_expand {n : Nat} :
    (φ.expand p hp).coeff n = if p ∣ n then φ.coeff (n / p) else 0 := by
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    rw [hq]; rw [coeff_expand_mul]; rw [Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
  exact coeff_expand_of_not_dvd p hp _ h

@[simp]
/--
theorem `order_expand` / 定理 `order_expand`

English:
theorem order_expand
  statement: (φ.expand p hp).order = p • φ.order
  proof: by
  simp_rw [expand, order_eq_order, MvPowerSeries.order_expand p hp φ]

中文:
定理 order_expand
  结论: (φ.expand p hp).order = p • φ.order
  证明: by
  simp_rw [expand, order_eq_order, MvPowerSeries.order_expand p hp φ]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.order_expand, expand, order_eq_order, order_expand, simp_rw
-/
theorem order_expand : (φ.expand p hp).order = p • φ.order := by
  simp_rw [expand, order_eq_order, MvPowerSeries.order_expand p hp φ]

end PowerSeries
