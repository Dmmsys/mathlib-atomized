/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Data.Int.WithZero

/-!
# Discrete valuations have rank one

## Main Definitions and Results
* `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt` : the order-preserving isomorphism
  between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
* `Valuation.IsRankOneDiscrete.rankOne` : a discrete valuation has rank one.

## Tags
valuation, discrete, rank one
-/

@[expose] public section

namespace Valuation.IsRankOneDiscrete

open WithZero MonoidWithZeroHom NNReal WithZeroMulInt

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {R : Type*} [Ring R]

section LinearOrderedCommGroupWithZero

variable (v : Valuation R Γ) [hv : v.IsRankOneDiscrete]

/-- An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase. -/
@[simps!]
/--
Definition of `valueGroup₀_equiv_withZeroMulInt` / `valueGroup₀_equiv_withZeroMulInt` 的定义

English:
definition valueGroup₀_equiv_withZeroMulInt
  signature: : ValueGroup₀ (.ofClass v) ≃*o Intᵐ⁰ where
  body: MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generato

中文:
定义 valueGroup₀_equiv_withZeroMul整数
  签名: : ValueGroup₀ (.ofClass v) ≃*o 整数ᵐ⁰ where
  定义体: MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generato

Depends on / 依赖: MulEquiv, MulEquiv.withZero, intEquivOfZPowersEqTop, withZero
-/
noncomputable def valueGroup₀_equiv_withZeroMulInt : ValueGroup₀ (.ofClass v) ≃*o Intᵐ⁰ where
  __ := MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le]

/--
lemma `valueGroup₀_equiv_withZeroMulInt_apply_zero` / 引理 `valueGroup₀_equiv_withZeroMulInt_apply_zero`

English:
lemma valueGroup₀_equiv_withZeroMulInt_apply_zero
  proof: by simp

中文:
引理 valueGroup₀_equiv_withZeroMul整数_apply_zero
  证明: by simp
-/
lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp

/--
lemma `valueGroup₀_equiv_withZeroMulInt_apply_zpow` / 引理 `valueGroup₀_equiv_withZeroMulInt_apply_zpow`

English:
lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow
  given: (k : Int)
  proof: by
  simp [WithZero.exp, ← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

中文:
引理 valueGroup₀_equiv_withZeroMul整数_apply_zpow
  条件: (k : 整数)
  证明: by
  simp [WithZero.exp, ← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

Depends on / 依赖: Subgroup, Subgroup.zpowers_inv, WithZero, WithZero.exp, _zpowers_eq_top, generator, hv.generator, mulintEquivOfZPowersEqTop_symm_apply_zpow, zpowers_inv
-/
lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : Int) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator' ^ k) = WithZero.exp (- k) := by
  simp [WithZero.exp, ← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

/--
lemma `valueGroup₀_equiv_withZeroMulInt_strictMono` / 引理 `valueGroup₀_equiv_withZeroMulInt_strictMono`

English:
lemma valueGroup₀_equiv_withZeroMulInt_strictMono
  proof: by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

中文:
引理 valueGroup₀_equiv_withZeroMul整数_strictMono
  证明: by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

Depends on / 依赖: Left.one_lt_inv_iff.mpr, MulEquiv, MulEquiv.strictMono_symm, Subgroup, Subgroup.zpowers_inv, WithZero, WithZero.map, _lt_one, _strictMono, _zpowers_eq_top, generator, hv.generator, lt_iff_lt, mulintEquivOfZPowersEqTop_strictMono, one_lt_inv_iff, strictMono_symm, zpowers_inv
-/
lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) := by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

/-- A discrete valuation has rank one. -/
@[instance_reducible]
/--
Definition of `rankOne` / `rankOne` 的定义

English:
definition rankOne
  signature: {e : Real>=0} (he : 1 < e)
  body: (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

中文:
定义 rankOne
  签名: {e : 实数>=0} (he : 1 < e)
  定义体: (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

Depends on / 依赖: lt_trans, ne_of_gt, toNNReal, zero_lt_one
-/
noncomputable def rankOne {e : Real>=0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R Intᵐ⁰} [hv : v.IsRankOneDiscrete]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective` / 引理 `valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective`

English:
lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
  statement: (hsurj : Function.Surjective v)
  proof: by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0 <;>
  simp only [MonoidWithZeroHom.coe_ofClass] at h0
  · simp [h0]
  · rw [WithZero.map'_coe, ← coe_unzero h0, WithZero.coe_inj,
    ← (MulEquiv.injective (intEquivOf

中文:
引理 valueGroup₀_equiv_withZeroMul整数_restrict_apply_of_surjective
  结论: (hsurj : 函数.满射 v)
  证明: by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0 <;>
  simp only [MonoidWithZeroHom.coe_ofClass] at h0
  · simp [h0]
  · rw [WithZero.map'_coe, ← coe_unzero h0, WithZero.coe_inj,
    ← (MulEquiv.injective (intEquivOf

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_ofClass, MulEquiv, MulEquiv.injective, Subgroup, Subgroup.zpowers_inv, Valuation, Valuation.restrict_def, WithZero, WithZero.coe_inj, WithZero.map, _coe, _zpowers_eq_top, coe_inj, coe_ofClass, coe_unzero, eq_iff, exp_log, generator, generator_eq_exp_neg_one_of_surjective
-/
lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj : Function.Surjective v)
    (x : R) : (valueGroup₀_equiv_withZeroMulInt v) (v.restrict x) = v x := by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0 <;>
  simp only [MonoidWithZeroHom.coe_ofClass] at h0
  · simp [h0]
  · rw [WithZero.map'_coe, ← coe_unzero h0, WithZero.coe_inj,
    ← (MulEquiv.injective (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top))).eq_iff]
    ext
    simp [generator', generator_eq_exp_neg_one_of_surjective hsurj, toAdd_unzero_eq_log h0,
      exp_log h0]

end WithZeroMulInt

end Ring

end Valuation.IsRankOneDiscrete
