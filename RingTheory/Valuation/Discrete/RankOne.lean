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
/-
**Valuation.IsRankOneDiscrete.valueGroup** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.Is
RankOneDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuatio
n and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase.
-/
noncomputable def valueGroup₀_equiv_withZeroMulInt : ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ where
  __ := MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le]
/-
**Valuation.IsRankOneDiscrete.valueGroup** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Is
RankOneDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp
/-
**Valuation.IsRankOneDiscrete.valueGroup** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Is
RankOneDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator' ^ k) = WithZero.exp (- k) := by
  simp [WithZero.exp, ← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]
/-
**Valuation.IsRankOneDiscrete.valueGroup** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Is
RankOneDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) := by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

/-- A discrete valuation has rank one. -/
@[instance_reducible]
/-
**Valuation.IsRankOneDiscrete.rankOne** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsRan
kOneDiscrete`。
形式化陈述：rankOne {e : Real>=0} (he : 1 < e) : v.RankOne where hom'
参数：he : 1 < e。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…

--- 原说明 ---
A discrete valuation has rank one.
-/
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valuation.IsRankOneDiscrete.valueGroup** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Is
RankOneDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

