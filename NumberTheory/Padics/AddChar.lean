/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.Topology.Algebra.Monoid.AddChar
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Additive characters of `ℤ_[p]`

We show that for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, there is a bijection between
continuous additive characters `ℤ_[p] → R` and topologically nilpotent elements of `R`, given by
sending `κ` to the element `κ 1 - 1`. This is used to define the Mahler transform for `p`-adic
measures.

Note that if the norm on `R` is not strictly multiplicative, then the condition that `κ 1 - 1` be
topologically nilpotent is strictly weaker than assuming `‖κ 1 - 1‖ < 1`, although they are
equivalent if `NormMulClass R` holds.

## Main definitions and theorems:

* `addChar_of_value_at_one`: given a topologically nilpotent `r : R`, construct a continuous
  additive character of `ℤ_[p]` mapping `1` to `1 + r`.
* `continuousAddCharEquiv`: for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, the map
  `addChar_of_value_at_one` defines a bijection between continuous additive characters `ℤ_[p] → R`
  and topologically nilpotent elements of `R`.
* `continuousAddCharEquiv_of_norm_mul`: if the norm on `R` is strictly multiplicative (not just
  sub-multiplicative), then `addChar_of_value_at_one` is a bijection between continuous additive
  characters `ℤ_[p] → R` and elements of `R` with `‖r‖ < 1`.

## TODO:

* Show that the above equivalences are homeomorphisms, for appropriate choices of the topology.
-/

@[expose] public section

open scoped fwdDiff
open Filter Topology

variable {p : Nat} [Fact p.Prime]

variable {R : Type*} [NormedRing R] [Algebra Int_[p] R] [IsBoundedSMul Int_[p] R]
  [IsUltrametricDist R]

/--
lemma `AddChar.tendsto_eval_one_sub_pow` / 引理 `AddChar.tendsto_eval_one_sub_pow`

English:
lemma AddChar.tendsto_eval_one_sub_pow
  given: {κ : AddChar Int_[p] R} (hκ : Continuous κ)
  proof: by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n => ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using! fwdDiff_addChar_eq κ 0 1 n

中文:
引理 加法特征.tendsto_eval_one_sub_pow
  条件: {κ : 加法特征 整数_[p] R} (hκ : 连续 κ)
  证明: by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n => ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using! fwdDiff_addChar_eq κ 0 1 n

Depends on / 依赖: AddChar, AddChar.map_zero_eq_one, PadicInt, PadicInt.fwdDiff_tendsto_zero, fwdDiff_addChar_eq, fwdDiff_tendsto_zero, map_zero_eq_one, mul_one
-/
lemma AddChar.tendsto_eval_one_sub_pow {κ : AddChar Int_[p] R} (hκ : Continuous κ) :
    Tendsto (fun n => (κ 1 - 1) ^ n) atTop (𝓝 0) := by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n => ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using! fwdDiff_addChar_eq κ 0 1 n

namespace PadicInt
variable [CompleteSpace R]

/--
Definition of `addChar_of_value_at_one` / `addChar_of_value_at_one` 的定义

English:
definition addChar_of_value_at_one
  signature: (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  body: mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero]; rw [mahlerSeries_apply_nat hr le_rfl]; rw [zero_add]; rw [Finset.sum_range_one]; rw [Nat.choose_self]; rw [pow_zero]; rw [one_smul]
  map_add_eq_mul' a b := by
    let F : C(Int_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : Nat) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl]; rw [(Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [one_pow]; rw [mul_one]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ => ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

@[fun_prop]

中文:
定义 addChar_of_value_at_one
  签名: (r : R) (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  定义体: mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero]; rw [mahlerSeries_apply_nat hr le_rfl]; rw [zero_add]; rw [Finset.sum_range_one]; rw [Nat.choose_self]; rw [pow_zero]; rw [one_smul]
  map_add_eq_mul' a b := by
    let F : C(Int_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : Nat) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl]; rw [(Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [one_pow]; rw [mul_one]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ => ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

@[fun_prop]

Depends on / 依赖: mahlerSeries
-/
noncomputable def addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    AddChar Int_[p] R where
  toFun := mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero]; rw [mahlerSeries_apply_nat hr le_rfl]; rw [zero_add]; rw [Finset.sum_range_one]; rw [Nat.choose_self]; rw [pow_zero]; rw [one_smul]
  map_add_eq_mul' a b := by
    let F : C(Int_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : Nat) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl]; rw [(Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [one_pow]; rw [mul_one]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ => ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

@[fun_prop]
/--
lemma `continuous_addChar_of_value_at_one` / 引理 `continuous_addChar_of_value_at_one`

English:
lemma continuous_addChar_of_value_at_one
  given: {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  proof: map_continuous (mahlerSeries (r ^ ·))

中文:
引理 continuous_addChar_of_value_at_one
  条件: {r : R} (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  证明: map_continuous (mahlerSeries (r ^ ·))

Depends on / 依赖: mahlerSeries, map_continuous
-/
lemma continuous_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    Continuous (addChar_of_value_at_one r hr : Int_[p] -> R) :=
  map_continuous (mahlerSeries (r ^ ·))

/--
lemma `coe_addChar_of_value_at_one` / 引理 `coe_addChar_of_value_at_one`

English:
lemma coe_addChar_of_value_at_one
  given: {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  proof: rfl

@[simp]

中文:
引理 coe_addChar_of_value_at_one
  条件: {r : R} (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  证明: rfl

@[simp]
-/
lemma coe_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (addChar_of_value_at_one r hr : Int_[p] -> R) = mahlerSeries (r ^ ·) :=
  rfl

@[simp]
/--
lemma `addChar_of_value_at_one_def` / 引理 `addChar_of_value_at_one_def`

English:
lemma addChar_of_value_at_one_def
  given: {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  proof: by
  change mahlerSeries (r ^ ·) ↑(1 : Nat) = _
  rw [mahlerSeries_apply_nat hr le_rfl]; rw [Finset.sum_range_succ]; rw [Finset.sum_range_one]; rw [Nat.choose_zero_right]; rw [Nat.choose_self]; rw [one_smul]; rw [one_smul]; rw [pow_zero]; rw [pow_one]

中文:
引理 addChar_of_value_at_one_def
  条件: {r : R} (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  证明: by
  change mahlerSeries (r ^ ·) ↑(1 : Nat) = _
  rw [mahlerSeries_apply_nat hr le_rfl]; rw [Finset.sum_range_succ]; rw [Finset.sum_range_one]; rw [Nat.choose_zero_right]; rw [Nat.choose_self]; rw [one_smul]; rw [one_smul]; rw [pow_zero]; rw [pow_one]

Depends on / 依赖: Finset, Finset.sum_range_one, Finset.sum_range_succ, Nat.choose_self, Nat.choose_zero_right, choose_self, choose_zero_right, le_rfl, mahlerSeries, mahlerSeries_apply_nat, one_smul, pow_one, pow_zero, sum_range_one, sum_range_succ
-/
lemma addChar_of_value_at_one_def {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    addChar_of_value_at_one r hr (1 : Int_[p]) = 1 + r := by
  change mahlerSeries (r ^ ·) ↑(1 : Nat) = _
  rw [mahlerSeries_apply_nat hr le_rfl]; rw [Finset.sum_range_succ]; rw [Finset.sum_range_one]; rw [Nat.choose_zero_right]; rw [Nat.choose_self]; rw [one_smul]; rw [one_smul]; rw [pow_zero]; rw [pow_one]

/--
lemma `eq_addChar_of_value_at_one` / 引理 `eq_addChar_of_value_at_one`

English:
lemma eq_addChar_of_value_at_one
  statement: {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  proof: denseRange_natCast.addChar_eq_of_eval_one_eq hκ (by fun_prop) (by simp [hκ'])

中文:
引理 eq_addChar_of_value_at_one
  结论: {r : R} (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  证明: denseRange_natCast.addChar_eq_of_eval_one_eq hκ (by fun_prop) (by simp [hκ'])

Depends on / 依赖: addChar_eq_of_eval_one_eq, denseRange_natCast, denseRange_natCast.addChar_eq_of_eval_one_eq, fun_prop
-/
lemma eq_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
    {κ : AddChar Int_[p] R} (hκ : Continuous κ) (hκ' : κ 1 = 1 + r) :
    κ = addChar_of_value_at_one r hr :=
  denseRange_natCast.addChar_eq_of_eval_one_eq hκ (by fun_prop) (by simp [hκ'])

variable (p R) in
/--
Definition of `continuousAddCharEquiv` / `continuousAddCharEquiv` 的定义

English:
definition continuousAddCharEquiv
  signature: :
  body: fun ⟨κ, hκ⟩ => ⟨κ 1 - 1, κ.tendsto_eval_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ => ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ => by simpa using (eq_addChar_of_value_at_one _ hκ (by abel)).symm
  right_inv := fun ⟨r, hr⟩ => by simp [addChar_of_value_at_one_def hr]

中文:
定义 continuousAddCharEquiv
  签名: :
  定义体: fun ⟨κ, hκ⟩ => ⟨κ 1 - 1, κ.tendsto_eval_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ => ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ => by simpa using (eq_addChar_of_value_at_one _ hκ (by abel)).symm
  right_inv := fun ⟨r, hr⟩ => by simp [addChar_of_value_at_one_def hr]

Depends on / 依赖: tendsto_eval_one_sub_pow
-/
noncomputable def continuousAddCharEquiv :
    {κ : AddChar Int_[p] R // Continuous κ} ≃ {r : R // Tendsto (r ^ ·) atTop (𝓝 0)} where
  toFun := fun ⟨κ, hκ⟩ => ⟨κ 1 - 1, κ.tendsto_eval_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ => ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ => by simpa using (eq_addChar_of_value_at_one _ hκ (by abel)).symm
  right_inv := fun ⟨r, hr⟩ => by simp [addChar_of_value_at_one_def hr]

/--
lemma `continuousAddCharEquiv_apply` / 引理 `continuousAddCharEquiv_apply`

English:
lemma continuousAddCharEquiv_apply
  given: {κ : AddChar Int_[p] R} (hκ : Continuous κ)
  proof: rfl

中文:
引理 continuousAddCharEquiv_apply
  条件: {κ : 加法特征 整数_[p] R} (hκ : 连续 κ)
  证明: rfl
-/
@[simp] lemma continuousAddCharEquiv_apply {κ : AddChar Int_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl

/--
lemma `continuousAddCharEquiv_symm_apply` / 引理 `continuousAddCharEquiv_symm_apply`

English:
lemma continuousAddCharEquiv_symm_apply
  given: {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
  proof: rfl

中文:
引理 continuousAddCharEquiv_symm_apply
  条件: {r : R} (hr : 收敛 (r ^ ·) atTop (𝓝 0))
  证明: rfl
-/
@[simp] lemma continuousAddCharEquiv_symm_apply {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (continuousAddCharEquiv p R).symm ⟨r, hr⟩ =
    (addChar_of_value_at_one r hr : AddChar Int_[p] R) :=
  rfl

section NormMulClass
variable [NormMulClass R]

variable (p R) in
/--
Definition of `continuousAddCharEquiv_of_norm_mul` / `continuousAddCharEquiv_of_norm_mul` 的定义

English:
definition continuousAddCharEquiv_of_norm_mul
  signature: :
  body: (continuousAddCharEquiv p R).trans
    .subtypeEquivProp (by simp only [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one])

中文:
定义 continuousAddCharEquiv_of_norm_mul
  签名: :
  定义体: (continuousAddCharEquiv p R).trans
    .subtypeEquivProp (by simp only [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one])

Depends on / 依赖: continuousAddCharEquiv, subtypeEquivProp, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
-/
noncomputable def continuousAddCharEquiv_of_norm_mul :
    {κ : AddChar Int_[p] R // Continuous κ} ≃ {r : R // ‖r‖ < 1} :=
(continuousAddCharEquiv p R).trans
    .subtypeEquivProp (by simp only [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one])

/--
lemma `continuousAddCharEquiv_of_norm_mul_apply` / 引理 `continuousAddCharEquiv_of_norm_mul_apply`

English:
lemma continuousAddCharEquiv_of_norm_mul_apply
  given: {κ : AddChar Int_[p] R} (hκ : Continuous κ)
  proof: rfl

中文:
引理 continuousAddCharEquiv_of_norm_mul_apply
  条件: {κ : 加法特征 整数_[p] R} (hκ : 连续 κ)
  证明: rfl
-/
@[simp] lemma continuousAddCharEquiv_of_norm_mul_apply {κ : AddChar Int_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv_of_norm_mul p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl

/--
lemma `continuousAddCharEquiv_of_norm_mul_symm_apply` / 引理 `continuousAddCharEquiv_of_norm_mul_symm_apply`

English:
lemma continuousAddCharEquiv_of_norm_mul_symm_apply
  given: {r : R} (hr : ‖r‖ < 1)
  proof: rfl

中文:
引理 continuousAddCharEquiv_of_norm_mul_symm_apply
  条件: {r : R} (hr : ‖r‖ < 1)
  证明: rfl
-/
@[simp] lemma continuousAddCharEquiv_of_norm_mul_symm_apply {r : R} (hr : ‖r‖ < 1) :
    (continuousAddCharEquiv_of_norm_mul p R).symm ⟨r, hr⟩ = (addChar_of_value_at_one r
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hr) : AddChar Int_[p] R) :=
  rfl

end NormMulClass

end PadicInt
