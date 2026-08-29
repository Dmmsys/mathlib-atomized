/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developed in `Mathlib/Analysis/Asymptotics/Defs.lean` and
`Mathlib/Analysis/Asymptotics/Lemmas.lean`.
-/

public section

open Bornology Filter Asymptotics Set Topology

section NormedField

/--
theorem `Filter.IsBoundedUnder.isLittleO_sub_self_inv` / 定理 `Filter.IsBoundedUnder.isLittleO_sub_self_inv`

English:
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv
  statement: {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜}
  proof: by
  refine (h.isBigO_const (one_ne_zero' Real)).trans_isLittleO (isLittleO_const_left.2 <| Or.inr ?_)
  simp only [Function.comp_def, norm_inv]
  exact (tendsto_norm_sub_self_nhdsNE a).inv_tendsto_nhdsGT_zero

中文:
定理 Filter.IsBoundedUnder.isLittleO_sub_self_inv
  结论: {𝕜 E : 类型} [NormedField 𝕜] [Norm E] {a : 𝕜}
  证明: by
  refine (h.isBigO_const (one_ne_zero' Real)).trans_isLittleO (isLittleO_const_left.2 <| Or.inr ?_)
  simp only [Function.comp_def, norm_inv]
  exact (tendsto_norm_sub_self_nhdsNE a).inv_tendsto_nhdsGT_zero

Depends on / 依赖: Function, Function.comp_def, Or.inr, comp_def, h.isBigO_const, inv_tendsto_nhdsGT_zero, isBigO_const, isLittleO_const_left, norm_inv, one_ne_zero, tendsto_norm_sub_self_nhdsNE, trans_isLittleO
-/
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜}
    {f : 𝕜 -> E} (h : IsBoundedUnder (· <= ·) (𝓝[!=] a) (norm ∘ f)) :
    f =o[𝓝[!=] a] fun x => (x - a)⁻¹ := by
  refine (h.isBigO_const (one_ne_zero' Real)).trans_isLittleO (isLittleO_const_left.2 <| Or.inr ?_)
  simp only [Function.comp_def, norm_inv]
  exact (tendsto_norm_sub_self_nhdsNE a).inv_tendsto_nhdsGT_zero

end NormedField

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R] {p q : Nat}

open Bornology

/--
theorem `Asymptotics.isLittleO_pow_pow_cobounded_of_lt` / 定理 `Asymptotics.isLittleO_pow_pow_cobounded_of_lt`

English:
theorem Asymptotics.isLittleO_pow_pow_cobounded_of_lt
  given: (hpq : p < q)
  proof: by
  rw [← Nat.add_sub_of_le hpq.le]
  simpa [pow_add] using (isBigO_refl (· ^ p) (cobounded R)).mul_isLittleO
    ((isLittleO_const_id_cobounded 1).pow (Nat.sub_pos_of_lt hpq))

中文:
定理 Asymptotics.isLittleO_pow_pow_cobounded_of_lt
  条件: (hpq : p < q)
  证明: by
  rw [← Nat.add_sub_of_le hpq.le]
  simpa [pow_add] using (isBigO_refl (· ^ p) (cobounded R)).mul_isLittleO
    ((isLittleO_const_id_cobounded 1).pow (Nat.sub_pos_of_lt hpq))

Depends on / 依赖: Nat.add_sub_of_le, Nat.sub_pos_of_lt, add_sub_of_le, cobounded, hpq.le, isBigO_refl, isLittleO_const_id_cobounded, mul_isLittleO, pow_add, sub_pos_of_lt
-/
theorem Asymptotics.isLittleO_pow_pow_cobounded_of_lt (hpq : p < q) :
    (· ^ p) =o[cobounded R] (· ^ q) := by
  rw [← Nat.add_sub_of_le hpq.le]
  simpa [pow_add] using (isBigO_refl (· ^ p) (cobounded R)).mul_isLittleO
    ((isLittleO_const_id_cobounded 1).pow (Nat.sub_pos_of_lt hpq))

/--
theorem `Asymptotics.isBigO_pow_pow_cobounded_of_le` / 定理 `Asymptotics.isBigO_pow_pow_cobounded_of_le`

English:
theorem Asymptotics.isBigO_pow_pow_cobounded_of_le
  given: (hpq : p <= q)
  proof: by
  rcases hpq.eq_or_lt with rfl | h
  · exact isBigO_refl ..
  · exact (isLittleO_pow_pow_cobounded_of_lt h).isBigO

中文:
定理 Asymptotics.isBigO_pow_pow_cobounded_of_le
  条件: (hpq : p <= q)
  证明: by
  rcases hpq.eq_or_lt with rfl | h
  · exact isBigO_refl ..
  · exact (isLittleO_pow_pow_cobounded_of_lt h).isBigO

Depends on / 依赖: eq_or_lt, hpq.eq_or_lt, isBigO, isBigO_refl, isLittleO_pow_pow_cobounded_of_lt
-/
theorem Asymptotics.isBigO_pow_pow_cobounded_of_le (hpq : p <= q) :
    (· ^ p) =O[cobounded R] (· ^ q) := by
  rcases hpq.eq_or_lt with rfl | h
  · exact isBigO_refl ..
  · exact (isLittleO_pow_pow_cobounded_of_lt h).isBigO

end NormedRing

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/--
theorem `pow_div_pow_eventuallyEq_atTop` / 定理 `pow_div_pow_eventuallyEq_atTop`

English:
theorem pow_div_pow_eventuallyEq_atTop
  given: {p q : Nat}
  proof: by
  apply (eventually_gt_atTop (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne']

中文:
定理 pow_div_pow_eventuallyEq_atTop
  条件: {p q : 自然数}
  证明: by
  apply (eventually_gt_atTop (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne']

Depends on / 依赖: eventually_gt_atTop, hx.ne
-/
theorem pow_div_pow_eventuallyEq_atTop {p q : Nat} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : Int) - q) := by
  apply (eventually_gt_atTop (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne']

/--
theorem `pow_div_pow_eventuallyEq_atBot` / 定理 `pow_div_pow_eventuallyEq_atBot`

English:
theorem pow_div_pow_eventuallyEq_atBot
  given: {p q : Nat}
  proof: by
  apply (eventually_lt_atBot (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne]

中文:
定理 pow_div_pow_eventuallyEq_atBot
  条件: {p q : 自然数}
  证明: by
  apply (eventually_lt_atBot (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne]

Depends on / 依赖: eventually_lt_atBot, hx.ne
-/
theorem pow_div_pow_eventuallyEq_atBot {p q : Nat} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atBot] fun x => x ^ ((p : Int) - q) := by
  apply (eventually_lt_atBot (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne]

/--
theorem `tendsto_pow_div_pow_atTop_atTop` / 定理 `tendsto_pow_div_pow_atTop_atTop`

English:
theorem tendsto_pow_div_pow_atTop_atTop
  given: {p q : Nat} (hpq : q < p)
  proof: by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  lia

中文:
定理 tendsto_pow_div_pow_atTop_atTop
  条件: {p q : 自然数} (hpq : q < p)
  证明: by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  lia

Depends on / 依赖: pow_div_pow_eventuallyEq_atTop, tendsto_congr, tendsto_zpow_atTop_atTop
-/
theorem tendsto_pow_div_pow_atTop_atTop {p q : Nat} (hpq : q < p) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  lia

/--
theorem `tendsto_pow_div_pow_atTop_zero` / 定理 `tendsto_pow_div_pow_atTop_zero`

English:
theorem tendsto_pow_div_pow_atTop_zero
  statement: [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : Nat}
  proof: by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  lia

中文:
定理 tendsto_pow_div_pow_atTop_zero
  结论: [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : 自然数}
  证明: by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  lia

Depends on / 依赖: pow_div_pow_eventuallyEq_atTop, tendsto_congr, tendsto_zpow_atTop_zero
-/
theorem tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : Nat}
    (hpq : p < q) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  lia

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type*} [NormedField 𝕜]

/--
theorem `Asymptotics.isLittleO_pow_pow_atTop_of_lt` / 定理 `Asymptotics.isLittleO_pow_pow_atTop_of_lt`

English:
theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt
  proof: by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

中文:
定理 Asymptotics.isLittleO_pow_pow_atTop_of_lt
  证明: by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

Depends on / 依赖: eventually_gt_atTop, hx.ne, isLittleO_iff_tendsto, pow_ne_zero, tendsto_pow_div_pow_atTop_zero
-/
theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : Nat} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[atTop] fun x => x ^ q := by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

/--
theorem `Asymptotics.IsBigO.trans_tendsto_norm_atTop` / 定理 `Asymptotics.IsBigO.trans_tendsto_norm_atTop`

English:
theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop
  statement: {α : Type*} {u v : α -> 𝕜} {l : Filter α}
  proof: by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert! Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀ _ hc.ne.symm]

中文:
定理 Asymptotics.IsBigO.trans_tendsto_norm_atTop
  结论: {α : 类型} {u v : α -> 𝕜} {l : Filter α}
  证明: by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert! Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀ _ hc.ne.symm]

Depends on / 依赖: IsBigOWith, Tendsto, Tendsto.atTop_div_const, atTop_div_const, convert, exists_pos, hc.ne.symm, huv.exists_pos, tendsto_atTop_mono
-/
theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type*} {u v : α -> 𝕜} {l : Filter α}
    (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) :
    Tendsto (fun x => ‖v x‖) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert! Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀ _ hc.ne.symm]

end NormedLinearOrderedField

section Real

/--
theorem `Asymptotics.IsEquivalent.rpow` / 定理 `Asymptotics.IsEquivalent.rpow`

English:
theorem Asymptotics.IsEquivalent.rpow
  statement: {α : Type*} {u v : α -> Real} {l : Filter α}
  proof: by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x => x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter

中文:
定理 Asymptotics.IsEquivalent.rpow
  结论: {α : 类型} {u v : α -> 实数} {l : Filter α}
  证明: by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x => x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter

Depends on / 依赖: IsEquivalent, IsEquivalent.exists_eq_mul, Real.continuousAt_rpow_const, Real.mul_rpow, Real.one_rpow, Tendsto, Tendsto.comp, Tendsto.eventually_const_lt, continuousAt_rpow_const, eventually_const_lt, exists_eq_mul, filter_upwards, isEquivalent_iff_exists_eq_mul, le_of_lt, mul_rpow, one_rpow, zero_lt_one
-/
theorem Asymptotics.IsEquivalent.rpow {α : Type*} {u v : α -> Real} {l : Filter α}
    (hv : 0 <= v) (h : u ~[l] v) {r : Real} :
    u ^ r ~[l] v ^ r := by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x => x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x => φ x ^ r * v x ^ r
  filter_upwards [Tendsto.eventually_const_lt (zero_lt_one) hφ, huφv] with x hφ_pos huv'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hv x), huv']

/--
theorem `Asymptotics.IsEquivalent.log` / 定理 `Asymptotics.IsEquivalent.log`

English:
theorem Asymptotics.IsEquivalent.log
  statement: {α : Type*} {l : Filter α} {f g : α -> Real} (hfg : f ~[l] g)
  proof: by
  have hg := g_tendsto.eventually_ne_atTop 0
.eventually_ne_atTop 0 have hf := hfg.symm.tendsto_atTop g_tendsto
  rw [isEquivalent_iff_tendsto_one hg] at hfg
.congr' by have := hfg.log (by norm_num)
    filter_upwards [hf, hg] with n hf hg using Real.log_div hf hg
exact IsLittleO.isEquivalent cal

中文:
定理 Asymptotics.IsEquivalent.log
  结论: {α : 类型} {l : Filter α} {f g : α -> 实数} (hfg : f ~[l] g)
  证明: by
  have hg := g_tendsto.eventually_ne_atTop 0
.eventually_ne_atTop 0 have hf := hfg.symm.tendsto_atTop g_tendsto
  rw [isEquivalent_iff_tendsto_one hg] at hfg
.congr' by have := hfg.log (by norm_num)
    filter_upwards [hf, hg] with n hf hg using Real.log_div hf hg
exact IsLittleO.isEquivalent cal

Depends on / 依赖: IsLittleO, IsLittleO.isEquivalent, Real.log, Real.log_div, Real.tendsto_log_atTop.comp, eventually_ne_atTop, filter_upwards, g_tendsto, g_tendsto.eventually_ne_atTop, hfg.log, hfg.symm.tendsto_atTop, isEquivalent, isEquivalent_iff_tendsto_one, isLittleO_one_left_iff, log_div, tendsto_atTop, tendsto_log_atTop, tendsto_norm_atTop_atTop, tendsto_norm_atTop_atTop.comp
-/
theorem Asymptotics.IsEquivalent.log {α : Type*} {l : Filter α} {f g : α -> Real} (hfg : f ~[l] g)
    (g_tendsto : Tendsto g l atTop) :
    (fun n => Real.log (f n)) ~[l] (fun n => Real.log (g n)) := by
  have hg := g_tendsto.eventually_ne_atTop 0
.eventually_ne_atTop 0 have hf := hfg.symm.tendsto_atTop g_tendsto
  rw [isEquivalent_iff_tendsto_one hg] at hfg
.congr' by have := hfg.log (by norm_num)
    filter_upwards [hf, hg] with n hf hg using Real.log_div hf hg
exact IsLittleO.isEquivalent calc
    (fun n => Real.log (f n) - Real.log (g n)) =o[l] fun _ => (1 : Real) := by simpa
.mpr _ =o[l] fun n => Real.log (g n) := isLittleO_one_left_iff Real
tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop.comp g_tendsto

open Finset

/--
theorem `Asymptotics.IsLittleO.sum_range` / 定理 `Asymptotics.IsLittleO.sum_range`

English:
theorem Asymptotics.IsLittleO.sum_range
  statement: {α : Type*} [NormedAddCommGroup α] {f : Nat -> α} {g : Nat -> Real}
  proof: by
  have A : forall i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : forall n, ‖∑ i in range n, g i‖ = ∑ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : exists N : Nat, forall b

中文:
定理 Asymptotics.IsLittleO.sum_range
  结论: {α : 类型} [NormedAddCommGroup α] {f : 自然数 -> α} {g : 自然数 -> 实数}
  证明: by
  have A : forall i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : forall n, ‖∑ i in range n, g i‖ = ∑ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : exists N : Nat, forall b

Depends on / 依赖: Real.norm_eq_abs, Real.norm_of_nonneg, abs_sum_of_nonneg, eventually_atTop, half_pos, isLittleO_iff, isLittleO_iff.mp, norm_eq_abs, norm_of_nonneg
-/
theorem Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : Nat -> α} {g : Nat -> Real}
    (h : f =o[atTop] g) (hg : 0 <= g) (h'g : Tendsto (fun n => ∑ i in range n, g i) atTop atTop) :
    (fun n => ∑ i in range n, f i) =o[atTop] fun n => ∑ i in range n, g i := by
  have A : forall i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : forall n, ‖∑ i in range n, g i‖ = ∑ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : exists N : Nat, forall b : Nat, N <= b -> ‖f b‖ <= ε / 2 * g b := by
    simpa only [A, eventually_atTop] using isLittleO_iff.mp h (half_pos εpos)
  have : (fun _ : Nat => ∑ i in range N, f i) =o[atTop] fun n : Nat => ∑ i in range n, g i := by
    apply isLittleO_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [isLittleO_iff.1 this (half_pos εpos), Ici_mem_atTop N] with n hn Nn
  calc
    ‖∑ i in range n, f i‖ = ‖(∑ i in range N, f i) + ∑ i in Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ <= ‖∑ i in range N, f i‖ + ‖∑ i in Ico N n, f i‖ := norm_add_le _ _
    _ <= ‖∑ i in range N, f i‖ + ∑ i in Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ <= ‖∑ i in range N, f i‖ + ∑ i in range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ => mul_nonneg (half_pos εpos).le (hg i)
      · rw [range_eq_Ico]
        exact Ico_subset_Ico zero_le le_rfl
    _ <= ε / 2 * ‖∑ i in range n, g i‖ + ε / 2 * ∑ i in range n, g i := by rw [← mul_sum]; gcongr
    _ = ε * ‖∑ i in range n, g i‖ := by
      simp only [B]
      ring

/--
theorem `Asymptotics.isLittleO_sum_range_of_tendsto_zero` / 定理 `Asymptotics.isLittleO_sum_range_of_tendsto_zero`

English:
theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero
  statement: {α : Type*} [NormedAddCommGroup α]
  proof: by
  have := ((isLittleO_one_iff Real).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

中文:
定理 Asymptotics.isLittleO_sum_range_of_tendsto_zero
  结论: {α : 类型} [NormedAddCommGroup α]
  证明: by
  have := ((isLittleO_one_iff Real).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

Depends on / 依赖: Nat.smul_one_eq_cast, card_range, isLittleO_one_iff, smul_one_eq_cast, sum_const, sum_range, tendsto_natCast_atTop_atTop, zero_le_one
-/
theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α]
    {f : Nat -> α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i in range n, f i) =o[atTop] fun n => (n : Real) := by
  have := ((isLittleO_one_iff Real).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

/--
theorem `Filter.Tendsto.cesaro_smul` / 定理 `Filter.Tendsto.cesaro_smul`

English:
theorem Filter.Tendsto.cesaro_smul
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {u : Nat -> E}
  proof: by
  rw [← tendsto_sub_nhds_zero_iff]; rw [← isLittleO_one_iff Real]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : Nat => (n : Real)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
 

中文:
定理 Filter.Tendsto.cesaro_smul
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E] {u : 自然数 -> E}
  证明: by
  rw [← tendsto_sub_nhds_zero_iff]; rw [← isLittleO_one_iff Real]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : Nat => (n : Real)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
 

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_sum_range_of_tendsto_zero, Ici_mem_atTop, Nat.cast_pos, Nat.cast_smul_eq_nsmul, card_range, cast_pos, cast_smul_eq_nsmul, filter_upwards, isBigO_refl, isLittleO_one_iff, isLittleO_sum_range_of_tendsto_zero, nposRea, nposReal, smul_isLittleO, smul_smul, smul_sub, sub_right_inj, sum_const, sum_sub_distrib
-/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {u : Nat -> E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : Nat => (n⁻¹ : Real) • ∑ i in range n, u i) atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff]; rw [← isLittleO_one_iff Real]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : Nat => (n : Real)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposReal : (0 : Real) < n := Nat.cast_pos.2 npos
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj]
    rw [← Nat.cast_smul_eq_nsmul Real]; rw [smul_smul]; rw [inv_mul_cancel₀ nposReal.ne']; rw [one_smul]
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposReal : (0 : Real) < n := Nat.cast_pos.2 npos
    rw [smul_eq_mul]; rw [inv_mul_cancel₀ nposReal.ne']

/--
theorem `Filter.Tendsto.cesaro` / 定理 `Filter.Tendsto.cesaro`

English:
theorem Filter.Tendsto.cesaro
  given: {u : Nat -> Real} {l : Real} (h : Tendsto u atTop (𝓝 l))
  proof: h.cesaro_smul

中文:
定理 Filter.Tendsto.cesaro
  条件: {u : 自然数 -> 实数} {l : 实数} (h : Tendsto u atTop (𝓝 l))
  证明: h.cesaro_smul

Depends on / 依赖: cesaro_smul, h.cesaro_smul
-/
theorem Filter.Tendsto.cesaro {u : Nat -> Real} {l : Real} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : Nat => (n⁻¹ : Real) * ∑ i in range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul

end Real

section NormedLinearOrderedField

variable {R : Type*} [NormedField R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

/--
theorem `Asymptotics.isEquivalent_nat_floor` / 定理 `Asymptotics.isEquivalent_nat_floor`

English:
theorem Asymptotics.isEquivalent_nat_floor
  proof: isEquivalent_of_tendsto_one tendsto_nat_floor_div_atTop

中文:
定理 Asymptotics.isEquivalent_nat_floor
  证明: isEquivalent_of_tendsto_one tendsto_nat_floor_div_atTop

Depends on / 依赖: isEquivalent_of_tendsto_one, tendsto_nat_floor_div_atTop
-/
theorem Asymptotics.isEquivalent_nat_floor :
    (fun (x : R) => ↑⌊x⌋₊) ~[atTop] (fun x => x) :=
  isEquivalent_of_tendsto_one tendsto_nat_floor_div_atTop

/--
theorem `Asymptotics.isEquivalent_nat_ceil` / 定理 `Asymptotics.isEquivalent_nat_ceil`

English:
theorem Asymptotics.isEquivalent_nat_ceil
  proof: isEquivalent_of_tendsto_one tendsto_nat_ceil_div_atTop

中文:
定理 Asymptotics.isEquivalent_nat_ceil
  证明: isEquivalent_of_tendsto_one tendsto_nat_ceil_div_atTop

Depends on / 依赖: isEquivalent_of_tendsto_one, tendsto_nat_ceil_div_atTop
-/
theorem Asymptotics.isEquivalent_nat_ceil :
    (fun (x : R) => ↑⌈x⌉₊) ~[atTop] (fun x => x) :=
  isEquivalent_of_tendsto_one tendsto_nat_ceil_div_atTop

end NormedLinearOrderedField

section boundedRange

/-!
## Bounded Range versus `IsBigO` Asymptotics

For a continuous function `f` into a seminormed space, having bounded range is equivalent to being
`O(1)` along the cocompact filter (`Continuous.isBounded_range_iff_isBigO`). On an unbounded linear
order whose order topology has compact intervals, this means being `O(1)` along both `atTop` and
`atBot` (`Continuous.isBounded_range_iff_isBigO_atTop_atBot`). For an even function a single `O(1)`
bound along `atTop` already suffices (`Continuous.isBounded_range_iff_isBigO_atTop_of_even`).
-/

variable
  {E : Type*} [SeminormedAddCommGroup E]
  {D : Type*} [TopologicalSpace D]
  {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β] [CompactIccSpace β]
    [NoMaxOrder β] [NoMinOrder β]

/--
theorem `Continuous.isBounded_range_iff_isBigO` / 定理 `Continuous.isBounded_range_iff_isBigO`

English:
theorem Continuous.isBounded_range_iff_isBigO
  given: {f : D -> E} (hf : Continuous f)
  proof: by
  constructor <;> intro h
  · rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨c, hc⟩ := h
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
    rw [isBigO_iff]
    use c
    apply Eventually.of_forall
    simpa using hc
  · simp_rw [isBigO_iff, Filter.Eventually

中文:
定理 Continuous.isBounded_range_iff_isBigO
  条件: {f : D -> E} (hf : Continuous f)
  证明: by
  constructor <;> intro h
  · rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨c, hc⟩ := h
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
    rw [isBigO_iff]
    use c
    apply Eventually.of_forall
    simpa using hc
  · simp_rw [isBigO_iff, Filter.Eventually

Depends on / 依赖: Eventually, Eventually.of_forall, Filter, Filter.Eventually, Filter.mem_cocompact, IsBounded, IsBounded.union, IsCompact, IsCompact.image, Pi.one_apply, Set.image_union_image_compl_eq_range, Set.mem_range, forall_apply_eq_imp_iff, forall_exists_index, hcompact, image_union_image_compl_eq_range, isBigO_iff, isBound, isBounded_iff_forall_norm_le, mem_cocompact
-/
theorem Continuous.isBounded_range_iff_isBigO {f : D -> E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[cocompact D] (1 : D -> Real) := by
  constructor <;> intro h
  · rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨c, hc⟩ := h
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
    rw [isBigO_iff]
    use c
    apply Eventually.of_forall
    simpa using hc
  · simp_rw [isBigO_iff, Filter.Eventually, Filter.mem_cocompact] at h
    simp only [Pi.one_apply, norm_one, mul_one] at h
    obtain ⟨c, t, hcompact, h⟩ := h
    rw [← Set.image_union_image_compl_eq_range (s := t)]
    apply IsBounded.union
    · apply (IsCompact.image hcompact hf).isBounded
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨c, fun x hx => ?_⟩
      rw [Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using mem_of_mem_of_subset hy h

/--
theorem `Continuous.isBounded_range_iff_isBigO_atTop_atBot` / 定理 `Continuous.isBounded_range_iff_isBigO_atTop_atBot`

English:
theorem Continuous.isBounded_range_iff_isBigO_atTop_atBot
  given: {f : β -> E} (hf : Continuous f)
  proof: by
  rw [hf.isBounded_range_iff_isBigO]; rw [cocompact_eq_atBot_atTop]; rw [isBigO_sup]; rw [and_comm]

中文:
定理 Continuous.isBounded_range_iff_isBigO_atTop_atBot
  条件: {f : β -> E} (hf : Continuous f)
  证明: by
  rw [hf.isBounded_range_iff_isBigO]; rw [cocompact_eq_atBot_atTop]; rw [isBigO_sup]; rw [and_comm]

Depends on / 依赖: and_comm, cocompact_eq_atBot_atTop, hf.isBounded_range_iff_isBigO, isBigO_sup, isBounded_range_iff_isBigO
-/
theorem Continuous.isBounded_range_iff_isBigO_atTop_atBot {f : β -> E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β -> Real) ∧ f =O[atBot] (1 : β -> Real) := by
  rw [hf.isBounded_range_iff_isBigO]; rw [cocompact_eq_atBot_atTop]; rw [isBigO_sup]; rw [and_comm]

/--
theorem `Continuous.isBounded_range_iff_isBigO_atTop_of_even` / 定理 `Continuous.isBounded_range_iff_isBigO_atTop_of_even`

English:
theorem Continuous.isBounded_range_iff_isBigO_atTop_of_even
  statement: [AddCommGroup β] [IsOrderedAddMonoid β]
  proof: ⟨fun h => (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h => hf.isBounded_range_iff_isBigO_atTop_atBot.mpr
     ⟨h, by simpa only [← neg_atTop, ← Filter.map_neg, isBigO_map, Function.comp_def, heven.eq]⟩⟩

中文:
定理 Continuous.isBounded_range_iff_isBigO_atTop_of_even
  结论: [AddCommGroup β] [IsOrderedAddMonoid β]
  证明: ⟨fun h => (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h => hf.isBounded_range_iff_isBigO_atTop_atBot.mpr
     ⟨h, by simpa only [← neg_atTop, ← Filter.map_neg, isBigO_map, Function.comp_def, heven.eq]⟩⟩

Depends on / 依赖: Filter, Filter.map_neg, Function, Function.comp_def, comp_def, heven.eq, hf.isBounded_range_iff_isBigO_atTop_atBot.mp, hf.isBounded_range_iff_isBigO_atTop_atBot.mpr, isBigO_map, isBounded_range_iff_isBigO_atTop_atBot, map_neg, neg_atTop
-/
theorem Continuous.isBounded_range_iff_isBigO_atTop_of_even [AddCommGroup β] [IsOrderedAddMonoid β]
    {f : β -> E} (hf : Continuous f) (heven : Function.Even f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β -> Real) :=
  ⟨fun h => (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h => hf.isBounded_range_iff_isBigO_atTop_atBot.mpr
     ⟨h, by simpa only [← neg_atTop, ← Filter.map_neg, isBigO_map, Function.comp_def, heven.eq]⟩⟩

end boundedRange
