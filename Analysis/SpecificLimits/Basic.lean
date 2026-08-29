/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Iterate
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.Rat

/-!
# A collection of specific limit computations

This file, by design, is independent of `NormedSpace` in the import hierarchy. It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

@[expose] public section

assert_not_exists Module.Basis NormedSpace

noncomputable section

open Set Function Filter Finset Metric Topology Nat uniformity NNReal ENNReal

variable {α : Type*} {β : Type*} {ι : Type*}

/--
theorem `NNRat.tendsto_inv_atTop_nhds_zero_nat` / 定理 `NNRat.tendsto_inv_atTop_nhds_zero_nat`

English:
theorem NNRat.tendsto_inv_atTop_nhds_zero_nat
  statement: Tendsto (fun n : Nat => (n : Rat>=0)⁻¹) atTop (𝓝 0)
  proof: tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

中文:
定理 NNRat.tendsto_inv_atTop_nhds_zero_nat
  结论: Tendsto (fun n : 自然数 => (n : Rat>=0)⁻¹) atTop (𝓝 0)
  证明: tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp, tendsto_natCast_atTop_atTop
-/
theorem NNRat.tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : Nat => (n : Rat>=0)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/--
theorem `NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat` / 定理 `NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat`

English:
theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat
  statement: (𝕜 : Type*) [Semiring 𝕜]
  proof: by
  convert! (continuous_algebraMap Rat>=0 𝕜).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

中文:
定理 NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat
  结论: (𝕜 : 类型) [Semiring 𝕜]
  证明: by
  convert! (continuous_algebraMap Rat>=0 𝕜).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

Depends on / 依赖: continuousAt, continuousAt.tendsto.comp, continuous_algebraMap, convert, map_zero, tendsto, tendsto_inv_atTop_nhds_zero_nat
-/
theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜]
    [Algebra Rat>=0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] :
    Tendsto (algebraMap Rat>=0 𝕜 ∘ fun n : Nat => (n : Rat>=0)⁻¹) atTop (𝓝 0) := by
  convert! (continuous_algebraMap Rat>=0 𝕜).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

/--
theorem `tendsto_inv_atTop_nhds_zero_nat` / 定理 `tendsto_inv_atTop_nhds_zero_nat`

English:
theorem tendsto_inv_atTop_nhds_zero_nat
  statement: {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
  proof: by
  convert! NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

中文:
定理 tendsto_inv_atTop_nhds_zero_nat
  结论: {𝕜 : 类型} [DivisionSemiring 𝕜] [CharZero 𝕜]
  证明: by
  convert! NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

Depends on / 依赖: NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat, convert, tendsto_algebraMap_inv_atTop_nhds_zero_nat
-/
theorem tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] :
    Tendsto (fun n : Nat => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert! NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

/--
theorem `tendsto_const_div_atTop_nhds_zero_nat` / 定理 `tendsto_const_div_atTop_nhds_zero_nat`

English:
theorem tendsto_const_div_atTop_nhds_zero_nat
  statement: {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
  proof: by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

中文:
定理 tendsto_const_div_atTop_nhds_zero_nat
  结论: {𝕜 : 类型} [DivisionSemiring 𝕜] [CharZero 𝕜]
  证明: by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

Depends on / 依赖: div_eq_mul_inv, mul_zero, tendsto_const_nhds, tendsto_inv_atTop_nhds_zero_nat
-/
theorem tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) :
    Tendsto (fun n : Nat => C / n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

/--
theorem `tendsto_one_div_atTop_nhds_zero_nat` / 定理 `tendsto_one_div_atTop_nhds_zero_nat`

English:
theorem tendsto_one_div_atTop_nhds_zero_nat
  statement: {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
  proof: by
  simp [tendsto_inv_atTop_nhds_zero_nat]

中文:
定理 tendsto_one_div_atTop_nhds_zero_nat
  结论: {𝕜 : 类型} [DivisionSemiring 𝕜] [CharZero 𝕜]
  证明: by
  simp [tendsto_inv_atTop_nhds_zero_nat]

Depends on / 依赖: tendsto_inv_atTop_nhds_zero_nat
-/
theorem tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] :
    Tendsto (fun n : Nat => 1 / (n : 𝕜)) atTop (𝓝 0) := by
  simp [tendsto_inv_atTop_nhds_zero_nat]

/--
theorem `EReal.tendsto_const_div_atTop_nhds_zero_nat` / 定理 `EReal.tendsto_const_div_atTop_nhds_zero_nat`

English:
theorem EReal.tendsto_const_div_atTop_nhds_zero_nat
  given: {C : EReal} (h : C != ⊥) (h' : C != ⊤)
  proof: by
  have : (fun n : Nat => C / n) = fun n : Nat => ((C.toReal / n : Real) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this]; rw [← coe_zero]; rw [tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal

中文:
定理 EReal.tendsto_const_div_atTop_nhds_zero_nat
  条件: {C : E实数} (h : C != ⊥) (h' : C != ⊤)
  证明: by
  have : (fun n : Nat => C / n) = fun n : Nat => ((C.toReal / n : Real) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this]; rw [← coe_zero]; rw [tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal

Depends on / 依赖: C.toReal, _root_, _root_.tendsto_const_div_atTop_nhds_zero_nat, coe_coe_eq_natCast, coe_div, coe_toReal, coe_zero, nth_rw, tendsto_coe, tendsto_const_div_atTop_nhds_zero_nat, toReal
-/
theorem EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C != ⊥) (h' : C != ⊤) :
    Tendsto (fun n : Nat => C / n) atTop (𝓝 0) := by
  have : (fun n : Nat => C / n) = fun n : Nat => ((C.toReal / n : Real) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this]; rw [← coe_zero]; rw [tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal

/--
theorem `tendsto_one_div_add_atTop_nhds_zero_nat` / 定理 `tendsto_one_div_add_atTop_nhds_zero_nat`

English:
theorem tendsto_one_div_add_atTop_nhds_zero_nat
  statement: {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
  proof: suffices Tendsto (fun n : Nat => 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat

中文:
定理 tendsto_one_div_add_atTop_nhds_zero_nat
  结论: {𝕜 : 类型} [DivisionSemiring 𝕜] [CharZero 𝕜]
  证明: suffices Tendsto (fun n : Nat => 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat

Depends on / 依赖: Tendsto, tendsto_add_atTop_iff_nat, tendsto_one_div_atTop_nhds_zero_nat
-/
theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] :
    Tendsto (fun n : Nat => 1 / ((n : 𝕜) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : Nat => 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat

/--
theorem `tendsto_algebraMap_inv_atTop_nhds_zero_nat` / 定理 `tendsto_algebraMap_inv_atTop_nhds_zero_nat`

English:
theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat
  statement: {𝕜 : Type*} (A : Type*)
  proof: by
  convert! (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

中文:
定理 tendsto_algebraMap_inv_atTop_nhds_zero_nat
  结论: {𝕜 : 类型} (A : 类型)
  证明: by
  convert! (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

Depends on / 依赖: BasedNatTrans, BasedNatTrans.ext, continuousAt, continuousAt.tendsto.comp, continuous_algebraMap, convert, map_zero, tendsto, tendsto_inv_atTop_nhds_zero_nat
-/
theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*)
    [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜]
    [Semiring A] [Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] :
    Tendsto (algebraMap 𝕜 A ∘ fun n : Nat => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert! (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

/--
theorem `tendsto_natCast_div_add_atTop` / 定理 `tendsto_natCast_div_add_atTop`

English:
theorem tendsto_natCast_div_add_atTop
  statement: {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
  proof: by
  convert! Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => _)) _
  · exact fun n : Nat => 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero]; rw [add_zero]; rw [div_one]
    rw [this]

中文:
定理 tendsto_natCast_div_add_atTop
  结论: {𝕜 : 类型} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
  证明: by
  convert! Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => _)) _
  · exact fun n : Nat => 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero]; rw [add_zero]; rw [div_one]
    rw [this]

Depends on / 依赖: Eventually, Eventually.of_forall, Nat.cast_ne_zero.mpr, Tendsto, Tendsto.congr, add_div, add_zero, cast_ne_zero, convert, div_eq_mul_inv, div_one, eventually_ne_atTop, mul_zero, of_forall, simp_rw, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_const_nhds.div, tendsto_const_nhds.mul, tendsto_inv_atTop_nhds_zero_nat
-/
theorem tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
    [CharZero 𝕜] [ContinuousSMul Rat>=0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (x : 𝕜) :
    Tendsto (fun n : Nat => (n : 𝕜) / (n + x)) atTop (𝓝 1) := by
  convert! Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => _)) _
  · exact fun n : Nat => 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero]; rw [add_zero]; rw [div_one]
    rw [this]
    refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by simp)
    simp_rw [div_eq_mul_inv]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat

/--
theorem `tendsto_add_mul_div_add_mul_atTop_nhds` / 定理 `tendsto_add_mul_div_add_mul_atTop_nhds`

English:
theorem tendsto_add_mul_div_add_mul_atTop_nhds
  statement: {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
  proof: by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k => (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    dsimp
    field (discharger := norm_cast)
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜)

中文:
定理 tendsto_add_mul_div_add_mul_atTop_nhds
  结论: {𝕜 : 类型} [Semifield 𝕜] [CharZero 𝕜]
  证明: by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k => (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    dsimp
    field (discharger := norm_cast)
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜)

Depends on / 依赖: Eventually, Eventually.of_forall, Filter, Filter.Tendsto.add_const, Filter.Tendsto.congr, Filter.Tendsto.const_mul, Filter.Tendsto.div, Tendsto, add_const, all_goals, const_mul, discharger, eventually_ne_atTop, mul_zero, of_forall, tendsto_inv_atTop_nhds_zero_nat, zero_add
-/
theorem tendsto_add_mul_div_add_mul_atTop_nhds {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜]
    (a b c : 𝕜) {d : 𝕜} (hd : d != 0) :
    Tendsto (fun k : Nat => (a + c * k) / (b + d * k)) atTop (𝓝 (c / d)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k => (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    dsimp
    field (discharger := norm_cast)
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const _ _
      apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
      exact tendsto_inv_atTop_nhds_zero_nat

/--
theorem `tendsto_mod_div_atTop_nhds_zero_nat` / 定理 `tendsto_mod_div_atTop_nhds_zero_nat`

English:
theorem tendsto_mod_div_atTop_nhds_zero_nat
  given: {m : Nat} (hm : 0 < m)
  proof: by
  have h0 : forallᶠ n : Nat in atTop, 0 <= (fun n : Nat => ((n % m : Nat) : Real)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n => cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

中文:
定理 tendsto_mod_div_atTop_nhds_zero_nat
  条件: {m : 自然数} (hm : 0 < m)
  证明: by
  have h0 : forallᶠ n : Nat in atTop, 0 <= (fun n : Nat => ((n % m : Nat) : Real)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n => cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

Depends on / 依赖: F.toFunctor, cast_le, cast_le.mpr, forgetful_map, infer_instance, mod_lt, of_forall, tendsto_bdd_div_atTop_nhds_zero, tendsto_natCast_atTop_atTop, toFunctor, toNatTrans
-/
theorem tendsto_mod_div_atTop_nhds_zero_nat {m : Nat} (hm : 0 < m) :
    Tendsto (fun n : Nat => ((n % m : Nat) : Real) / (n : Real)) atTop (𝓝 0) := by
  have h0 : forallᶠ n : Nat in atTop, 0 <= (fun n : Nat => ((n % m : Nat) : Real)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n => cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

/--
theorem `tendsto_mul_add_inv_atTop_nhds_zero` / 定理 `tendsto_mul_add_inv_atTop_nhds_zero`

English:
theorem tendsto_mul_add_inv_atTop_nhds_zero
  given: (a c : Real) (ha : a != 0)
  proof: by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))

中文:
定理 tendsto_mul_add_inv_atTop_nhds_zero
  条件: (a c : 实数) (ha : a != 0)
  证明: by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))

Depends on / 依赖: const_mul_atTop, const_mul_atTop_of_neg, lt_or_gt_of_ne, tendsto_atBot_add_const_right, tendsto_atTop_add_const_right, tendsto_id, tendsto_id.const_mul_atTop, tendsto_id.const_mul_atTop_of_neg, tendsto_inv_atBot_zero, tendsto_inv_atBot_zero.comp, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp
-/
theorem tendsto_mul_add_inv_atTop_nhds_zero (a c : Real) (ha : a != 0) :
    Tendsto (fun x => (a * x + c)⁻¹) atTop (𝓝 0) := by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))

/--
theorem `Filter.EventuallyEq.div_mul_cancel` / 定理 `Filter.EventuallyEq.div_mul_cancel`

English:
theorem Filter.EventuallyEq.div_mul_cancel
  statement: {α G : Type*} [GroupWithZero G] {f g : α -> G}
  proof: by
  filter_upwards [hg.le_comap <| preimage_mem_comap (m := g) (mem_principal_self {0}ᶜ)] with x hx
  simp_all

中文:
定理 Filter.EventuallyEq.div_mul_cancel
  结论: {α G : 类型} [GroupWithZero G] {f g : α -> G}
  证明: by
  filter_upwards [hg.le_comap <| preimage_mem_comap (m := g) (mem_principal_self {0}ᶜ)] with x hx
  simp_all

Depends on / 依赖: filter_upwards, hg.le_comap, le_comap, mem_principal_self, preimage_mem_comap
-/
theorem Filter.EventuallyEq.div_mul_cancel {α G : Type*} [GroupWithZero G] {f g : α -> G}
    {l : Filter α} (hg : Tendsto g l (𝓟 {0}ᶜ)) : (fun x => f x / g x * g x) =ᶠ[l] fun x => f x := by
  filter_upwards [hg.le_comap <| preimage_mem_comap (m := g) (mem_principal_self {0}ᶜ)] with x hx
  simp_all

/--
theorem `Filter.EventuallyEq.div_mul_cancel_atTop` / 定理 `Filter.EventuallyEq.div_mul_cancel_atTop`

English:
theorem Filter.EventuallyEq.div_mul_cancel_atTop
  statement: {α K : Type*}
  proof: div_mul_cancel hg.mono_right le_principal_iff.mpr
mem_of_superset (Ioi_mem_atTop 0) by simp

中文:
定理 Filter.EventuallyEq.div_mul_cancel_atTop
  结论: {α K : 类型}
  证明: div_mul_cancel hg.mono_right le_principal_iff.mpr
mem_of_superset (Ioi_mem_atTop 0) by simp

Depends on / 依赖: Ioi_mem_atTop, div_mul_cancel, hg.mono_right, le_principal_iff, le_principal_iff.mpr, mem_of_superset, mono_right
-/
theorem Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*}
    [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : α -> K} {l : Filter α} (hg : Tendsto g l atTop) :
    (fun x => f x / g x * g x) =ᶠ[l] fun x => f x :=
div_mul_cancel hg.mono_right le_principal_iff.mpr
mem_of_superset (Ioi_mem_atTop 0) by simp

/--
theorem `Filter.Tendsto.num` / 定理 `Filter.Tendsto.num`

English:
theorem Filter.Tendsto.num
  statement: {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  proof: (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

中文:
定理 Filter.Tendsto.num
  结论: {α K : 类型} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  证明: (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

Depends on / 依赖: EventuallyEq, EventuallyEq.div_mul_cancel_atTop, div_mul_cancel_atTop, hlim.pos_mul_atTop, pos_mul_atTop
-/
theorem Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α -> K} {l : Filter α} (hg : Tendsto g l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop :=
  (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

/--
theorem `Filter.Tendsto.den` / 定理 `Filter.Tendsto.den`

English:
theorem Filter.Tendsto.den
  statement: {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  proof: have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

中文:
定理 Filter.Tendsto.den
  结论: {α K : 类型} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  证明: have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

Depends on / 依赖: Filter, Filter.Tendsto.inv, Tendsto, div_mul_cancel_atTop, inv_div, inv_pos_of_pos, pos_mul_atTop, simp_rw
-/
theorem Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    [ContinuousInv K] {f g : α -> K} {l : Filter α} (hf : Tendsto f l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto g l atTop :=
  have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

/--
theorem `Filter.Tendsto.num_atTop_iff_den_atTop` / 定理 `Filter.Tendsto.num_atTop_iff_den_atTop`

English:
theorem Filter.Tendsto.num_atTop_iff_den_atTop
  statement: {α K : Type*}
  proof: ⟨fun hf => hf.den ha hlim, fun hg => hg.num ha hlim⟩

中文:
定理 Filter.Tendsto.num_atTop_iff_den_atTop
  结论: {α K : 类型}
  证明: ⟨fun hf => hf.den ha hlim, fun hg => hg.num ha hlim⟩

Depends on / 依赖: hf.den, hg.num
-/
theorem Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
    [OrderTopology K] [ContinuousInv K] {f g : α -> K} {l : Filter α} {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop ↔ Tendsto g l atTop :=
  ⟨fun hf => hf.den ha hlim, fun hg => hg.num ha hlim⟩



/--
theorem `tendsto_add_one_pow_atTop_atTop_of_pos` / 定理 `tendsto_add_one_pow_atTop_atTop_of_pos`

English:
theorem tendsto_add_one_pow_atTop_atTop_of_pos
  proof: tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le)
not_bddAbove_iff.2 fun _ => Set.exists_range_iff.2 add_one_pow_unbounded_of_pos _ h

中文:
定理 tendsto_add_one_pow_atTop_atTop_of_pos
  证明: tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le)
not_bddAbove_iff.2 fun _ => Set.exists_range_iff.2 add_one_pow_unbounded_of_pos _ h

Depends on / 依赖: Set.exists_range_iff, add_one_pow_unbounded_of_pos, exists_range_iff, h.le, le_add_of_nonneg_left, not_bddAbove_iff, tendsto_atTop_atTop_of_monotone
-/
theorem tendsto_add_one_pow_atTop_atTop_of_pos
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : Nat => (r + 1) ^ n) atTop atTop :=
tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le)
not_bddAbove_iff.2 fun _ => Set.exists_range_iff.2 add_one_pow_unbounded_of_pos _ h

/--
theorem `tendsto_pow_atTop_atTop_of_one_lt` / 定理 `tendsto_pow_atTop_atTop_of_one_lt`

English:
theorem tendsto_pow_atTop_atTop_of_one_lt
  proof: by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

中文:
定理 tendsto_pow_atTop_atTop_of_one_lt
  证明: by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

Depends on / 依赖: add_comm, exists_pos_add_of_lt, tendsto_add_one_pow_atTop_atTop_of_pos
-/
theorem tendsto_pow_atTop_atTop_of_one_lt
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : Nat => r ^ n) atTop atTop := by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

/--
theorem `tendsto_pow_atTop_nhds_zero_of_lt_one` / 定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`

English:
theorem tendsto_pow_atTop_nhds_zero_of_lt_one
  statement: {𝕜 : Type*}
  proof: h₁.eq_or_lt.elim
    (fun hr => (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr =>
tendsto_pow_atTop_atTop_of_one_lt have := (one_lt_inv₀ hr).2 h₂
      (tendsto_inv_atTop_zero.comp this).congr fun n => by simp)

中文:
定理 tendsto_pow_atTop_nhds_zero_of_lt_one
  结论: {𝕜 : 类型}
  证明: h₁.eq_or_lt.elim
    (fun hr => (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr =>
tendsto_pow_atTop_atTop_of_one_lt have := (one_lt_inv₀ hr).2 h₂
      (tendsto_inv_atTop_zero.comp this).congr fun n => by simp)

Depends on / 依赖: _root_, _root_.pow_succ, eq_or_lt, eq_or_lt.elim, pow_succ, tendsto_add_atTop_iff_nat, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp, tendsto_pow_atTop_atTop_of_one_lt
-/
theorem tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 <= r) (h₂ : r < 1) :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr => (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr =>
tendsto_pow_atTop_atTop_of_one_lt have := (one_lt_inv₀ hr).2 h₂
      (tendsto_inv_atTop_zero.comp this).congr fun n => by simp)

/--
theorem `tendsto_pow_atTop_nhds_zero_iff` / 定理 `tendsto_pow_atTop_nhds_zero_iff`

English:
theorem tendsto_pow_atTop_nhds_zero_iff
  statement: {𝕜 : Type*}
  proof: by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h => by_contra (fun hr_le => ?_), fun h => ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : Nat => |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
exact zero_ne_one tendsto_nhds_uni

中文:
定理 tendsto_pow_atTop_nhds_zero_iff
  结论: {𝕜 : 类型}
  证明: by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h => by_contra (fun hr_le => ?_), fun h => ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : Nat => |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
exact zero_ne_one tendsto_nhds_uni
-/
@[simp] theorem tendsto_pow_atTop_nhds_zero_iff {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) ↔ |r| < 1 := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h => by_contra (fun hr_le => ?_), fun h => ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : Nat => |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
exact zero_ne_one tendsto_nhds_unique h tendsto_const_nhds
    · apply @not_tendsto_nhds_of_tendsto_atTop 𝕜 Nat _ _ _ _ atTop _ (fun n => |r| ^ n) _ 0 _
      · refine (pow_right_strictMono₀ <| lt_of_le_of_ne (le_of_not_gt hr_le)
          hr).monotone.tendsto_atTop_atTop (fun b => ?_)
        obtain ⟨n, hn⟩ := (pow_unbounded_of_one_lt b (lt_of_le_of_ne (le_of_not_gt hr_le) hr))
        exact ⟨n, le_of_lt hn⟩
      · simpa only [← abs_pow]
  · simpa only [← abs_pow] using! (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r)) h

/--
theorem `tendsto_pow_atTop_nhdsWithin_zero_of_lt_one` / 定理 `tendsto_pow_atTop_nhdsWithin_zero_of_lt_one`

English:
theorem tendsto_pow_atTop_nhdsWithin_zero_of_lt_one
  statement: {𝕜 : Type*}
  proof: tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
tendsto_principal.2 Eventually.of_forall fun _ => pow_pos h₁ _⟩

中文:
定理 tendsto_pow_atTop_nhdsWithin_zero_of_lt_one
  结论: {𝕜 : 类型}
  证明: tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
tendsto_principal.2 Eventually.of_forall fun _ => pow_pos h₁ _⟩

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, pow_pos, tendsto_inf, tendsto_pow_atTop_nhds_zero_of_lt_one, tendsto_principal
-/
theorem tendsto_pow_atTop_nhdsWithin_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜]
    [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
tendsto_principal.2 Eventually.of_forall fun _ => pow_pos h₁ _⟩

/--
theorem `uniformity_basis_dist_pow_of_lt_one` / 定理 `uniformity_basis_dist_pow_of_lt_one`

English:
theorem uniformity_basis_dist_pow_of_lt_one
  statement: {α : Type*} [PseudoMetricSpace α] {r : Real} (h₀ : 0 < r)
  proof: Metric.mk_uniformity_basis (fun _ _ => pow_pos h₀ _) fun _ ε0 =>
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk => ⟨trivial, hk.le⟩

中文:
定理 uniformity_basis_dist_pow_of_lt_one
  结论: {α : 类型} [PseudoMetricSpace α] {r : 实数} (h₀ : 0 < r)
  证明: Metric.mk_uniformity_basis (fun _ _ => pow_pos h₀ _) fun _ ε0 =>
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk => ⟨trivial, hk.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis, exists_pow_lt_of_lt_one, hk.le, mk_uniformity_basis, pow_pos
-/
theorem uniformity_basis_dist_pow_of_lt_one {α : Type*} [PseudoMetricSpace α] {r : Real} (h₀ : 0 < r)
    (h₁ : r < 1) :
    (uniformity α).HasBasis (fun _ : Nat => True) fun k => { p : α × α | dist p.1 p.2 < r ^ k } :=
  Metric.mk_uniformity_basis (fun _ _ => pow_pos h₀ _) fun _ ε0 =>
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk => ⟨trivial, hk.le⟩

/--
theorem `geom_lt` / 定理 `geom_lt`

English:
theorem geom_lt
  statement: {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n)
  proof: by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc]

中文:
定理 geom_lt
  结论: {u : 自然数 -> 实数} {c : 实数} (hc : 0 <= c) {n : 自然数} (hn : 0 < n)
  证明: by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc]

Depends on / 依赖: _root_, _root_.pow_succ, monotone_mul_left_of_nonneg, mul_assoc, pow_succ, seq_pos_lt_seq_of_le_of_lt
-/
theorem geom_lt {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n)
    (h : forall k < n, c * u k < u (k + 1)) : c ^ n * u 0 < u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc]

/--
theorem `geom_le` / 定理 `geom_le`

English:
theorem geom_le
  given: {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k < n, c * u k <= u (k + 1))
  proof: by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc]

中文:
定理 geom_le
  条件: {u : 自然数 -> 实数} {c : 实数} (hc : 0 <= c) (n : 自然数) (h : 对任意 k < n, c * u k <= u (k + 1))
  证明: by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc]

Depends on / 依赖: _root_, _root_.pow_succ, monotone_mul_left_of_nonneg, mul_assoc, pow_succ, seq_le_seq
-/
theorem geom_le {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k < n, c * u k <= u (k + 1)) :
    c ^ n * u 0 <= u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc]

/--
theorem `lt_geom` / 定理 `lt_geom`

English:
theorem lt_geom
  statement: {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n)
  proof: by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc]

中文:
定理 lt_geom
  结论: {u : 自然数 -> 实数} {c : 实数} (hc : 0 <= c) {n : 自然数} (hn : 0 < n)
  证明: by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc]

Depends on / 依赖: _root_, _root_.pow_succ, monotone_mul_left_of_nonneg, mul_assoc, pow_succ, seq_pos_lt_seq_of_lt_of_le
-/
theorem lt_geom {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n)
    (h : forall k < n, u (k + 1) < c * u k) : u n < c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc]

/--
theorem `le_geom` / 定理 `le_geom`

English:
theorem le_geom
  given: {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k < n, u (k + 1) <= c * u k)
  proof: by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc]

中文:
定理 le_geom
  条件: {u : 自然数 -> 实数} {c : 实数} (hc : 0 <= c) (n : 自然数) (h : 对任意 k < n, u (k + 1) <= c * u k)
  证明: by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc]

Depends on / 依赖: _root_, _root_.pow_succ, monotone_mul_left_of_nonneg, mul_assoc, pow_succ, seq_le_seq
-/
theorem le_geom {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k < n, u (k + 1) <= c * u k) :
    u n <= c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc]

/--
theorem `tendsto_atTop_of_geom_le` / 定理 `tendsto_atTop_of_geom_le`

English:
theorem tendsto_atTop_of_geom_le
  statement: {v : Nat -> Real} {c : Real} (h₀ : 0 < v 0) (hc : 1 < c)
  proof: (tendsto_atTop_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k _ => hu k)
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀

中文:
定理 tendsto_atTop_of_geom_le
  结论: {v : 自然数 -> 实数} {c : 实数} (h₀ : 0 < v 0) (hc : 1 < c)
  证明: (tendsto_atTop_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k _ => hu k)
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀

Depends on / 依赖: atTop_mul_const, geom_le, hc.le, tendsto_atTop_mono, tendsto_pow_atTop_atTop_of_one_lt, zero_le_one, zero_le_one.trans
-/
theorem tendsto_atTop_of_geom_le {v : Nat -> Real} {c : Real} (h₀ : 0 < v 0) (hc : 1 < c)
    (hu : forall n, c * v n <= v (n + 1)) : Tendsto v atTop atTop :=
(tendsto_atTop_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k _ => hu k)
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀

/--
theorem `NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one` / 定理 `NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`

English:
theorem NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
  given: {r : Real>=0} (hr : r < 1)
  proof: NNReal.tendsto_coe.1 by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]

中文:
定理 NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
  条件: {r : 实数>=0} (hr : r < 1)
  证明: NNReal.tendsto_coe.1 by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_pow, NNReal.coe_zero, NNReal.tendsto_coe, _root_, _root_.tendsto_pow_atTop_nhds_zero_of_lt_one, coe_nonneg, coe_pow, coe_zero, r.coe_nonneg, tendsto_coe, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
theorem NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : Real>=0} (hr : r < 1) :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) :=
NNReal.tendsto_coe.1 by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]
/--
theorem `NNReal.tendsto_pow_atTop_nhds_zero_iff` / 定理 `NNReal.tendsto_pow_atTop_nhds_zero_iff`

English:
theorem NNReal.tendsto_pow_atTop_nhds_zero_iff
  given: {r : Real>=0}
  proof: ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
tendsto_pow_atTop_nhds_zero_iff.mp tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩

中文:
定理 NNReal.tendsto_pow_atTop_nhds_zero_iff
  条件: {r : 实数>=0}
  证明: ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
tendsto_pow_atTop_nhds_zero_iff.mp tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
-/
protected theorem NNReal.tendsto_pow_atTop_nhds_zero_iff {r : Real>=0} :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) ↔ r < 1 :=
  ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
tendsto_pow_atTop_nhds_zero_iff.mp tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩

/--
theorem `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one` / 定理 `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`

English:
theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
  given: {r : Real>=0∞} (hr : r < 1)
  proof: by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]

中文:
定理 ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
  条件: {r : 实数>=0∞} (hr : r < 1)
  证明: by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.lt_iff_exists_coe, NNReal, NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one, coe_zero, lt_iff_exists_coe, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : Real>=0∞} (hr : r < 1) :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) := by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]
/--
theorem `ENNReal.tendsto_pow_atTop_nhds_zero_iff` / 定理 `ENNReal.tendsto_pow_atTop_nhds_zero_iff`

English:
theorem ENNReal.tendsto_pow_atTop_nhds_zero_iff
  given: {r : Real>=0∞}
  proof: by
  refine ⟨fun h => ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr => top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn => pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  n

中文:
定理 ENNReal.tendsto_pow_atTop_nhds_zero_iff
  条件: {r : 实数>=0∞}
  证明: by
  refine ⟨fun h => ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr => top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn => pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  n
-/
protected theorem ENNReal.tendsto_pow_atTop_nhds_zero_iff {r : Real>=0∞} :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) ↔ r < 1 := by
  refine ⟨fun h => ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr => top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn => pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  norm_cast at h ⊢
  exact NNReal.tendsto_pow_atTop_nhds_zero_iff.mp h

@[simp]
/--
theorem `ENNReal.tendsto_pow_atTop_nhds_top_iff` / 定理 `ENNReal.tendsto_pow_atTop_nhds_top_iff`

English:
theorem ENNReal.tendsto_pow_atTop_nhds_top_iff
  given: {r : Real>=0∞}
  proof: by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
exact lt_irrefl _ lt_of_lt_of_le (hn n le_rfl) pow_le_one₀ zero_le r

中文:
定理 ENNReal.tendsto_pow_atTop_nhds_top_iff
  条件: {r : 实数>=0∞}
  证明: by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
exact lt_irrefl _ lt_of_lt_of_le (hn n le_rfl) pow_le_one₀ zero_le r
-/
protected theorem ENNReal.tendsto_pow_atTop_nhds_top_iff {r : Real>=0∞} :
    Tendsto (fun n => r ^ n) atTop (𝓝 ∞) ↔ 1 < r := by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
exact lt_irrefl _ lt_of_lt_of_le (hn n le_rfl) pow_le_one₀ zero_le r_le_one
  · intro r_gt_one
    have obs := @Tendsto.inv Real>=0∞ Nat _ _ _ (fun n => (r⁻¹) ^ n) atTop 0
    simp only [ENNReal.tendsto_pow_atTop_nhds_zero_iff, inv_zero] at obs
simpa [← ENNReal.inv_pow] using obs ENNReal.inv_lt_one.mpr r_gt_one

/--
lemma `ENNReal.eq_zero_of_le_mul_pow` / 引理 `ENNReal.eq_zero_of_le_mul_pow`

English:
lemma ENNReal.eq_zero_of_le_mul_pow
  statement: {x r : Real>=0∞} {ε : Real>=0} (hr : r < 1)
  proof: by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : Nat) => ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := Real>=0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

中文:
引理 ENNReal.eq_zero_of_le_mul_pow
  结论: {x r : 实数>=0∞} {ε : 实数>=0} (hr : r < 1)
  证明: by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : Nat) => ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := Real>=0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

Depends on / 依赖: Or.inr, Tendsto, Tendsto.const_mul, coe_ne_top, const_mul, ge_of_tendsto, mul_zero, nonpos_iff_eq_zero, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
lemma ENNReal.eq_zero_of_le_mul_pow {x r : Real>=0∞} {ε : Real>=0} (hr : r < 1)
    (h : forall n : Nat, x <= ε * r ^ n) : x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : Nat) => ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := Real>=0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

/-! ### Geometric series -/

section Geometric

/--
theorem `hasSum_geometric_of_lt_one` / 定理 `hasSum_geometric_of_lt_one`

English:
theorem hasSum_geometric_of_lt_one
  given: {r : Real} (h₁ : 0 <= r) (h₂ : r < 1)
  proof: have : r != 1 := ne_of_lt h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
(hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr by
    simp_all [neg_inv, geo

中文:
定理 hasSum_geometric_of_lt_one
  条件: {r : 实数} (h₁ : 0 <= r) (h₂ : r < 1)
  证明: have : r != 1 := ne_of_lt h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
(hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr by
    simp_all [neg_inv, geo

Depends on / 依赖: Tendsto, div_eq_mul_inv, geom_sum_eq, hasSum_iff_tendsto_nat_of_nonneg, ne_of_lt, neg_inv, pow_nonneg, tendsto_const_nhds, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
theorem hasSum_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) :
    HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹ :=
  have : r != 1 := ne_of_lt h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
(hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr by
    simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]

/--
theorem `summable_geometric_of_lt_one` / 定理 `summable_geometric_of_lt_one`

English:
theorem summable_geometric_of_lt_one
  given: {r : Real} (h₁ : 0 <= r) (h₂ : r < 1)
  proof: ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩

中文:
定理 summable_geometric_of_lt_one
  条件: {r : 实数} (h₁ : 0 <= r) (h₂ : r < 1)
  证明: ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩

Depends on / 依赖: hasSum_geometric_of_lt_one
-/
theorem summable_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) :
    Summable fun n : Nat => r ^ n :=
  ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩


/--
theorem `tsum_geometric_of_lt_one` / 定理 `tsum_geometric_of_lt_one`

English:
theorem tsum_geometric_of_lt_one
  given: {r : Real} (h₁ : 0 <= r) (h₂ : r < 1)
  statement: ∑' n : Nat, r ^ n = (1 - r)⁻¹
  proof: (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq

中文:
定理 tsum_geometric_of_lt_one
  条件: {r : 实数} (h₁ : 0 <= r) (h₂ : r < 1)
  结论: ∑' n : 自然数, r ^ n = (1 - r)⁻¹
  证明: (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq

Depends on / 依赖: hasSum_geometric_of_lt_one, tsum_eq
-/
theorem tsum_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) : ∑' n : Nat, r ^ n = (1 - r)⁻¹ :=
  (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq

/--
theorem `hasSum_geometric_two` / 定理 `hasSum_geometric_two`

English:
theorem hasSum_geometric_two
  statement: HasSum (fun n : Nat => ((1 : Real) / 2) ^ n) 2
  proof: by
  convert! hasSum_geometric_of_lt_one _ _ <;> norm_num

中文:
定理 hasSum_geometric_two
  结论: HasSum (fun n : 自然数 => ((1 : 实数) / 2) ^ n) 2
  证明: by
  convert! hasSum_geometric_of_lt_one _ _ <;> norm_num

Depends on / 依赖: convert, hasSum_geometric_of_lt_one
-/
theorem hasSum_geometric_two : HasSum (fun n : Nat => ((1 : Real) / 2) ^ n) 2 := by
  convert! hasSum_geometric_of_lt_one _ _ <;> norm_num

/--
theorem `summable_geometric_two` / 定理 `summable_geometric_two`

English:
theorem summable_geometric_two
  statement: Summable fun n : Nat => ((1 : Real) / 2) ^ n
  proof: ⟨_, hasSum_geometric_two⟩

中文:
定理 summable_geometric_two
  结论: Summable fun n : 自然数 => ((1 : 实数) / 2) ^ n
  证明: ⟨_, hasSum_geometric_two⟩

Depends on / 依赖: hasSum_geometric_two
-/
theorem summable_geometric_two : Summable fun n : Nat => ((1 : Real) / 2) ^ n :=
  ⟨_, hasSum_geometric_two⟩

/--
theorem `summable_geometric_two_encode` / 定理 `summable_geometric_two_encode`

English:
theorem summable_geometric_two_encode
  given: {ι : Type*} [Encodable ι]
  proof: summable_geometric_two.comp_injective Encodable.encode_injective

中文:
定理 summable_geometric_two_encode
  条件: {ι : 类型} [Encodable ι]
  证明: summable_geometric_two.comp_injective Encodable.encode_injective

Depends on / 依赖: Encodable, Encodable.encode_injective, comp_injective, encode_injective, summable_geometric_two, summable_geometric_two.comp_injective
-/
theorem summable_geometric_two_encode {ι : Type*} [Encodable ι] :
    Summable fun i : ι => (1 / 2 : Real) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective

/--
theorem `tsum_geometric_two` / 定理 `tsum_geometric_two`

English:
theorem tsum_geometric_two
  statement: (∑' n : Nat, ((1 : Real) / 2) ^ n) = 2
  proof: hasSum_geometric_two.tsum_eq

中文:
定理 tsum_geometric_two
  结论: (∑' n : 自然数, ((1 : 实数) / 2) ^ n) = 2
  证明: hasSum_geometric_two.tsum_eq

Depends on / 依赖: hasSum_geometric_two, hasSum_geometric_two.tsum_eq, tsum_eq
-/
theorem tsum_geometric_two : (∑' n : Nat, ((1 : Real) / 2) ^ n) = 2 :=
  hasSum_geometric_two.tsum_eq

/--
theorem `sum_geometric_two_le` / 定理 `sum_geometric_two_le`

English:
theorem sum_geometric_two_le
  given: (n : Nat)
  statement: (∑ i in range n, (1 / (2 : Real)) ^ i) <= 2
  proof: by
  have : forall i, 0 <= (1 / (2 : Real)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert! summable_geometric_two.sum_le_tsum (range n) (fun i _ => this i)
  exact tsum_geometric_two.symm

中文:
定理 sum_geometric_two_le
  条件: (n : 自然数)
  结论: (∑ i in range n, (1 / (2 : 实数)) ^ i) <= 2
  证明: by
  have : forall i, 0 <= (1 / (2 : Real)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert! summable_geometric_two.sum_le_tsum (range n) (fun i _ => this i)
  exact tsum_geometric_two.symm

Depends on / 依赖: convert, pow_nonneg, sum_le_tsum, summable_geometric_two, summable_geometric_two.sum_le_tsum, tsum_geometric_two, tsum_geometric_two.symm
-/
theorem sum_geometric_two_le (n : Nat) : (∑ i in range n, (1 / (2 : Real)) ^ i) <= 2 := by
  have : forall i, 0 <= (1 / (2 : Real)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert! summable_geometric_two.sum_le_tsum (range n) (fun i _ => this i)
  exact tsum_geometric_two.symm

/--
theorem `tsum_geometric_inv_two` / 定理 `tsum_geometric_inv_two`

English:
theorem tsum_geometric_inv_two
  statement: (∑' n : Nat, (2 : Real)⁻¹ ^ n) = 2
  proof: (inv_eq_one_div (2 : Real)).symm ▸ tsum_geometric_two

中文:
定理 tsum_geometric_inv_two
  结论: (∑' n : 自然数, (2 : 实数)⁻¹ ^ n) = 2
  证明: (inv_eq_one_div (2 : Real)).symm ▸ tsum_geometric_two

Depends on / 依赖: inv_eq_one_div, tsum_geometric_two
-/
theorem tsum_geometric_inv_two : (∑' n : Nat, (2 : Real)⁻¹ ^ n) = 2 :=
  (inv_eq_one_div (2 : Real)).symm ▸ tsum_geometric_two

/--
theorem `tsum_geometric_inv_two_ge` / 定理 `tsum_geometric_inv_two_ge`

English:
theorem tsum_geometric_inv_two_ge
  given: (n : Nat)
  proof: by
  have A : Summable fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div]
      using! summable_geometric_two.indicator {i | n <= i}
  have B : ((Finset.range n).sum fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0) = 0 :=
    Finset.sum_eq_zero

中文:
定理 tsum_geometric_inv_two_ge
  条件: (n : 自然数)
  证明: by
  have A : Summable fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div]
      using! summable_geometric_two.indicator {i | n <= i}
  have B : ((Finset.range n).sum fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0) = 0 :=
    Finset.sum_eq_zero

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, Finset.sum_eq_zero, Summable, Summable.sum_add_tsum_nat_add, _root_, _root_.tsum_mul_right, indicator, inv_pow, ite_eq_right_iff, lt_irrefl, mem_range, one_div, piecewise_eq_indicator, pow_add, sum_add_tsum_nat_add, sum_eq_zero, summable_geometric_two, summable_geometric_two.indicator
-/
theorem tsum_geometric_inv_two_ge (n : Nat) :
    (∑' i, ite (n <= i) ((2 : Real)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div]
      using! summable_geometric_two.indicator {i | n <= i}
  have B : ((Finset.range n).sum fun i : Nat => ite (n <= i) ((2⁻¹ : Real) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi =>
      ite_eq_right_iff.2 fun h => (lt_irrefl _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp [-inv_pow, ← Summable.sum_add_tsum_nat_add n A, B, pow_add, _root_.tsum_mul_right,
    tsum_geometric_inv_two]

/--
theorem `hasSum_geometric_two'` / 定理 `hasSum_geometric_two'`

English:
theorem hasSum_geometric_two'
  given: (a : Real)
  statement: HasSum (fun n : Nat => a / 2 / 2 ^ n) a
  proof: by
  convert!
    HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div, inv_pow]
    rfl
  · norm_num

中文:
定理 hasSum_geometric_two'
  条件: (a : 实数)
  结论: HasSum (fun n : 自然数 => a / 2 / 2 ^ n) a
  证明: by
  convert!
    HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div, inv_pow]
    rfl
  · norm_num

Depends on / 依赖: HasSum, HasSum.mul_left, convert, hasSum_geometric_of_lt_one, inv_pow, le_of_lt, mul_left, one_div, one_half_lt_one, one_half_pos
-/
theorem hasSum_geometric_two' (a : Real) : HasSum (fun n : Nat => a / 2 / 2 ^ n) a := by
  convert!
    HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div, inv_pow]
    rfl
  · norm_num

/--
theorem `summable_geometric_two'` / 定理 `summable_geometric_two'`

English:
theorem summable_geometric_two'
  given: (a : Real)
  statement: Summable fun n : Nat => a / 2 / 2 ^ n
  proof: ⟨a, hasSum_geometric_two' a⟩

中文:
定理 summable_geometric_two'
  条件: (a : 实数)
  结论: Summable fun n : 自然数 => a / 2 / 2 ^ n
  证明: ⟨a, hasSum_geometric_two' a⟩

Depends on / 依赖: hasSum_geometric_two
-/
theorem summable_geometric_two' (a : Real) : Summable fun n : Nat => a / 2 / 2 ^ n :=
  ⟨a, hasSum_geometric_two' a⟩

/--
theorem `tsum_geometric_two'` / 定理 `tsum_geometric_two'`

English:
theorem tsum_geometric_two'
  given: (a : Real)
  statement: ∑' n : Nat, a / 2 / 2 ^ n = a
  proof: (hasSum_geometric_two' a).tsum_eq

中文:
定理 tsum_geometric_two'
  条件: (a : 实数)
  结论: ∑' n : 自然数, a / 2 / 2 ^ n = a
  证明: (hasSum_geometric_two' a).tsum_eq

Depends on / 依赖: hasSum_geometric_two, tsum_eq
-/
theorem tsum_geometric_two' (a : Real) : ∑' n : Nat, a / 2 / 2 ^ n = a :=
  (hasSum_geometric_two' a).tsum_eq

/--
theorem `NNReal.hasSum_geometric` / 定理 `NNReal.hasSum_geometric`

English:
theorem NNReal.hasSum_geometric
  given: {r : Real>=0} (hr : r < 1)
  statement: HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
  proof: by
  apply NNReal.hasSum_coe.1
  push_cast
  rw [NNReal.coe_sub (le_of_lt hr)]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr

中文:
定理 NNReal.hasSum_geometric
  条件: {r : 实数>=0} (hr : r < 1)
  结论: HasSum (fun n : 自然数 => r ^ n) (1 - r)⁻¹
  证明: by
  apply NNReal.hasSum_coe.1
  push_cast
  rw [NNReal.coe_sub (le_of_lt hr)]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr

Depends on / 依赖: NNReal, NNReal.coe_sub, NNReal.hasSum_coe, coe_nonneg, coe_sub, hasSum_coe, hasSum_geometric_of_lt_one, le_of_lt, r.coe_nonneg
-/
theorem NNReal.hasSum_geometric {r : Real>=0} (hr : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹ := by
  apply NNReal.hasSum_coe.1
  push_cast
  rw [NNReal.coe_sub (le_of_lt hr)]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr

/--
theorem `NNReal.summable_geometric` / 定理 `NNReal.summable_geometric`

English:
theorem NNReal.summable_geometric
  given: {r : Real>=0} (hr : r < 1)
  statement: Summable fun n : Nat => r ^ n
  proof: ⟨_, NNReal.hasSum_geometric hr⟩

中文:
定理 NNReal.summable_geometric
  条件: {r : 实数>=0} (hr : r < 1)
  结论: Summable fun n : 自然数 => r ^ n
  证明: ⟨_, NNReal.hasSum_geometric hr⟩

Depends on / 依赖: NNReal, NNReal.hasSum_geometric, hasSum_geometric
-/
theorem NNReal.summable_geometric {r : Real>=0} (hr : r < 1) : Summable fun n : Nat => r ^ n :=
  ⟨_, NNReal.hasSum_geometric hr⟩

/--
theorem `NNReal.tsum_geometric` / 定理 `NNReal.tsum_geometric`

English:
theorem NNReal.tsum_geometric
  given: {r : Real>=0} (hr : r < 1)
  statement: ∑' n : Nat, r ^ n = (1 - r)⁻¹
  proof: (NNReal.hasSum_geometric hr).tsum_eq

@[deprecated (since := "2026-03-18")] alias tsum_geometric_nnreal := NNReal.tsum_geometric

中文:
定理 NNReal.tsum_geometric
  条件: {r : 实数>=0} (hr : r < 1)
  结论: ∑' n : 自然数, r ^ n = (1 - r)⁻¹
  证明: (NNReal.hasSum_geometric hr).tsum_eq

@[deprecated (since := "2026-03-18")] alias tsum_geometric_nnreal := NNReal.tsum_geometric

Depends on / 依赖: NNReal, NNReal.hasSum_geometric, hasSum_geometric, tsum_eq
-/
theorem NNReal.tsum_geometric {r : Real>=0} (hr : r < 1) : ∑' n : Nat, r ^ n = (1 - r)⁻¹ :=
  (NNReal.hasSum_geometric hr).tsum_eq

@[deprecated (since := "2026-03-18")] alias tsum_geometric_nnreal := NNReal.tsum_geometric

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
/--
theorem `ENNReal.tsum_geometric` / 定理 `ENNReal.tsum_geometric`

English:
theorem ENNReal.tsum_geometric
  given: (r : Real>=0∞)
  statement: ∑' n : Nat, r ^ n = (1 - r)⁻¹
  proof: by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert! ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv <| ne_of_gt <| tsub_pos_iff_lt.2 hr]; rw [coe_sub]; rw [coe_one]
  · rw [tsub_eq_zero_iff_le.mpr

中文:
定理 ENNReal.tsum_geometric
  条件: (r : 实数>=0∞)
  结论: ∑' n : 自然数, r ^ n = (1 - r)⁻¹
  证明: by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert! ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv <| ne_of_gt <| tsub_pos_iff_lt.2 hr]; rw [coe_sub]; rw [coe_one]
  · rw [tsub_eq_zero_iff_le.mpr

Depends on / 依赖: ENNReal, ENNReal.coe_inv, ENNReal.exists_nat_gt, ENNReal.inv_zero, ENNReal.lt_iff_exists_coe, ENNReal.tsum_coe_eq, ENNReal.tsum_eq_iSup_nat, NNReal, NNReal.hasSum_geometric, coe_inv, coe_one, coe_sub, convert, exists_nat_gt, hasSum_geometric, iSup_eq_top, inv_zero, lt_iff_exists_coe, lt_of_lt_of_le, lt_or_ge
-/
theorem ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : Nat, r ^ n = (1 - r)⁻¹ := by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert! ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv <| ne_of_gt <| tsub_pos_iff_lt.2 hr]; rw [coe_sub]; rw [coe_one]
  · rw [tsub_eq_zero_iff_le.mpr hr, ENNReal.inv_zero, ENNReal.tsum_eq_iSup_nat, iSup_eq_top]
    refine fun a ha =>
      (ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn => lt_of_lt_of_le hn ?_
    calc
      (n : Real>=0∞) = ∑ i in range n, 1 := by rw [sum_const, nsmul_one, card_range]
      _ <= ∑ i in range n, r ^ i := by gcongr; apply one_le_pow₀ hr

/--
theorem `ENNReal.tsum_geometric_add_one` / 定理 `ENNReal.tsum_geometric_add_one`

English:
theorem ENNReal.tsum_geometric_add_one
  given: (r : Real>=0∞)
  statement: ∑' n : Nat, r ^ (n + 1) = r * (1 - r)⁻¹
  proof: by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

中文:
定理 ENNReal.tsum_geometric_add_one
  条件: (r : 实数>=0∞)
  结论: ∑' n : 自然数, r ^ (n + 1) = r * (1 - r)⁻¹
  证明: by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

Depends on / 依赖: ENNReal, ENNReal.tsum_geometric, ENNReal.tsum_mul_left, _root_, _root_.pow_succ, pow_succ, tsum_geometric, tsum_mul_left
-/
theorem ENNReal.tsum_geometric_add_one (r : Real>=0∞) : ∑' n : Nat, r ^ (n + 1) = r * (1 - r)⁻¹ := by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/--
lemma `ENNReal.tsum_two_zpow_neg_add_one` / 引理 `ENNReal.tsum_two_zpow_neg_add_one`

English:
lemma ENNReal.tsum_two_zpow_neg_add_one
  proof: by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := Int), ← Nat.cast_add, zpow_natCast,
    ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

中文:
引理 ENNReal.tsum_two_zpow_neg_add_one
  证明: by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := Int), ← Nat.cast_add, zpow_natCast,
    ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, ENNReal.zpow_neg, Nat.cast_add, Nat.cast_one, Ne.symm, NeZero, NeZero.ne, cast_add, cast_one, inv_inv, inv_mul_cancel, inv_pow, neg_sub_left, one_sub_inv_two, simp_rw, top_ne_ofNat, tsum_geometric_add_one
-/
lemma ENNReal.tsum_two_zpow_neg_add_one :
    ∑' m : Nat, 2 ^ (-1 - m : Int) = (1 : Real>=0∞) := by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := Int), ← Nat.cast_add, zpow_natCast,
    ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

open Encodable

/--
lemma `ENNReal.tsum_geometric_two` / 引理 `ENNReal.tsum_geometric_two`

English:
lemma ENNReal.tsum_geometric_two
  statement: ∑' n, (2⁻¹ : Real>=0∞) ^ n = 2
  proof: by simp

中文:
引理 ENNReal.tsum_geometric_two
  结论: ∑' n, (2⁻¹ : 实数>=0∞) ^ n = 2
  证明: by simp
-/
protected lemma ENNReal.tsum_geometric_two : ∑' n, (2⁻¹ : Real>=0∞) ^ n = 2 := by simp

/--
lemma `ENNReal.tsum_geometric_two_encode_le_two` / 引理 `ENNReal.tsum_geometric_two_encode_le_two`

English:
lemma ENNReal.tsum_geometric_two_encode_le_two
  given: {ι : Type*} [Encodable ι]
  proof: (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two

中文:
引理 ENNReal.tsum_geometric_two_encode_le_two
  条件: {ι : 类型} [Encodable ι]
  证明: (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two

Depends on / 依赖: ENNReal, ENNReal.tsum_comp_le_tsum_of_injective, ENNReal.tsum_geometric_two, encode_injective, trans_eq, tsum_comp_le_tsum_of_injective, tsum_geometric_two
-/
lemma ENNReal.tsum_geometric_two_encode_le_two {ι : Type*} [Encodable ι] :
    ∑' i : ι, (2⁻¹ : Real>=0∞) ^ encode i <= 2 :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two

/--
lemma `tsum_geometric_lt_top` / 引理 `tsum_geometric_lt_top`

English:
lemma tsum_geometric_lt_top
  given: {r : Real>=0∞}
  statement: ∑' n, r ^ n < ∞ ↔ r < 1
  proof: by simp

中文:
引理 tsum_geometric_lt_top
  条件: {r : 实数>=0∞}
  结论: ∑' n, r ^ n < ∞ ↔ r < 1
  证明: by simp
-/
lemma tsum_geometric_lt_top {r : Real>=0∞} : ∑' n, r ^ n < ∞ ↔ r < 1 := by simp

/--
lemma `tsum_geometric_encode_lt_top` / 引理 `tsum_geometric_encode_lt_top`

English:
lemma tsum_geometric_encode_lt_top
  given: {r : Real>=0∞} (hr : r < 1) {ι : Type*} [Encodable ι]
  proof: (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt by simpa

中文:
引理 tsum_geometric_encode_lt_top
  条件: {r : 实数>=0∞} (hr : r < 1) {ι : 类型} [Encodable ι]
  证明: (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt by simpa

Depends on / 依赖: ENNReal, ENNReal.tsum_comp_le_tsum_of_injective, encode_injective, trans_lt, tsum_comp_le_tsum_of_injective
-/
lemma tsum_geometric_encode_lt_top {r : Real>=0∞} (hr : r < 1) {ι : Type*} [Encodable ι] :
    ∑' i : ι, (r : Real>=0∞) ^ encode i < ∞ :=
(ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt by simpa

end Geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EDistLeGeometric

variable [PseudoEMetricSpace α] (r C : Real>=0∞) (hr : r < 1) (hC : C != ⊤) {f : Nat -> α}
  (hu : forall n, edist (f n) (f (n + 1)) <= C * r ^ n)

include hr hC hu in
/--
theorem `cauchySeq_of_edist_le_geometric` / 定理 `cauchySeq_of_edist_le_geometric`

English:
theorem cauchySeq_of_edist_le_geometric
  statement: CauchySeq f
  proof: by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left]; rw [ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hr).ne']

include hu in

中文:
定理 cauchySeq_of_edist_le_geometric
  结论: CauchySeq f
  证明: by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left]; rw [ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hr).ne']

include hu in

Depends on / 依赖: ENNReal, ENNReal.tsum_geometric, ENNReal.tsum_mul_left, cauchySeq_of_edist_le_of_tsum_ne_top, finiteness, tsub_pos_iff_lt, tsum_geometric, tsum_mul_left
-/
theorem cauchySeq_of_edist_le_geometric : CauchySeq f := by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left]; rw [ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hr).ne']

include hu in
/--
theorem `edist_le_of_edist_le_geometric_of_tendsto` / 定理 `edist_le_of_edist_le_geometric_of_tendsto`

English:
theorem edist_le_of_edist_le_geometric_of_tendsto
  given: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat)
  proof: by
  convert! edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, mul_assoc]

include hu in

中文:
定理 edist_le_of_edist_le_geometric_of_tendsto
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : 自然数)
  证明: by
  convert! edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, mul_assoc]

include hu in

Depends on / 依赖: ENNReal, ENNReal.tsum_geometric, ENNReal.tsum_mul_left, convert, div_eq_mul_inv, edist_le_tsum_of_edist_le_of_tendsto, mul_assoc, pow_add, tsum_geometric, tsum_mul_left
-/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) :
    edist (f n) a <= C * r ^ n / (1 - r) := by
  convert! edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, mul_assoc]

include hu in
/--
theorem `edist_le_of_edist_le_geometric_of_tendsto₀` / 定理 `edist_le_of_edist_le_geometric_of_tendsto₀`

English:
theorem edist_le_of_edist_le_geometric_of_tendsto₀
  given: {a : α} (ha : Tendsto f atTop (𝓝 a))
  proof: by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

中文:
定理 edist_le_of_edist_le_geometric_of_tendsto₀
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a))
  证明: by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

Depends on / 依赖: _root_, _root_.pow_zero, edist_le_of_edist_le_geometric_of_tendsto, mul_one, pow_zero
-/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a <= C / (1 - r) := by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EDistLeGeometric

section EDistLeGeometricTwo

variable [PseudoEMetricSpace α] (C : Real>=0∞) (hC : C != ⊤) {f : Nat -> α}
  (hu : forall n, edist (f n) (f (n + 1)) <= C / 2 ^ n) {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu in
/--
theorem `cauchySeq_of_edist_le_geometric_two` / 定理 `cauchySeq_of_edist_le_geometric_two`

English:
theorem cauchySeq_of_edist_le_geometric_two
  statement: CauchySeq f
  proof: by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in

中文:
定理 cauchySeq_of_edist_le_geometric_two
  结论: CauchySeq f
  证明: by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in

Depends on / 依赖: ENNReal, ENNReal.inv_pow, cauchySeq_of_edist_le_geometric, div_eq_mul_inv, inv_pow
-/
theorem cauchySeq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in
/--
theorem `edist_le_of_edist_le_geometric_two_of_tendsto` / 定理 `edist_le_of_edist_le_geometric_two_of_tendsto`

English:
theorem edist_le_of_edist_le_geometric_two_of_tendsto
  given: (n : Nat)
  statement: edist (f n) a <= 2 * C / 2 ^ n
  proof: by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at *
  rw [mul_assoc]; rw [mul_comm]
  convert! edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n using 1
  rw [ENNReal.one_sub_inv_two]; rw [div_eq_mul_inv]; rw [inv_inv]

include hu ha in

中文:
定理 edist_le_of_edist_le_geometric_two_of_tendsto
  条件: (n : 自然数)
  结论: edist (f n) a <= 2 * C / 2 ^ n
  证明: by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at *
  rw [mul_assoc]; rw [mul_comm]
  convert! edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n using 1
  rw [ENNReal.one_sub_inv_two]; rw [div_eq_mul_inv]; rw [inv_inv]

include hu ha in

Depends on / 依赖: ENNReal, ENNReal.inv_pow, ENNReal.one_sub_inv_two, convert, div_eq_mul_inv, edist_le_of_edist_le_geometric_of_tendsto, inv_inv, inv_pow, mul_assoc, mul_comm, one_sub_inv_two
-/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : Nat) : edist (f n) a <= 2 * C / 2 ^ n := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at *
  rw [mul_assoc]; rw [mul_comm]
  convert! edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n using 1
  rw [ENNReal.one_sub_inv_two]; rw [div_eq_mul_inv]; rw [inv_inv]

include hu ha in
/--
theorem `edist_le_of_edist_le_geometric_two_of_tendsto₀` / 定理 `edist_le_of_edist_le_geometric_two_of_tendsto₀`

English:
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀
  statement: edist (f 0) a <= 2 * C
  proof: by
  simpa only [_root_.pow_zero, div_eq_mul_inv, inv_one, mul_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

中文:
定理 edist_le_of_edist_le_geometric_two_of_tendsto₀
  结论: edist (f 0) a <= 2 * C
  证明: by
  simpa only [_root_.pow_zero, div_eq_mul_inv, inv_one, mul_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

Depends on / 依赖: _root_, _root_.pow_zero, div_eq_mul_inv, edist_le_of_edist_le_geometric_two_of_tendsto, inv_one, mul_one, pow_zero
-/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a <= 2 * C := by
  simpa only [_root_.pow_zero, div_eq_mul_inv, inv_one, mul_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EDistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : Real} {f : Nat -> α}

section
variable (hr : r < 1) (hu : forall n, dist (f n) (f (n + 1)) <= C * r ^ n)
include hr hu

/--
theorem `aux_hasSum_of_le_geometric` / 定理 `aux_hasSum_of_le_geometric`

English:
theorem aux_hasSum_of_le_geometric
  statement: HasSum (fun n : Nat => C * r ^ n) (C / (1 - r))
  proof: by
  rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · refine HasSum.mul_left C ?_
    simpa using hasSum_geometric_of_lt_one r₀ hr

中文:
定理 aux_hasSum_of_le_geometric
  结论: HasSum (fun n : 自然数 => C * r ^ n) (C / (1 - r))
  证明: by
  rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · refine HasSum.mul_left C ?_
    simpa using hasSum_geometric_of_lt_one r₀ hr

Depends on / 依赖: HasSum, HasSum.mul_left, dist_nonneg, dist_nonneg.trans, hasSum_geometric_of_lt_one, hasSum_zero, mul_left, sign_cases_of_C_mul_pow_nonneg
-/
theorem aux_hasSum_of_le_geometric : HasSum (fun n : Nat => C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · refine HasSum.mul_left C ?_
    simpa using hasSum_geometric_of_lt_one r₀ hr

variable (r C)

/--
theorem `cauchySeq_of_le_geometric` / 定理 `cauchySeq_of_le_geometric`

English:
theorem cauchySeq_of_le_geometric
  statement: CauchySeq f
  proof: cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

中文:
定理 cauchySeq_of_le_geometric
  结论: CauchySeq f
  证明: cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

Depends on / 依赖: aux_hasSum_of_le_geometric, cauchySeq_of_dist_le_of_summable
-/
theorem cauchySeq_of_le_geometric : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

/--
theorem `dist_le_of_le_geometric_of_tendsto₀` / 定理 `dist_le_of_le_geometric_of_tendsto₀`

English:
theorem dist_le_of_le_geometric_of_tendsto₀
  given: {a : α} (ha : Tendsto f atTop (𝓝 a))
  proof: (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

中文:
定理 dist_le_of_le_geometric_of_tendsto₀
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a))
  证明: (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

Depends on / 依赖: aux_hasSum_of_le_geometric, tsum_eq
-/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a <= C / (1 - r) :=
  (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

/--
theorem `dist_le_of_le_geometric_of_tendsto` / 定理 `dist_le_of_le_geometric_of_tendsto`

English:
theorem dist_le_of_le_geometric_of_tendsto
  given: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat)
  proof: by
  have := aux_hasSum_of_le_geometric hr hu
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

中文:
定理 dist_le_of_le_geometric_of_tendsto
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : 自然数)
  证明: by
  have := aux_hasSum_of_le_geometric hr hu
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

Depends on / 依赖: aux_hasSum_of_le_geometric, convert, dist_le_tsum_of_dist_le_of_tendsto, mul_comm, mul_div_right_comm, mul_left, mul_left_comm, pow_add, this.mul_left, tsum_eq, tsum_eq.symm
-/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) :
    dist (f n) a <= C * r ^ n / (1 - r) := by
  have := aux_hasSum_of_le_geometric hr hu
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

end

variable (hu₂ : forall n, dist (f n) (f (n + 1)) <= C / 2 / 2 ^ n)
include hu₂

/--
theorem `cauchySeq_of_le_geometric_two` / 定理 `cauchySeq_of_le_geometric_two`

English:
theorem cauchySeq_of_le_geometric_two
  statement: CauchySeq f
  proof: cauchySeq_of_dist_le_of_summable _ hu₂ ⟨_, hasSum_geometric_two' C⟩

中文:
定理 cauchySeq_of_le_geometric_two
  结论: CauchySeq f
  证明: cauchySeq_of_dist_le_of_summable _ hu₂ ⟨_, hasSum_geometric_two' C⟩

Depends on / 依赖: cauchySeq_of_dist_le_of_summable, hasSum_geometric_two
-/
theorem cauchySeq_of_le_geometric_two : CauchySeq f :=
cauchySeq_of_dist_le_of_summable _ hu₂ ⟨_, hasSum_geometric_two' C⟩

/--
theorem `dist_le_of_le_geometric_two_of_tendsto₀` / 定理 `dist_le_of_le_geometric_two_of_tendsto₀`

English:
theorem dist_le_of_le_geometric_two_of_tendsto₀
  given: {a : α} (ha : Tendsto f atTop (𝓝 a))
  proof: tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

中文:
定理 dist_le_of_le_geometric_two_of_tendsto₀
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a))
  证明: tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

Depends on / 依赖: summable_geometric_two, tsum_geometric_two
-/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a <= C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

/--
theorem `dist_le_of_le_geometric_two_of_tendsto` / 定理 `dist_le_of_le_geometric_two_of_tendsto`

English:
theorem dist_le_of_le_geometric_two_of_tendsto
  given: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat)
  proof: by
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_comm n, pow_add, ← div_div]
  symm
  exact ((hasSum_geometric_two' C).div_const _).tsum_eq

中文:
定理 dist_le_of_le_geometric_two_of_tendsto
  条件: {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : 自然数)
  证明: by
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_comm n, pow_add, ← div_div]
  symm
  exact ((hasSum_geometric_two' C).div_const _).tsum_eq

Depends on / 依赖: add_comm, convert, dist_le_tsum_of_dist_le_of_tendsto, div_const, div_div, hasSum_geometric_two, pow_add, summable_geometric_two, tsum_eq
-/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) :
    dist (f n) a <= C / 2 ^ n := by
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_comm n, pow_add, ← div_div]
  symm
  exact ((hasSum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

/-! ### Summability tests based on comparison with geometric series -/


/--
theorem `summable_one_div_pow_of_le` / 定理 `summable_one_div_pow_of_le`

English:
theorem summable_one_div_pow_of_le
  given: {m : Real} {f : Nat -> Nat} (hm : 1 < m) (fi : forall i, i <= f i)
  proof: by
  refine .of_nonneg_of_le (fun a => by positivity) (fun a => ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow]; rw [one_pow]
  refine (one_div_le_one_div

中文:
定理 summable_one_div_pow_of_le
  条件: {m : 实数} {f : 自然数 -> 自然数} (hm : 1 < m) (fi : 对任意 i, i <= f i)
  证明: by
  refine .of_nonneg_of_le (fun a => by positivity) (fun a => ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow]; rw [one_pow]
  refine (one_div_le_one_div

Depends on / 依赖: div_pow, hm.le, of_nonneg_of_le, one_div_le_one_div, one_div_lt, one_div_nonneg, one_div_nonneg.mpr, one_div_one, one_div_one.le.trans_lt, one_pow, pow_pos, summable_geometric_of_lt_one, trans_lt, zero_le_one, zero_le_one.trans, zero_lt_one, zero_lt_one.trans
-/
theorem summable_one_div_pow_of_le {m : Real} {f : Nat -> Nat} (hm : 1 < m) (fi : forall i, i <= f i) :
    Summable fun i => 1 / m ^ f i := by
  refine .of_nonneg_of_le (fun a => by positivity) (fun a => ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow]; rw [one_pow]
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ hm.le (fi a)) <;>
    exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on countable types -/


/--
Definition of `posSumOfEncodable` / `posSumOfEncodable` 的定义

English:
definition posSumOfEncodable
  signature: {ε : Real} (hε : 0 < ε) (ι) [Encodable ι]
  body: by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : forall n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i => f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg

中文:
定义 posSumOfEncodable
  签名: {ε : 实数} (hε : 0 < ε) (ι) [Encodable ι]
  定义体: by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : forall n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i => f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg

Depends on / 依赖: Encodable, Encodable.encode, Encodable.encode_injective, HasSum, comp_injective, div_pos, encode, encode_injective, half_pos, hasSum_geometric_two, hasSum_le_inj, hf.summable.comp_injective, le_of_lt, le_rfl, pow_pos, summable, zero_lt_two
-/
def posSumOfEncodable {ε : Real} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι -> Real // (forall i, 0 < ε' i) ∧ exists c, HasSum ε' c ∧ c <= ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : forall n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i => f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) ?_ ?_ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl

/--
theorem `Set.Countable.exists_pos_hasSum_le` / 定理 `Set.Countable.exists_pos_hasSum_le`

English:
theorem Set.Countable.exists_pos_hasSum_le
  statement: {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real}
  proof: by
  classical
  have := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i => if h : i in s then f ⟨i, h⟩ else 1, fun i => ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dif_pos, Subtype

中文:
定理 Set.Countable.exists_pos_hasSum_le
  结论: {ι : 类型} {s : Set ι} (hs : s.Countable) {ε : 实数}
  证明: by
  classical
  have := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i => if h : i in s then f ⟨i, h⟩ else 1, fun i => ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dif_pos, Subtype

Depends on / 依赖: Subtype, Subtype.coe_eta, Subtype.coe_prop, classical, coe_eta, coe_prop, conv_rhs, dif_pos, exacts, hs.toEncodable, posSumOfEncodable, split_ifs, toEncodable, zero_lt_one
-/
theorem Set.Countable.exists_pos_hasSum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real}
    (hε : 0 < ε) : exists ε' : ι -> Real, (forall i, 0 < ε' i) ∧ exists c, HasSum (fun i : s => ε' i) c ∧ c <= ε := by
  classical
  have := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i => if h : i in s then f ⟨i, h⟩ else 1, fun i => ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dif_pos, Subtype.coe_eta]

/--
theorem `Set.Countable.exists_pos_forall_sum_le` / 定理 `Set.Countable.exists_pos_forall_sum_le`

English:
theorem Set.Countable.exists_pos_forall_sum_le
  statement: {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real}
  proof: by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht => ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ => (hpos _).le

中文:
定理 Set.Countable.exists_pos_forall_sum_le
  结论: {ι : 类型} {s : Set ι} (hs : s.Countable) {ε : 实数}
  证明: by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht => ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ => (hpos _).le

Depends on / 依赖: classical, exists_pos_hasSum_le, hs.exists_pos_hasSum_le, sum_le_hasSum, sum_subtype_of_mem
-/
theorem Set.Countable.exists_pos_forall_sum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real}
    (hε : 0 < ε) : exists ε' : ι -> Real,
    (forall i, 0 < ε' i) ∧ forall t : Finset ι, ↑t subseteq s -> ∑ i in t, ε' i <= ε := by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht => ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ => (hpos _).le

namespace NNReal

/--
theorem `exists_pos_sum_of_countable` / 定理 `exists_pos_sum_of_countable`

English:
theorem exists_pos_sum_of_countable
  given: {ε : Real>=0} (hε : ε != 0) (ι) [Countable ι]
  proof: by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
⟨fun i => ⟨ε' i, (hε' i).le⟩, fun i => NNReal.coe_lt_coe.1 hε' i,
      ⟨c, hasSum_le (fun i => (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_co

中文:
定理 exists_pos_sum_of_countable
  条件: {ε : 实数>=0} (hε : ε != 0) (ι) [Countable ι]
  证明: by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
⟨fun i => ⟨ε' i, (hε' i).le⟩, fun i => NNReal.coe_lt_coe.1 hε' i,
      ⟨c, hasSum_le (fun i => (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_co

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_lt_coe, NNReal.hasSum_coe, coe_le_coe, coe_lt_coe, exists_between, hasSum_coe, hasSum_le, hasSum_zero, nonempty_encodable, posSumOfEncodable, pos_iff_ne_zero, trans_le
-/
theorem exists_pos_sum_of_countable {ε : Real>=0} (hε : ε != 0) (ι) [Countable ι] :
    exists ε' : ι -> Real>=0, (forall i, 0 < ε' i) ∧ exists c, HasSum ε' c ∧ c < ε := by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
⟨fun i => ⟨ε' i, (hε' i).le⟩, fun i => NNReal.coe_lt_coe.1 hε' i,
      ⟨c, hasSum_le (fun i => (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_coe.1 hc,
aε.trans_le' NNReal.coe_le_coe.1 hcε⟩

end NNReal

namespace ENNReal

/--
theorem `exists_pos_sum_of_countable` / 定理 `exists_pos_sum_of_countable`

English:
theorem exists_pos_sum_of_countable
  given: {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι]
  proof: by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩

中文:
定理 exists_pos_sum_of_countable
  条件: {ε : 实数>=0∞} (hε : ε != 0) (ι) [Countable ι]
  证明: by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩

Depends on / 依赖: ENNReal, ENNReal.tsum_coe_eq, NNReal, NNReal.exists_pos_sum_of_countable, coe_lt_coe, coe_pos, exists_between, exists_pos_sum_of_countable, lt_iff_exists_coe, lt_trans, pos_iff_ne_zero, tsum_coe_eq
-/
theorem exists_pos_sum_of_countable {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι] :
    exists ε' : ι -> Real>=0, (forall i, 0 < ε' i) ∧ (∑' i, (ε' i : Real>=0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩

/--
theorem `exists_pos_sum_of_countable'` / 定理 `exists_pos_sum_of_countable'`

English:
theorem exists_pos_sum_of_countable'
  given: {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι]
  proof: let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i => δ i, fun i => ENNReal.coe_pos.2 (δpos i), hδ⟩

中文:
定理 exists_pos_sum_of_countable'
  条件: {ε : 实数>=0∞} (hε : ε != 0) (ι) [Countable ι]
  证明: let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i => δ i, fun i => ENNReal.coe_pos.2 (δpos i), hδ⟩

Depends on / 依赖: ENNReal, ENNReal.coe_pos, coe_pos, exists_pos_sum_of_countable
-/
theorem exists_pos_sum_of_countable' {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι] :
    exists ε' : ι -> Real>=0∞, (forall i, 0 < ε' i) ∧ ∑' i, ε' i < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i => δ i, fun i => ENNReal.coe_pos.2 (δpos i), hδ⟩

/--
theorem `exists_pos_tsum_mul_lt_of_countable` / 定理 `exists_pos_tsum_mul_lt_of_countable`

English:
theorem exists_pos_tsum_mul_lt_of_countable
  statement: {ε : Real>=0∞} (hε : ε != 0) {ι} [Countable ι] (w : ι -> Real>=0∞)
  proof: by
  lift w to ι -> Real>=0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : forall i, 0 < max 1 (w i) := fun i => zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i => δ' i / max 1 (w i), fun i => div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.t

中文:
定理 exists_pos_tsum_mul_lt_of_countable
  结论: {ε : 实数>=0∞} (hε : ε != 0) {ι} [Countable ι] (w : ι -> 实数>=0∞)
  证明: by
  lift w to ι -> Real>=0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : forall i, 0 < max 1 (w i) := fun i => zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i => δ' i / max 1 (w i), fun i => div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.t

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, coe_div, div_pos, exists_pos_sum_of_countable, le_max_left, le_max_right, lt_of_le_of_lt, mul_le_of_le_div, trans_le, tsum_le_tsum, zero_lt_one, zero_lt_one.trans_le
-/
theorem exists_pos_tsum_mul_lt_of_countable {ε : Real>=0∞} (hε : ε != 0) {ι} [Countable ι] (w : ι -> Real>=0∞)
    (hw : forall i, w i != ∞) : exists δ : ι -> Real>=0, (forall i, 0 < δ i) ∧ (∑' i, (w i * δ i : Real>=0∞)) < ε := by
  lift w to ι -> Real>=0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : forall i, 0 < max 1 (w i) := fun i => zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i => δ' i / max 1 (w i), fun i => div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_) Hsum
  rw [coe_div (this i).ne']
  refine mul_le_of_le_div' ?_
  grw [← le_max_right]

end ENNReal



/--
theorem `factorial_tendsto_atTop` / 定理 `factorial_tendsto_atTop`

English:
theorem factorial_tendsto_atTop
  statement: Tendsto Nat.factorial atTop atTop
  proof: tendsto_atTop_atTop_of_monotone (fun _ _ => Nat.factorial_le) fun n => ⟨n, n.self_le_factorial⟩

中文:
定理 factorial_tendsto_atTop
  结论: Tendsto 自然数.factorial atTop atTop
  证明: tendsto_atTop_atTop_of_monotone (fun _ _ => Nat.factorial_le) fun n => ⟨n, n.self_le_factorial⟩

Depends on / 依赖: Nat.factorial_le, factorial_le, n.self_le_factorial, self_le_factorial, tendsto_atTop_atTop_of_monotone
-/
theorem factorial_tendsto_atTop : Tendsto Nat.factorial atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ => Nat.factorial_le) fun n => ⟨n, n.self_le_factorial⟩

/--
theorem `tendsto_factorial_div_pow_self_atTop` / 定理 `tendsto_factorial_div_pow_self_atTop`

English:
theorem tendsto_factorial_div_pow_self_atTop
  proof: tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1)
    (Eventually.of_forall fun n =>
      div_nonneg (mod_cast n.factorial_pos.le)
        (pow_nonneg (mod_cast n.zero_le) _))
    (by
      refine (eventually_gt_atTop 0).mono fun n hn => ?_


中文:
定理 tendsto_factorial_div_pow_self_atTop
  证明: tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1)
    (Eventually.of_forall fun n =>
      div_nonneg (mod_cast n.factorial_pos.le)
        (pow_nonneg (mod_cast n.zero_le) _))
    (by
      refine (eventually_gt_atTop 0).mono fun n hn => ?_


Depends on / 依赖: Eventually, Eventually.of_forall, Finset, Finset.prod_inv_dis, Nat.cast_succ, Nat.exists_eq_succ_of_ne_zero, cast_succ, div_eq_mul_inv, div_nonneg, eventually_gt_atTop, exists_eq_succ_of_ne_zero, factorial_eq_prod_range_add_one, factorial_pos, hn.ne.symm, inv_eq_one_div, mod_cast, n.factorial_pos.le, n.zero_le, of_forall, pow_eq_prod_const
-/
theorem tendsto_factorial_div_pow_self_atTop :
    Tendsto (fun n => n ! / (n : Real) ^ n : Nat -> Real) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1)
    (Eventually.of_forall fun n =>
      div_nonneg (mod_cast n.factorial_pos.le)
        (pow_nonneg (mod_cast n.zero_le) _))
    (by
      refine (eventually_gt_atTop 0).mono fun n hn => ?_
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [factorial_eq_prod_range_add_one]; rw [pow_eq_prod_const]; rw [div_eq_mul_inv]; rw [← inv_eq_one_div]; rw [prod_natCast]; rw [Nat.cast_succ]; rw [← Finset.prod_inv_distrib]; rw [← prod_mul_distrib]; rw [Finset.prod_range_succ']
      simp only [one_mul, Nat.cast_add, zero_add, Nat.cast_one]
      refine
            mul_le_of_le_one_left (inv_nonneg.mpr <| mod_cast hn.le) (prod_le_one ?_ ?_) <;>
          intro x hx <;>
        rw [Finset.mem_range] at hx
      · positivity
      · refine (div_le_one <| mod_cast hn).mpr ?_
        norm_cast
        lia)

/-!
### Ceil and floor
-/


section

/--
theorem `tendsto_nat_floor_atTop` / 定理 `tendsto_nat_floor_atTop`

English:
theorem tendsto_nat_floor_atTop
  statement: {α : Type*}
  proof: Nat.floor_mono.tendsto_atTop_atTop fun x => ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩

中文:
定理 tendsto_nat_floor_atTop
  结论: {α : 类型}
  证明: Nat.floor_mono.tendsto_atTop_atTop fun x => ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩

Depends on / 依赖: Nat.floor_mono.tendsto_atTop_atTop, Nat.le_floor_iff, floor_mono, le_floor_iff, tendsto_atTop_atTop
-/
theorem tendsto_nat_floor_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌊x⌋₊) atTop atTop :=
  Nat.floor_mono.tendsto_atTop_atTop fun x => ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩

/--
lemma `tendsto_nat_ceil_atTop` / 引理 `tendsto_nat_ceil_atTop`

English:
lemma tendsto_nat_ceil_atTop
  statement: {α : Type*}
  proof: by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x => ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

中文:
引理 tendsto_nat_ceil_atTop
  结论: {α : 类型}
  证明: by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x => ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

Depends on / 依赖: Nat.ceil_mono.tendsto_atTop_atTop, Nat.ceil_natCast, ceil_mono, ceil_natCast, le_refl, tendsto_atTop_atTop
-/
lemma tendsto_nat_ceil_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x => ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

/--
lemma `tendsto_nat_floor_mul_atTop` / 引理 `tendsto_nat_floor_mul_atTop`

English:
lemma tendsto_nat_floor_mul_atTop
  statement: {α : Type _}
  proof: Tendsto.comp tendsto_nat_floor_atTop
 Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

中文:
引理 tendsto_nat_floor_mul_atTop
  结论: {α : Type _}
  证明: Tendsto.comp tendsto_nat_floor_atTop
 Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

Depends on / 依赖: IsFibered, IsFibered.comp, Tendsto, Tendsto.comp, Tendsto.const_mul_atTop, const_mul_atTop, tendsto_natCast_atTop_atTop, tendsto_nat_floor_atTop
-/
lemma tendsto_nat_floor_mul_atTop {α : Type _}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α]
    [Archimedean α] (a : α) (ha : 0 < a) : Tendsto (fun (x : Nat) => ⌊a * x⌋₊) atTop atTop :=
  Tendsto.comp tendsto_nat_floor_atTop
 Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

variable {R : Type*} [TopologicalSpace R] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

/--
theorem `tendsto_nat_floor_mul_div_atTop` / 定理 `tendsto_nat_floor_mul_div_atTop`

English:
theorem tendsto_nat_floor_mul_div_atTop
  given: {a : R} (ha : 0 <= a)
  proof: by
  have A : Tendsto (fun x : R => a - x⁻¹) atTop (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    simp only [le_div_iff₀ (zero_lt_one.t

中文:
定理 tendsto_nat_floor_mul_div_atTop
  条件: {a : R} (ha : 0 <= a)
  证明: by
  have A : Tendsto (fun x : R => a - x⁻¹) atTop (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    simp only [le_div_iff₀ (zero_lt_one.t

Depends on / 依赖: Nat.lt_floor_add_one, Tendsto, _root_, _root_.sub_mul, eventually_atTop, lt_floor_add_one, sub_mul, sub_zero, tendsto_const_nhds, tendsto_const_nhds.sub, tendsto_inv_atTop_zero, tendsto_of_tendsto_of_tendsto_of_le_of_le, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 <= a) :
    Tendsto (fun x => (⌊a * x⌋₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R => a - x⁻¹) atTop (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    simp only [le_div_iff₀ (zero_lt_one.trans_le hx), _root_.sub_mul,
      inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne']
    have := Nat.lt_floor_add_one (a * x)
    linarith
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    rw [div_le_iff₀ (zero_lt_one.trans_le hx)]
    simp [Nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))]

/--
theorem `tendsto_nat_floor_div_atTop` / 定理 `tendsto_nat_floor_div_atTop`

English:
theorem tendsto_nat_floor_div_atTop
  statement: Tendsto (fun x => (⌊x⌋₊ : R) / x) atTop (𝓝 1)
  proof: by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)

中文:
定理 tendsto_nat_floor_div_atTop
  结论: Tendsto (fun x => (⌊x⌋₊ : R) / x) atTop (𝓝 1)
  证明: by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)

Depends on / 依赖: tendsto_nat_floor_mul_div_atTop, zero_le_one
-/
theorem tendsto_nat_floor_div_atTop : Tendsto (fun x => (⌊x⌋₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)

/--
theorem `tendsto_nat_ceil_mul_div_atTop` / 定理 `tendsto_nat_ceil_mul_div_atTop`

English:
theorem tendsto_nat_ceil_mul_div_atTop
  given: {a : R} (ha : 0 <= a)
  proof: by
  have A : Tendsto (fun x : R => a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le

中文:
定理 tendsto_nat_ceil_mul_div_atTop
  条件: {a : R} (ha : 0 <= a)
  证明: by
  have A : Tendsto (fun x : R => a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le

Depends on / 依赖: Nat.ceil_lt_add_one, Nat.le_ceil, Tendsto, add_zero, ceil_lt_add_one, eventually_atTop, le_ceil, mul_nonneg, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_inv_atTop_zero, tendsto_of_tendsto_of_tendsto_of_le_of_le, trans_le, zero_le_one, zero_le_one.t, zero_lt_one, zero_lt_one.trans_le
-/
theorem tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 <= a) :
    Tendsto (fun x => (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R => a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
  · refine eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    simp [div_le_iff₀ (zero_lt_one.trans_le hx), inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne',
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, add_mul]

/--
theorem `tendsto_nat_ceil_div_atTop` / 定理 `tendsto_nat_ceil_div_atTop`

English:
theorem tendsto_nat_ceil_div_atTop
  statement: Tendsto (fun x => (⌈x⌉₊ : R) / x) atTop (𝓝 1)
  proof: by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)

中文:
定理 tendsto_nat_ceil_div_atTop
  结论: Tendsto (fun x => (⌈x⌉₊ : R) / x) atTop (𝓝 1)
  证明: by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)

Depends on / 依赖: tendsto_nat_ceil_mul_div_atTop, zero_le_one
-/
theorem tendsto_nat_ceil_div_atTop : Tendsto (fun x => (⌈x⌉₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)

/--
lemma `Nat.tendsto_div_const_atTop` / 引理 `Nat.tendsto_div_const_atTop`

English:
lemma Nat.tendsto_div_const_atTop
  given: {n : Nat} (hn : n != 0)
  statement: Tendsto (· / n) atTop atTop
  proof: by
  rw [Tendsto]; rw [map_div_atTop_eq_nat n hn.bot_lt]

中文:
引理 Nat.tendsto_div_const_atTop
  条件: {n : 自然数} (hn : n != 0)
  结论: Tendsto (· / n) atTop atTop
  证明: by
  rw [Tendsto]; rw [map_div_atTop_eq_nat n hn.bot_lt]

Depends on / 依赖: Tendsto, bot_lt, hn.bot_lt, map_div_atTop_eq_nat
-/
lemma Nat.tendsto_div_const_atTop {n : Nat} (hn : n != 0) : Tendsto (· / n) atTop atTop := by
  rw [Tendsto]; rw [map_div_atTop_eq_nat n hn.bot_lt]

end
