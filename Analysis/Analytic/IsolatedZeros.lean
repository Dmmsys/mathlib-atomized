/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.Perfect

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is useful
in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.

## Applications

* Vanishing of products of analytic functions, `eq_zero_or_eq_zero_of_smul_eq_zero`: If `f, g` are
  analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0` on `U`, then either
  `f = 0` on `U` or `g = 0` on `U`.
* Preimages of codiscrete sets, `AnalyticOnNhd.preimage_mem_codiscreteWithin`: if `f` is analytic
  on a neighbourhood of `U` and not locally constant, then the preimage of any subset codiscrete
  within `f '' U` is codiscrete within `U`.
-/

public section

open Filter Function Module Nat FormalMultilinearSeries EMetric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 -> E} {n : Nat} {z z₀ : 𝕜}

namespace HasSum

variable {a : Nat -> E}

/--
theorem `hasSum_at_zero` / 定理 `hasSum_at_zero`

English:
theorem hasSum_at_zero
  given: (a : Nat -> E)
  statement: HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0)
  proof: by
  convert! hasSum_single (α := E) 0 fun b h => _ <;> simp [*]

中文:
定理 hasSum_at_zero
  条件: (a : 自然数 -> E)
  结论: HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0)
  证明: by
  convert! hasSum_single (α := E) 0 fun b h => _ <;> simp [*]

Depends on / 依赖: convert, hasSum_single
-/
theorem hasSum_at_zero (a : Nat -> E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert! hasSum_single (α := E) 0 fun b h => _ <;> simp [*]

/--
theorem `exists_hasSum_smul_of_apply_eq_zero` / 定理 `exists_hasSum_smul_of_apply_eq_zero`

English:
theorem exists_hasSum_smul_of_apply_eq_zero
  statement: (hs : HasSum (fun m => z ^ m • a m) s)
  proof: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i in Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert! h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

中文:
定理 存在_hasSum_smul_of_apply_eq_zero
  结论: (hs : HasSum (fun m => z ^ m • a m) s)
  证明: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i in Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert! h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

Depends on / 依赖: Finset, Finset.mem_range.mp, Finset.range, Finset.sum_eq_zero, HasSum, eq_zero_or_pos, hasSum_at_zero, hasSum_nat_, hn.ne, hs.unique, match_scalars, mem_range, n.eq_zero_or_pos, sum_eq_zero, unique
-/
theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : forall k < n, a k = 0) : exists t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i in Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert! h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

end HasSum

namespace HasFPowerSeriesAt

/--
theorem `has_fpower_series_dslope_fslope` / 定理 `has_fpower_series_dslope_fslope`

English:
theorem has_fpower_series_dslope_fslope
  given: (hp : HasFPowerSeriesAt f p z₀)
  proof: by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert! hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : forall n : Nat, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

中文:
定理 has_fpower_series_dslope_fslope
  条件: (hp : HasFPowerSeriesAt f p z₀)
  证明: by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert! hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : forall n : Nat, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

Depends on / 依赖: HasSum, _root_, _root_.pow_succ, coeff_fslope, coeff_zero, convert, dslope, hasFPowerSeriesAt_iff, hasSum_single, hp.coeff_zero, hp.deriv, hp.mono, intros, p.coeff, pow_succ, smul_smul
-/
theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert! hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : forall n : Nat, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

/--
theorem `has_fpower_series_iterate_dslope_fslope` / 定理 `has_fpower_series_iterate_dslope_fslope`

English:
theorem has_fpower_series_iterate_dslope_fslope
  given: (n : Nat) (hp : HasFPowerSeriesAt f p z₀)
  proof: by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

中文:
定理 has_fpower_series_iterate_dslope_fslope
  条件: (n : 自然数) (hp : HasFPowerSeriesAt f p z₀)
  证明: by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

Depends on / 依赖: generalizing, has_fpower_series_dslope_fslope
-/
theorem has_fpower_series_iterate_dslope_fslope (n : Nat) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

/--
theorem `iterate_dslope_fslope_ne_zero` / 定理 `iterate_dslope_fslope_ne_zero`

English:
theorem iterate_dslope_fslope_ne_zero
  given: (hp : HasFPowerSeriesAt f p z₀) (h : p != 0)
  proof: by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h

中文:
定理 iterate_dslope_fslope_ne_zero
  条件: (hp : HasFPowerSeriesAt f p z₀) (h : p != 0)
  证明: by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h

Depends on / 依赖: apply_order_ne_zero, coeff_eq_zero, coeff_zero, has_fpower_series_iterate_dslope_fslope, p.order
-/
theorem iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p != 0) :
    (swap dslope z₀)^[p.order] f z₀ != 0 := by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h

/--
theorem `eq_pow_order_mul_iterate_dslope` / 定理 `eq_pow_order_mul_iterate_dslope`

English:
theorem eq_pow_order_mul_iterate_dslope
  given: (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜)
  proof: by
  refine (pow_sub_smul_iterate_dslope_of_zero _ (fun k hk => ?_) z).symm
  rw [← (has_fpower_series_iterate_dslope_fslope k hp).coeff_zero 1]; rw [← coeff]; rw [coeff_iterate_fslope]; rw [zero_add]; rw [coeff]; rw [p.apply_eq_zero_of_lt_order hk]; rw [_root_.zero_apply]

中文:
定理 eq_pow_order_mul_iterate_dslope
  条件: (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜)
  证明: by
  refine (pow_sub_smul_iterate_dslope_of_zero _ (fun k hk => ?_) z).symm
  rw [← (has_fpower_series_iterate_dslope_fslope k hp).coeff_zero 1]; rw [← coeff]; rw [coeff_iterate_fslope]; rw [zero_add]; rw [coeff]; rw [p.apply_eq_zero_of_lt_order hk]; rw [_root_.zero_apply]

Depends on / 依赖: _root_, _root_.zero_apply, apply_eq_zero_of_lt_order, coeff_iterate_fslope, coeff_zero, has_fpower_series_iterate_dslope_fslope, p.apply_eq_zero_of_lt_order, pow_sub_smul_iterate_dslope_of_zero, zero_add, zero_apply
-/
theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜) :
    f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  refine (pow_sub_smul_iterate_dslope_of_zero _ (fun k hk => ?_) z).symm
  rw [← (has_fpower_series_iterate_dslope_fslope k hp).coeff_zero 1]; rw [← coeff]; rw [coeff_iterate_fslope]; rw [zero_add]; rw [coeff]; rw [p.apply_eq_zero_of_lt_order hk]; rw [_root_.zero_apply]

/--
theorem `locally_ne_zero` / 定理 `locally_ne_zero`

English:
theorem locally_ne_zero
  given: (hp : HasFPowerSeriesAt f p z₀) (h : p != 0)
  statement: forallᶠ z in 𝓝[!=] z₀, f z != 0
  proof: by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [h3] with z e1 e2
  simpa [eq_pow_order_mul_iterate_dslope hp, e1, e2] using pow_ne_zero p.order (sub_ne_zero.mpr e2)

中文:
定理 locally_ne_zero
  条件: (hp : HasFPowerSeriesAt f p z₀) (h : p != 0)
  结论: 对任意ᶠ z in 𝓝[!=] z₀, f z != 0
  证明: by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [h3] with z e1 e2
  simpa [eq_pow_order_mul_iterate_dslope hp, e1, e2] using pow_ne_zero p.order (sub_ne_zero.mpr e2)

Depends on / 依赖: continuousAt, eq_pow_order_mul_iterate_dslope, eventually_ne, eventually_nhdsWithin_iff, filter_upwards, h2.eventually_ne, has_fpower_series_iterate_dslope_fslope, iterate_dslope_fslope_ne_zero, p.order, pow_ne_zero, sub_ne_zero, sub_ne_zero.mpr
-/
theorem locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p != 0) : forallᶠ z in 𝓝[!=] z₀, f z != 0 := by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [h3] with z e1 e2
  simpa [eq_pow_order_mul_iterate_dslope hp, e1, e2] using pow_ne_zero p.order (sub_ne_zero.mpr e2)

/--
theorem `locally_zero_iff` / 定理 `locally_zero_iff`

English:
theorem locally_zero_iff
  given: (hp : HasFPowerSeriesAt f p z₀)
  statement: (forallᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0
  proof: ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

中文:
定理 locally_zero_iff
  条件: (hp : HasFPowerSeriesAt f p z₀)
  结论: (对任意ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0
  证明: ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

Depends on / 依赖: eq_zero_of_eventually, eventually_eq_zero, hp.eq_zero_of_eventually
-/
theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

end HasFPowerSeriesAt

namespace AnalyticAt

/--
theorem `eventually_eq_zero_or_eventually_ne_zero` / 定理 `eventually_eq_zero_or_eventually_ne_zero`

English:
theorem eventually_eq_zero_or_eventually_ne_zero
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)

中文:
定理 eventually_eq_zero_or_eventually_ne_zero
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)

Depends on / 依赖: HasFPowerSeriesAt, HasFPowerSeriesAt.eventually_eq_zero, Or.inl, Or.inr, eventually_eq_zero, hp.locally_ne_zero, locally_ne_zero
-/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (forallᶠ z in 𝓝 z₀, f z = 0) ∨ forallᶠ z in 𝓝[!=] z₀, f z != 0 := by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)

/--
theorem `eventually_eq_or_eventually_ne` / 定理 `eventually_eq_or_eventually_ne`

English:
theorem eventually_eq_or_eventually_ne
  given: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  proof: by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

中文:
定理 eventually_eq_or_eventually_ne
  条件: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  证明: by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

Depends on / 依赖: eventually_eq_zero_or_eventually_ne_zero, hf.sub, sub_eq_zero
-/
theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (forallᶠ z in 𝓝 z₀, f z = g z) ∨ forallᶠ z in 𝓝[!=] z₀, f z != g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

/--
theorem `frequently_zero_iff_eventually_zero` / 定理 `frequently_zero_iff_eventually_zero`

English:
theorem frequently_zero_iff_eventually_zero
  given: {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w)
  proof: ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩

中文:
定理 frequently_zero_iff_eventually_zero
  条件: {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w)
  证明: ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩

Depends on / 依赖: eventually_eq_zero_or_eventually_ne_zero, filter_mono, frequently, h.filter_mono, hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, nhdsWithin_le_nhds, resolve_right
-/
theorem frequently_zero_iff_eventually_zero {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (existsᶠ z in 𝓝[!=] w, f z = 0) ↔ forallᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩

/--
theorem `frequently_eq_iff_eventually_eq` / 定理 `frequently_eq_iff_eventually_eq`

English:
theorem frequently_eq_iff_eventually_eq
  given: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  proof: by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

中文:
定理 frequently_eq_iff_eventually_eq
  条件: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  证明: by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

Depends on / 依赖: frequently_zero_iff_eventually_zero, hf.sub, sub_eq_zero
-/
theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (existsᶠ z in 𝓝[!=] z₀, f z = g z) ↔ forallᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

/--
lemma `unique_eventuallyEq_zpow_smul_nonzero` / 引理 `unique_eventuallyEq_zpow_smul_nonzero`

English:
lemma unique_eventuallyEq_zpow_smul_nonzero
  statement: {m n : Int}
  proof: by
  wlog! h_le : n <= m generalizing m n
  · exact ((this hn hm) h_le.le).symm
  let ⟨g, hg_an, _, hg_eq⟩ := hm
  let ⟨j, hj_an, hj_ne, hj_eq⟩ := hn
  contrapose! hj_ne
  have : existsᶠ z in 𝓝[!=] z₀, j z = (z - z₀) ^ (m - n) • g z := by
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq hj_eq ⊢
    filter_upwards [hg_eq, hj_eq] with z hfz hfz' hz
    rw [← add_sub_cancel_left n m]; rw [add_sub_assoc]; rw [zpow_add₀ <| sub_ne_zero.mpr hz]; rw [mul_smul]; rw [hfz' hz]; rw [smul_right_inj zpow_ne_zero _ sub_ne_zero.mpr hz] at hfz
    exact hfz hz
  rw [frequently_eq_iff_eventually_eq hj_an] at this
  · rw [EventuallyEq.eq_of_nhds this, sub_self, zero_zpow _ (sub_ne_zero.mpr hj_ne), zero_smul]
  conv => enter [2, z, 1]; rw [← Int.toNat_sub_of_le h_le, zpow_natCast]
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an

中文:
引理 unique_eventuallyEq_zpow_smul_nonzero
  结论: {m n : 整数}
  证明: by
  wlog! h_le : n <= m generalizing m n
  · exact ((this hn hm) h_le.le).symm
  let ⟨g, hg_an, _, hg_eq⟩ := hm
  let ⟨j, hj_an, hj_ne, hj_eq⟩ := hn
  contrapose! hj_ne
  have : existsᶠ z in 𝓝[!=] z₀, j z = (z - z₀) ^ (m - n) • g z := by
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq hj_eq ⊢
    filter_upwards [hg_eq, hj_eq] with z hfz hfz' hz
    rw [← add_sub_cancel_left n m]; rw [add_sub_assoc]; rw [zpow_add₀ <| sub_ne_zero.mpr hz]; rw [mul_smul]; rw [hfz' hz]; rw [smul_right_inj zpow_ne_zero _ sub_ne_zero.mpr hz] at hfz
    exact hfz hz
  rw [frequently_eq_iff_eventually_eq hj_an] at this
  · rw [EventuallyEq.eq_of_nhds this, sub_self, zero_zpow _ (sub_ne_zero.mpr hj_ne), zero_smul]
  conv => enter [2, z, 1]; rw [← Int.toNat_sub_of_le h_le, zpow_natCast]
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an

Depends on / 依赖: Eventually, Filter, Filter.Eventually.frequently, add_sub_assoc, add_sub_cancel_left, contrapose, eventually_nhdsWithin_iff, filter_upwards, frequently, generalizing, h_le, h_le.le, hg_an, hg_eq, hj_an, hj_eq, hj_ne, mul_smul, smul_right_inj, sub_ne_zero
-/
lemma unique_eventuallyEq_zpow_smul_nonzero {m n : Int}
    (hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[!=] z₀, f z = (z - z₀) ^ m • g z)
    (hn : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[!=] z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  wlog! h_le : n <= m generalizing m n
  · exact ((this hn hm) h_le.le).symm
  let ⟨g, hg_an, _, hg_eq⟩ := hm
  let ⟨j, hj_an, hj_ne, hj_eq⟩ := hn
  contrapose! hj_ne
  have : existsᶠ z in 𝓝[!=] z₀, j z = (z - z₀) ^ (m - n) • g z := by
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq hj_eq ⊢
    filter_upwards [hg_eq, hj_eq] with z hfz hfz' hz
    rw [← add_sub_cancel_left n m]; rw [add_sub_assoc]; rw [zpow_add₀ <| sub_ne_zero.mpr hz]; rw [mul_smul]; rw [hfz' hz]; rw [smul_right_inj zpow_ne_zero _ sub_ne_zero.mpr hz] at hfz
    exact hfz hz
  rw [frequently_eq_iff_eventually_eq hj_an] at this
  · rw [EventuallyEq.eq_of_nhds this, sub_self, zero_zpow _ (sub_ne_zero.mpr hj_ne), zero_smul]
  conv => enter [2, z, 1]; rw [← Int.toNat_sub_of_le h_le, zpow_natCast]
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an

/--
lemma `unique_eventuallyEq_pow_smul_nonzero` / 引理 `unique_eventuallyEq_pow_smul_nonzero`

English:
lemma unique_eventuallyEq_pow_smul_nonzero
  statement: {m n : Nat}
  proof: by
  simp_rw [← zpow_natCast] at hm hn
exact Int.ofNat_inj.mp unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)

中文:
引理 unique_eventuallyEq_pow_smul_nonzero
  结论: {m n : 自然数}
  证明: by
  simp_rw [← zpow_natCast] at hm hn
exact Int.ofNat_inj.mp unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)

Depends on / 依赖: Int.ofNat_inj.mp, filter_mono, nhdsWithin_le_nhds, ofNat_inj, simp_rw, unique_eventuallyEq_zpow_smul_nonzero, zpow_natCast
-/
lemma unique_eventuallyEq_pow_smul_nonzero {m n : Nat}
    (hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z)
    (hn : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  simp_rw [← zpow_natCast] at hm hn
exact Int.ofNat_inj.mp unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)

/--
theorem `exists_eventuallyEq_pow_smul_nonzero_iff` / 定理 `exists_eventuallyEq_pow_smul_nonzero_iff`

English:
theorem exists_eventuallyEq_pow_smul_nonzero_iff
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      .of_forall hp.eq_pow_order_mul_iterate_dslope⟩

中文:
定理 存在_eventuallyEq_pow_smul_nonzero_iff
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      .of_forall hp.eq_pow_order_mul_iterate_dslope⟩

Depends on / 依赖: AnalyticAt, AnalyticAt.frequently_eq_iff_eventually_eq, EventuallyEq, EventuallyEq.eq_of_nhds, analyticAt_const, contrapose, eq_comm, eq_of_nhds, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, filter_upwards, frequently, frequently_eq_iff_eventually_eq, has_fpower_series_iterate_dslope_fslope, hf_eq, hf_ne, hg_an, hg_eq, hg_ne, hp.has_fpower_series_iterate_dslope_fslope
-/
theorem exists_eventuallyEq_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) :
    (exists (n : Nat), exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧
    forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) ↔ (¬forallᶠ z in 𝓝 z₀, f z = 0) := by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      .of_forall hp.eq_pow_order_mul_iterate_dslope⟩

end AnalyticAt

namespace AnalyticOnNhd

variable {U : Set 𝕜}

/--
theorem `eqOn_zero_of_preconnected_of_frequently_eq_zero` / 定理 `eqOn_zero_of_preconnected_of_frequently_eq_zero`

English:
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero
  statement: (hf : AnalyticOnNhd 𝕜 f U)
  proof: hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

中文:
定理 eqOn_zero_of_preconnected_of_frequently_eq_zero
  结论: (hf : AnalyticOnNhd 𝕜 f U)
  证明: hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

Depends on / 依赖: eqOn_zero_of_preconnected_of_eventuallyEq_zero, frequently_zero_iff_eventually_zero, hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
-/
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] z₀, f z = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

/--
theorem `eqOn_zero_or_eventually_ne_zero_of_preconnected` / 定理 `eqOn_zero_or_eventually_ne_zero_of_preconnected`

English:
theorem eqOn_zero_or_eventually_ne_zero_of_preconnected
  statement: (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  simp only [or_iff_not_imp_right, ne_eq, eventually_iff, mem_codiscreteWithin,
    disjoint_principal_right, not_forall]
  rintro ⟨x, hx, hx2⟩
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hx fun nh => hx2 ?_
  filter_upwards [nh] with a ha
  simp_all

中文:
定理 eqOn_zero_or_eventually_ne_zero_of_preconnected
  结论: (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  simp only [or_iff_not_imp_right, ne_eq, eventually_iff, mem_codiscreteWithin,
    disjoint_principal_right, not_forall]
  rintro ⟨x, hx, hx2⟩
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hx fun nh => hx2 ?_
  filter_upwards [nh] with a ha
  simp_all

Depends on / 依赖: disjoint_principal_right, eqOn_zero_of_preconnected_of_frequently_eq_zero, eventually_iff, filter_upwards, hf.eqOn_zero_of_preconnected_of_frequently_eq_zero, mem_codiscreteWithin, ne_eq, not_forall, or_iff_not_imp_right
-/
theorem eqOn_zero_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) : EqOn f 0 U ∨ forallᶠ x in codiscreteWithin U, f x != 0 := by
  simp only [or_iff_not_imp_right, ne_eq, eventually_iff, mem_codiscreteWithin,
    disjoint_principal_right, not_forall]
  rintro ⟨x, hx, hx2⟩
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hx fun nh => hx2 ?_
  filter_upwards [nh] with a ha
  simp_all

/--
theorem `eqOn_zero_of_preconnected_of_mem_closure` / 定理 `eqOn_zero_of_preconnected_of_mem_closure`

English:
theorem eqOn_zero_of_preconnected_of_mem_closure
  statement: (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
  proof: hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

中文:
定理 eqOn_zero_of_preconnected_of_mem_closure
  结论: (hf : AnalyticOnNhd 𝕜 f U) (hU : 是预连通 U)
  证明: hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

Depends on / 依赖: eqOn_zero_of_preconnected_of_frequently_eq_zero, hf.eqOn_zero_of_preconnected_of_frequently_eq_zero, mem_closure_ne_iff_frequently_within, mem_closure_ne_iff_frequently_within.mp
-/
theorem eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ in U) (hfz₀ : z₀ in closure ({z | f z = 0} \ {z₀})) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

/--
theorem `eqOn_of_preconnected_of_frequently_eq` / 定理 `eqOn_of_preconnected_of_frequently_eq`

English:
theorem eqOn_of_preconnected_of_frequently_eq
  statement: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  proof: by
  have hfg' : existsᶠ z in 𝓝[!=] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

中文:
定理 eqOn_of_preconnected_of_frequently_eq
  结论: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  证明: by
  have hfg' : existsᶠ z in 𝓝[!=] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

Depends on / 依赖: Pi.sub_apply, eqOn_zero_of_preconnected_of_frequently_eq_zero, hf.sub, hfg.mono, sub_apply, sub_eq_zero, sub_self
-/
theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ in U) (hfg : existsᶠ z in 𝓝[!=] z₀, f z = g z) : EqOn f g U := by
  have hfg' : existsᶠ z in 𝓝[!=] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

/--
theorem `eqOn_or_eventually_ne_of_preconnected` / 定理 `eqOn_or_eventually_ne_of_preconnected`

English:
theorem eqOn_or_eventually_ne_of_preconnected
  statement: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  proof: (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx => eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])

中文:
定理 eqOn_or_eventually_ne_of_preconnected
  结论: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  证明: (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx => eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])

Depends on / 依赖: Pi.sub_apply, eqOn_zero_or_eventually_ne_zero_of_preconnected, eq_of_sub_eq_zero, hf.sub, imp_self, ne_eq, sub_apply, sub_eq_zero
-/
theorem eqOn_or_eventually_ne_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) : EqOn f g U ∨ forallᶠ x in codiscreteWithin U, f x != g x :=
  (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx => eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])

/--
theorem `eqOn_of_preconnected_of_mem_closure` / 定理 `eqOn_of_preconnected_of_mem_closure`

English:
theorem eqOn_of_preconnected_of_mem_closure
  statement: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  proof: hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

中文:
定理 eqOn_of_preconnected_of_mem_closure
  结论: (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
  证明: hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

Depends on / 依赖: eqOn_of_preconnected_of_frequently_eq, hf.eqOn_of_preconnected_of_frequently_eq, mem_closure_ne_iff_frequently_within, mem_closure_ne_iff_frequently_within.mp
-/
theorem eqOn_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ in U) (hfg : z₀ in closure ({z | f z = g z} \ {z₀})) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

/--
theorem `eq_of_frequently_eq` / 定理 `eq_of_frequently_eq`

English:
theorem eq_of_frequently_eq
  statement: [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
  proof: funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

中文:
定理 eq_of_frequently_eq
  结论: [连通空间 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
  证明: funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

Depends on / 依赖: eqOn_of_preconnected_of_frequently_eq, isPreconnected_univ, mem_univ
-/
theorem eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) (hfg : existsᶠ z in 𝓝[!=] z₀, f z = g z) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

section Mul
/-!
### Vanishing of products of analytic functions
-/

variable {A : Type*} [NormedRing A] [IsDomain A] [NormedAlgebra 𝕜 A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Module A B]

/--
lemma `eq_zero_or_eq_zero_of_smul_eq_zero` / 引理 `eq_zero_or_eq_zero_of_smul_eq_zero`

English:
lemma eq_zero_or_eq_zero_of_smul_eq_zero
  statement: [IsTorsionFree A B]
  proof: by
  -- We want to apply `IsPreconnected.preperfect_of_nontrivial` which requires `U` to have at least
  -- two elements. So we need to dispose of the cases `#U = 0` and `#U = 1` first.
  by_cases hU' : U = ∅
  · simp [hU']
  obtain ⟨z, hz⟩ : exists z, z in U := nonempty_iff_ne_empty.mpr hU'
  by_cases hU'' : U = {z}
  · simpa [hU''] using hfg z hz
  apply (nontrivial_iff_ne_singleton hz).mpr at hU''
  -- Now connectedness implies that `z` is an accumulation point of `U`, so at least one of
  -- `f` and `g` must vanish frequently in a neighbourhood of `z`.
  have : existsᶠ w in 𝓝[!=] z, w in U :=
frequently_mem_iff_neBot.mpr hU.preperfect_of_nontrivial hU'' z hz
  have : existsᶠ w in 𝓝[!=] z, f w = 0 ∨ g w = 0 :=
this.mp by filter_upwards with w hw using smul_eq_zero.mp (hfg w hw)
  cases frequently_or_distrib.mp this with
| inl h => exact Or.inl hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
| inr h => exact Or.inr hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h

中文:
引理 eq_zero_or_eq_zero_of_smul_eq_zero
  结论: [是无挠 A B]
  证明: by
  -- We want to apply `IsPreconnected.preperfect_of_nontrivial` which requires `U` to have at least
  -- two elements. So we need to dispose of the cases `#U = 0` and `#U = 1` first.
  by_cases hU' : U = ∅
  · simp [hU']
  obtain ⟨z, hz⟩ : exists z, z in U := nonempty_iff_ne_empty.mpr hU'
  by_cases hU'' : U = {z}
  · simpa [hU''] using hfg z hz
  apply (nontrivial_iff_ne_singleton hz).mpr at hU''
  -- Now connectedness implies that `z` is an accumulation point of `U`, so at least one of
  -- `f` and `g` must vanish frequently in a neighbourhood of `z`.
  have : existsᶠ w in 𝓝[!=] z, w in U :=
frequently_mem_iff_neBot.mpr hU.preperfect_of_nontrivial hU'' z hz
  have : existsᶠ w in 𝓝[!=] z, f w = 0 ∨ g w = 0 :=
this.mp by filter_upwards with w hw using smul_eq_zero.mp (hfg w hw)
  cases frequently_or_distrib.mp this with
| inl h => exact Or.inl hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
| inr h => exact Or.inr hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
-/
lemma eq_zero_or_eq_zero_of_smul_eq_zero [IsTorsionFree A B]
    {f : 𝕜 -> A} {g : 𝕜 -> B} (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hfg : forall z in U, f z • g z = 0) (hU : IsPreconnected U) :
    (forall z in U, f z = 0) ∨ (forall z in U, g z = 0) := by
  -- We want to apply `IsPreconnected.preperfect_of_nontrivial` which requires `U` to have at least
  -- two elements. So we need to dispose of the cases `#U = 0` and `#U = 1` first.
  by_cases hU' : U = ∅
  · simp [hU']
  obtain ⟨z, hz⟩ : exists z, z in U := nonempty_iff_ne_empty.mpr hU'
  by_cases hU'' : U = {z}
  · simpa [hU''] using hfg z hz
  apply (nontrivial_iff_ne_singleton hz).mpr at hU''
  -- Now connectedness implies that `z` is an accumulation point of `U`, so at least one of
  -- `f` and `g` must vanish frequently in a neighbourhood of `z`.
  have : existsᶠ w in 𝓝[!=] z, w in U :=
frequently_mem_iff_neBot.mpr hU.preperfect_of_nontrivial hU'' z hz
  have : existsᶠ w in 𝓝[!=] z, f w = 0 ∨ g w = 0 :=
this.mp by filter_upwards with w hw using smul_eq_zero.mp (hfg w hw)
  cases frequently_or_distrib.mp this with
| inl h => exact Or.inl hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
| inr h => exact Or.inr hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h

/--
lemma `eq_zero_or_eq_zero_of_mul_eq_zero` / 引理 `eq_zero_or_eq_zero_of_mul_eq_zero`

English:
lemma eq_zero_or_eq_zero_of_mul_eq_zero
  statement: {f g : 𝕜 -> A} (hf : AnalyticOnNhd 𝕜 f U)
  proof: eq_zero_or_eq_zero_of_smul_eq_zero hf hg hfg hU

中文:
引理 eq_zero_or_eq_zero_of_mul_eq_zero
  结论: {f g : 𝕜 -> A} (hf : AnalyticOnNhd 𝕜 f U)
  证明: eq_zero_or_eq_zero_of_smul_eq_zero hf hg hfg hU

Depends on / 依赖: eq_zero_or_eq_zero_of_smul_eq_zero
-/
lemma eq_zero_or_eq_zero_of_mul_eq_zero {f g : 𝕜 -> A} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hfg : forall z in U, f z * g z = 0) (hU : IsPreconnected U) :
    (forall z in U, f z = 0) ∨ (forall z in U, g z = 0) :=
  eq_zero_or_eq_zero_of_smul_eq_zero hf hg hfg hU

end Mul
end AnalyticOnNhd

/-!
### Preimages of codiscrete sets
-/

section PreimgCodiscrete

/--
theorem `AnalyticAt.preimage_of_nhdsNE` / 定理 `AnalyticAt.preimage_of_nhdsNE`

English:
theorem AnalyticAt.preimage_of_nhdsNE
  statement: {x : 𝕜} {f : 𝕜 -> E} {s : Set E} (hfx : AnalyticAt 𝕜 f x)
  proof: by
  have : forallᶠ (z : 𝕜) in 𝓝 x, f z in insert (f x) s := by
    filter_upwards [hfx.continuousAt.preimage_mem_nhds (insert_mem_nhds_iff.2 hs)]
    tauto
  contrapose h₂f with h
  rw [eventuallyConst_iff_exists_eventuallyEq]
  use f x
  rw [EventuallyEq]; rw [← hfx.frequently_eq_iff_eventually_eq analyticAt_const]
  apply ((frequently_imp_distrib_right.2 h).and_eventually
    (eventually_nhdsWithin_of_eventually_nhds this)).mono
  intro z ⟨h₁z, h₂z⟩
  rw [Set.mem_insert_iff] at h₂z
  tauto

中文:
定理 AnalyticAt.preimage_of_nhdsNE
  结论: {x : 𝕜} {f : 𝕜 -> E} {s : 集合 E} (hfx : AnalyticAt 𝕜 f x)
  证明: by
  have : forallᶠ (z : 𝕜) in 𝓝 x, f z in insert (f x) s := by
    filter_upwards [hfx.continuousAt.preimage_mem_nhds (insert_mem_nhds_iff.2 hs)]
    tauto
  contrapose h₂f with h
  rw [eventuallyConst_iff_exists_eventuallyEq]
  use f x
  rw [EventuallyEq]; rw [← hfx.frequently_eq_iff_eventually_eq analyticAt_const]
  apply ((frequently_imp_distrib_right.2 h).and_eventually
    (eventually_nhdsWithin_of_eventually_nhds this)).mono
  intro z ⟨h₁z, h₂z⟩
  rw [Set.mem_insert_iff] at h₂z
  tauto

Depends on / 依赖: EventuallyEq, Set.mem_insert_iff, analyticAt_const, and_eventually, continuousAt, contrapose, eventuallyConst_iff_exists_eventuallyEq, eventually_nhdsWithin_of_eventually_nhds, filter_upwards, frequently_eq_iff_eventually_eq, frequently_imp_distrib_right, hfx.continuousAt.preimage_mem_nhds, hfx.frequently_eq_iff_eventually_eq, insert, insert_mem_nhds_iff, mem_insert_iff, preimage_mem_nhds
-/
theorem AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f : 𝕜 -> E} {s : Set E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) (hs : s in 𝓝[!=] f x) :
    f ⁻¹' s in 𝓝[!=] x := by
  have : forallᶠ (z : 𝕜) in 𝓝 x, f z in insert (f x) s := by
    filter_upwards [hfx.continuousAt.preimage_mem_nhds (insert_mem_nhds_iff.2 hs)]
    tauto
  contrapose h₂f with h
  rw [eventuallyConst_iff_exists_eventuallyEq]
  use f x
  rw [EventuallyEq]; rw [← hfx.frequently_eq_iff_eventually_eq analyticAt_const]
  apply ((frequently_imp_distrib_right.2 h).and_eventually
    (eventually_nhdsWithin_of_eventually_nhds this)).mono
  intro z ⟨h₁z, h₂z⟩
  rw [Set.mem_insert_iff] at h₂z
  tauto

/--
theorem `AnalyticAt.map_nhdsNE` / 定理 `AnalyticAt.map_nhdsNE`

English:
theorem AnalyticAt.map_nhdsNE
  statement: {x : 𝕜} {f : 𝕜 -> E} (hfx : AnalyticAt 𝕜 f x)
  proof: fun _ hs => mem_map.1 (preimage_of_nhdsNE hfx h₂f hs)

中文:
定理 AnalyticAt.map_nhdsNE
  结论: {x : 𝕜} {f : 𝕜 -> E} (hfx : AnalyticAt 𝕜 f x)
  证明: fun _ hs => mem_map.1 (preimage_of_nhdsNE hfx h₂f hs)

Depends on / 依赖: mem_map, preimage_of_nhdsNE
-/
theorem AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 -> E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) :
    (𝓝[!=] x).map f <= (𝓝[!=] f x) := fun _ hs => mem_map.1 (preimage_of_nhdsNE hfx h₂f hs)

/--
theorem `AnalyticOnNhd.preimage_mem_codiscreteWithin` / 定理 `AnalyticOnNhd.preimage_mem_codiscreteWithin`

English:
theorem AnalyticOnNhd.preimage_mem_codiscreteWithin
  statement: {U : Set 𝕜} {s : Set E} {f : 𝕜 -> E}
  proof: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff] at *
  intro x hx
  apply mem_of_superset ((hfU x hx).preimage_of_nhdsNE (h₂f x hx) (hs (f x) (by tauto)))
  grind

中文:
定理 AnalyticOnNhd.preimage_mem_codiscreteWithin
  结论: {U : 集合 𝕜} {s : 集合 E} {f : 𝕜 -> E}
  证明: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff] at *
  intro x hx
  apply mem_of_superset ((hfU x hx).preimage_of_nhdsNE (h₂f x hx) (hs (f x) (by tauto)))
  grind

Depends on / 依赖: Set.compl_sdiff, compl_sdiff, disjoint_principal_right, mem_codiscreteWithin, mem_of_superset, preimage_of_nhdsNE, simp_rw
-/
theorem AnalyticOnNhd.preimage_mem_codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜 -> E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : forall x in U, ¬EventuallyConst f (𝓝 x))
    (hs : s in codiscreteWithin (f '' U)) :
    f ⁻¹' s in codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff] at *
  intro x hx
  apply mem_of_superset ((hfU x hx).preimage_of_nhdsNE (h₂f x hx) (hs (f x) (by tauto)))
  grind

/--
theorem `AnalyticOnNhd.map_codiscreteWithin` / 定理 `AnalyticOnNhd.map_codiscreteWithin`

English:
theorem AnalyticOnNhd.map_codiscreteWithin
  statement: {U : Set 𝕜} {f : 𝕜 -> E}
  proof: fun _ hs => mem_map.1 (preimage_mem_codiscreteWithin hfU h₂f hs)

中文:
定理 AnalyticOnNhd.map_codiscreteWithin
  结论: {U : 集合 𝕜} {f : 𝕜 -> E}
  证明: fun _ hs => mem_map.1 (preimage_mem_codiscreteWithin hfU h₂f hs)

Depends on / 依赖: mem_map, preimage_mem_codiscreteWithin
-/
theorem AnalyticOnNhd.map_codiscreteWithin {U : Set 𝕜} {f : 𝕜 -> E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : forall x in U, ¬EventuallyConst f (𝓝 x)) :
    map f (codiscreteWithin U) <= (codiscreteWithin (f '' U)) :=
  fun _ hs => mem_map.1 (preimage_mem_codiscreteWithin hfU h₂f hs)

end PreimgCodiscrete
