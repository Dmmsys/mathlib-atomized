/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Complex.Asymptotics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Complex and real exponential

In this file we prove continuity of `Complex.exp` and `Real.exp`. We also prove a few facts about
limits of `Real.exp` at infinity.

## Tags

exp
-/

@[expose] public section

noncomputable section

open Asymptotics Bornology Finset Filter Function Metric Set Topology

open scoped Nat

namespace Complex

variable {z y x : Real}

/--
theorem `exp_bound_sq` / 定理 `exp_bound_sq`

English:
theorem exp_bound_sq
  given: (x z : Complex) (hz : ‖z‖ <= 1)
  proof: calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by
      congr
      rw [exp_add]
      ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := norm_mul _ _
    _ <= ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_exp_sub_one_sub_id_le hz) (norm_nonneg _)

中文:
定理 exp_bound_sq
  条件: (x z : Complex) (hz : ‖z‖ <= 1)
  证明: calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by
      congr
      rw [exp_add]
      ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := norm_mul _ _
    _ <= ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_exp_sub_one_sub_id_le hz) (norm_nonneg _)

Depends on / 依赖: exp_add, mul_le_mul_of_nonneg_left, norm_exp_sub_one_sub_id_le, norm_mul, norm_nonneg
-/
theorem exp_bound_sq (x z : Complex) (hz : ‖z‖ <= 1) :
    ‖exp (x + z) - exp x - z • exp x‖ <= ‖exp x‖ * ‖z‖ ^ 2 :=
  calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by
      congr
      rw [exp_add]
      ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := norm_mul _ _
    _ <= ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_exp_sub_one_sub_id_le hz) (norm_nonneg _)

/--
theorem `locally_lipschitz_exp` / 定理 `locally_lipschitz_exp`

English:
theorem locally_lipschitz_exp
  statement: {r : Real} (hr_nonneg : 0 <= r) (hr_le : r <= 1) (x y : Complex)
  proof: by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 <= r * ‖y - x‖ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : forall z, ‖z‖ <= 1 -> ‖exp (x + z) - exp x‖ <= ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 := by
    intro z hz
    have 

中文:
定理 locally_lipschitz_exp
  结论: {r : 实数} (hr_nonneg : 0 <= r) (hr_le : r <= 1) (x y : Complex)
  证明: by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 <= r * ‖y - x‖ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : forall z, ‖z‖ <= 1 -> ‖exp (x + z) - exp x‖ <= ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 := by
    intro z hz
    have 

Depends on / 依赖: exp_bound_sq, h_sq, hr_nonneg, hy_eq, hyx.le, hyx_sq_le, le_rfl, mul_le_mul, norm_nonneg, norm_smul, norm_sub_norm_le, pow_two, sub_le_iff_le_add
-/
theorem locally_lipschitz_exp {r : Real} (hr_nonneg : 0 <= r) (hr_le : r <= 1) (x y : Complex)
    (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ <= (1 + r) * ‖exp x‖ * ‖y - x‖ := by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 <= r * ‖y - x‖ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : forall z, ‖z‖ <= 1 -> ‖exp (x + z) - exp x‖ <= ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 := by
    intro z hz
    have : ‖exp (x + z) - exp x - z • exp x‖ <= ‖exp x‖ * ‖z‖ ^ 2 := exp_bound_sq x z hz
    rw [← sub_le_iff_le_add']; rw [← norm_smul z]
    exact (norm_sub_norm_le _ _).trans this
  calc
    ‖exp y - exp x‖ = ‖exp (x + (y - x)) - exp x‖ := by nth_rw 1 [hy_eq]
    _ <= ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * ‖y - x‖ ^ 2 := h_sq (y - x) (hyx.le.trans hr_le)
    _ <= ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * (r * ‖y - x‖) := by grw [hyx_sq_le]
    _ = (1 + r) * ‖exp x‖ * ‖y - x‖ := by ring

-- Porting note: proof by term mode `locally_lipschitz_exp zero_le_one le_rfl x`
-- doesn't work because `‖y - x‖` and `dist y x` don't unify
@[continuity]
/--
theorem `continuous_exp` / 定理 `continuous_exp`

English:
theorem continuous_exp
  statement: Continuous exp
  proof: continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (fun y => by
        simpa [dist_eq_norm, one_add_one_eq_two] using locally_lipschitz_exp zero_le_one le_rfl x y)

中文:
定理 continuous_exp
  结论: Continuous exp
  证明: continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (fun y => by
        simpa [dist_eq_norm, one_add_one_eq_two] using locally_lipschitz_exp zero_le_one le_rfl x y)

Depends on / 依赖: continuousAt_of_locally_lipschitz, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, dist_eq_norm, le_rfl, locally_lipschitz_exp, one_add_one_eq_two, zero_le_one, zero_lt_one
-/
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (fun y => by
        simpa [dist_eq_norm, one_add_one_eq_two] using locally_lipschitz_exp zero_le_one le_rfl x y)

/--
theorem `continuousOn_exp` / 定理 `continuousOn_exp`

English:
theorem continuousOn_exp
  given: {s : Set Complex}
  statement: ContinuousOn exp s
  proof: continuous_exp.continuousOn

中文:
定理 continuousOn_exp
  条件: {s : Set Complex}
  结论: ContinuousOn exp s
  证明: continuous_exp.continuousOn

Depends on / 依赖: continuousOn, continuous_exp, continuous_exp.continuousOn
-/
theorem continuousOn_exp {s : Set Complex} : ContinuousOn exp s :=
  continuous_exp.continuousOn

/--
lemma `exp_sub_sum_range_isBigO_pow` / 引理 `exp_sub_sum_range_isBigO_pow`

English:
lemma exp_sub_sum_range_isBigO_pow
  given: (n : Nat)
  proof: by
  rcases eq_zero_or_pos n with rfl | hn
  · simpa using continuous_exp.continuousAt.norm.isBoundedUnder_le
  · refine .of_bound (n.succ / (n ! * n)) ?_
    rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    refine ⟨1, one_pos, fun x hx => ?_⟩
    convert! exp_bound hx.out.le hn using 

中文:
引理 exp_sub_sum_range_isBigO_pow
  条件: (n : 自然数)
  证明: by
  rcases eq_zero_or_pos n with rfl | hn
  · simpa using continuous_exp.continuousAt.norm.isBoundedUnder_le
  · refine .of_bound (n.succ / (n ! * n)) ?_
    rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    refine ⟨1, one_pos, fun x hx => ?_⟩
    convert! exp_bound hx.out.le hn using 

Depends on / 依赖: NormedAddGroup, NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff, continuousAt, continuous_exp, continuous_exp.continuousAt.norm.isBoundedUnder_le, convert, eq_zero_or_pos, eventually_iff, exp_bound, hx.out.le, isBoundedUnder_le, n.succ, nhds_zero_basis_norm_lt, of_bound, one_pos
-/
lemma exp_sub_sum_range_isBigO_pow (n : Nat) :
    (fun x => exp x - ∑ i in Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n) := by
  rcases eq_zero_or_pos n with rfl | hn
  · simpa using continuous_exp.continuousAt.norm.isBoundedUnder_le
  · refine .of_bound (n.succ / (n ! * n)) ?_
    rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    refine ⟨1, one_pos, fun x hx => ?_⟩
    convert! exp_bound hx.out.le hn using 1
    simp [field]

/--
lemma `exp_sub_sum_range_succ_isLittleO_pow` / 引理 `exp_sub_sum_range_succ_isLittleO_pow`

English:
lemma exp_sub_sum_range_succ_isLittleO_pow
  given: (n : Nat)
  proof: (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

中文:
引理 exp_sub_sum_range_succ_isLittleO_pow
  条件: (n : 自然数)
  证明: (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

Depends on / 依赖: exp_sub_sum_range_isBigO_pow, isLittleO_pow_pow, lt_succ_self, n.lt_succ_self, trans_isLittleO
-/
lemma exp_sub_sum_range_succ_isLittleO_pow (n : Nat) :
    (fun x => exp x - ∑ i in Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n) :=
(exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

end Complex

section ComplexContinuousExpComp

variable {α : Type*}

open Complex

/--
theorem `Filter.Tendsto.cexp` / 定理 `Filter.Tendsto.cexp`

English:
theorem Filter.Tendsto.cexp
  given: {l : Filter α} {f : α -> Complex} {z : Complex} (hf : Tendsto f l (𝓝 z))
  proof: (continuous_exp.tendsto _).comp hf

中文:
定理 Filter.Tendsto.cexp
  条件: {l : Filter α} {f : α -> Complex} {z : Complex} (hf : Tendsto f l (𝓝 z))
  证明: (continuous_exp.tendsto _).comp hf

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, tendsto
-/
theorem Filter.Tendsto.cexp {l : Filter α} {f : α -> Complex} {z : Complex} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf

variable [TopologicalSpace α] {f : α -> Complex} {s : Set α} {x : α}

nonrec
/--
theorem `ContinuousWithinAt.cexp` / 定理 `ContinuousWithinAt.cexp`

English:
theorem ContinuousWithinAt.cexp
  given: (h : ContinuousWithinAt f s x)
  proof: h.cexp

@[fun_prop]
nonrec

中文:
定理 ContinuousWithinAt.cexp
  条件: (h : ContinuousWithinAt f s x)
  证明: h.cexp

@[fun_prop]
nonrec

Depends on / 依赖: h.cexp
-/
theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp

@[fun_prop]
nonrec
/--
theorem `ContinuousAt.cexp` / 定理 `ContinuousAt.cexp`

English:
theorem ContinuousAt.cexp
  given: (h : ContinuousAt f x)
  statement: ContinuousAt (fun y => exp (f y)) x
  proof: h.cexp

@[fun_prop]

中文:
定理 ContinuousAt.cexp
  条件: (h : ContinuousAt f x)
  结论: ContinuousAt (fun y => exp (f y)) x
  证明: h.cexp

@[fun_prop]

Depends on / 依赖: h.cexp
-/
theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp

@[fun_prop]
/--
theorem `ContinuousOn.cexp` / 定理 `ContinuousOn.cexp`

English:
theorem ContinuousOn.cexp
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (fun y => exp (f y)) s
  proof: fun x hx => (h x hx).cexp

@[fun_prop]

中文:
定理 ContinuousOn.cexp
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (fun y => exp (f y)) s
  证明: fun x hx => (h x hx).cexp

@[fun_prop]
-/
theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).cexp

@[fun_prop]
/--
theorem `Continuous.cexp` / 定理 `Continuous.cexp`

English:
theorem Continuous.cexp
  given: (h : Continuous f)
  statement: Continuous fun y => exp (f y)
  proof: continuous_iff_continuousAt.2 fun _ => h.continuousAt.cexp

中文:
定理 Continuous.cexp
  条件: (h : Continuous f)
  结论: Continuous fun y => exp (f y)
  证明: continuous_iff_continuousAt.2 fun _ => h.continuousAt.cexp

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, h.continuousAt.cexp
-/
theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun _ => h.continuousAt.cexp

/--
lemma `UniformContinuousOn.cexp` / 引理 `UniformContinuousOn.cexp`

English:
lemma UniformContinuousOn.cexp
  given: (a : Real)
  statement: UniformContinuousOn exp {x : Complex | x.re <= a}
  proof: by
  have : Continuous (cexp - 1) := Continuous.sub (by fun_prop) continuous_one
  rw [Metric.uniformContinuousOn_iff]; rw [Metric.continuous_iff'] at *
  intro ε hε
  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
    sub_add_cancel] at this
  have ha : 0 < ε / (2 * R

中文:
引理 UniformContinuousOn.cexp
  条件: (a : 实数)
  结论: UniformContinuousOn exp {x : Complex | x.re <= a}
  证明: by
  have : Continuous (cexp - 1) := Continuous.sub (by fun_prop) continuous_one
  rw [Metric.uniformContinuousOn_iff]; rw [Metric.continuous_iff'] at *
  intro ε hε
  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
    sub_add_cancel] at this
  have ha : 0 < ε / (2 * R

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.ext_apply, ConcreteCategory.hom, ConcreteCategory.hom_ofHom, ConcreteCategory.id_apply, ConcreteCategory.ofHom, ConcreteCategory.ofHom_hom, Continuous, Continuous.sub, Metric, Metric.continuous_iff, Metric.eventually_nhds_iff, Metric.uniformContinuousOn_iff, Pi.one_apply, Pi.sub_apply, Real.exp, comp_apply
-/
lemma UniformContinuousOn.cexp (a : Real) : UniformContinuousOn exp {x : Complex | x.re <= a} := by
  have : Continuous (cexp - 1) := Continuous.sub (by fun_prop) continuous_one
  rw [Metric.uniformContinuousOn_iff]; rw [Metric.continuous_iff'] at *
  intro ε hε
  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
    sub_add_cancel] at this
  have ha : 0 < ε / (2 * Real.exp a) := by positivity
  have H := this 0 (ε / (2 * Real.exp a)) ha
  rw [Metric.eventually_nhds_iff] at H
  obtain ⟨δ, hδ⟩ := H
  refine ⟨δ, hδ.1, ?_⟩
  intro x _ y hy hxy
  have h3 := hδ.2 (y := x - y) (by simpa only [dist_eq_norm, sub_zero] using hxy)
  rw [dist_eq_norm]; rw [exp_zero] at *
  have : cexp x - cexp y = cexp y * (cexp (x - y) - 1) := by
    rw [mul_sub_one]; rw [← exp_add]
    ring_nf
  rw [this]; rw [mul_comm]
  have hya : ‖cexp y‖ <= Real.exp a := by simpa only [norm_exp, Real.exp_le_exp]
  simp only [gt_iff_lt, dist_zero_right, Set.mem_ofPred_eq, norm_mul, Complex.norm_exp] at *
  apply lt_of_le_of_lt (mul_le_mul h3.le hya (Real.exp_nonneg y.re) ha.le)
  simp [field]

end ComplexContinuousExpComp

namespace Real

@[continuity, fun_prop]
/--
theorem `continuous_exp` / 定理 `continuous_exp`

English:
theorem continuous_exp
  statement: Continuous exp
  proof: by
  unfold Real.exp; fun_prop

中文:
定理 continuous_exp
  结论: Continuous exp
  证明: by
  unfold Real.exp; fun_prop

Depends on / 依赖: Real.exp, fun_prop
-/
theorem continuous_exp : Continuous exp := by
  unfold Real.exp; fun_prop

/--
theorem `continuousOn_exp` / 定理 `continuousOn_exp`

English:
theorem continuousOn_exp
  given: {s : Set Real}
  statement: ContinuousOn exp s
  proof: by fun_prop

中文:
定理 continuousOn_exp
  条件: {s : Set 实数}
  结论: ContinuousOn exp s
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem continuousOn_exp {s : Set Real} : ContinuousOn exp s := by fun_prop

/--
lemma `exp_sub_sum_range_isBigO_pow` / 引理 `exp_sub_sum_range_isBigO_pow`

English:
lemma exp_sub_sum_range_isBigO_pow
  given: (n : Nat)
  proof: by
  have := (Complex.exp_sub_sum_range_isBigO_pow n).comp_tendsto
    (Complex.continuous_ofReal.tendsto' 0 0 rfl)
  simp only [Function.comp_def] at this
  norm_cast at this

中文:
引理 exp_sub_sum_range_isBigO_pow
  条件: (n : 自然数)
  证明: by
  have := (Complex.exp_sub_sum_range_isBigO_pow n).comp_tendsto
    (Complex.continuous_ofReal.tendsto' 0 0 rfl)
  simp only [Function.comp_def] at this
  norm_cast at this

Depends on / 依赖: Complex.continuous_ofReal.tendsto, Complex.exp_sub_sum_range_isBigO_pow, Function, Function.comp_def, comp_def, comp_tendsto, continuous_ofReal, exp_sub_sum_range_isBigO_pow, tendsto
-/
lemma exp_sub_sum_range_isBigO_pow (n : Nat) :
    (fun x => exp x - ∑ i in Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n) := by
  have := (Complex.exp_sub_sum_range_isBigO_pow n).comp_tendsto
    (Complex.continuous_ofReal.tendsto' 0 0 rfl)
  simp only [Function.comp_def] at this
  norm_cast at this

/--
lemma `exp_sub_sum_range_succ_isLittleO_pow` / 引理 `exp_sub_sum_range_succ_isLittleO_pow`

English:
lemma exp_sub_sum_range_succ_isLittleO_pow
  given: (n : Nat)
  proof: (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

中文:
引理 exp_sub_sum_range_succ_isLittleO_pow
  条件: (n : 自然数)
  证明: (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

Depends on / 依赖: exp_sub_sum_range_isBigO_pow, isLittleO_pow_pow, lt_succ_self, n.lt_succ_self, trans_isLittleO
-/
lemma exp_sub_sum_range_succ_isLittleO_pow (n : Nat) :
    (fun x => exp x - ∑ i in Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n) :=
(exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO isLittleO_pow_pow n.lt_succ_self

end Real

section RealContinuousExpComp

variable {α : Type*}

open Real

/--
theorem `Filter.Tendsto.rexp` / 定理 `Filter.Tendsto.rexp`

English:
theorem Filter.Tendsto.rexp
  given: {l : Filter α} {f : α -> Real} {z : Real} (hf : Tendsto f l (𝓝 z))
  proof: (continuous_exp.tendsto _).comp hf

中文:
定理 Filter.Tendsto.rexp
  条件: {l : Filter α} {f : α -> 实数} {z : 实数} (hf : Tendsto f l (𝓝 z))
  证明: (continuous_exp.tendsto _).comp hf

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, tendsto
-/
theorem Filter.Tendsto.rexp {l : Filter α} {f : α -> Real} {z : Real} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf

variable [TopologicalSpace α] {f : α -> Real} {s : Set α} {x : α}

nonrec
/--
theorem `ContinuousWithinAt.rexp` / 定理 `ContinuousWithinAt.rexp`

English:
theorem ContinuousWithinAt.rexp
  given: (h : ContinuousWithinAt f s x)
  proof: h.rexp

@[fun_prop]
nonrec

中文:
定理 ContinuousWithinAt.rexp
  条件: (h : ContinuousWithinAt f s x)
  证明: h.rexp

@[fun_prop]
nonrec

Depends on / 依赖: h.rexp
-/
theorem ContinuousWithinAt.rexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.rexp

@[fun_prop]
nonrec
/--
theorem `ContinuousAt.rexp` / 定理 `ContinuousAt.rexp`

English:
theorem ContinuousAt.rexp
  given: (h : ContinuousAt f x)
  statement: ContinuousAt (fun y => exp (f y)) x
  proof: h.rexp
@[fun_prop]

中文:
定理 ContinuousAt.rexp
  条件: (h : ContinuousAt f x)
  结论: ContinuousAt (fun y => exp (f y)) x
  证明: h.rexp
@[fun_prop]

Depends on / 依赖: fun_prop, h.rexp
-/
theorem ContinuousAt.rexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.rexp
@[fun_prop]
/--
theorem `ContinuousOn.rexp` / 定理 `ContinuousOn.rexp`

English:
theorem ContinuousOn.rexp
  given: (h : ContinuousOn f s)
  proof: fun x hx => (h x hx).rexp
@[fun_prop]

中文:
定理 ContinuousOn.rexp
  条件: (h : ContinuousOn f s)
  证明: fun x hx => (h x hx).rexp
@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem ContinuousOn.rexp (h : ContinuousOn f s) :
    ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).rexp
@[fun_prop]
/--
theorem `Continuous.rexp` / 定理 `Continuous.rexp`

English:
theorem Continuous.rexp
  given: (h : Continuous f)
  statement: Continuous fun y => exp (f y)
  proof: continuous_iff_continuousAt.2 fun _ => h.continuousAt.rexp

中文:
定理 Continuous.rexp
  条件: (h : Continuous f)
  结论: Continuous fun y => exp (f y)
  证明: continuous_iff_continuousAt.2 fun _ => h.continuousAt.rexp

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, h.continuousAt.rexp
-/
theorem Continuous.rexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun _ => h.continuousAt.rexp
end RealContinuousExpComp

namespace Real

variable {α : Type*} {x y z : Real} {l : Filter α}

/--
theorem `exp_half` / 定理 `exp_half`

English:
theorem exp_half
  given: (x : Real)
  statement: exp (x / 2) = √(exp x)
  proof: by
  rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [sq]; rw [← exp_add]; rw [add_halves] <;> exact (exp_pos _).le

中文:
定理 exp_half
  条件: (x : 实数)
  结论: exp (x / 2) = √(exp x)
  证明: by
  rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [sq]; rw [← exp_add]; rw [add_halves] <;> exact (exp_pos _).le

Depends on / 依赖: add_halves, eq_comm, exp_add, exp_pos, sqrt_eq_iff_eq_sq
-/
theorem exp_half (x : Real) : exp (x / 2) = √(exp x) := by
  rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [sq]; rw [← exp_add]; rw [add_halves] <;> exact (exp_pos _).le

/--
theorem `tendsto_exp_atTop` / 定理 `tendsto_exp_atTop`

English:
theorem tendsto_exp_atTop
  statement: Tendsto exp atTop atTop
  proof: by
  have A : Tendsto (fun x : Real => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have B : forallᶠ x in atTop, x + 1 <= exp x := eventually_atTop.2 ⟨0, fun x _ => add_one_le_exp x⟩
  exact tendsto_atTop_mono' atTop B A

中文:
定理 tendsto_exp_atTop
  结论: Tendsto exp atTop atTop
  证明: by
  have A : Tendsto (fun x : Real => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have B : forallᶠ x in atTop, x + 1 <= exp x := eventually_atTop.2 ⟨0, fun x _ => add_one_le_exp x⟩
  exact tendsto_atTop_mono' atTop B A

Depends on / 依赖: Tendsto, add_one_le_exp, eventually_atTop, tendsto_atTop_add_const_right, tendsto_atTop_mono, tendsto_id
-/
theorem tendsto_exp_atTop : Tendsto exp atTop atTop := by
  have A : Tendsto (fun x : Real => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have B : forallᶠ x in atTop, x + 1 <= exp x := eventually_atTop.2 ⟨0, fun x _ => add_one_le_exp x⟩
  exact tendsto_atTop_mono' atTop B A

/--
theorem `mul_exp_neg_le_exp_neg_one` / 定理 `mul_exp_neg_le_exp_neg_one`

English:
theorem mul_exp_neg_le_exp_neg_one
  given: (y : Real)
  statement: y * exp (-y) <= exp (-1)
  proof: by
  have h_le : y <= exp (y - 1) := by simpa using add_one_le_exp (y - 1)
  have h_mul_le : y * rexp (-y) <= rexp (y - 1) * rexp (-y) := by gcongr
  simpa [← exp_add, sub_add_eq_add_sub] using h_mul_le

中文:
定理 mul_exp_neg_le_exp_neg_one
  条件: (y : 实数)
  结论: y * exp (-y) <= exp (-1)
  证明: by
  have h_le : y <= exp (y - 1) := by simpa using add_one_le_exp (y - 1)
  have h_mul_le : y * rexp (-y) <= rexp (y - 1) * rexp (-y) := by gcongr
  simpa [← exp_add, sub_add_eq_add_sub] using h_mul_le

Depends on / 依赖: add_one_le_exp, exp_add, h_le, h_mul_le, sub_add_eq_add_sub
-/
theorem mul_exp_neg_le_exp_neg_one (y : Real) : y * exp (-y) <= exp (-1) := by
  have h_le : y <= exp (y - 1) := by simpa using add_one_le_exp (y - 1)
  have h_mul_le : y * rexp (-y) <= rexp (y - 1) * rexp (-y) := by gcongr
  simpa [← exp_add, sub_add_eq_add_sub] using h_mul_le

/--
theorem `tendsto_exp_neg_atTop_nhds_zero` / 定理 `tendsto_exp_neg_atTop_nhds_zero`

English:
theorem tendsto_exp_neg_atTop_nhds_zero
  statement: Tendsto (fun x => exp (-x)) atTop (𝓝 0)
  proof: (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm

中文:
定理 tendsto_exp_neg_atTop_nhds_zero
  结论: Tendsto (fun x => exp (-x)) atTop (𝓝 0)
  证明: (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm

Depends on / 依赖: exp_neg, tendsto_exp_atTop, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp
-/
theorem tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun x => exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm

/--
theorem `tendsto_exp_nhds_zero_nhds_one` / 定理 `tendsto_exp_nhds_zero_nhds_one`

English:
theorem tendsto_exp_nhds_zero_nhds_one
  statement: Tendsto exp (𝓝 0) (𝓝 1)
  proof: by
  convert! continuous_exp.tendsto 0
  simp

中文:
定理 tendsto_exp_nhds_zero_nhds_one
  结论: Tendsto exp (𝓝 0) (𝓝 1)
  证明: by
  convert! continuous_exp.tendsto 0
  simp

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, convert, tendsto
-/
theorem tendsto_exp_nhds_zero_nhds_one : Tendsto exp (𝓝 0) (𝓝 1) := by
  convert! continuous_exp.tendsto 0
  simp

/--
theorem `tendsto_exp_atBot` / 定理 `tendsto_exp_atBot`

English:
theorem tendsto_exp_atBot
  statement: Tendsto exp atBot (𝓝 0)
  proof: (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).congr fun x =>
congr_arg exp neg_neg x

中文:
定理 tendsto_exp_atBot
  结论: Tendsto exp atBot (𝓝 0)
  证明: (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).congr fun x =>
congr_arg exp neg_neg x

Depends on / 依赖: F.map_injective, apply_fun, congr_arg, f.hom, map_injective, neg_neg, tendsto_exp_neg_atTop_nhds_zero, tendsto_exp_neg_atTop_nhds_zero.comp, tendsto_neg_atBot_atTop
-/
theorem tendsto_exp_atBot : Tendsto exp atBot (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).congr fun x =>
congr_arg exp neg_neg x

/--
theorem `tendsto_exp_atBot_nhdsGT` / 定理 `tendsto_exp_atBot_nhdsGT`

English:
theorem tendsto_exp_atBot_nhdsGT
  statement: Tendsto exp atBot (𝓝[>] 0)
  proof: tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 Eventually.of_forall exp_pos⟩

@[simp]

中文:
定理 tendsto_exp_atBot_nhdsGT
  结论: Tendsto exp atBot (𝓝[>] 0)
  证明: tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 Eventually.of_forall exp_pos⟩

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, exp_pos, of_forall, tendsto_exp_atBot, tendsto_inf, tendsto_principal
-/
theorem tendsto_exp_atBot_nhdsGT : Tendsto exp atBot (𝓝[>] 0) :=
tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 Eventually.of_forall exp_pos⟩

@[simp]
/--
theorem `isBoundedUnder_ge_exp_comp` / 定理 `isBoundedUnder_ge_exp_comp`

English:
theorem isBoundedUnder_ge_exp_comp
  given: (l : Filter α) (f : α -> Real)
  proof: isBoundedUnder_of ⟨0, fun _ => (exp_pos _).le⟩

@[simp]

中文:
定理 isBoundedUnder_ge_exp_comp
  条件: (l : Filter α) (f : α -> 实数)
  证明: isBoundedUnder_of ⟨0, fun _ => (exp_pos _).le⟩

@[simp]

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, exp_pos, isBoundedUnder_of, mapAction, ofFullyFaithful
-/
theorem isBoundedUnder_ge_exp_comp (l : Filter α) (f : α -> Real) :
    IsBoundedUnder (· >= ·) l fun x => exp (f x) :=
  isBoundedUnder_of ⟨0, fun _ => (exp_pos _).le⟩

@[simp]
/--
theorem `isBoundedUnder_le_exp_comp` / 定理 `isBoundedUnder_le_exp_comp`

English:
theorem isBoundedUnder_le_exp_comp
  given: {f : α -> Real}
  proof: exp_monotone.isBoundedUnder_le_comp_iff tendsto_exp_atTop

中文:
定理 isBoundedUnder_le_exp_comp
  条件: {f : α -> 实数}
  证明: exp_monotone.isBoundedUnder_le_comp_iff tendsto_exp_atTop

Depends on / 依赖: exp_monotone, exp_monotone.isBoundedUnder_le_comp_iff, isBoundedUnder_le_comp_iff, tendsto_exp_atTop
-/
theorem isBoundedUnder_le_exp_comp {f : α -> Real} :
    (IsBoundedUnder (· <= ·) l fun x => exp (f x)) ↔ IsBoundedUnder (· <= ·) l f :=
  exp_monotone.isBoundedUnder_le_comp_iff tendsto_exp_atTop

/--
theorem `tendsto_exp_div_pow_atTop` / 定理 `tendsto_exp_div_pow_atTop`

English:
theorem tendsto_exp_div_pow_atTop
  given: (n : Nat)
  statement: Tendsto (fun x => exp x / x ^ n) atTop atTop
  proof: by
  refine (atTop_basis_Ioi.tendsto_iff (atTop_basis' 1)).2 fun C hC₁ => ?_
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : exists N : Nat, forall k >= N, (↑k : Real) ^ n / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventuall

中文:
定理 tendsto_exp_div_pow_atTop
  条件: (n : 自然数)
  结论: Tendsto (fun x => exp x / x ^ n) atTop atTop
  证明: by
  refine (atTop_basis_Ioi.tendsto_iff (atTop_basis' 1)).2 fun C hC₁ => ?_
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : exists N : Nat, forall k >= N, (↑k : Real) ^ n / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventuall

Depends on / 依赖: atTop_basis, atTop_basis_Ioi, atTop_basis_Ioi.tendsto_iff, div_eq_inv_mul, eventually, eventually_atTop, exp_nat_mul, exp_pos, gt_mem_nhds, inv_pos, mul_one, mul_pos, one_lt_exp_iff, tendsto_iff, tendsto_pow_const_div_const_pow_of_one_lt, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem tendsto_exp_div_pow_atTop (n : Nat) : Tendsto (fun x => exp x / x ^ n) atTop atTop := by
  refine (atTop_basis_Ioi.tendsto_iff (atTop_basis' 1)).2 fun C hC₁ => ?_
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : exists N : Nat, forall k >= N, (↑k : Real) ^ n / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_atTop.1
      ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).eventually
        (gt_mem_nhds this))
  simp only [← exp_nat_mul, mul_one, div_lt_iff₀, exp_pos, ← div_eq_inv_mul] at hN
  refine ⟨N, trivial, fun x hx => ?_⟩
  rw [Set.mem_Ioi] at hx
  have hx₀ : 0 < x := (Nat.cast_nonneg N).trans_lt hx
  rw [Set.mem_Ici]; rw [le_div_iff₀ (pow_pos hx₀ _)]; rw [← le_div_iff₀' hC₀]
  calc
    x ^ n <= ⌈x⌉₊ ^ n := by gcongr; exact Nat.le_ceil _
    _ <= exp ⌈x⌉₊ / (exp 1 * C) := mod_cast (hN _ (Nat.lt_ceil.2 hx).le).le
    _ <= exp (x + 1) / (exp 1 * C) := by gcongr; exact (Nat.ceil_lt_add_one hx₀.le).le
    _ = exp x / C := by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']

/--
theorem `tendsto_pow_mul_exp_neg_atTop_nhds_zero` / 定理 `tendsto_pow_mul_exp_neg_atTop_nhds_zero`

English:
theorem tendsto_pow_mul_exp_neg_atTop_nhds_zero
  given: (n : Nat)
  proof: (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_apply]; rw [inv_eq_one_div]; rw [div_div_eq_mul_div]; rw [one_mul]; rw [div_eq_mul_inv]; rw [exp_neg]

中文:
定理 tendsto_pow_mul_exp_neg_atTop_nhds_zero
  条件: (n : 自然数)
  证明: (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_apply]; rw [inv_eq_one_div]; rw [div_div_eq_mul_div]; rw [one_mul]; rw [div_eq_mul_inv]; rw [exp_neg]

Depends on / 依赖: comp_apply, div_div_eq_mul_div, div_eq_mul_inv, exp_neg, inv_eq_one_div, one_mul, tendsto_exp_div_pow_atTop, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp
-/
theorem tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : Nat) :
    Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_apply]; rw [inv_eq_one_div]; rw [div_div_eq_mul_div]; rw [one_mul]; rw [div_eq_mul_inv]; rw [exp_neg]

/--
theorem `tendsto_mul_exp_add_div_pow_atTop` / 定理 `tendsto_mul_exp_add_div_pow_atTop`

English:
theorem tendsto_mul_exp_add_div_pow_atTop
  given: (b c : Real) (n : Nat) (hb : 0 < b)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_atTop.const_mul_atTop hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_atTop n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_atTop (

中文:
定理 tendsto_mul_exp_add_div_pow_atTop
  条件: (b c : 实数) (n : 自然数) (hb : 0 < b)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_atTop.const_mul_atTop hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_atTop n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_atTop (

Depends on / 依赖: CoeFun, add_div, atTop_add, const_mul_atTop, div_atTop, div_one, eq_or_ne, mul_div_assoc, pow_zero, tendsto_const_nhds, tendsto_const_nhds.div_atTop, tendsto_exp_atTop, tendsto_exp_atTop.const_mul_atTop, tendsto_exp_div_pow_atTop, tendsto_pow_atTop
-/
theorem tendsto_mul_exp_add_div_pow_atTop (b c : Real) (n : Nat) (hb : 0 < b) :
    Tendsto (fun x => (b * exp x + c) / x ^ n) atTop atTop := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_atTop.const_mul_atTop hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_atTop n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop hn))

/--
theorem `tendsto_div_pow_mul_exp_add_atTop` / 定理 `tendsto_div_pow_mul_exp_add_atTop`

English:
theorem tendsto_div_pow_mul_exp_add_atTop
  given: (b c : Real) (n : Nat) (hb : 0 != b)
  proof: by
  have H : forall d e, 0 < d -> Tendsto (fun x : Real => x ^ n / (d * exp x + e)) atTop (𝓝 0) := by
    intro b' c' h
    convert! (tendsto_mul_exp_add_div_pow_atTop b' c' n h).inv_tendsto_atTop using 1
    ext x
    simp
  rcases lt_or_gt_of_ne hb with h | h
  · exact H b c h
  · convert! (H (-b

中文:
定理 tendsto_div_pow_mul_exp_add_atTop
  条件: (b c : 实数) (n : 自然数) (hb : 0 != b)
  证明: by
  have H : forall d e, 0 < d -> Tendsto (fun x : Real => x ^ n / (d * exp x + e)) atTop (𝓝 0) := by
    intro b' c' h
    convert! (tendsto_mul_exp_add_div_pow_atTop b' c' n h).inv_tendsto_atTop using 1
    ext x
    simp
  rcases lt_or_gt_of_ne hb with h | h
  · exact H b c h
  · convert! (H (-b

Depends on / 依赖: Tendsto, convert, div_neg, inv_tendsto_atTop, lt_or_gt_of_ne, neg_add, neg_neg, neg_pos, neg_pos.mpr, neg_zero, tendsto_mul_exp_add_div_pow_atTop
-/
theorem tendsto_div_pow_mul_exp_add_atTop (b c : Real) (n : Nat) (hb : 0 != b) :
    Tendsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0) := by
  have H : forall d e, 0 < d -> Tendsto (fun x : Real => x ^ n / (d * exp x + e)) atTop (𝓝 0) := by
    intro b' c' h
    convert! (tendsto_mul_exp_add_div_pow_atTop b' c' n h).inv_tendsto_atTop using 1
    ext x
    simp
  rcases lt_or_gt_of_ne hb with h | h
  · exact H b c h
  · convert! (H (-b) (-c) (neg_pos.mpr h)).neg using 1
    · ext x
      field_simp
      rw [← neg_add (b * exp x) c]; rw [div_neg]; rw [neg_neg]
    · rw [neg_zero]

/--
Definition of `expOrderIso` / `expOrderIso` 的定义

English:
definition expOrderIso
  signature: : Real ≃o Ioi (0 : Real)
  body: StrictMono.orderIsoOfSurjective _
(exp_strictMono.codRestrict fun x => Set.mem_Ioi.mpr (exp_pos x))
    (continuous_exp.subtype_mk _).surjective
      (by rw [tendsto_Ioi_atTop]; simp only [tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsGT])

@[simp]

中文:
定义 expOrderIso
  签名: : 实数 ≃o Ioi (0 : 实数)
  定义体: StrictMono.orderIsoOfSurjective _
(exp_strictMono.codRestrict fun x => Set.mem_Ioi.mpr (exp_pos x))
    (continuous_exp.subtype_mk _).surjective
      (by rw [tendsto_Ioi_atTop]; simp only [tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsGT])

@[simp]

Depends on / 依赖: Set.mem_Ioi.mpr, StrictMono, StrictMono.orderIsoOfSurjective, codRestrict, continuous_exp, continuous_exp.subtype_mk, exp_pos, exp_strictMono, exp_strictMono.codRestrict, mem_Ioi, orderIsoOfSurjective, subtype_mk, surjective, tendsto_Ioi_atTop, tendsto_exp_atBot_nhdsGT, tendsto_exp_atTop
-/
def expOrderIso : Real ≃o Ioi (0 : Real) :=
  StrictMono.orderIsoOfSurjective _
(exp_strictMono.codRestrict fun x => Set.mem_Ioi.mpr (exp_pos x))
    (continuous_exp.subtype_mk _).surjective
      (by rw [tendsto_Ioi_atTop]; simp only [tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsGT])

@[simp]
/--
theorem `coe_expOrderIso_apply` / 定理 `coe_expOrderIso_apply`

English:
theorem coe_expOrderIso_apply
  given: (x : Real)
  statement: (expOrderIso x : Real) = exp x
  proof: rfl

@[simp]

中文:
定理 coe_expOrderIso_apply
  条件: (x : 实数)
  结论: (expOrderIso x : 实数) = exp x
  证明: rfl

@[simp]
-/
theorem coe_expOrderIso_apply (x : Real) : (expOrderIso x : Real) = exp x :=
  rfl

@[simp]
/--
theorem `coe_comp_expOrderIso` / 定理 `coe_comp_expOrderIso`

English:
theorem coe_comp_expOrderIso
  statement: (↑) ∘ expOrderIso = exp
  proof: rfl

@[simp]

中文:
定理 coe_comp_expOrderIso
  结论: (↑) ∘ expOrderIso = exp
  证明: rfl

@[simp]
-/
theorem coe_comp_expOrderIso : (↑) ∘ expOrderIso = exp :=
  rfl

@[simp]
/--
theorem `range_exp` / 定理 `range_exp`

English:
theorem range_exp
  statement: range exp = Set.Ioi 0
  proof: by
  rw [← coe_comp_expOrderIso]; rw [range_comp]; rw [expOrderIso.range_eq]; rw [image_univ]; rw [Subtype.range_coe]

@[simp]

中文:
定理 range_exp
  结论: range exp = Set.Ioi 0
  证明: by
  rw [← coe_comp_expOrderIso]; rw [range_comp]; rw [expOrderIso.range_eq]; rw [image_univ]; rw [Subtype.range_coe]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe, coe_comp_expOrderIso, expOrderIso, expOrderIso.range_eq, image_univ, range_coe, range_comp, range_eq
-/
theorem range_exp : range exp = Set.Ioi 0 := by
  rw [← coe_comp_expOrderIso]; rw [range_comp]; rw [expOrderIso.range_eq]; rw [image_univ]; rw [Subtype.range_coe]

@[simp]
/--
theorem `image_exp_Ioi` / 定理 `image_exp_Ioi`

English:
theorem image_exp_Ioi
  given: (a : Real)
  statement: exp '' Ioi a = Ioi (exp a)
  proof: continuous_exp.continuousOn.image_Ioi_of_strictMonoOn (exp_strictMono.strictMonoOn _)
    tendsto_exp_atTop

@[simp]

中文:
定理 image_exp_Ioi
  条件: (a : 实数)
  结论: exp '' Ioi a = Ioi (exp a)
  证明: continuous_exp.continuousOn.image_Ioi_of_strictMonoOn (exp_strictMono.strictMonoOn _)
    tendsto_exp_atTop

@[simp]

Depends on / 依赖: continuousOn, continuous_exp, continuous_exp.continuousOn.image_Ioi_of_strictMonoOn, exp_strictMono, exp_strictMono.strictMonoOn, image_Ioi_of_strictMonoOn, strictMonoOn, tendsto_exp_atTop
-/
theorem image_exp_Ioi (a : Real) : exp '' Ioi a = Ioi (exp a) :=
  continuous_exp.continuousOn.image_Ioi_of_strictMonoOn (exp_strictMono.strictMonoOn _)
    tendsto_exp_atTop

@[simp]
/--
theorem `image_exp_Ici` / 定理 `image_exp_Ici`

English:
theorem image_exp_Ici
  given: (a : Real)
  statement: exp '' Ici a = Ici (exp a)
  proof: continuous_exp.continuousOn.image_Ici_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)
    tendsto_exp_atTop

@[simp]

中文:
定理 image_exp_Ici
  条件: (a : 实数)
  结论: exp '' Ici a = Ici (exp a)
  证明: continuous_exp.continuousOn.image_Ici_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)
    tendsto_exp_atTop

@[simp]

Depends on / 依赖: continuousOn, continuous_exp, continuous_exp.continuousOn.image_Ici_of_monotoneOn, exp_strictMono, exp_strictMono.monotone.monotoneOn, image_Ici_of_monotoneOn, monotone, monotoneOn, tendsto_exp_atTop
-/
theorem image_exp_Ici (a : Real) : exp '' Ici a = Ici (exp a) :=
  continuous_exp.continuousOn.image_Ici_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)
    tendsto_exp_atTop

@[simp]
/--
theorem `image_exp_Icc` / 定理 `image_exp_Icc`

English:
theorem image_exp_Icc
  given: (a b : Real)
  statement: exp '' Icc a b = Icc (exp a) (exp b)
  proof: continuous_exp.image_Icc_of_strictMono exp_strictMono

@[simp]

中文:
定理 image_exp_Icc
  条件: (a b : 实数)
  结论: exp '' Icc a b = Icc (exp a) (exp b)
  证明: continuous_exp.image_Icc_of_strictMono exp_strictMono

@[simp]

Depends on / 依赖: continuous_exp, continuous_exp.image_Icc_of_strictMono, exp_strictMono, image_Icc_of_strictMono
-/
theorem image_exp_Icc (a b : Real) : exp '' Icc a b = Icc (exp a) (exp b) :=
  continuous_exp.image_Icc_of_strictMono exp_strictMono

@[simp]
/--
theorem `image_exp_Ico` / 定理 `image_exp_Ico`

English:
theorem image_exp_Ico
  given: (a b : Real)
  statement: exp '' Ico a b = Ico (exp a) (exp b)
  proof: continuous_exp.image_Ico_of_strictMono exp_strictMono

@[simp]

中文:
定理 image_exp_Ico
  条件: (a b : 实数)
  结论: exp '' Ico a b = Ico (exp a) (exp b)
  证明: continuous_exp.image_Ico_of_strictMono exp_strictMono

@[simp]

Depends on / 依赖: continuous_exp, continuous_exp.image_Ico_of_strictMono, exp_strictMono, image_Ico_of_strictMono
-/
theorem image_exp_Ico (a b : Real) : exp '' Ico a b = Ico (exp a) (exp b) :=
  continuous_exp.image_Ico_of_strictMono exp_strictMono

@[simp]
/--
theorem `image_exp_Ioc` / 定理 `image_exp_Ioc`

English:
theorem image_exp_Ioc
  given: (a b : Real)
  statement: exp '' Ioc a b = Ioc (exp a) (exp b)
  proof: continuous_exp.image_Ioc_of_strictMono exp_strictMono

@[simp]

中文:
定理 image_exp_Ioc
  条件: (a b : 实数)
  结论: exp '' Ioc a b = Ioc (exp a) (exp b)
  证明: continuous_exp.image_Ioc_of_strictMono exp_strictMono

@[simp]

Depends on / 依赖: MulAction, continuous_exp, continuous_exp.image_Ioc_of_strictMono, exp_strictMono, image_Ioc_of_strictMono
-/
theorem image_exp_Ioc (a b : Real) : exp '' Ioc a b = Ioc (exp a) (exp b) :=
  continuous_exp.image_Ioc_of_strictMono exp_strictMono

@[simp]
/--
theorem `image_exp_Ioo` / 定理 `image_exp_Ioo`

English:
theorem image_exp_Ioo
  given: (a b : Real)
  statement: exp '' Ioo a b = Ioo (exp a) (exp b)
  proof: continuous_exp.image_Ioo_of_strictMono exp_strictMono

@[simp]

中文:
定理 image_exp_Ioo
  条件: (a b : 实数)
  结论: exp '' Ioo a b = Ioo (exp a) (exp b)
  证明: continuous_exp.image_Ioo_of_strictMono exp_strictMono

@[simp]

Depends on / 依赖: continuous_exp, continuous_exp.image_Ioo_of_strictMono, exp_strictMono, image_Ioo_of_strictMono
-/
theorem image_exp_Ioo (a b : Real) : exp '' Ioo a b = Ioo (exp a) (exp b) :=
  continuous_exp.image_Ioo_of_strictMono exp_strictMono

@[simp]
/--
theorem `image_exp_uIcc` / 定理 `image_exp_uIcc`

English:
theorem image_exp_uIcc
  given: (a b : Real)
  statement: exp '' uIcc a b = uIcc (exp a) (exp b)
  proof: continuous_exp.continuousOn.image_uIcc_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)

@[simp]

中文:
定理 image_exp_uIcc
  条件: (a b : 实数)
  结论: exp '' uIcc a b = uIcc (exp a) (exp b)
  证明: continuous_exp.continuousOn.image_uIcc_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)

@[simp]

Depends on / 依赖: continuousOn, continuous_exp, continuous_exp.continuousOn.image_uIcc_of_monotoneOn, exp_strictMono, exp_strictMono.monotone.monotoneOn, image_uIcc_of_monotoneOn, monotone, monotoneOn
-/
theorem image_exp_uIcc (a b : Real) : exp '' uIcc a b = uIcc (exp a) (exp b) :=
  continuous_exp.continuousOn.image_uIcc_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)

@[simp]
/--
theorem `image_exp_Iio` / 定理 `image_exp_Iio`

English:
theorem image_exp_Iio
  given: (a : Real)
  statement: exp '' Iio a = Ioo 0 (exp a)
  proof: by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iio]; rw [image_subtype_val_Ioi_Iio]; rw [Function.comp_apply]

@[simp]

中文:
定理 image_exp_Iio
  条件: (a : 实数)
  结论: exp '' Iio a = Ioo 0 (exp a)
  证明: by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iio]; rw [image_subtype_val_Ioi_Iio]; rw [Function.comp_apply]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, coe_comp_expOrderIso, comp_apply, expOrderIso, expOrderIso.image_Iio, image_Iio, image_comp, image_subtype_val_Ioi_Iio
-/
theorem image_exp_Iio (a : Real) : exp '' Iio a = Ioo 0 (exp a) := by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iio]; rw [image_subtype_val_Ioi_Iio]; rw [Function.comp_apply]

@[simp]
/--
theorem `image_exp_Iic` / 定理 `image_exp_Iic`

English:
theorem image_exp_Iic
  given: (a : Real)
  statement: exp '' Iic a = Ioc 0 (exp a)
  proof: by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iic]; rw [image_subtype_val_Ioi_Iic]; rw [Function.comp_apply]

@[simp]

中文:
定理 image_exp_Iic
  条件: (a : 实数)
  结论: exp '' Iic a = Ioc 0 (exp a)
  证明: by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iic]; rw [image_subtype_val_Ioi_Iic]; rw [Function.comp_apply]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, coe_comp_expOrderIso, comp_apply, expOrderIso, expOrderIso.image_Iic, image_Iic, image_comp, image_subtype_val_Ioi_Iic
-/
theorem image_exp_Iic (a : Real) : exp '' Iic a = Ioc 0 (exp a) := by
  rw [← coe_comp_expOrderIso]; rw [image_comp]; rw [expOrderIso.image_Iic]; rw [image_subtype_val_Ioi_Iic]; rw [Function.comp_apply]

@[simp]
/--
theorem `map_exp_atTop` / 定理 `map_exp_atTop`

English:
theorem map_exp_atTop
  statement: map exp atTop = atTop
  proof: by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [OrderIso.map_atTop]; rw [map_val_Ioi_atTop]

@[simp]

中文:
定理 map_exp_atTop
  结论: map exp atTop = atTop
  证明: by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [OrderIso.map_atTop]; rw [map_val_Ioi_atTop]

@[simp]

Depends on / 依赖: Filter, Filter.map_map, OrderIso, OrderIso.map_atTop, coe_comp_expOrderIso, map_atTop, map_map, map_val_Ioi_atTop
-/
theorem map_exp_atTop : map exp atTop = atTop := by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [OrderIso.map_atTop]; rw [map_val_Ioi_atTop]

@[simp]
/--
theorem `comap_exp_atTop` / 定理 `comap_exp_atTop`

English:
theorem comap_exp_atTop
  statement: comap exp atTop = atTop
  proof: by
  rw [← map_exp_atTop]; rw [comap_map exp_injective]; rw [map_exp_atTop]

@[simp]

中文:
定理 comap_exp_atTop
  结论: comap exp atTop = atTop
  证明: by
  rw [← map_exp_atTop]; rw [comap_map exp_injective]; rw [map_exp_atTop]

@[simp]

Depends on / 依赖: comap_map, exp_injective, map_exp_atTop
-/
theorem comap_exp_atTop : comap exp atTop = atTop := by
  rw [← map_exp_atTop]; rw [comap_map exp_injective]; rw [map_exp_atTop]

@[simp]
/--
theorem `tendsto_exp_comp_atTop` / 定理 `tendsto_exp_comp_atTop`

English:
theorem tendsto_exp_comp_atTop
  given: {f : α -> Real}
  proof: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_atTop]

中文:
定理 tendsto_exp_comp_atTop
  条件: {f : α -> 实数}
  证明: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_atTop]

Depends on / 依赖: comap_exp_atTop, comp_apply, simp_rw, tendsto_comap_iff
-/
theorem tendsto_exp_comp_atTop {f : α -> Real} :
    Tendsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_atTop]

/--
theorem `tendsto_comp_exp_atTop` / 定理 `tendsto_comp_exp_atTop`

English:
theorem tendsto_comp_exp_atTop
  given: {f : Real -> α}
  proof: by
  simp_rw [← comp_apply (g := exp), ← tendsto_map'_iff, map_exp_atTop]

@[simp]

中文:
定理 tendsto_comp_exp_atTop
  条件: {f : 实数 -> α}
  证明: by
  simp_rw [← comp_apply (g := exp), ← tendsto_map'_iff, map_exp_atTop]

@[simp]

Depends on / 依赖: _iff, comp_apply, map_exp_atTop, simp_rw, tendsto_map
-/
theorem tendsto_comp_exp_atTop {f : Real -> α} :
    Tendsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l := by
  simp_rw [← comp_apply (g := exp), ← tendsto_map'_iff, map_exp_atTop]

@[simp]
/--
theorem `map_exp_atBot` / 定理 `map_exp_atBot`

English:
theorem map_exp_atBot
  statement: map exp atBot = 𝓝[>] 0
  proof: by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [expOrderIso.map_atBot]; rw [← map_coe_Ioi_atBot]

@[simp]

中文:
定理 map_exp_atBot
  结论: map exp atBot = 𝓝[>] 0
  证明: by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [expOrderIso.map_atBot]; rw [← map_coe_Ioi_atBot]

@[simp]

Depends on / 依赖: Filter, Filter.map_map, coe_comp_expOrderIso, expOrderIso, expOrderIso.map_atBot, map_atBot, map_coe_Ioi_atBot, map_map
-/
theorem map_exp_atBot : map exp atBot = 𝓝[>] 0 := by
  rw [← coe_comp_expOrderIso]; rw [← Filter.map_map]; rw [expOrderIso.map_atBot]; rw [← map_coe_Ioi_atBot]

@[simp]
/--
theorem `comap_exp_nhdsGT_zero` / 定理 `comap_exp_nhdsGT_zero`

English:
theorem comap_exp_nhdsGT_zero
  statement: comap exp (𝓝[>] 0) = atBot
  proof: by
  rw [← map_exp_atBot]; rw [comap_map exp_injective]

中文:
定理 comap_exp_nhdsGT_zero
  结论: comap exp (𝓝[>] 0) = atBot
  证明: by
  rw [← map_exp_atBot]; rw [comap_map exp_injective]

Depends on / 依赖: comap_map, exp_injective, map_exp_atBot
-/
theorem comap_exp_nhdsGT_zero : comap exp (𝓝[>] 0) = atBot := by
  rw [← map_exp_atBot]; rw [comap_map exp_injective]

/--
theorem `tendsto_comp_exp_atBot` / 定理 `tendsto_comp_exp_atBot`

English:
theorem tendsto_comp_exp_atBot
  given: {f : Real -> α}
  proof: by
  rw [← map_exp_atBot]; rw [tendsto_map'_iff]
  rfl

@[simp]

中文:
定理 tendsto_comp_exp_atBot
  条件: {f : 实数 -> α}
  证明: by
  rw [← map_exp_atBot]; rw [tendsto_map'_iff]
  rfl

@[simp]

Depends on / 依赖: Action, Action.instMulAction, _iff, instMulAction, map_exp_atBot, tendsto_map
-/
theorem tendsto_comp_exp_atBot {f : Real -> α} :
    Tendsto (fun x => f (exp x)) atBot l ↔ Tendsto f (𝓝[>] 0) l := by
  rw [← map_exp_atBot]; rw [tendsto_map'_iff]
  rfl

@[simp]
/--
theorem `comap_exp_nhds_zero` / 定理 `comap_exp_nhds_zero`

English:
theorem comap_exp_nhds_zero
  statement: comap exp (𝓝 0) = atBot
  proof: (comap_nhdsWithin_range exp 0).symm.trans by simp

@[simp]

中文:
定理 comap_exp_nhds_zero
  结论: comap exp (𝓝 0) = atBot
  证明: (comap_nhdsWithin_range exp 0).symm.trans by simp

@[simp]

Depends on / 依赖: comap_nhdsWithin_range, symm.trans
-/
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = atBot :=
(comap_nhdsWithin_range exp 0).symm.trans by simp

@[simp]
/--
theorem `tendsto_exp_comp_nhds_zero` / 定理 `tendsto_exp_comp_nhds_zero`

English:
theorem tendsto_exp_comp_nhds_zero
  given: {f : α -> Real}
  proof: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero]

@[fun_prop]

中文:
定理 tendsto_exp_comp_nhds_zero
  条件: {f : α -> 实数}
  证明: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero]

@[fun_prop]

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, TopCat, comap_exp_nhds_zero, comp_apply, simp_rw, tendsto_comap_iff
-/
theorem tendsto_exp_comp_nhds_zero {f : α -> Real} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto f l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero]

@[fun_prop]
/--
theorem `isOpenEmbedding_exp` / 定理 `isOpenEmbedding_exp`

English:
theorem isOpenEmbedding_exp
  statement: IsOpenEmbedding exp
  proof: isOpen_Ioi.isOpenEmbedding_subtypeVal.comp expOrderIso.toHomeomorph.isOpenEmbedding

@[simp]

中文:
定理 isOpenEmbedding_exp
  结论: IsOpenEmbedding exp
  证明: isOpen_Ioi.isOpenEmbedding_subtypeVal.comp expOrderIso.toHomeomorph.isOpenEmbedding

@[simp]

Depends on / 依赖: expOrderIso, expOrderIso.toHomeomorph.isOpenEmbedding, isOpenEmbedding, isOpenEmbedding_subtypeVal, isOpen_Ioi, isOpen_Ioi.isOpenEmbedding_subtypeVal.comp, toHomeomorph
-/
theorem isOpenEmbedding_exp : IsOpenEmbedding exp :=
  isOpen_Ioi.isOpenEmbedding_subtypeVal.comp expOrderIso.toHomeomorph.isOpenEmbedding

@[simp]
/--
theorem `map_exp_nhds` / 定理 `map_exp_nhds`

English:
theorem map_exp_nhds
  given: (x : Real)
  statement: map exp (𝓝 x) = 𝓝 (exp x)
  proof: isOpenEmbedding_exp.map_nhds_eq x

@[simp]

中文:
定理 map_exp_nhds
  条件: (x : 实数)
  结论: map exp (𝓝 x) = 𝓝 (exp x)
  证明: isOpenEmbedding_exp.map_nhds_eq x

@[simp]

Depends on / 依赖: isOpenEmbedding_exp, isOpenEmbedding_exp.map_nhds_eq, map_nhds_eq
-/
theorem map_exp_nhds (x : Real) : map exp (𝓝 x) = 𝓝 (exp x) :=
  isOpenEmbedding_exp.map_nhds_eq x

@[simp]
/--
theorem `comap_exp_nhds_exp` / 定理 `comap_exp_nhds_exp`

English:
theorem comap_exp_nhds_exp
  given: (x : Real)
  statement: comap exp (𝓝 (exp x)) = 𝓝 x
  proof: (isOpenEmbedding_exp.nhds_eq_comap x).symm

中文:
定理 comap_exp_nhds_exp
  条件: (x : 实数)
  结论: comap exp (𝓝 (exp x)) = 𝓝 x
  证明: (isOpenEmbedding_exp.nhds_eq_comap x).symm

Depends on / 依赖: isOpenEmbedding_exp, isOpenEmbedding_exp.nhds_eq_comap, nhds_eq_comap
-/
theorem comap_exp_nhds_exp (x : Real) : comap exp (𝓝 (exp x)) = 𝓝 x :=
  (isOpenEmbedding_exp.nhds_eq_comap x).symm

/--
theorem `isLittleO_pow_exp_atTop` / 定理 `isLittleO_pow_exp_atTop`

English:
theorem isLittleO_pow_exp_atTop
  given: {n : Nat}
  statement: (fun x : Real => x ^ n) =o[atTop] Real.exp
  proof: by
  simpa [isLittleO_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_atTop 1 0 n zero_ne_one

@[simp]

中文:
定理 isLittleO_pow_exp_atTop
  条件: {n : 自然数}
  结论: (fun x : 实数 => x ^ n) =o[atTop] 实数.exp
  证明: by
  simpa [isLittleO_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_atTop 1 0 n zero_ne_one

@[simp]

Depends on / 依赖: exp_pos, isLittleO_iff_tendsto, tendsto_div_pow_mul_exp_add_atTop, zero_ne_one
-/
theorem isLittleO_pow_exp_atTop {n : Nat} : (fun x : Real => x ^ n) =o[atTop] Real.exp := by
  simpa [isLittleO_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_atTop 1 0 n zero_ne_one

@[simp]
/--
theorem `isBigO_exp_comp_exp_comp` / 定理 `isBigO_exp_comp_exp_comp`

English:
theorem isBigO_exp_comp_exp_comp
  given: {f g : α -> Real}
  proof: Iff.trans (isBigO_iff_isBoundedUnder_le_div <| Eventually.of_forall fun _ => exp_ne_zero _) by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, isBoundedUnder_le_exp_comp, Pi.sub_def]

@[simp]

中文:
定理 isBigO_exp_comp_exp_comp
  条件: {f g : α -> 实数}
  证明: Iff.trans (isBigO_iff_isBoundedUnder_le_div <| Eventually.of_forall fun _ => exp_ne_zero _) by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, isBoundedUnder_le_exp_comp, Pi.sub_def]

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, Iff.trans, Pi.sub_def, abs_exp, exp_ne_zero, exp_sub, isBigO_iff_isBoundedUnder_le_div, isBoundedUnder_le_exp_comp, norm_eq_abs, of_forall, sub_def
-/
theorem isBigO_exp_comp_exp_comp {f g : α -> Real} :
    ((fun x => exp (f x)) =O[l] fun x => exp (g x)) ↔ IsBoundedUnder (· <= ·) l (f - g) :=
Iff.trans (isBigO_iff_isBoundedUnder_le_div <| Eventually.of_forall fun _ => exp_ne_zero _) by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, isBoundedUnder_le_exp_comp, Pi.sub_def]

@[simp]
/--
theorem `isTheta_exp_comp_exp_comp` / 定理 `isTheta_exp_comp_exp_comp`

English:
theorem isTheta_exp_comp_exp_comp
  given: {f g : α -> Real}
  proof: by
  simp only [isBoundedUnder_le_abs, ← isBoundedUnder_le_neg, neg_sub, IsTheta,
    isBigO_exp_comp_exp_comp, Pi.sub_def]

@[simp]

中文:
定理 isTheta_exp_comp_exp_comp
  条件: {f g : α -> 实数}
  证明: by
  simp only [isBoundedUnder_le_abs, ← isBoundedUnder_le_neg, neg_sub, IsTheta,
    isBigO_exp_comp_exp_comp, Pi.sub_def]

@[simp]

Depends on / 依赖: IsTheta, Pi.sub_def, isBigO_exp_comp_exp_comp, isBoundedUnder_le_abs, isBoundedUnder_le_neg, neg_sub, sub_def
-/
theorem isTheta_exp_comp_exp_comp {f g : α -> Real} :
    ((fun x => exp (f x)) =Θ[l] fun x => exp (g x)) ↔
      IsBoundedUnder (· <= ·) l fun x => |f x - g x| := by
  simp only [isBoundedUnder_le_abs, ← isBoundedUnder_le_neg, neg_sub, IsTheta,
    isBigO_exp_comp_exp_comp, Pi.sub_def]

@[simp]
/--
theorem `isLittleO_exp_comp_exp_comp` / 定理 `isLittleO_exp_comp_exp_comp`

English:
theorem isLittleO_exp_comp_exp_comp
  given: {f g : α -> Real}
  proof: by
  simp only [isLittleO_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_atTop_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]

中文:
定理 isLittleO_exp_comp_exp_comp
  条件: {f g : α -> 实数}
  证明: by
  simp only [isLittleO_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_atTop_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]

Depends on / 依赖: exp_ne_zero, exp_sub, false_imp_iff, imp_true_iff, isLittleO_iff_tendsto, neg_sub, tendsto_exp_comp_nhds_zero, tendsto_neg_atTop_iff
-/
theorem isLittleO_exp_comp_exp_comp {f g : α -> Real} :
    ((fun x => exp (f x)) =o[l] fun x => exp (g x)) ↔ Tendsto (fun x => g x - f x) l atTop := by
  simp only [isLittleO_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_atTop_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]

/--
theorem `isLittleO_one_exp_comp` / 定理 `isLittleO_one_exp_comp`

English:
theorem isLittleO_one_exp_comp
  given: {f : α -> Real}
  proof: by
  simp only [← exp_zero, isLittleO_exp_comp_exp_comp, sub_zero]

中文:
定理 isLittleO_one_exp_comp
  条件: {f : α -> 实数}
  证明: by
  simp only [← exp_zero, isLittleO_exp_comp_exp_comp, sub_zero]

Depends on / 依赖: exp_zero, isLittleO_exp_comp_exp_comp, sub_zero
-/
theorem isLittleO_one_exp_comp {f : α -> Real} :
    ((fun _ => 1 : α -> Real) =o[l] fun x => exp (f x)) ↔ Tendsto f l atTop := by
  simp only [← exp_zero, isLittleO_exp_comp_exp_comp, sub_zero]

/-- `Real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
@[simp]
/--
theorem `isBigO_one_exp_comp` / 定理 `isBigO_one_exp_comp`

English:
theorem isBigO_one_exp_comp
  given: {f : α -> Real}
  proof: by
  simp only [← exp_zero, isBigO_exp_comp_exp_comp, Pi.sub_def, zero_sub, isBoundedUnder_le_neg]

中文:
定理 isBigO_one_exp_comp
  条件: {f : α -> 实数}
  证明: by
  simp only [← exp_zero, isBigO_exp_comp_exp_comp, Pi.sub_def, zero_sub, isBoundedUnder_le_neg]

Depends on / 依赖: Pi.sub_def, exp_zero, isBigO_exp_comp_exp_comp, isBoundedUnder_le_neg, sub_def, zero_sub
-/
theorem isBigO_one_exp_comp {f : α -> Real} :
    ((fun _ => 1 : α -> Real) =O[l] fun x => exp (f x)) ↔ IsBoundedUnder (· >= ·) l f := by
  simp only [← exp_zero, isBigO_exp_comp_exp_comp, Pi.sub_def, zero_sub, isBoundedUnder_le_neg]

/--
theorem `isBigO_exp_comp_one` / 定理 `isBigO_exp_comp_one`

English:
theorem isBigO_exp_comp_one
  given: {f : α -> Real}
  proof: by
  simp only [isBigO_one_iff, norm_eq_abs, abs_exp, isBoundedUnder_le_exp_comp]

中文:
定理 isBigO_exp_comp_one
  条件: {f : α -> 实数}
  证明: by
  simp only [isBigO_one_iff, norm_eq_abs, abs_exp, isBoundedUnder_le_exp_comp]

Depends on / 依赖: abs_exp, isBigO_one_iff, isBoundedUnder_le_exp_comp, norm_eq_abs
-/
theorem isBigO_exp_comp_one {f : α -> Real} :
    (fun x => exp (f x)) =O[l] (fun _ => 1 : α -> Real) ↔ IsBoundedUnder (· <= ·) l f := by
  simp only [isBigO_one_iff, norm_eq_abs, abs_exp, isBoundedUnder_le_exp_comp]

/-- `Real.exp (f x)` is bounded away from zero and infinity along a filter `l` if and only if
`|f x|` is bounded from above along this filter. -/
@[simp]
/--
theorem `isTheta_exp_comp_one` / 定理 `isTheta_exp_comp_one`

English:
theorem isTheta_exp_comp_one
  given: {f : α -> Real}
  proof: by
  simp only [← exp_zero, isTheta_exp_comp_exp_comp, sub_zero]

中文:
定理 isTheta_exp_comp_one
  条件: {f : α -> 实数}
  证明: by
  simp only [← exp_zero, isTheta_exp_comp_exp_comp, sub_zero]

Depends on / 依赖: exp_zero, isTheta_exp_comp_exp_comp, sub_zero
-/
theorem isTheta_exp_comp_one {f : α -> Real} :
    (fun x => exp (f x)) =Θ[l] (fun _ => 1 : α -> Real) ↔ IsBoundedUnder (· <= ·) l fun x => |f x| := by
  simp only [← exp_zero, isTheta_exp_comp_exp_comp, sub_zero]

/--
lemma `summable_exp_nat_mul_iff` / 引理 `summable_exp_nat_mul_iff`

English:
lemma summable_exp_nat_mul_iff
  given: {a : Real}
  proof: by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]

中文:
引理 summable_exp_nat_mul_iff
  条件: {a : 实数}
  证明: by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]

Depends on / 依赖: exp_lt_one_iff, exp_nat_mul, exp_nonneg, norm_of_nonneg, summable_geometric_iff_norm_lt_one
-/
lemma summable_exp_nat_mul_iff {a : Real} :
    Summable (fun n : Nat => exp (n * a)) ↔ a < 0 := by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]

/--
lemma `summable_exp_neg_nat` / 引理 `summable_exp_neg_nat`

English:
lemma summable_exp_neg_nat
  statement: Summable fun n : Nat => exp (-n)
  proof: by
  simpa only [mul_neg_one] using summable_exp_nat_mul_iff.mpr neg_one_lt_zero

中文:
引理 summable_exp_neg_nat
  结论: Summable fun n : 自然数 => exp (-n)
  证明: by
  simpa only [mul_neg_one] using summable_exp_nat_mul_iff.mpr neg_one_lt_zero

Depends on / 依赖: mul_neg_one, neg_one_lt_zero, summable_exp_nat_mul_iff, summable_exp_nat_mul_iff.mpr
-/
lemma summable_exp_neg_nat : Summable fun n : Nat => exp (-n) := by
  simpa only [mul_neg_one] using summable_exp_nat_mul_iff.mpr neg_one_lt_zero

/--
lemma `summable_exp_nat_mul_of_ge` / 引理 `summable_exp_nat_mul_of_ge`

English:
lemma summable_exp_nat_mul_of_ge
  given: {c : Real} (hc : c < 0) {f : Nat -> Real} (hf : forall i, i <= f i)
  proof: by
  refine (Real.summable_exp_nat_mul_iff.mpr hc).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
  refine Real.exp_monotone ?_
  conv_rhs => rw [mul_comm]
  exact mul_le_mul_of_nonpos_left (hf i) hc.le

中文:
引理 summable_exp_nat_mul_of_ge
  条件: {c : 实数} (hc : c < 0) {f : 自然数 -> 实数} (hf : 对任意 i, i <= f i)
  证明: by
  refine (Real.summable_exp_nat_mul_iff.mpr hc).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
  refine Real.exp_monotone ?_
  conv_rhs => rw [mul_comm]
  exact mul_le_mul_of_nonpos_left (hf i) hc.le

Depends on / 依赖: Real.exp_monotone, Real.summable_exp_nat_mul_iff.mpr, conv_rhs, exp_monotone, hc.le, mul_comm, mul_le_mul_of_nonpos_left, of_nonneg_of_le, summable_exp_nat_mul_iff
-/
lemma summable_exp_nat_mul_of_ge {c : Real} (hc : c < 0) {f : Nat -> Real} (hf : forall i, i <= f i) :
    Summable fun i : Nat => exp (c * f i) := by
  refine (Real.summable_exp_nat_mul_iff.mpr hc).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
  refine Real.exp_monotone ?_
  conv_rhs => rw [mul_comm]
  exact mul_le_mul_of_nonpos_left (hf i) hc.le

/--
lemma `summable_pow_mul_exp_neg_nat_mul` / 引理 `summable_pow_mul_exp_neg_nat_mul`

English:
lemma summable_pow_mul_exp_neg_nat_mul
  given: (k : Nat) {r : Real} (hr : 0 < r)
  proof: by
  simp_rw [mul_comm (-r), exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

中文:
引理 summable_pow_mul_exp_neg_nat_mul
  条件: (k : 自然数) {r : 实数} (hr : 0 < r)
  证明: by
  simp_rw [mul_comm (-r), exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

Depends on / 依赖: X.property, exp_lt_one_iff, exp_nat_mul, exp_nonneg, mul_comm, neg_lt_zero, norm_of_nonneg, property, simp_rw, summable_pow_mul_geometric_of_norm_lt_one
-/
lemma summable_pow_mul_exp_neg_nat_mul (k : Nat) {r : Real} (hr : 0 < r) :
    Summable fun n : Nat => n ^ k * exp (-r * n) := by
  simp_rw [mul_comm (-r), exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

end Real

open Real in
/--
lemma `HasSum.rexp` / 引理 `HasSum.rexp`

English:
lemma HasSum.rexp
  given: {ι} {f : ι -> Real} {a : Real} (h : HasSum f a)
  statement: HasProd (rexp ∘ f) (rexp a)
  proof: Tendsto.congr (fun s => exp_sum s f) Tendsto.rexp h

中文:
引理 HasSum.rexp
  条件: {ι} {f : ι -> 实数} {a : 实数} (h : HasSum f a)
  结论: HasProd (rexp ∘ f) (rexp a)
  证明: Tendsto.congr (fun s => exp_sum s f) Tendsto.rexp h

Depends on / 依赖: Tendsto, Tendsto.congr, Tendsto.rexp, exp_sum
-/
lemma HasSum.rexp {ι} {f : ι -> Real} {a : Real} (h : HasSum f a) : HasProd (rexp ∘ f) (rexp a) :=
Tendsto.congr (fun s => exp_sum s f) Tendsto.rexp h

namespace Complex

@[simp]
/--
theorem `comap_exp_cobounded` / 定理 `comap_exp_cobounded`

English:
theorem comap_exp_cobounded
  statement: comap exp (cobounded Complex) = comap re atTop
  proof: calc
    comap exp (cobounded Complex) = comap re (comap Real.exp atTop) := by
      simp only [← comap_norm_atTop, comap_comap, comp_def, norm_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]

@[simp]

中文:
定理 comap_exp_cobounded
  结论: comap exp (cobounded Complex) = comap re atTop
  证明: calc
    comap exp (cobounded Complex) = comap re (comap Real.exp atTop) := by
      simp only [← comap_norm_atTop, comap_comap, comp_def, norm_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]

@[simp]

Depends on / 依赖: Real.comap_exp_atTop, Real.exp, cobounded, comap_comap, comap_exp_atTop, comap_norm_atTop, comp_def, norm_exp
-/
theorem comap_exp_cobounded : comap exp (cobounded Complex) = comap re atTop :=
  calc
    comap exp (cobounded Complex) = comap re (comap Real.exp atTop) := by
      simp only [← comap_norm_atTop, comap_comap, comp_def, norm_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]

@[simp]
/--
theorem `comap_exp_nhds_zero` / 定理 `comap_exp_nhds_zero`

English:
theorem comap_exp_nhds_zero
  statement: comap exp (𝓝 0) = comap re atBot
  proof: calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      rw [← comap_norm_nhds_zero]; rw [comap_comap]; rw [Function.comp_def]
      simp_rw [norm_exp, comap_comap, Function.comp_def]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]

中文:
定理 comap_exp_nhds_zero
  结论: comap exp (𝓝 0) = comap re atBot
  证明: calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      rw [← comap_norm_nhds_zero]; rw [comap_comap]; rw [Function.comp_def]
      simp_rw [norm_exp, comap_comap, Function.comp_def]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]

Depends on / 依赖: Function, Function.comp_def, Real.comap_exp_nhds_zero, Real.exp, comap_comap, comap_exp_nhds_zero, comap_norm_nhds_zero, comp_def, norm_exp, simp_rw
-/
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot :=
  calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      rw [← comap_norm_nhds_zero]; rw [comap_comap]; rw [Function.comp_def]
      simp_rw [norm_exp, comap_comap, Function.comp_def]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]

/--
theorem `comap_exp_nhdsNE` / 定理 `comap_exp_nhdsNE`

English:
theorem comap_exp_nhdsNE
  statement: comap exp (𝓝[!=] 0) = comap re atBot
  proof: by
  have : (exp ⁻¹' {0})ᶜ = Set.univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]

中文:
定理 comap_exp_nhdsNE
  结论: comap exp (𝓝[!=] 0) = comap re atBot
  证明: by
  have : (exp ⁻¹' {0})ᶜ = Set.univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]

Depends on / 依赖: Set.univ, comap_exp_nhds_zero, eq_univ_of_forall, exp_ne_zero, nhdsWithin
-/
theorem comap_exp_nhdsNE : comap exp (𝓝[!=] 0) = comap re atBot := by
  have : (exp ⁻¹' {0})ᶜ = Set.univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]

/--
theorem `tendsto_exp_nhds_zero_iff` / 定理 `tendsto_exp_nhds_zero_iff`

English:
theorem tendsto_exp_nhds_zero_iff
  given: {α : Type*} {l : Filter α} {f : α -> Complex}
  proof: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
  rfl

中文:
定理 tendsto_exp_nhds_zero_iff
  条件: {α : 类型} {l : Filter α} {f : α -> Complex}
  证明: by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
  rfl

Depends on / 依赖: comap_exp_nhds_zero, comp_apply, simp_rw, tendsto_comap_iff
-/
theorem tendsto_exp_nhds_zero_iff {α : Type*} {l : Filter α} {f : α -> Complex} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
  rfl

/--
theorem `tendsto_exp_comap_re_atTop` / 定理 `tendsto_exp_comap_re_atTop`

English:
theorem tendsto_exp_comap_re_atTop
  statement: Tendsto exp (comap re atTop) (cobounded Complex)
  proof: comap_exp_cobounded ▸ tendsto_comap

中文:
定理 tendsto_exp_comap_re_atTop
  结论: Tendsto exp (comap re atTop) (cobounded Complex)
  证明: comap_exp_cobounded ▸ tendsto_comap

Depends on / 依赖: comap_exp_cobounded, tendsto_comap
-/
theorem tendsto_exp_comap_re_atTop : Tendsto exp (comap re atTop) (cobounded Complex) :=
  comap_exp_cobounded ▸ tendsto_comap

/--
theorem `tendsto_exp_comap_re_atBot` / 定理 `tendsto_exp_comap_re_atBot`

English:
theorem tendsto_exp_comap_re_atBot
  statement: Tendsto exp (comap re atBot) (𝓝 0)
  proof: comap_exp_nhds_zero ▸ tendsto_comap

中文:
定理 tendsto_exp_comap_re_atBot
  结论: Tendsto exp (comap re atBot) (𝓝 0)
  证明: comap_exp_nhds_zero ▸ tendsto_comap

Depends on / 依赖: comap_exp_nhds_zero, tendsto_comap
-/
theorem tendsto_exp_comap_re_atBot : Tendsto exp (comap re atBot) (𝓝 0) :=
  comap_exp_nhds_zero ▸ tendsto_comap

/--
theorem `tendsto_exp_comap_re_atBot_nhdsNE` / 定理 `tendsto_exp_comap_re_atBot_nhdsNE`

English:
theorem tendsto_exp_comap_re_atBot_nhdsNE
  statement: Tendsto exp (comap re atBot) (𝓝[!=] 0)
  proof: comap_exp_nhdsNE ▸ tendsto_comap

中文:
定理 tendsto_exp_comap_re_atBot_nhdsNE
  结论: Tendsto exp (comap re atBot) (𝓝[!=] 0)
  证明: comap_exp_nhdsNE ▸ tendsto_comap

Depends on / 依赖: comap_exp_nhdsNE, tendsto_comap
-/
theorem tendsto_exp_comap_re_atBot_nhdsNE : Tendsto exp (comap re atBot) (𝓝[!=] 0) :=
  comap_exp_nhdsNE ▸ tendsto_comap

end Complex

open Complex in
/--
lemma `HasSum.cexp` / 引理 `HasSum.cexp`

English:
lemma HasSum.cexp
  given: {ι : Type*} {f : ι -> Complex} {a : Complex} (h : HasSum f a)
  statement: HasProd (cexp ∘ f) (cexp a)
  proof: Filter.Tendsto.congr (fun s => exp_sum s f) Filter.Tendsto.cexp h

中文:
引理 HasSum.cexp
  条件: {ι : 类型} {f : ι -> Complex} {a : Complex} (h : HasSum f a)
  结论: HasProd (cexp ∘ f) (cexp a)
  证明: Filter.Tendsto.congr (fun s => exp_sum s f) Filter.Tendsto.cexp h

Depends on / 依赖: Filter, Filter.Tendsto.cexp, Filter.Tendsto.congr, Tendsto, exp_sum
-/
lemma HasSum.cexp {ι : Type*} {f : ι -> Complex} {a : Complex} (h : HasSum f a) : HasProd (cexp ∘ f) (cexp a) :=
Filter.Tendsto.congr (fun s => exp_sum s f) Filter.Tendsto.cexp h
