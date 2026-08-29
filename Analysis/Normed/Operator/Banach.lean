/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

@[expose] public section

open Function Metric Set Filter Finset Topology NNReal

open LinearMap (range ker)

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 ->+* 𝕜'}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E ->SL[σ] F)

namespace ContinuousLinearMap

/--
Definition of `NonlinearRightInverse` / `NonlinearRightInverse` 的定义

English:
structure NonlinearRightInverse
  parameters: where
  axioms and operations (4):
    - toFun : F -> E
    - nnnorm : Real>=0
    - bound' : forall y, ‖toFun y‖ <= nnnorm * ‖y‖
    - right_inv' : forall y, f (toFun y) = y

中文:
结构 NonlinearRightInverse
  参数: where
  公理与运算 (4 个):
    - toFun : F -> E
    - nnnorm : 实数>=0
    - bound' : 对任意 y, ‖toFun y‖ <= nnnorm * ‖y‖
    - right_inv' : 对任意 y, f (toFun y) = y
-/
structure NonlinearRightInverse where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : F -> E
  /-- The bound `C` so that `‖inverse x‖ ≤ C * ‖x‖` for all `x`. -/
  nnnorm : Real>=0
  bound' : forall y, ‖toFun y‖ <= nnnorm * ‖y‖
  right_inv' : forall y, f (toFun y) = y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (NonlinearRightInverse f) fun _ => F -> E
  body: ⟨fun fsymm => fsymm.toFun⟩

@[simp]

中文:
实例 :
  签名: CoeFun (NonlinearRightInverse f) fun _ => F -> E
  定义体: ⟨fun fsymm => fsymm.toFun⟩

@[simp]

Depends on / 依赖: fsymm.toFun
-/
instance : CoeFun (NonlinearRightInverse f) fun _ => F -> E :=
  ⟨fun fsymm => fsymm.toFun⟩

@[simp]
/--
theorem `NonlinearRightInverse.right_inv` / 定理 `NonlinearRightInverse.right_inv`

English:
theorem NonlinearRightInverse.right_inv
  given: {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F)
  proof: fsymm.right_inv' y

中文:
定理 NonlinearRightInverse.right_inv
  条件: {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F)
  证明: fsymm.right_inv' y

Depends on / 依赖: fsymm.right_inv, right_inv
-/
theorem NonlinearRightInverse.right_inv {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    f (fsymm y) = y :=
  fsymm.right_inv' y

/--
theorem `NonlinearRightInverse.bound` / 定理 `NonlinearRightInverse.bound`

English:
theorem NonlinearRightInverse.bound
  given: {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F)
  proof: fsymm.bound' y

中文:
定理 NonlinearRightInverse.bound
  条件: {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F)
  证明: fsymm.bound' y

Depends on / 依赖: fsymm.bound
-/
theorem NonlinearRightInverse.bound {f : E ->SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    ‖fsymm y‖ <= fsymm.nnnorm * ‖y‖ :=
  fsymm.bound' y

end ContinuousLinearMap

variable {σ' : 𝕜' ->+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ']

/--
Definition of `ContinuousLinearEquiv.toNonlinearRightInverse` / `ContinuousLinearEquiv.toNonlinearRightInverse` 的定义

English:
definition ContinuousLinearEquiv.toNonlinearRightInverse
  body: f.invFun
  nnnorm := ‖(f.symm : F ->SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F ->SL[σ'] E) _
  right_inv' := f.apply_symm_apply

中文:
定义 连续线性等价.toNonlinearRightInverse
  定义体: f.invFun
  nnnorm := ‖(f.symm : F ->SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F ->SL[σ'] E) _
  right_inv' := f.apply_symm_apply

Depends on / 依赖: f.invFun, invFun
-/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse
    [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E ->SL[σ] F) where
  toFun := f.invFun
  nnnorm := ‖(f.symm : F ->SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F ->SL[σ'] E) _
  right_inv' := f.apply_symm_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RingHomInvPair
  signature: σ' σ] (f
  body: ⟨f.toNonlinearRightInverse⟩

中文:
实例 [RingHomInvPair
  签名: σ' σ] (f
  定义体: ⟨f.toNonlinearRightInverse⟩

Depends on / 依赖: f.toNonlinearRightInverse, toNonlinearRightInverse
-/
noncomputable instance [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E ->SL[σ] F)) :=
  ⟨f.toNonlinearRightInverse⟩

/-! ### Proof of the Banach open mapping theorem -/


variable [CompleteSpace F]

namespace ContinuousLinearMap

include σ' in
/--
theorem `exists_approx_preimage_norm_le` / 定理 `exists_approx_preimage_norm_le`

English:
theorem exists_approx_preimage_norm_le
  given: (surj : Surjective f)
  proof: by
  have A : ⋃ n : Nat, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem

中文:
定理 存在_approx_preimage_norm_le
  条件: (surj : 满射 f)
  证明: by
  have A : ⋃ n : Nat, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem

Depends on / 依赖: Metric, Metric.mem_nh, Set.univ, Subset, Subset.antisymm, antisymm, closure, dist_eq_norm, exists_nat_gt, interior, isClosed_closure, mem_ball, mem_iUnion, mem_image, mem_interior_iff_mem_nhds, mem_nh, nonempty_interior_of_iUnion_of_closed, sub_zero, subset_closure, subset_univ
-/
theorem exists_approx_preimage_norm_le (surj : Surjective f) :
    exists C >= 0, forall y, exists x, dist (f x) y <= 1 / 2 * ‖y‖ ∧ ‖x‖ <= C * ‖y‖ := by
  have A : ⋃ n : Nat, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  have : exists (n : Nat) (x : _), x in interior (closure (f '' ball 0 n)) :=
    nonempty_interior_of_iUnion_of_closed (fun n => isClosed_closure) A
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at this
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hc' : 1 < ‖σ c‖ := by simp only [RingHomIsometric.norm_map, hc]
    rcases rescale_to_shell hc' (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y in ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball]; rw [dist_eq_norm]; rw [sub_zero] at hx₁
    have : a in ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball]; rw [dist_eq_norm]; rw [sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ <= 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ <= ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ <= 2 * δ := by grind [dist_eq_norm']
    have J : ‖f (σ' d⁻¹ • x) - y‖ <= 1 / 2 * ‖y‖ :=
      calc
        ‖f (σ' d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rwa [f.map_smulₛₗ _, inv_mul_cancel₀, one_smul, map_inv₀, map_inv₀,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ <= ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = 1 / 2 * ‖y‖ := by simp [δ, field]; norm_num
    rw [← dist_eq_norm] at J
    have K : ‖σ' d⁻¹ • x‖ <= (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖σ' d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, RingHomIsometric.norm_map, norm_inv]
        _ <= (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          gcongr
          · simpa using dinv
          · exact le_trans (norm_sub_le _ _) (by gcongr)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨σ' d⁻¹ • x, J, K⟩

variable [CompleteSpace E]

section
include σ'

/--
theorem `exists_preimage_norm_le` / 定理 `exists_preimage_norm_le`

English:
theorem exists_preimage_norm_le
  given: (surj : Surjective f)
  proof: by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate

中文:
定理 存在_preimage_norm_le
  条件: (surj : 满射 f)
  证明: by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate

Depends on / 依赖: exists_approx_preimage_norm_le
-/
theorem exists_preimage_norm_le (surj : Surjective f) :
    exists C > 0, forall y, exists x, f x = y ∧ ‖x‖ <= C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : forall y, ‖h y‖ <= 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm]; rw [dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : forall n : Nat, ‖h^[n] y‖ <= (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ']; rw [mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : forall n, ‖u n‖ <= (1 / 2) ^ n * (C * ‖y‖) := fun n => by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ <= C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ <= (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ <= ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ <= ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
sNu.tsum_le_tsum ule Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ <= 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : forall n : Nat, f (∑ i in Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i in Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i in Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  given: (surj : Surjective f)
  statement: IsOpenMap f
  proof: by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x 

中文:
定理 isOpenMap
  条件: (surj : 满射 f)
  结论: 是开映射 f
  证明: by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x 
-/
protected theorem isOpenMap (surj : Surjective f) : IsOpenMap f := by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x + w) = z := by rw [f.map_add, wim, fxy, add_sub_cancel]
  rw [← this]
  have : x + w in ball x ε :=
    calc
      dist (x + w) x = ‖w‖ := by
        simp
      _ <= C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ (ne_of_gt Cpos)
  exact Set.mem_image_of_mem _ (hε this)

/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  given: (surj : Surjective f)
  statement: IsQuotientMap f
  proof: (f.isOpenMap surj).isQuotientMap f.continuous surj

中文:
定理 isQuotientMap
  条件: (surj : 满射 f)
  结论: 是商映射 f
  证明: (f.isOpenMap surj).isQuotientMap f.continuous surj

Depends on / 依赖: continuous, f.continuous, f.isOpenMap, isOpenMap, isQuotientMap
-/
theorem isQuotientMap (surj : Surjective f) : IsQuotientMap f :=
  (f.isOpenMap surj).isQuotientMap f.continuous surj

end

/--
theorem `_root_.AffineMap.isOpenMap` / 定理 `_root_.AffineMap.isOpenMap`

English:
theorem _root_.AffineMap.isOpenMap
  statement: {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  proof: AffineMap.isOpenMap_linear_iff.mp
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)

中文:
定理 _root_.仿射映射.isOpenMap
  结论: {F : 类型} [赋范交换加群 F] [赋范空间 𝕜 F]
  证明: AffineMap.isOpenMap_linear_iff.mp
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)

Depends on / 依赖: AffineMap, AffineMap.continuous_linear_iff.mpr, AffineMap.isOpenMap_linear_iff.mp, ContinuousLinearMap, ContinuousLinearMap.isOpenMap, continuous_linear_iff, f.linear, f.linear_surjective_iff.mpr, isOpenMap, isOpenMap_linear_iff, linear, linear_surjective_iff
-/
theorem _root_.AffineMap.isOpenMap {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] {P Q : Type*} [MetricSpace P] [NormedAddTorsor E P] [MetricSpace Q]
    [NormedAddTorsor F Q] (f : P ->ᵃ[𝕜] Q) (hf : Continuous f) (surj : Surjective f) :
    IsOpenMap f :=
AffineMap.isOpenMap_linear_iff.mp
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)

/-! ### Applications of the Banach open mapping theorem -/

section
include σ'

/--
theorem `interior_preimage` / 定理 `interior_preimage`

English:
theorem interior_preimage
  given: (hsurj : Surjective f) (s : Set F)
  proof: ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

中文:
定理 interior_preimage
  条件: (hsurj : 满射 f) (s : 集合 F)
  证明: ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

Depends on / 依赖: continuous, f.continuous, f.isOpenMap, isOpenMap, preimage_interior_eq_interior_preimage
-/
theorem interior_preimage (hsurj : Surjective f) (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

/--
theorem `closure_preimage` / 定理 `closure_preimage`

English:
theorem closure_preimage
  given: (hsurj : Surjective f) (s : Set F)
  statement: closure (f ⁻¹' s) = f ⁻¹' closure s
  proof: ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

中文:
定理 closure_preimage
  条件: (hsurj : 满射 f) (s : 集合 F)
  结论: closure (f ⁻¹' s) = f ⁻¹' closure s
  证明: ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

Depends on / 依赖: continuous, f.continuous, f.isOpenMap, isOpenMap, preimage_closure_eq_closure_preimage
-/
theorem closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

/--
theorem `frontier_preimage` / 定理 `frontier_preimage`

English:
theorem frontier_preimage
  given: (hsurj : Surjective f) (s : Set F)
  proof: ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

中文:
定理 frontier_preimage
  条件: (hsurj : 满射 f) (s : 集合 F)
  证明: ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

Depends on / 依赖: continuous, f.continuous, f.isOpenMap, isOpenMap, preimage_frontier_eq_frontier_preimage
-/
theorem frontier_preimage (hsurj : Surjective f) (s : Set F) :
    frontier (f ⁻¹' s) = f ⁻¹' frontier s :=
  ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

/--
theorem `exists_nonlinearRightInverse_of_surjective` / 定理 `exists_nonlinearRightInverse_of_surjective`

English:
theorem exists_nonlinearRightInverse_of_surjective
  given: (f : E ->SL[σ] F) (hsurj : f.range = ⊤)
  proof: by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

中文:
定理 存在_nonlinearRightInverse_of_surjective
  条件: (f : E ->SL[σ] F) (hsurj : f.range = ⊤)
  证明: by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, exists_preimage_norm_le, hC.lt.le, nnnorm, range_eq_top, right_inv
-/
theorem exists_nonlinearRightInverse_of_surjective (f : E ->SL[σ] F) (hsurj : f.range = ⊤) :
    exists fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm := by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

end

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
noncomputable irreducible_def nonlinearRightInverseOfSurjective (f : E ->SL[σ] F)
  (hsurj : f.range = ⊤) : NonlinearRightInverse f :=
  Classical.choose (exists_nonlinearRightInverse_of_surjective f hsurj)

/--
theorem `nonlinearRightInverseOfSurjective_nnnorm_pos` / 定理 `nonlinearRightInverseOfSurjective_nnnorm_pos`

English:
theorem nonlinearRightInverseOfSurjective_nnnorm_pos
  given: (f : E ->SL[σ] F) (hsurj : f.range = ⊤)
  proof: by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

中文:
定理 nonlinearRightInverseOfSurjective_nnnorm_pos
  条件: (f : E ->SL[σ] F) (hsurj : f.range = ⊤)
  证明: by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_nonlinearRightInverse_of_surjective, nonlinearRightInverseOfSurjective
-/
theorem nonlinearRightInverseOfSurjective_nnnorm_pos (f : E ->SL[σ] F) (hsurj : f.range = ⊤) :
    0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm := by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

end ContinuousLinearMap

namespace LinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
@[continuity]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  given: (e : E ≃ₛₗ[σ] F) (h : Continuous e)
  statement: Continuous e.symm
  proof: by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

中文:
定理 continuous_symm
  条件: (e : E ≃ₛₗ[σ] F) (h : 连续 e)
  结论: 连续 e.symm
  证明: by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isOpenMap, coe_coe, continuous_def, e.coe_coe, e.image_eq_preimage_symm, e.surjective, image_eq_preimage_symm, isOpenMap, surjective
-/
theorem continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

/--
Definition of `toContinuousLinearEquivOfContinuous` / `toContinuousLinearEquivOfContinuous` 的定义

English:
definition toContinuousLinearEquivOfContinuous
  signature: (e : E ≃ₛₗ[σ] F) (h : Continuous e)
  body: { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]

中文:
定义 toContinuousLinearEquivOfContinuous
  签名: (e : E ≃ₛₗ[σ] F) (h : 连续 e)
  定义体: { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]

Depends on / 依赖: continuous_invFun, continuous_symm, continuous_toFun, e.continuous_symm
-/
def toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : E ≃SL[σ] F :=
  { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]
/--
theorem `coeFn_toContinuousLinearEquivOfContinuous` / 定理 `coeFn_toContinuousLinearEquivOfContinuous`

English:
theorem coeFn_toContinuousLinearEquivOfContinuous
  given: (e : E ≃ₛₗ[σ] F) (h : Continuous e)
  proof: rfl

@[simp]

中文:
定理 coeFn_toContinuousLinearEquivOfContinuous
  条件: (e : E ≃ₛₗ[σ] F) (h : 连续 e)
  证明: rfl

@[simp]
-/
theorem coeFn_toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h) = e :=
  rfl

@[simp]
/--
theorem `coeFn_toContinuousLinearEquivOfContinuous_symm` / 定理 `coeFn_toContinuousLinearEquivOfContinuous_symm`

English:
theorem coeFn_toContinuousLinearEquivOfContinuous_symm
  given: (e : E ≃ₛₗ[σ] F) (h : Continuous e)
  proof: rfl

中文:
定理 coeFn_toContinuousLinearEquivOfContinuous_symm
  条件: (e : E ≃ₛₗ[σ] F) (h : 连续 e)
  证明: rfl
-/
theorem coeFn_toContinuousLinearEquivOfContinuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E] [RingHomInvPair σ' σ] {f : E ->SL[σ] F}

/--
Definition of `equivRange` / `equivRange` 的定义

English:
definition equivRange
  signature: (hinj : Injective f) (hclo : IsClosed (range f))
  body: have : CompleteSpace f.range := hclo.completeSpace_coe
LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj)
    (f.continuous.codRestrict fun x => f.mem_range_self x).congr fun _ => rfl

@[simp]

中文:
定义 equivRange
  签名: (hinj : 单射 f) (hclo : 是闭集 (range f))
  定义体: have : CompleteSpace f.range := hclo.completeSpace_coe
LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj)
    (f.continuous.codRestrict fun x => f.mem_range_self x).congr fun _ => rfl

@[simp]

Depends on / 依赖: CompleteSpace, LinearEquiv, LinearEquiv.ofInjective, LinearEquiv.toContinuousLinearEquivOfContinuous, codRestrict, completeSpace_coe, continuous, f.continuous.codRestrict, f.mem_range_self, f.range, f.toLinearMap, hclo.completeSpace_coe, mem_range_self, ofInjective, toContinuousLinearEquivOfContinuous, toLinearMap
-/
noncomputable def equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] f.range :=
  have : CompleteSpace f.range := hclo.completeSpace_coe
LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj)
    (f.continuous.codRestrict fun x => f.mem_range_self x).congr fun _ => rfl

@[simp]
/--
theorem `coe_linearMap_equivRange` / 定理 `coe_linearMap_equivRange`

English:
theorem coe_linearMap_equivRange
  given: (hinj : Injective f) (hclo : IsClosed (range f))
  proof: rfl

@[simp]

中文:
定理 coe_linearMap_equivRange
  条件: (hinj : 单射 f) (hclo : 是闭集 (range f))
  证明: rfl

@[simp]
-/
theorem coe_linearMap_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    f.equivRange hinj hclo = f.rangeRestrict :=
  rfl

@[simp]
/--
theorem `coe_equivRange` / 定理 `coe_equivRange`

English:
theorem coe_equivRange
  given: (hinj : Injective f) (hclo : IsClosed (range f))
  proof: rfl

@[simp]

中文:
定理 coe_equivRange
  条件: (hinj : 单射 f) (hclo : 是闭集 (range f))
  证明: rfl

@[simp]
-/
theorem coe_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo : E -> f.range) = f.rangeRestrict :=
  rfl

@[simp]
/--
lemma `equivRange_symm_toLinearEquiv` / 引理 `equivRange_symm_toLinearEquiv`

English:
lemma equivRange_symm_toLinearEquiv
  given: (hinj : Injective f) (hclo : IsClosed (range f))
  proof: rfl

中文:
引理 equivRange_symm_toLinearEquiv
  条件: (hinj : 单射 f) (hclo : 是闭集 (range f))
  证明: rfl
-/
lemma equivRange_symm_toLinearEquiv (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo).toLinearEquiv.symm =
      (LinearEquiv.ofInjective f.toLinearMap hinj).symm := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `equivRange_symm_apply` / 引理 `equivRange_symm_apply`

English:
lemma equivRange_symm_apply
  statement: (hinj : Injective f) (hclo : IsClosed (range f))
  proof: by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

中文:
引理 equivRange_symm_apply
  结论: (hinj : 单射 f) (hclo : 是闭集 (range f))
  证明: by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.symm_apply_eq, Subtype, Subtype.ext_iff, ext_iff, symm_apply_eq
-/
lemma equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f))
    (x : E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x := by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

-- TODO: once mathlib has Fredholm operators, generalise the next four lemmas accordingly

/--
lemma `antilipschitz_of_injective_of_isClosed_range` / 引理 `antilipschitz_of_injective_of_isClosed_range`

English:
lemma antilipschitz_of_injective_of_isClosed_range
  statement: (f : E ->L[𝕜] F)
  proof: ⟨_, .comp (.subtype_coe (Set.range f)) (f.equivRange hf hf').antilipschitz⟩

中文:
引理 antilipschitz_of_injective_of_isClosed_range
  结论: (f : E ->L[𝕜] F)
  证明: ⟨_, .comp (.subtype_coe (Set.range f)) (f.equivRange hf hf').antilipschitz⟩

Depends on / 依赖: Set.range, antilipschitz, equivRange, f.equivRange, subtype_coe
-/
lemma antilipschitz_of_injective_of_isClosed_range (f : E ->L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : exists K, AntilipschitzWith K f :=
  ⟨_, .comp (.subtype_coe (Set.range f)) (f.equivRange hf hf').antilipschitz⟩

/--
Definition of `antilipschitzConstant_of_injective_of_isClosed_range` / `antilipschitzConstant_of_injective_of_isClosed_range` 的定义

English:
definition antilipschitzConstant_of_injective_of_isClosed_range
  signature: (f : E ->L[𝕜] F)
  body: Classical.choose (f.antilipschitz_of_injective_of_isClosed_range hf hf')

中文:
定义 antilipschitzConstant_of_injective_of_isClosed_range
  签名: (f : E ->L[𝕜] F)
  定义体: Classical.choose (f.antilipschitz_of_injective_of_isClosed_range hf hf')

Depends on / 依赖: Classical, Classical.choose, antilipschitz_of_injective_of_isClosed_range, f.antilipschitz_of_injective_of_isClosed_range
-/
noncomputable def antilipschitzConstant_of_injective_of_isClosed_range (f : E ->L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : Real>=0 :=
  Classical.choose (f.antilipschitz_of_injective_of_isClosed_range hf hf')

/--
lemma `antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range` / 引理 `antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range`

English:
lemma antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range
  statement: (f : E ->L[𝕜] F)
  proof: Classical.choose_spec (f.antilipschitz_of_injective_of_isClosed_range hf hf')

中文:
引理 antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range
  结论: (f : E ->L[𝕜] F)
  证明: Classical.choose_spec (f.antilipschitz_of_injective_of_isClosed_range hf hf')

Depends on / 依赖: Classical, Classical.choose_spec, antilipschitz_of_injective_of_isClosed_range, choose_spec, f.antilipschitz_of_injective_of_isClosed_range
-/
lemma antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range (f : E ->L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) :
    AntilipschitzWith (f.antilipschitzConstant_of_injective_of_isClosed_range hf hf') f :=
  Classical.choose_spec (f.antilipschitz_of_injective_of_isClosed_range hf hf')

/--
lemma `isClosed_range_iff_antilipschitz_of_injective` / 引理 `isClosed_range_iff_antilipschitz_of_injective`

English:
lemma isClosed_range_iff_antilipschitz_of_injective
  statement: (f : E ->L[𝕜] F)
  proof: by
  refine ⟨fun h => f.antilipschitz_of_injective_of_isClosed_range hf h, fun h => ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

中文:
引理 isClosed_range_iff_antilipschitz_of_injective
  结论: (f : E ->L[𝕜] F)
  证明: by
  refine ⟨fun h => f.antilipschitz_of_injective_of_isClosed_range hf h, fun h => ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

Depends on / 依赖: antilipschitz_of_injective_of_isClosed_range, f.antilipschitz_of_injective_of_isClosed_range, f.uniformContinuous, isClosed_range, uniformContinuous
-/
lemma isClosed_range_iff_antilipschitz_of_injective (f : E ->L[𝕜] F)
    (hf : Injective f) : IsClosed (Set.range f) ↔ exists K, AntilipschitzWith K f := by
  refine ⟨fun h => f.antilipschitz_of_injective_of_isClosed_range hf h, fun h => ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

/--
Definition of `leftInverse_of_injective_of_isClosed_range` / `leftInverse_of_injective_of_isClosed_range` 的定义

English:
definition leftInverse_of_injective_of_isClosed_range
  body: letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, x, rfl⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_

中文:
定义 leftInverse_of_injective_of_isClosed_range
  定义体: letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, x, rfl⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, LinearMap.mkContinuous, antilipschitzConstant_of_injective_of_isClosed_range, antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range, convert, dist_zero_right, f.antilipschitzConstant_of_injective_of_isClosed_range, f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range, f.rangeRestrict.leftInverse, f.rangeRestrict.leftInverse_apply_of_inj, hfK.le_mul_dist, ker_codRestrict, ker_eq_bot, le_mul_dist, leftInverse, leftInverse_apply_of_inj, map_zero, mkContinuous, rangeRestrict
-/
noncomputable def leftInverse_of_injective_of_isClosed_range
    (f : E ->L[𝕜] F) (hf : Injective f) (hf' : IsClosed (range f)) : f.range ->L[𝕜] E :=
  letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, x, rfl⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_zero_right, map_zero] at aux
    convert! aux
    exact f.rangeRestrict.leftInverse_apply_of_inj
      (by rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf) x)

end

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  body: (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
    (by exact f.continuous)

@[simp]

中文:
定义 ofBijective
  签名: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  定义体: (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
    (by exact f.continuous)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.ker_eq_bot.mp, LinearMap.range_eq_top.mp, ker_eq_bot, ofBijective, range_eq_top, toContinuousLinearEquivOfContinuous
-/
noncomputable def ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
    (by exact f.continuous)

@[simp]
/--
theorem `coeFn_ofBijective` / 定理 `coeFn_ofBijective`

English:
theorem coeFn_ofBijective
  given: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  proof: rfl

中文:
定理 coeFn_ofBijective
  条件: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  证明: rfl
-/
theorem coeFn_ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ⇑(ofBijective f hinj hsurj) = f :=
  rfl

/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 coe_ofBijective
  条件: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  证明: by
  ext
  rfl

@[simp]
-/
theorem coe_ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ↑(ofBijective f hinj hsurj) = f := by
  ext
  rfl

@[simp]
/--
theorem `ofBijective_symm_apply_apply` / 定理 `ofBijective_symm_apply_apply`

English:
theorem ofBijective_symm_apply_apply
  statement: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  proof: (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]

中文:
定理 ofBijective_symm_apply_apply
  结论: (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
  证明: (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]

Depends on / 依赖: ofBijective, symm_apply_apply
-/
theorem ofBijective_symm_apply_apply (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
    (x : E) : (ofBijective f hinj hsurj).symm (f x) = x :=
  (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]
/--
theorem `ofBijective_apply_symm_apply` / 定理 `ofBijective_apply_symm_apply`

English:
theorem ofBijective_apply_symm_apply
  statement: (f : E ->SL[σ] F) (hinj : f.ker = ⊥)
  proof: (ofBijective f hinj hsurj).apply_symm_apply y

中文:
定理 ofBijective_apply_symm_apply
  结论: (f : E ->SL[σ] F) (hinj : f.ker = ⊥)
  证明: (ofBijective f hinj hsurj).apply_symm_apply y

Depends on / 依赖: apply_symm_apply, ofBijective
-/
theorem ofBijective_apply_symm_apply (f : E ->SL[σ] F) (hinj : f.ker = ⊥)
    (hsurj : f.range = ⊤) (y : F) : f ((ofBijective f hinj hsurj).symm y) = y :=
  (ofBijective f hinj hsurj).apply_symm_apply y

/--
lemma `_root_.ContinuousLinearMap.isUnit_iff_bijective` / 引理 `_root_.ContinuousLinearMap.isUnit_iff_bijective`

English:
lemma _root_.ContinuousLinearMap.isUnit_iff_bijective
  given: {f : E ->L[𝕜] E}
  proof: by
  constructor
  · rintro ⟨f, rfl⟩
.bijective exact ofUnit f
· refine fun h => ⟨toUnit .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]

中文:
引理 _root_.连续线性映射.isUnit_iff_bijective
  条件: {f : E ->L[𝕜] E}
  证明: by
  constructor
  · rintro ⟨f, rfl⟩
.bijective exact ofUnit f
· refine fun h => ⟨toUnit .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, LinearMap.range_eq_top, bijective, coe_coe, f.coe_coe, ker_eq_bot, ofBijective, ofUnit, range_eq_top, toUnit
-/
lemma _root_.ContinuousLinearMap.isUnit_iff_bijective {f : E ->L[𝕜] E} :
    IsUnit f ↔ Bijective f := by
  constructor
  · rintro ⟨f, rfl⟩
.bijective exact ofUnit f
· refine fun h => ⟨toUnit .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E]

/--
theorem `isUnit_iff_isUnit_toLinearMap` / 定理 `isUnit_iff_isUnit_toLinearMap`

English:
theorem isUnit_iff_isUnit_toLinearMap
  given: {f : E ->L[𝕜] E}
  proof: f.isUnit_iff_bijective.trans (Module.End.isUnit_iff _).symm

中文:
定理 isUnit_iff_isUnit_toLinearMap
  条件: {f : E ->L[𝕜] E}
  证明: f.isUnit_iff_bijective.trans (Module.End.isUnit_iff _).symm

Depends on / 依赖: Module, Module.End.isUnit_iff, f.isUnit_iff_bijective.trans, isUnit_iff, isUnit_iff_bijective
-/
theorem isUnit_iff_isUnit_toLinearMap {f : E ->L[𝕜] E} :
    IsUnit f ↔ IsUnit (f : E ->ₗ[𝕜] E) :=
  f.isUnit_iff_bijective.trans (Module.End.isUnit_iff _).symm

/--
theorem `spectrum_eq` / 定理 `spectrum_eq`

English:
theorem spectrum_eq
  given: {f : E ->L[𝕜] E}
  proof: by
  ext μ
  rw [spectrum.mem_iff]; rw [spectrum.mem_iff]; rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  rfl

中文:
定理 spectrum_eq
  条件: {f : E ->L[𝕜] E}
  证明: by
  ext μ
  rw [spectrum.mem_iff]; rw [spectrum.mem_iff]; rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  rfl

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, isUnit_iff_isUnit_toLinearMap, mem_iff, spectrum, spectrum.mem_iff
-/
theorem spectrum_eq {f : E ->L[𝕜] E} :
    spectrum 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜 E) := by
  ext μ
  rw [spectrum.mem_iff]; rw [spectrum.mem_iff]; rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  rfl

/--
Definition of `coprodSubtypeLEquivOfIsCompl` / `coprodSubtypeLEquivOfIsCompl` 的定义

English:
definition coprodSubtypeLEquivOfIsCompl
  signature: {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  body: ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · simp [hker]
      · simp [h.disjoint])
    (by simp [LinearMap.range_coprod, h.sup_eq_top])

中文:
定义 coprodSubtypeLEquivOfIsCompl
  签名: {F : 类型} [赋范交换加群 F] [赋范空间 𝕜 F]
  定义体: ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · simp [hker]
      · simp [h.disjoint])
    (by simp [LinearMap.range_coprod, h.sup_eq_top])

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofBijective, G.subtypeL, LinearMap, LinearMap.range_coprod, coprod, disjoint, f.coprod, h.disjoint, h.sup_eq_top, ker_coprod_of_disjoint_range, ofBijective, range_coprod, subtypeL, sup_eq_top
-/
noncomputable def coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (f : E ->L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · simp [hker]
      · simp [h.disjoint])
    (by simp [LinearMap.range_coprod, h.sup_eq_top])

/--
theorem `range_eq_map_coprodSubtypeLEquivOfIsCompl` / 定理 `range_eq_map_coprodSubtypeLEquivOfIsCompl`

English:
theorem range_eq_map_coprodSubtypeLEquivOfIsCompl
  statement: {F : Type*} [NormedAddCommGroup F]
  proof: by
  rw [coprodSubtypeLEquivOfIsCompl]; rw [← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]; rw [ContinuousLinearEquiv.coe_ofBijective]; rw [coe_coprod]; rw [LinearMap.coprod_map_prod]; rw [Submodule.map_bot]; rw [sup_bot_eq]; rw [Submodule.map_top]

中文:
定理 range_eq_map_coprodSubtypeLEquivOfIsCompl
  结论: {F : 类型} [赋范交换加群 F]
  证明: by
  rw [coprodSubtypeLEquivOfIsCompl]; rw [← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]; rw [ContinuousLinearEquiv.coe_ofBijective]; rw [coe_coprod]; rw [LinearMap.coprod_map_prod]; rw [Submodule.map_bot]; rw [sup_bot_eq]; rw [Submodule.map_top]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_ofBijective, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearMap, LinearMap.coprod_map_prod, Submodule, Submodule.map_bot, Submodule.map_top, coe_coprod, coe_ofBijective, coprodSubtypeLEquivOfIsCompl, coprod_map_prod, map_bot, map_top, sup_bot_eq, toLinearMap_toContinuousLinearMap
-/
theorem range_eq_map_coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) :
    f.range =
      ((⊤ : Submodule 𝕜 E).prod (⊥ : Submodule 𝕜 G)).map
        (f.coprodSubtypeLEquivOfIsCompl h hker : E × G ->ₗ[𝕜] F) := by
  rw [coprodSubtypeLEquivOfIsCompl]; rw [← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]; rw [ContinuousLinearEquiv.coe_ofBijective]; rw [coe_coprod]; rw [LinearMap.coprod_map_prod]; rw [Submodule.map_bot]; rw [sup_bot_eq]; rw [Submodule.map_top]

/--
theorem `closed_complemented_range_of_isCompl_of_ker_eq_bot` / 定理 `closed_complemented_range_of_isCompl_of_ker_eq_bot`

English:
theorem closed_complemented_range_of_isCompl_of_ker_eq_bot
  statement: {F : Type*} [NormedAddCommGroup F]
  proof: by
  have : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

中文:
定理 closed_complemented_range_of_isCompl_of_ker_eq_bot
  结论: {F : 类型} [赋范交换加群 F]
  证明: by
  have : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

Depends on / 依赖: CompleteSpace, completeSpace_coe, coprodSubtypeLEquivOfIsCompl, g.toHomeomorph.isClosed_image, hG.completeSpace_coe, isClosed_image, isClosed_singleton, isClosed_univ, isClosed_univ.prod, range_eq_map_coprodSubtypeLEquivOfIsCompl, toHomeomorph
-/
theorem closed_complemented_range_of_isCompl_of_ker_eq_bot {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) (G : Submodule 𝕜 F)
    (h : IsCompl f.range G) (hG : IsClosed (G : Set F)) (hker : f.ker = ⊥) :
    IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

end ContinuousLinearMap

section ClosedGraphThm

variable [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (g : E ->ₗ[𝕜] F)

/--
theorem `LinearMap.continuous_of_isClosed_graph` / 定理 `LinearMap.continuous_of_isClosed_graph`

English:
theorem LinearMap.continuous_of_isClosed_graph
  given: (hg : IsClosed (g.graph : Set <| E × F))
  proof: by
  let : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E ->ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_r

中文:
定理 线性映射.continuous_of_isClosed_graph
  条件: (hg : 是闭集 (g.graph : 集合 <| E × F))
  证明: by
  let : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E ->ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_r

Depends on / 依赖: CompleteSpace, Function, Function.LeftInverse, LeftInverse, LinearEquiv, LinearEquiv.ofEq, LinearEquiv.ofLeftInverse, LinearMap, LinearMap.id.prod, Prod.fst, completeSpace_coe_iff_isComplete, completeSpace_coe_iff_isComplete.mpr, continuous, continuous_subtype_val, continuous_subtype_val.comp, continuous_subtype_val.fst, g.graph, g.graph_eq_range_prod.symm, graph_eq_range_prod, hg.isComplete
-/
theorem LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    Continuous g := by
  let : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E ->ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E :=
    φ.symm.toContinuousLinearEquivOfContinuous continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/--
theorem `LinearMap.continuous_of_seq_closed_graph` / 定理 `LinearMap.continuous_of_seq_closed_graph`

English:
theorem LinearMap.continuous_of_seq_closed_graph
  proof: by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

中文:
定理 线性映射.continuous_of_seq_closed_graph
  证明: by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

Depends on / 依赖: IsSeqClosed, IsSeqClosed.isClosed, Prod.fst, Prod.snd, continuous_fst, continuous_fst.tendsto, continuous_of_isClosed_graph, continuous_snd, continuous_snd.tendsto, g.continuous_of_isClosed_graph, isClosed, tendsto
-/
theorem LinearMap.continuous_of_seq_closed_graph
    (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) :
    Continuous g := by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

variable {g}

namespace ContinuousLinearMap

/--
Definition of `ofIsClosedGraph` / `ofIsClosedGraph` 的定义

English:
definition ofIsClosedGraph
  signature: (hg : IsClosed (g.graph : Set <| E × F))
  body: g
  cont := g.continuous_of_isClosed_graph hg

@[simp]

中文:
定义 ofIsClosedGraph
  签名: (hg : 是闭集 (g.graph : 集合 <| E × F))
  定义体: g
  cont := g.continuous_of_isClosed_graph hg

@[simp]
-/
def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E ->L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_isClosed_graph hg

@[simp]
/--
theorem `coeFn_ofIsClosedGraph` / 定理 `coeFn_ofIsClosedGraph`

English:
theorem coeFn_ofIsClosedGraph
  given: (hg : IsClosed (g.graph : Set <| E × F))
  proof: rfl

中文:
定理 coeFn_ofIsClosedGraph
  条件: (hg : 是闭集 (g.graph : 集合 <| E × F))
  证明: rfl
-/
theorem coeFn_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ⇑(ContinuousLinearMap.ofIsClosedGraph hg) = g :=
  rfl

/--
theorem `coe_ofIsClosedGraph` / 定理 `coe_ofIsClosedGraph`

English:
theorem coe_ofIsClosedGraph
  given: (hg : IsClosed (g.graph : Set <| E × F))
  proof: by
  ext
  rfl

中文:
定理 coe_ofIsClosedGraph
  条件: (hg : 是闭集 (g.graph : 集合 <| E × F))
  证明: by
  ext
  rfl
-/
theorem coe_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ↑(ContinuousLinearMap.ofIsClosedGraph hg) = g := by
  ext
  rfl

/--
Definition of `ofSeqClosedGraph` / `ofSeqClosedGraph` 的定义

English:
definition ofSeqClosedGraph
  body: g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]

中文:
定义 ofSeqClosedGraph
  定义体: g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
-/
def ofSeqClosedGraph
    (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) :
    E ->L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
/--
theorem `coeFn_ofSeqClosedGraph` / 定理 `coeFn_ofSeqClosedGraph`

English:
theorem coeFn_ofSeqClosedGraph
  proof: rfl

中文:
定理 coeFn_ofSeqClosedGraph
  证明: rfl
-/
theorem coeFn_ofSeqClosedGraph
    (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) :
    ⇑(ContinuousLinearMap.ofSeqClosedGraph hg) = g :=
  rfl

/--
theorem `coe_ofSeqClosedGraph` / 定理 `coe_ofSeqClosedGraph`

English:
theorem coe_ofSeqClosedGraph
  proof: by
  ext
  rfl

中文:
定理 coe_ofSeqClosedGraph
  证明: by
  ext
  rfl
-/
theorem coe_ofSeqClosedGraph
    (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) :
    ↑(ContinuousLinearMap.ofSeqClosedGraph hg) = g := by
  ext
  rfl

end ContinuousLinearMap

end ClosedGraphThm

section BijectivityCriteria

namespace ContinuousLinearMap

variable {σ : 𝕜 ->+* 𝕜'} {σ' : 𝕜' ->+* 𝕜} [RingHomInvPair σ σ']
variable {F : Type u_4} [NormedAddCommGroup F] [NormedSpace 𝕜' F]
variable [CompleteSpace E]

/--
lemma `closed_range_of_antilipschitz` / 引理 `closed_range_of_antilipschitz`

English:
lemma closed_range_of_antilipschitz
  given: {f : E ->SL[σ] F} {c : Real>=0} (hf : AntilipschitzWith c f)
  proof: SetLike.ext'_iff.mpr (hf.isClosed_range f.uniformContinuous).closure_eq

中文:
引理 closed_range_of_antilipschitz
  条件: {f : E ->SL[σ] F} {c : 实数>=0} (hf : AntilipschitzWith c f)
  证明: SetLike.ext'_iff.mpr (hf.isClosed_range f.uniformContinuous).closure_eq

Depends on / 依赖: SetLike, SetLike.ext, _iff, _iff.mpr, closure_eq, f.uniformContinuous, hf.isClosed_range, isClosed_range, uniformContinuous
-/
lemma closed_range_of_antilipschitz {f : E ->SL[σ] F} {c : Real>=0} (hf : AntilipschitzWith c f) :
    f.range.topologicalClosure = f.range :=
SetLike.ext'_iff.mpr (hf.isClosed_range f.uniformContinuous).closure_eq

variable [CompleteSpace F]

/--
lemma `_root_.AntilipschitzWith.completeSpace_range_clm` / 引理 `_root_.AntilipschitzWith.completeSpace_range_clm`

English:
lemma _root_.AntilipschitzWith.completeSpace_range_clm
  statement: {f : E ->SL[σ] F} {c : Real>=0}
  proof: IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

中文:
引理 _root_.AntilipschitzWith.completeSpace_range_clm
  结论: {f : E ->SL[σ] F} {c : 实数>=0}
  证明: IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

Depends on / 依赖: IsClosed, IsClosed.completeSpace_coe, completeSpace_coe, f.uniformContinuous, hf.isClosed_range, isClosed_range, uniformContinuous
-/
lemma _root_.AntilipschitzWith.completeSpace_range_clm {f : E ->SL[σ] F} {c : Real>=0}
    (hf : AntilipschitzWith c f) : CompleteSpace f.range :=
  IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

variable [RingHomInvPair σ' σ] [RingHomIsometric σ] [RingHomIsometric σ']

open Function
/--
lemma `bijective_iff_dense_range_and_antilipschitz` / 引理 `bijective_iff_dense_range_and_antilipschitz`

English:
lemma bijective_iff_dense_range_and_antilipschitz
  given: (f : E ->SL[σ] F)
  proof: by
  refine ⟨fun h => ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ => ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using! h.2.denseRange.closure_eq
  case anti =>
.antilipschitz⟩ <;> refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq

中文:
引理 bijective_iff_dense_range_and_antilipschitz
  条件: (f : E ->SL[σ] F)
  证明: by
  refine ⟨fun h => ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ => ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using! h.2.denseRange.closure_eq
  case anti =>
.antilipschitz⟩ <;> refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofBijective, LinearMap, LinearMap.ker_eq_bot, LinearMap.range_eq_top, SetLike, SetLike.ext, _iff, antilipschitz, closed_range_of_antilipschitz, closure_eq, coe_coe, denseRange, denseRange.closure_eq, eq_top, f.coe_coe, hf.injective, injective, ker_eq_bot, ofBijective
-/
lemma bijective_iff_dense_range_and_antilipschitz (f : E ->SL[σ] F) :
    Bijective f ↔ f.range.topologicalClosure = ⊤ ∧ exists c, AntilipschitzWith c f := by
  refine ⟨fun h => ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ => ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using! h.2.denseRange.closure_eq
  case anti =>
.antilipschitz⟩ <;> refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]
  case surj => rwa [← f.coe_coe, ← LinearMap.range_eq_top, ← closed_range_of_antilipschitz hf]

end ContinuousLinearMap

end BijectivityCriteria
