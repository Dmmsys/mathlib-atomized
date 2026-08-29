/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Properties about the powers of the norm

In this file we prove that `x ↦ ‖x‖ ^ p` is continuously differentiable for
an inner product space and for a real number `p > 1`.

## TODO
* `x ↦ ‖x‖ ^ p` should be `C^n` for `p > n`.

-/

public section

section ContDiffNormPow

open Asymptotics Real Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]

/--
theorem `hasFDerivAt_norm_rpow` / 定理 `hasFDerivAt_norm_rpow`

English:
theorem hasFDerivAt_norm_rpow
  given: (x : E) {p : Real} (hp : 1 < p)
  proof: by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, map_zero, smul_zero]
    have h2p : 0 < p - 1 := sub_pos.mpr hp
    refine .of_isLittleO ?_
    calc (fun x : E => ‖x‖ ^ p - ‖(0 : E)‖ ^ p - 0)
        = (fun x : E => ‖x‖ ^ p) := by simp [zero_lt_one.trans hp |>.ne']
      _ = (fun x : E => ‖x‖ * ‖x‖ ^ (p - 1)) := by
          ext x
          rw [← rpow_one_add' (norm_nonneg x) (by positivity)]
          ring_nf
      _ =o[𝓝 0] (fun x : E => ‖x‖ * 1) := by
refine (isBigO_refl _ _).mul_isLittleO (isLittleO_const_iff <| by simp).mpr ?_
.tendsto convert! continuousAt_id.norm.rpow_const (.inr h2p.le)
        simp [h2p.ne']
      _ =O[𝓝 0] (fun (x : E) => x - 0) := by
        simp_rw [mul_one, isBigO_norm_left (f' := fun x => x), sub_zero, isBigO_refl]
  · apply HasStrictFDerivAt.hasFDerivAt
    convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
    simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul Real, smul_smul]
    ring_nf

中文:
定理 hasFDerivAt_norm_rpow
  条件: (x : E) {p : 实数} (hp : 1 < p)
  证明: by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, map_zero, smul_zero]
    have h2p : 0 < p - 1 := sub_pos.mpr hp
    refine .of_isLittleO ?_
    calc (fun x : E => ‖x‖ ^ p - ‖(0 : E)‖ ^ p - 0)
        = (fun x : E => ‖x‖ ^ p) := by simp [zero_lt_one.trans hp |>.ne']
      _ = (fun x : E => ‖x‖ * ‖x‖ ^ (p - 1)) := by
          ext x
          rw [← rpow_one_add' (norm_nonneg x) (by positivity)]
          ring_nf
      _ =o[𝓝 0] (fun x : E => ‖x‖ * 1) := by
refine (isBigO_refl _ _).mul_isLittleO (isLittleO_const_iff <| by simp).mpr ?_
.tendsto convert! continuousAt_id.norm.rpow_const (.inr h2p.le)
        simp [h2p.ne']
      _ =O[𝓝 0] (fun (x : E) => x - 0) := by
        simp_rw [mul_one, isBigO_norm_left (f' := fun x => x), sub_zero, isBigO_refl]
  · apply HasStrictFDerivAt.hasFDerivAt
    convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
    simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul Real, smul_smul]
    ring_nf

Depends on / 依赖: convert, isBigO_refl, isLittleO_const_iff, map_zero, mul_isLittleO, norm_nonneg, norm_zero, of_isLittleO, ring_nf, rpow_one_add, smul_zero, sub_pos, sub_pos.mpr, tendsto, zero_lt_one, zero_lt_one.trans
-/
theorem hasFDerivAt_norm_rpow (x : E) {p : Real} (hp : 1 < p) :
    HasFDerivAt (fun x : E => ‖x‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL Real x) x := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, map_zero, smul_zero]
    have h2p : 0 < p - 1 := sub_pos.mpr hp
    refine .of_isLittleO ?_
    calc (fun x : E => ‖x‖ ^ p - ‖(0 : E)‖ ^ p - 0)
        = (fun x : E => ‖x‖ ^ p) := by simp [zero_lt_one.trans hp |>.ne']
      _ = (fun x : E => ‖x‖ * ‖x‖ ^ (p - 1)) := by
          ext x
          rw [← rpow_one_add' (norm_nonneg x) (by positivity)]
          ring_nf
      _ =o[𝓝 0] (fun x : E => ‖x‖ * 1) := by
refine (isBigO_refl _ _).mul_isLittleO (isLittleO_const_iff <| by simp).mpr ?_
.tendsto convert! continuousAt_id.norm.rpow_const (.inr h2p.le)
        simp [h2p.ne']
      _ =O[𝓝 0] (fun (x : E) => x - 0) := by
        simp_rw [mul_one, isBigO_norm_left (f' := fun x => x), sub_zero, isBigO_refl]
  · apply HasStrictFDerivAt.hasFDerivAt
    convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
    simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul Real, smul_smul]
    ring_nf

/--
theorem `differentiable_norm_rpow` / 定理 `differentiable_norm_rpow`

English:
theorem differentiable_norm_rpow
  given: {p : Real} (hp : 1 < p)
  proof: .differentiableAt fun x => hasFDerivAt_norm_rpow x hp

中文:
定理 differentiable_norm_rpow
  条件: {p : 实数} (hp : 1 < p)
  证明: .differentiableAt fun x => hasFDerivAt_norm_rpow x hp

Depends on / 依赖: differentiableAt, hasFDerivAt_norm_rpow
-/
theorem differentiable_norm_rpow {p : Real} (hp : 1 < p) :
    Differentiable Real (fun x : E => ‖x‖ ^ p) :=
.differentiableAt fun x => hasFDerivAt_norm_rpow x hp

/--
theorem `hasDerivAt_norm_rpow` / 定理 `hasDerivAt_norm_rpow`

English:
theorem hasDerivAt_norm_rpow
  given: (x : Real) {p : Real} (hp : 1 < p)
  proof: by
.hasDerivAt; simp convert hasFDerivAt_norm_rpow x hp

中文:
定理 hasDerivAt_norm_rpow
  条件: (x : 实数) {p : 实数} (hp : 1 < p)
  证明: by
.hasDerivAt; simp convert hasFDerivAt_norm_rpow x hp

Depends on / 依赖: convert, hasDerivAt, hasFDerivAt_norm_rpow
-/
theorem hasDerivAt_norm_rpow (x : Real) {p : Real} (hp : 1 < p) :
    HasDerivAt (fun x : Real => ‖x‖ ^ p) (p * ‖x‖ ^ (p - 2) * x) x := by
.hasDerivAt; simp convert hasFDerivAt_norm_rpow x hp

/--
theorem `hasDerivAt_abs_rpow` / 定理 `hasDerivAt_abs_rpow`

English:
theorem hasDerivAt_abs_rpow
  given: (x : Real) {p : Real} (hp : 1 < p)
  proof: by
  simpa using hasDerivAt_norm_rpow x hp

中文:
定理 hasDerivAt_abs_rpow
  条件: (x : 实数) {p : 实数} (hp : 1 < p)
  证明: by
  simpa using hasDerivAt_norm_rpow x hp

Depends on / 依赖: hasDerivAt_norm_rpow
-/
theorem hasDerivAt_abs_rpow (x : Real) {p : Real} (hp : 1 < p) :
    HasDerivAt (fun x : Real => |x| ^ p) (p * |x| ^ (p - 2) * x) x := by
  simpa using hasDerivAt_norm_rpow x hp

/--
theorem `fderiv_norm_rpow` / 定理 `fderiv_norm_rpow`

English:
theorem fderiv_norm_rpow
  given: (x : E) {p : Real} (hp : 1 < p)
  proof: .fderiv hasFDerivAt_norm_rpow x hp

中文:
定理 fderiv_norm_rpow
  条件: (x : E) {p : 实数} (hp : 1 < p)
  证明: .fderiv hasFDerivAt_norm_rpow x hp

Depends on / 依赖: fderiv, hasFDerivAt_norm_rpow
-/
theorem fderiv_norm_rpow (x : E) {p : Real} (hp : 1 < p) :
    fderiv Real (fun x => ‖x‖ ^ p) x = (p * ‖x‖ ^ (p - 2)) • innerSL Real x :=
.fderiv hasFDerivAt_norm_rpow x hp

/--
theorem `Differentiable.fderiv_norm_rpow` / 定理 `Differentiable.fderiv_norm_rpow`

English:
theorem Differentiable.fderiv_norm_rpow
  statement: {f : F -> E} (hf : Differentiable Real f)
  proof: .fderiv .comp x (hf x).hasFDerivAt hasFDerivAt_norm_rpow (f x) hp

中文:
定理 可微.fderiv_norm_rpow
  结论: {f : F -> E} (hf : 可微 实数 f)
  证明: .fderiv .comp x (hf x).hasFDerivAt hasFDerivAt_norm_rpow (f x) hp

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt_norm_rpow
-/
theorem Differentiable.fderiv_norm_rpow {f : F -> E} (hf : Differentiable Real f)
    {x : F} {p : Real} (hp : 1 < p) :
    fderiv Real (fun x => ‖f x‖ ^ p) x =
    (p * ‖f x‖ ^ (p - 2)) • (innerSL Real (f x)).comp (fderiv Real f x) :=
.fderiv .comp x (hf x).hasFDerivAt hasFDerivAt_norm_rpow (f x) hp

/--
theorem `norm_fderiv_norm_rpow_le` / 定理 `norm_fderiv_norm_rpow_le`

English:
theorem norm_fderiv_norm_rpow_le
  statement: {f : F -> E} (hf : Differentiable Real f) {x : F}
  proof: by
  rw [hf.fderiv_norm_rpow hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc]
  gcongr _ * ?_
  refine mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le ..) (by positivity)
.trans_eq ?_
  rw [innerSL_apply_norm]; rw [← mul_assoc]; rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

中文:
定理 norm_fderiv_norm_rpow_le
  结论: {f : F -> E} (hf : 可微 实数 f) {x : F}
  证明: by
  rw [hf.fderiv_norm_rpow hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc]
  gcongr _ * ?_
  refine mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le ..) (by positivity)
.trans_eq ?_
  rw [innerSL_apply_norm]; rw [← mul_assoc]; rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_comp_le, Real.rpow_add_one, abs_eq_self, abs_eq_self.mpr, fderiv_norm_rpow, hf.fderiv_norm_rpow, hp.le, innerSL_apply_norm, mul_assoc, mul_le_mul_of_nonneg_left, norm_eq_abs, norm_mul, norm_nonneg, norm_norm, norm_rpow_of_nonneg, norm_smul, opNorm_comp_le, ring_nf, rpow_add_one
-/
theorem norm_fderiv_norm_rpow_le {f : F -> E} (hf : Differentiable Real f) {x : F}
    {p : Real} (hp : 1 < p) :
    ‖fderiv Real (fun x => ‖f x‖ ^ p) x‖ <= p * ‖f x‖ ^ (p - 1) * ‖fderiv Real f x‖ := by
  rw [hf.fderiv_norm_rpow hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc]
  gcongr _ * ?_
  refine mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le ..) (by positivity)
.trans_eq ?_
  rw [innerSL_apply_norm]; rw [← mul_assoc]; rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

/--
theorem `norm_fderiv_norm_id_rpow` / 定理 `norm_fderiv_norm_id_rpow`

English:
theorem norm_fderiv_norm_id_rpow
  given: (x : E) {p : Real} (hp : 1 < p)
  proof: by
  rw [fderiv_norm_rpow x hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc, innerSL_apply_norm]
  rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

中文:
定理 norm_fderiv_norm_id_rpow
  条件: (x : E) {p : 实数} (hp : 1 < p)
  证明: by
  rw [fderiv_norm_rpow x hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc, innerSL_apply_norm]
  rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

Depends on / 依赖: Real.rpow_add_one, abs_eq_self, abs_eq_self.mpr, fderiv_norm_rpow, hp.le, innerSL_apply_norm, mul_assoc, norm_eq_abs, norm_mul, norm_nonneg, norm_norm, norm_rpow_of_nonneg, norm_smul, ring_nf, rpow_add_one, simp_rw, zero_le_one, zero_le_one.trans
-/
theorem norm_fderiv_norm_id_rpow (x : E) {p : Real} (hp : 1 < p) :
    ‖fderiv Real (fun x => ‖x‖ ^ p) x‖ = p * ‖x‖ ^ (p - 1) := by
  rw [fderiv_norm_rpow x hp]; rw [norm_smul]; rw [norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
abs_eq_self.mpr zero_le_one.trans hp.le, mul_assoc, innerSL_apply_norm]
  rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

/--
theorem `nnnorm_fderiv_norm_rpow_le` / 定理 `nnnorm_fderiv_norm_rpow_le`

English:
theorem nnnorm_fderiv_norm_rpow_le
  statement: {f : F -> E} (hf : Differentiable Real f)
  proof: norm_fderiv_norm_rpow_le hf hp

中文:
定理 nnnorm_fderiv_norm_rpow_le
  结论: {f : F -> E} (hf : 可微 实数 f)
  证明: norm_fderiv_norm_rpow_le hf hp

Depends on / 依赖: norm_fderiv_norm_rpow_le
-/
theorem nnnorm_fderiv_norm_rpow_le {f : F -> E} (hf : Differentiable Real f)
    {x : F} {p : Real>=0} (hp : 1 < p) :
    ‖fderiv Real (fun x => ‖f x‖ ^ (p : Real)) x‖₊ <= p * ‖f x‖₊ ^ ((p : Real) - 1) * ‖fderiv Real f x‖₊ :=
  norm_fderiv_norm_rpow_le hf hp

/--
lemma `enorm_fderiv_norm_rpow_le` / 引理 `enorm_fderiv_norm_rpow_le`

English:
lemma enorm_fderiv_norm_rpow_le
  statement: {f : F -> E} (hf : Differentiable Real f)
  proof: by
  simpa [enorm, ← ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.2 <| NNReal.one_le_coe.2 hp.le),
    ← ENNReal.coe_mul] using nnnorm_fderiv_norm_rpow_le hf hp

中文:
引理 enorm_fderiv_norm_rpow_le
  结论: {f : F -> E} (hf : 可微 实数 f)
  证明: by
  simpa [enorm, ← ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.2 <| NNReal.one_le_coe.2 hp.le),
    ← ENNReal.coe_mul] using nnnorm_fderiv_norm_rpow_le hf hp

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg, NNReal, NNReal.one_le_coe, coe_mul, coe_rpow_of_nonneg, hp.le, nnnorm_fderiv_norm_rpow_le, one_le_coe, sub_nonneg
-/
lemma enorm_fderiv_norm_rpow_le {f : F -> E} (hf : Differentiable Real f)
    {x : F} {p : Real>=0} (hp : 1 < p) :
    ‖fderiv Real (fun x => ‖f x‖ ^ (p : Real)) x‖ₑ <= p * ‖f x‖ₑ ^ ((p : Real) - 1) * ‖fderiv Real f x‖ₑ := by
  simpa [enorm, ← ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.2 <| NNReal.one_le_coe.2 hp.le),
    ← ENNReal.coe_mul] using nnnorm_fderiv_norm_rpow_le hf hp

/--
theorem `contDiff_norm_rpow` / 定理 `contDiff_norm_rpow`

English:
theorem contDiff_norm_rpow
  given: {p : Real} (hp : 1 < p)
  statement: ContDiff Real 1 (fun x : E => ‖x‖ ^ p)
  proof: by
  rw [contDiff_one_iff_fderiv]
.differentiableAt, ?_⟩ refine ⟨fun x => hasFDerivAt_norm_rpow x hp
  simp_rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simp_rw [hx, ContinuousAt, fderiv_norm_rpow (0 : E) hp, norm_zero, map_zero, smul_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_
      (fun _ => norm_nonneg _) (fun _ => norm_fderiv_norm_id_rpow _ hp |>.le)
    suffices ContinuousAt (fun x : E => p * ‖x‖ ^ (p - 1)) 0 by
      simpa [ContinuousAt, sub_ne_zero_of_ne hp.ne'] using this
    fun_prop (discharger := simp [hp.le])
  · simp_rw [funext fun x => fderiv_norm_rpow (E := E) (x := x) hp]
    fun_prop (discharger := simp [hx])

中文:
定理 contDiff_norm_rpow
  条件: {p : 实数} (hp : 1 < p)
  结论: 连续可微 实数 1 (fun x : E => ‖x‖ ^ p)
  证明: by
  rw [contDiff_one_iff_fderiv]
.differentiableAt, ?_⟩ refine ⟨fun x => hasFDerivAt_norm_rpow x hp
  simp_rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simp_rw [hx, ContinuousAt, fderiv_norm_rpow (0 : E) hp, norm_zero, map_zero, smul_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_
      (fun _ => norm_nonneg _) (fun _ => norm_fderiv_norm_id_rpow _ hp |>.le)
    suffices ContinuousAt (fun x : E => p * ‖x‖ ^ (p - 1)) 0 by
      simpa [ContinuousAt, sub_ne_zero_of_ne hp.ne'] using this
    fun_prop (discharger := simp [hp.le])
  · simp_rw [funext fun x => fderiv_norm_rpow (E := E) (x := x) hp]
    fun_prop (discharger := simp [hx])

Depends on / 依赖: ContinuousAt, contDiff_one_iff_fderiv, continuous_iff_continuousAt, differentiableAt, fderiv_norm_rpow, hasFDerivAt_norm_rpow, map_zero, norm_fderiv_norm_id_rpow, norm_nonneg, norm_zero, simp_rw, smul_zero, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_zero_iff_norm_tendsto_zero
-/
theorem contDiff_norm_rpow {p : Real} (hp : 1 < p) : ContDiff Real 1 (fun x : E => ‖x‖ ^ p) := by
  rw [contDiff_one_iff_fderiv]
.differentiableAt, ?_⟩ refine ⟨fun x => hasFDerivAt_norm_rpow x hp
  simp_rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simp_rw [hx, ContinuousAt, fderiv_norm_rpow (0 : E) hp, norm_zero, map_zero, smul_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_
      (fun _ => norm_nonneg _) (fun _ => norm_fderiv_norm_id_rpow _ hp |>.le)
    suffices ContinuousAt (fun x : E => p * ‖x‖ ^ (p - 1)) 0 by
      simpa [ContinuousAt, sub_ne_zero_of_ne hp.ne'] using this
    fun_prop (discharger := simp [hp.le])
  · simp_rw [funext fun x => fderiv_norm_rpow (E := E) (x := x) hp]
    fun_prop (discharger := simp [hx])

/--
theorem `ContDiff.norm_rpow` / 定理 `ContDiff.norm_rpow`

English:
theorem ContDiff.norm_rpow
  given: {f : F -> E} (hf : ContDiff Real 1 f) {p : Real} (hp : 1 < p)
  proof: .comp hf contDiff_norm_rpow hp

中文:
定理 连续可微.norm_rpow
  条件: {f : F -> E} (hf : 连续可微 实数 1 f) {p : 实数} (hp : 1 < p)
  证明: .comp hf contDiff_norm_rpow hp

Depends on / 依赖: contDiff_norm_rpow
-/
theorem ContDiff.norm_rpow {f : F -> E} (hf : ContDiff Real 1 f) {p : Real} (hp : 1 < p) :
    ContDiff Real 1 (fun x => ‖f x‖ ^ p) :=
.comp hf contDiff_norm_rpow hp

/--
theorem `Differentiable.norm_rpow` / 定理 `Differentiable.norm_rpow`

English:
theorem Differentiable.norm_rpow
  given: {f : F -> E} (hf : Differentiable Real f) {p : Real} (hp : 1 < p)
  proof: .comp hf .differentiable one_ne_zero contDiff_norm_rpow hp

中文:
定理 可微.norm_rpow
  条件: {f : F -> E} (hf : 可微 实数 f) {p : 实数} (hp : 1 < p)
  证明: .comp hf .differentiable one_ne_zero contDiff_norm_rpow hp

Depends on / 依赖: contDiff_norm_rpow, differentiable, one_ne_zero
-/
theorem Differentiable.norm_rpow {f : F -> E} (hf : Differentiable Real f) {p : Real} (hp : 1 < p) :
    Differentiable Real (fun x => ‖f x‖ ^ p) :=
.comp hf .differentiable one_ne_zero contDiff_norm_rpow hp

end ContDiffNormPow
