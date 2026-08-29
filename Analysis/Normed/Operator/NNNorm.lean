/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Operator norm as an `NNNorm`

Operator norm as an `NNNorm`, i.e. taking values in non-negative reals.

-/

public section

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped NNReal Topology Uniformity ENNReal
open Metric ContinuousLinearMap
open Set Real

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}

section NontriviallySemiNormed

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₁₃ : 𝕜 ->+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

namespace ContinuousLinearMap

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (f : E ->SL[σ₁₂] F)
  statement: ‖f‖₊ = sInf { c | forall x, ‖f x‖₊ <= c * ‖x‖₊ }
  proof: by
  ext
  rw [NNReal.coe_sInf]; rw [coe_nnnorm]; rw [norm_def]; rw [NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_ofPred_eq, NNReal.coe_mk,
    exists_prop]

@[simp, nontriviality]

中文:
定理 nnnorm_def
  条件: (f : E ->SL[σ₁₂] F)
  结论: ‖f‖₊ = sInf { c | 对任意 x, ‖f x‖₊ <= c * ‖x‖₊ }
  证明: by
  ext
  rw [NNReal.coe_sInf]; rw [coe_nnnorm]; rw [norm_def]; rw [NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_ofPred_eq, NNReal.coe_mk,
    exists_prop]

@[simp, nontriviality]

Depends on / 依赖: NNReal, NNReal.coe_image, NNReal.coe_le_coe, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_sInf, coe_image, coe_le_coe, coe_mk, coe_mul, coe_nnnorm, coe_sInf, exists_prop, mem_ofPred_eq, norm_def, simp_rw
-/
theorem nnnorm_def (f : E ->SL[σ₁₂] F) : ‖f‖₊ = sInf { c | forall x, ‖f x‖₊ <= c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf]; rw [coe_nnnorm]; rw [norm_def]; rw [NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_ofPred_eq, NNReal.coe_mk,
    exists_prop]

@[simp, nontriviality]
/--
theorem `opNNNorm_subsingleton` / 定理 `opNNNorm_subsingleton`

English:
theorem opNNNorm_subsingleton
  given: [Subsingleton E] (f : E ->SL[σ₁₂] F)
  statement: ‖f‖₊ = 0
  proof: NNReal.eq f.opNorm_subsingleton

中文:
定理 opNNNorm_subsingleton
  条件: [子单例 E] (f : E ->SL[σ₁₂] F)
  结论: ‖f‖₊ = 0
  证明: NNReal.eq f.opNorm_subsingleton

Depends on / 依赖: NNReal, NNReal.eq, f.opNorm_subsingleton, opNorm_subsingleton
-/
theorem opNNNorm_subsingleton [Subsingleton E] (f : E ->SL[σ₁₂] F) : ‖f‖₊ = 0 :=
NNReal.eq f.opNorm_subsingleton

/--
theorem `opNNNorm_le_bound` / 定理 `opNNNorm_le_bound`

English:
theorem opNNNorm_le_bound
  given: (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊)
  statement: ‖f‖₊ <= M
  proof: opNorm_le_bound f (zero_le (a := M)) hM

中文:
定理 opNNNorm_le_bound
  条件: (f : E ->SL[σ₁₂] F) (M : 实数>=0) (hM : 对任意 x, ‖f x‖₊ <= M * ‖x‖₊)
  结论: ‖f‖₊ <= M
  证明: opNorm_le_bound f (zero_le (a := M)) hM

Depends on / 依赖: opNorm_le_bound, zero_le
-/
theorem opNNNorm_le_bound (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M :=
  opNorm_le_bound f (zero_le (a := M)) hM

/--
theorem `opNNNorm_le_bound'` / 定理 `opNNNorm_le_bound'`

English:
theorem opNNNorm_le_bound'
  given: (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖x‖₊ != 0 -> ‖f x‖₊ <= M * ‖x‖₊)
  proof: opNorm_le_bound' f (zero_le (a := M)) fun x hx => hM x by rwa [← NNReal.coe_ne_zero]

中文:
定理 opNNNorm_le_bound'
  条件: (f : E ->SL[σ₁₂] F) (M : 实数>=0) (hM : 对任意 x, ‖x‖₊ != 0 -> ‖f x‖₊ <= M * ‖x‖₊)
  证明: opNorm_le_bound' f (zero_le (a := M)) fun x hx => hM x by rwa [← NNReal.coe_ne_zero]

Depends on / 依赖: NNReal, NNReal.coe_ne_zero, coe_ne_zero, opNorm_le_bound, zero_le
-/
theorem opNNNorm_le_bound' (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖x‖₊ != 0 -> ‖f x‖₊ <= M * ‖x‖₊) :
    ‖f‖₊ <= M :=
opNorm_le_bound' f (zero_le (a := M)) fun x hx => hM x by rwa [← NNReal.coe_ne_zero]

/--
theorem `opNNNorm_le_of_unit_nnnorm` / 定理 `opNNNorm_le_of_unit_nnnorm`

English:
theorem opNNNorm_le_of_unit_nnnorm
  statement: [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real>=0}
  proof: opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x by rwa [← NNReal.coe_eq_one]

中文:
定理 opNNNorm_le_of_unit_nnnorm
  结论: [赋范代数 实数 𝕜] {f : E ->SL[σ₁₂] F} {C : 实数>=0}
  证明: opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x by rwa [← NNReal.coe_eq_one]

Depends on / 依赖: C.coe_nonneg, NNReal, NNReal.coe_eq_one, coe_eq_one, coe_nonneg, opNorm_le_of_unit_norm
-/
theorem opNNNorm_le_of_unit_nnnorm [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real>=0}
    (hf : forall x, ‖x‖₊ = 1 -> ‖f x‖₊ <= C) : ‖f‖₊ <= C :=
opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x by rwa [← NNReal.coe_eq_one]

/--
theorem `opNNNorm_le_of_lipschitz` / 定理 `opNNNorm_le_of_lipschitz`

English:
theorem opNNNorm_le_of_lipschitz
  given: {f : E ->SL[σ₁₂] F} {K : Real>=0} (hf : LipschitzWith K f)
  proof: opNorm_le_of_lipschitz hf

中文:
定理 opNNNorm_le_of_lipschitz
  条件: {f : E ->SL[σ₁₂] F} {K : 实数>=0} (hf : LipschitzWith K f)
  证明: opNorm_le_of_lipschitz hf

Depends on / 依赖: opNorm_le_of_lipschitz
-/
theorem opNNNorm_le_of_lipschitz {f : E ->SL[σ₁₂] F} {K : Real>=0} (hf : LipschitzWith K f) :
    ‖f‖₊ <= K :=
  opNorm_le_of_lipschitz hf

/--
theorem `opNNNorm_eq_of_bounds` / 定理 `opNNNorm_eq_of_bounds`

English:
theorem opNNNorm_eq_of_bounds
  statement: {φ : E ->SL[σ₁₂] F} (M : Real>=0) (h_above : forall x, ‖φ x‖₊ <= M * ‖x‖₊)
  proof: Subtype.ext opNorm_eq_of_bounds (zero_le (a := M)) h_above Subtype.forall'.mpr h_below

中文:
定理 opNNNorm_eq_of_bounds
  结论: {φ : E ->SL[σ₁₂] F} (M : 实数>=0) (h_above : 对任意 x, ‖φ x‖₊ <= M * ‖x‖₊)
  证明: Subtype.ext opNorm_eq_of_bounds (zero_le (a := M)) h_above Subtype.forall'.mpr h_below

Depends on / 依赖: Subtype, Subtype.ext, Subtype.forall, h_above, h_below, opNorm_eq_of_bounds, zero_le
-/
theorem opNNNorm_eq_of_bounds {φ : E ->SL[σ₁₂] F} (M : Real>=0) (h_above : forall x, ‖φ x‖₊ <= M * ‖x‖₊)
    (h_below : forall N, (forall x, ‖φ x‖₊ <= N * ‖x‖₊) -> M <= N) : ‖φ‖₊ = M :=
Subtype.ext opNorm_eq_of_bounds (zero_le (a := M)) h_above Subtype.forall'.mpr h_below

/--
theorem `opNNNorm_le_iff` / 定理 `opNNNorm_le_iff`

English:
theorem opNNNorm_le_iff
  given: {f : E ->SL[σ₁₂] F} {C : Real>=0}
  statement: ‖f‖₊ <= C ↔ forall x, ‖f x‖₊ <= C * ‖x‖₊
  proof: opNorm_le_iff C.2

中文:
定理 opNNNorm_le_iff
  条件: {f : E ->SL[σ₁₂] F} {C : 实数>=0}
  结论: ‖f‖₊ <= C ↔ 对任意 x, ‖f x‖₊ <= C * ‖x‖₊
  证明: opNorm_le_iff C.2

Depends on / 依赖: opNorm_le_iff
-/
theorem opNNNorm_le_iff {f : E ->SL[σ₁₂] F} {C : Real>=0} : ‖f‖₊ <= C ↔ forall x, ‖f x‖₊ <= C * ‖x‖₊ :=
  opNorm_le_iff C.2

/--
theorem `isLeast_opNNNorm` / 定理 `isLeast_opNNNorm`

English:
theorem isLeast_opNNNorm
  given: (f : E ->SL[σ₁₂] F)
  statement: IsLeast {C : Real>=0 | forall x, ‖f x‖₊ <= C * ‖x‖₊} ‖f‖₊
  proof: by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

中文:
定理 isLeast_opNNNorm
  条件: (f : E ->SL[σ₁₂] F)
  结论: IsLeast {C : 实数>=0 | 对任意 x, ‖f x‖₊ <= C * ‖x‖₊} ‖f‖₊
  证明: by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

Depends on / 依赖: isLeast_Ici, opNNNorm_le_iff
-/
theorem isLeast_opNNNorm (f : E ->SL[σ₁₂] F) : IsLeast {C : Real>=0 | forall x, ‖f x‖₊ <= C * ‖x‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici

/--
theorem `opNNNorm_comp_le` / 定理 `opNNNorm_comp_le`

English:
theorem opNNNorm_comp_le
  given: (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F)
  statement: ‖h.comp f‖₊ <= ‖h‖₊ * ‖f‖₊
  proof: opNorm_comp_le h f

中文:
定理 opNNNorm_comp_le
  条件: (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F)
  结论: ‖h.comp f‖₊ <= ‖h‖₊ * ‖f‖₊
  证明: opNorm_comp_le h f

Depends on / 依赖: opNorm_comp_le
-/
theorem opNNNorm_comp_le (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F) : ‖h.comp f‖₊ <= ‖h‖₊ * ‖f‖₊ :=
  opNorm_comp_le h f

/--
lemma `opENorm_comp_le` / 引理 `opENorm_comp_le`

English:
lemma opENorm_comp_le
  given: (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F)
  statement: ‖h.comp f‖ₑ <= ‖h‖ₑ * ‖f‖ₑ
  proof: by
  simpa [enorm, ← ENNReal.coe_mul] using opNNNorm_comp_le h f

中文:
引理 opENorm_comp_le
  条件: (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F)
  结论: ‖h.comp f‖ₑ <= ‖h‖ₑ * ‖f‖ₑ
  证明: by
  simpa [enorm, ← ENNReal.coe_mul] using opNNNorm_comp_le h f

Depends on / 依赖: ENNReal, ENNReal.coe_mul, coe_mul, opNNNorm_comp_le
-/
lemma opENorm_comp_le (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F) : ‖h.comp f‖ₑ <= ‖h‖ₑ * ‖f‖ₑ := by
  simpa [enorm, ← ENNReal.coe_mul] using opNNNorm_comp_le h f

/--
theorem `le_opNNNorm` / 定理 `le_opNNNorm`

English:
theorem le_opNNNorm
  given: (f : E ->SL[σ₁₂] F) (x : E)
  statement: ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
  proof: f.le_opNorm x

中文:
定理 le_opNNNorm
  条件: (f : E ->SL[σ₁₂] F) (x : E)
  结论: ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
  证明: f.le_opNorm x

Depends on / 依赖: f.le_opNorm, le_opNorm
-/
theorem le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E) : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊ :=
  f.le_opNorm x

/--
lemma `le_opENorm` / 引理 `le_opENorm`

English:
lemma le_opENorm
  given: (f : E ->SL[σ₁₂] F) (x : E)
  statement: ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
  proof: by
  dsimp [enorm]; exact mod_cast le_opNNNorm ..

@[deprecated (since := "2026-06-27")] alias le_opNorm_enorm := le_opENorm

中文:
引理 le_opENorm
  条件: (f : E ->SL[σ₁₂] F) (x : E)
  结论: ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
  证明: by
  dsimp [enorm]; exact mod_cast le_opNNNorm ..

@[deprecated (since := "2026-06-27")] alias le_opNorm_enorm := le_opENorm

Depends on / 依赖: le_opNNNorm, mod_cast
-/
lemma le_opENorm (f : E ->SL[σ₁₂] F) (x : E) : ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ := by
  dsimp [enorm]; exact mod_cast le_opNNNorm ..

@[deprecated (since := "2026-06-27")] alias le_opNorm_enorm := le_opENorm

/--
theorem `opENorm_le_bound` / 定理 `opENorm_le_bound`

English:
theorem opENorm_le_bound
  given: (f : E ->SL[σ₁₂] F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ)
  proof: by
  rcases eq_top_or_lt_top M with rfl | h'M
  · simp
  lift M to NNReal using h'M.ne
  simp only [← ofReal_norm, ENNReal.ofReal_le_coe]
  apply opNorm_le_bound _ (by positivity) (fun x => ?_)
  specialize hM x
  simp only [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal] at hM
  rwa [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hM

中文:
定理 opENorm_le_bound
  条件: (f : E ->SL[σ₁₂] F) {M : 实数>=0∞} (hM : 对任意 x, ‖f x‖ₑ <= M * ‖x‖ₑ)
  证明: by
  rcases eq_top_or_lt_top M with rfl | h'M
  · simp
  lift M to NNReal using h'M.ne
  simp only [← ofReal_norm, ENNReal.ofReal_le_coe]
  apply opNorm_le_bound _ (by positivity) (fun x => ?_)
  specialize hM x
  simp only [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal] at hM
  rwa [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hM

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_coe, ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_mul, M.ne, NNReal, eq_top_or_lt_top, ofReal_coe_nnreal, ofReal_le_coe, ofReal_le_ofReal_iff, ofReal_mul, ofReal_norm, opNorm_le_bound, specialize
-/
theorem opENorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ) :
    ‖f‖ₑ <= M := by
  rcases eq_top_or_lt_top M with rfl | h'M
  · simp
  lift M to NNReal using h'M.ne
  simp only [← ofReal_norm, ENNReal.ofReal_le_coe]
  apply opNorm_le_bound _ (by positivity) (fun x => ?_)
  specialize hM x
  simp only [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal] at hM
  rwa [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hM

/--
theorem `le_of_opENorm_le_of_le` / 定理 `le_of_opENorm_le_of_le`

English:
theorem le_of_opENorm_le_of_le
  given: (f : E ->SL[σ₁₂] F) {x} {a b : Real>=0∞} (hf : ‖f‖ₑ <= a) (hx : ‖x‖ₑ <= b)
  proof: (f.le_opENorm x).trans by gcongr

中文:
定理 le_of_opENorm_le_of_le
  条件: (f : E ->SL[σ₁₂] F) {x} {a b : 实数>=0∞} (hf : ‖f‖ₑ <= a) (hx : ‖x‖ₑ <= b)
  证明: (f.le_opENorm x).trans by gcongr

Depends on / 依赖: f.le_opENorm, le_opENorm
-/
theorem le_of_opENorm_le_of_le (f : E ->SL[σ₁₂] F) {x} {a b : Real>=0∞} (hf : ‖f‖ₑ <= a) (hx : ‖x‖ₑ <= b) :
    ‖f x‖ₑ <= a * b :=
(f.le_opENorm x).trans by gcongr

/--
theorem `le_opENorm_of_le` / 定理 `le_opENorm_of_le`

English:
theorem le_opENorm_of_le
  given: (f : E ->SL[σ₁₂] F) {c : Real>=0∞} {x} (h : ‖x‖ₑ <= c)
  statement: ‖f x‖ₑ <= ‖f‖ₑ * c
  proof: f.le_of_opENorm_le_of_le le_rfl h

中文:
定理 le_opENorm_of_le
  条件: (f : E ->SL[σ₁₂] F) {c : 实数>=0∞} {x} (h : ‖x‖ₑ <= c)
  结论: ‖f x‖ₑ <= ‖f‖ₑ * c
  证明: f.le_of_opENorm_le_of_le le_rfl h

Depends on / 依赖: f.le_of_opENorm_le_of_le, le_of_opENorm_le_of_le, le_rfl
-/
theorem le_opENorm_of_le (f : E ->SL[σ₁₂] F) {c : Real>=0∞} {x} (h : ‖x‖ₑ <= c) : ‖f x‖ₑ <= ‖f‖ₑ * c :=
  f.le_of_opENorm_le_of_le le_rfl h

/--
theorem `le_of_opENorm_le` / 定理 `le_of_opENorm_le`

English:
theorem le_of_opENorm_le
  given: (f : E ->SL[σ₁₂] F) {c : Real>=0∞} (h : ‖f‖ₑ <= c) (x : E)
  statement: ‖f x‖ₑ <= c * ‖x‖ₑ
  proof: f.le_of_opENorm_le_of_le h le_rfl

中文:
定理 le_of_opENorm_le
  条件: (f : E ->SL[σ₁₂] F) {c : 实数>=0∞} (h : ‖f‖ₑ <= c) (x : E)
  结论: ‖f x‖ₑ <= c * ‖x‖ₑ
  证明: f.le_of_opENorm_le_of_le h le_rfl

Depends on / 依赖: f.le_of_opENorm_le_of_le, le_of_opENorm_le_of_le, le_rfl
-/
theorem le_of_opENorm_le (f : E ->SL[σ₁₂] F) {c : Real>=0∞} (h : ‖f‖ₑ <= c) (x : E) : ‖f x‖ₑ <= c * ‖x‖ₑ :=
  f.le_of_opENorm_le_of_le h le_rfl

/--
theorem `opENorm_le_iff` / 定理 `opENorm_le_iff`

English:
theorem opENorm_le_iff
  given: {f : E ->SL[σ₁₂] F} {M : Real>=0∞}
  proof: ⟨f.le_of_opENorm_le, opENorm_le_bound f⟩

中文:
定理 opENorm_le_iff
  条件: {f : E ->SL[σ₁₂] F} {M : 实数>=0∞}
  证明: ⟨f.le_of_opENorm_le, opENorm_le_bound f⟩

Depends on / 依赖: f.le_of_opENorm_le, le_of_opENorm_le, opENorm_le_bound
-/
theorem opENorm_le_iff {f : E ->SL[σ₁₂] F} {M : Real>=0∞} :
    ‖f‖ₑ <= M ↔ forall x, ‖f x‖ₑ <= M * ‖x‖ₑ :=
  ⟨f.le_of_opENorm_le, opENorm_le_bound f⟩

/--
theorem `nndist_le_opNNNorm` / 定理 `nndist_le_opNNNorm`

English:
theorem nndist_le_opNNNorm
  given: (f : E ->SL[σ₁₂] F) (x y : E)
  statement: nndist (f x) (f y) <= ‖f‖₊ * nndist x y
  proof: dist_le_opNorm f x y

中文:
定理 nndist_le_opNNNorm
  条件: (f : E ->SL[σ₁₂] F) (x y : E)
  结论: nndist (f x) (f y) <= ‖f‖₊ * nndist x y
  证明: dist_le_opNorm f x y

Depends on / 依赖: dist_le_opNorm
-/
theorem nndist_le_opNNNorm (f : E ->SL[σ₁₂] F) (x y : E) : nndist (f x) (f y) <= ‖f‖₊ * nndist x y :=
  dist_le_opNorm f x y

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  given: (f : E ->SL[σ₁₂] F)
  statement: LipschitzWith ‖f‖₊ f
  proof: AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

中文:
定理 lipschitz
  条件: (f : E ->SL[σ₁₂] F)
  结论: LipschitzWith ‖f‖₊ f
  证明: AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.lipschitz_of_bound_nnnorm, f.le_opNNNorm, le_opNNNorm, lipschitz_of_bound_nnnorm
-/
theorem lipschitz (f : E ->SL[σ₁₂] F) : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

/--
theorem `lipschitz_apply` / 定理 `lipschitz_apply`

English:
theorem lipschitz_apply
  given: (x : E)
  statement: LipschitzWith ‖x‖₊ fun f : E ->SL[σ₁₂] F => f x
  proof: lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)

中文:
定理 lipschitz_apply
  条件: (x : E)
  结论: LipschitzWith ‖x‖₊ fun f : E ->SL[σ₁₂] F => f x
  证明: lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)

Depends on / 依赖: le_opNorm, lipschitzWith_iff_norm_sub_le, mul_comm, trans_eq
-/
theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E ->SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)

/--
theorem `exists_mul_lt_apply_of_lt_opNNNorm` / 定理 `exists_mul_lt_apply_of_lt_opNNNorm`

English:
theorem exists_mul_lt_apply_of_lt_opNNNorm
  given: (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊)
  proof: by
  simpa only [not_forall, not_le, Set.mem_ofPred] using
    notMem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : Real>=0 | forall x, ‖f x‖₊ <= c * ‖x‖₊ })
      (OrderBot.bddBelow _)

中文:
定理 存在_mul_lt_apply_of_lt_opNNNorm
  条件: (f : E ->SL[σ₁₂] F) {r : 实数>=0} (hr : r < ‖f‖₊)
  证明: by
  simpa only [not_forall, not_le, Set.mem_ofPred] using
    notMem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : Real>=0 | forall x, ‖f x‖₊ <= c * ‖x‖₊ })
      (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, Set.mem_ofPred, bddBelow, mem_ofPred, nnnorm_def, notMem_of_lt_csInf, not_forall, not_le
-/
theorem exists_mul_lt_apply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) :
    exists x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [not_forall, not_le, Set.mem_ofPred] using
    notMem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : Real>=0 | forall x, ‖f x‖₊ <= c * ‖x‖₊ })
      (OrderBot.bddBelow _)

/--
theorem `exists_mul_lt_of_lt_opNorm` / 定理 `exists_mul_lt_of_lt_opNorm`

English:
theorem exists_mul_lt_of_lt_opNorm
  given: (f : E ->SL[σ₁₂] F) {r : Real} (hr₀ : 0 <= r) (hr : r < ‖f‖)
  proof: by
  lift r to Real>=0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

中文:
定理 存在_mul_lt_of_lt_opNorm
  条件: (f : E ->SL[σ₁₂] F) {r : 实数} (hr₀ : 0 <= r) (hr : r < ‖f‖)
  证明: by
  lift r to Real>=0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

Depends on / 依赖: exists_mul_lt_apply_of_lt_opNNNorm, f.exists_mul_lt_apply_of_lt_opNNNorm
-/
theorem exists_mul_lt_of_lt_opNorm (f : E ->SL[σ₁₂] F) {r : Real} (hr₀ : 0 <= r) (hr : r < ‖f‖) :
    exists x, r * ‖x‖ < ‖f x‖ := by
  lift r to Real>=0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

end ContinuousLinearMap

namespace ContinuousLinearEquiv
variable {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  given: (e : E ≃SL[σ₁₂] F)
  statement: LipschitzWith ‖(e : E ->SL[σ₁₂] F)‖₊ e
  proof: (e : E ->SL[σ₁₂] F).lipschitz

中文:
定理 lipschitz
  条件: (e : E ≃SL[σ₁₂] F)
  结论: LipschitzWith ‖(e : E ->SL[σ₁₂] F)‖₊ e
  证明: (e : E ->SL[σ₁₂] F).lipschitz
-/
protected theorem lipschitz (e : E ≃SL[σ₁₂] F) : LipschitzWith ‖(e : E ->SL[σ₁₂] F)‖₊ e :=
  (e : E ->SL[σ₁₂] F).lipschitz

end ContinuousLinearEquiv

end NontriviallySemiNormed

section DenselyNormedDomain
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

namespace ContinuousLinearMap

/--
theorem `exists_lt_apply_of_lt_opNNNorm` / 定理 `exists_lt_apply_of_lt_opNNNorm`

English:
theorem exists_lt_apply_of_lt_opNNNorm
  statement: (f : E ->SL[σ₁₂] F) {r : Real>=0}
  proof: by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ != 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero] at hy
  have hfy : ‖f y‖₊ != 0 := hy.ne_zero
  rw [← inv_inv ‖f y‖₊]; rw [NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy)]; rw [mul_assoc]; rw [mul_comm ‖y‖₊]; rw [←
    mul_assoc]; rw [← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv,
    RingHomIsometric.nnnorm_map]

中文:
定理 存在_lt_apply_of_lt_opNNNorm
  结论: (f : E ->SL[σ₁₂] F) {r : 实数>=0}
  证明: by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ != 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero] at hy
  have hfy : ‖f y‖₊ != 0 := hy.ne_zero
  rw [← inv_inv ‖f y‖₊]; rw [NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy)]; rw [mul_assoc]; rw [mul_comm ‖y‖₊]; rw [←
    mul_assoc]; rw [← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv,
    RingHomIsometric.nnnorm_map]

Depends on / 依赖: NNReal, NNReal.lt_inv_iff_mul_lt, NormedField, NormedField.exists_lt_nnnorm_lt, exists_lt_nnnorm_lt, exists_mul_lt_apply_of_lt_opNNNorm, f.exists_mul_lt_apply_of_lt_opNNNorm, hy.ne_zero, inv_inv, inv_ne_zero, lt_inv_iff_mul_lt, map_zero, mul_assoc, mul_comm, ne_zero, nnnorm_ne_zero_iff, nnnorm_smul, nnnorm_zero
-/
theorem exists_lt_apply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0}
    (hr : r < ‖f‖₊) : exists x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ != 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero] at hy
  have hfy : ‖f y‖₊ != 0 := hy.ne_zero
  rw [← inv_inv ‖f y‖₊]; rw [NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy)]; rw [mul_assoc]; rw [mul_comm ‖y‖₊]; rw [←
    mul_assoc]; rw [← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv,
    RingHomIsometric.nnnorm_map]

/--
theorem `exists_lt_apply_of_lt_opNorm` / 定理 `exists_lt_apply_of_lt_opNorm`

English:
theorem exists_lt_apply_of_lt_opNorm
  statement: (f : E ->SL[σ₁₂] F) {r : Real}
  proof: by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to Real>=0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr

中文:
定理 存在_lt_apply_of_lt_opNorm
  结论: (f : E ->SL[σ₁₂] F) {r : 实数}
  证明: by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to Real>=0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr

Depends on / 依赖: exists_lt_apply_of_lt_opNNNorm, f.exists_lt_apply_of_lt_opNNNorm, not_lt
-/
theorem exists_lt_apply_of_lt_opNorm (f : E ->SL[σ₁₂] F) {r : Real}
    (hr : r < ‖f‖) : exists x : E, ‖x‖ < 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to Real>=0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr

/--
theorem `sSup_unit_ball_eq_nnnorm` / 定理 `sSup_unit_ball_eq_nnnorm`

English:
theorem sSup_unit_ball_eq_nnnorm
  given: (f : E ->SL[σ₁₂] F)
  proof: by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩

中文:
定理 sSup_unit_ball_eq_nnnorm
  条件: (f : E ->SL[σ₁₂] F)
  证明: by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩

Depends on / 依赖: csSup_eq_of_forall_le_of_forall_lt_exists_gt, exists_lt_apply_of_lt_opNNNorm, f.exists_lt_apply_of_lt_opNNNorm, f.le_opNorm_of_le, le_opNorm_of_le, mem_ball_zero_iff, mul_one, nonempty_ball, nonempty_ball.mpr, zero_lt_one
-/
theorem sSup_unit_ball_eq_nnnorm (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩

/--
theorem `sSup_unit_ball_eq_norm` / 定理 `sSup_unit_ball_eq_norm`

English:
theorem sSup_unit_ball_eq_norm
  given: (f : E ->SL[σ₁₂] F)
  proof: by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm

中文:
定理 sSup_unit_ball_eq_norm
  条件: (f : E ->SL[σ₁₂] F)
  证明: by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_sSup, Set.image_image, coe_inj, coe_sSup, f.sSup_unit_ball_eq_nnnorm, image_image, sSup_unit_ball_eq_nnnorm
-/
theorem sSup_unit_ball_eq_norm (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm

/--
theorem `sSup_unitClosedBall_eq_nnnorm` / 定理 `sSup_unitClosedBall_eq_nnnorm`

English:
theorem sSup_unitClosedBall_eq_nnnorm
  given: (f : E ->SL[σ₁₂] F)
  proof: by
  have hbdd : forall y in (fun x => ‖f x‖₊) '' closedBall 0 1, y <= ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  gcongr
  exacts [⟨‖f‖₊, hbdd⟩, ball_subset_closedBall]

中文:
定理 sSup_unitClosedBall_eq_nnnorm
  条件: (f : E ->SL[σ₁₂] F)
  证明: by
  have hbdd : forall y in (fun x => ‖f x‖₊) '' closedBall 0 1, y <= ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  gcongr
  exacts [⟨‖f‖₊, hbdd⟩, ball_subset_closedBall]

Depends on / 依赖: ball_subset_closedBall, closedBall, csSup_le, exacts, f.unit_le_opNorm, le_antisymm, mem_closedBall_zero_iff, nonempty_closedBall, nonempty_closedBall.mpr, sSup_unit_ball_eq_nnnorm, unit_le_opNorm, zero_le_one
-/
theorem sSup_unitClosedBall_eq_nnnorm (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ := by
  have hbdd : forall y in (fun x => ‖f x‖₊) '' closedBall 0 1, y <= ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  gcongr
  exacts [⟨‖f‖₊, hbdd⟩, ball_subset_closedBall]

/--
theorem `sSup_unitClosedBall_eq_norm` / 定理 `sSup_unitClosedBall_eq_norm`

English:
theorem sSup_unitClosedBall_eq_norm
  given: (f : E ->SL[σ₁₂] F)
  proof: by
  simpa only [NNReal.coe_sSup, Set.image_image] using!
    NNReal.coe_inj.2 f.sSup_unitClosedBall_eq_nnnorm

中文:
定理 sSup_unitClosedBall_eq_norm
  条件: (f : E ->SL[σ₁₂] F)
  证明: by
  simpa only [NNReal.coe_sSup, Set.image_image] using!
    NNReal.coe_inj.2 f.sSup_unitClosedBall_eq_nnnorm

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_sSup, Set.image_image, coe_inj, coe_sSup, f.sSup_unitClosedBall_eq_nnnorm, image_image, sSup_unitClosedBall_eq_nnnorm
-/
theorem sSup_unitClosedBall_eq_norm (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using!
    NNReal.coe_inj.2 f.sSup_unitClosedBall_eq_nnnorm

/--
theorem `exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm` / 定理 `exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm`

English:
theorem exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm
  statement: [NormedAlgebra Real 𝕜]
  proof: by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNNNorm f hr
  obtain rfl | hx0 := eq_zero_or_nnnorm_pos x
  · simp at hr
  use algebraMap Real 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖₊⁻¹ * ‖f x‖₊ by simpa [nnnorm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖₊ := by simpa
    _ < ‖x‖₊⁻¹ * ‖f x‖₊ := by gcongr; exact hr.pos

中文:
定理 存在_nnnorm_eq_one_lt_apply_of_lt_opNNNorm
  结论: [赋范代数 实数 𝕜]
  证明: by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNNNorm f hr
  obtain rfl | hx0 := eq_zero_or_nnnorm_pos x
  · simp at hr
  use algebraMap Real 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖₊⁻¹ * ‖f x‖₊ by simpa [nnnorm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖₊ := by simpa
    _ < ‖x‖₊⁻¹ * ‖f x‖₊ := by gcongr; exact hr.pos

Depends on / 依赖: algebraMap, eq_zero_or_nnnorm_pos, exists_lt_apply_of_lt_opNNNorm, hr.pos, hx0.ne, nnnorm_smul
-/
theorem exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm [NormedAlgebra Real 𝕜]
    (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) :
    exists x : E, ‖x‖₊ = 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNNNorm f hr
  obtain rfl | hx0 := eq_zero_or_nnnorm_pos x
  · simp at hr
  use algebraMap Real 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖₊⁻¹ * ‖f x‖₊ by simpa [nnnorm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖₊ := by simpa
    _ < ‖x‖₊⁻¹ * ‖f x‖₊ := by gcongr; exact hr.pos

/--
theorem `sSup_sphere_eq_nnnorm` / 定理 `sSup_sphere_eq_nnnorm`

English:
theorem sSup_sphere_eq_nnnorm
  given: [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F)
  proof: by
  cases subsingleton_or_nontrivial E
  · simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _) ?_ fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_sphere_zero_iff_norm.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, by simpa using! congrArg NNReal.toReal hx, rfl⟩, hxf⟩

中文:
定理 sSup_sphere_eq_nnnorm
  条件: [赋范代数 实数 𝕜] (f : E ->SL[σ₁₂] F)
  证明: by
  cases subsingleton_or_nontrivial E
  · simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _) ?_ fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_sphere_zero_iff_norm.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, by simpa using! congrArg NNReal.toReal hx, rfl⟩, hxf⟩

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars, NormedSpace.sphere_nonempty.mpr, csSup_eq_of_forall_le_of_forall_lt_exists_gt, exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm, f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm, f.le_opNorm_of_le, le_opNorm_of_le, mem_sphere_zero_iff_norm, mul_one, one_ne_zero, restrictScalars, sphere_eq_empty_of_subsingleton, sphere_nonempty, subsingleton_or_nontrivial, zero_le_one
-/
theorem sSup_sphere_eq_nnnorm [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' Metric.sphere 0 1) = ‖f‖₊ := by
  cases subsingleton_or_nontrivial E
  · simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _) ?_ fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_sphere_zero_iff_norm.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, by simpa using! congrArg NNReal.toReal hx, rfl⟩, hxf⟩

/--
theorem `sSup_sphere_eq_norm` / 定理 `sSup_sphere_eq_norm`

English:
theorem sSup_sphere_eq_norm
  given: [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F)
  proof: by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_sphere_eq_nnnorm

中文:
定理 sSup_sphere_eq_norm
  条件: [赋范代数 实数 𝕜] (f : E ->SL[σ₁₂] F)
  证明: by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_sphere_eq_nnnorm

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_sSup, Set.image_image, coe_inj, coe_sSup, f.sSup_sphere_eq_nnnorm, image_image, sSup_sphere_eq_nnnorm
-/
theorem sSup_sphere_eq_norm [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' Metric.sphere 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_sphere_eq_nnnorm

end ContinuousLinearMap

end DenselyNormedDomain
