/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Measurable functions in normed spaces

-/

public section


open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [Module R E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SeminormedAddCommGroup F] [Module R F] [MeasurableSpace F] [BorelSpace F]

@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: (L : E ->L[R] F)
  statement: Measurable L
  proof: L.continuous.measurable

@[fun_prop]

中文:
定理 measurable
  条件: (L : E ->L[R] F)
  结论: Measurable L
  证明: L.continuous.measurable

@[fun_prop]
-/
protected theorem measurable (L : E ->L[R] F) : Measurable L :=
  L.continuous.measurable

@[fun_prop]
/--
theorem `measurable_comp` / 定理 `measurable_comp`

English:
theorem measurable_comp
  given: (L : E ->L[R] F) {φ : α -> E} (φ_meas : Measurable φ)
  proof: L.measurable.comp φ_meas

中文:
定理 measurable_comp
  条件: (L : E ->L[R] F) {φ : α -> E} (φ_meas : Measurable φ)
  证明: L.measurable.comp φ_meas

Depends on / 依赖: L.measurable.comp, measurable
-/
theorem measurable_comp (L : E ->L[R] F) {φ : α -> E} (φ_meas : Measurable φ) :
    Measurable fun a : α => L (φ a) :=
  L.measurable.comp φ_meas

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/--
Instance `instMeasurableSpace` / 实例 `instMeasurableSpace`

English:
instance instMeasurableSpace
  signature: : MeasurableSpace (E ->L[𝕜] F)
  body: borel _

中文:
实例 instMeasurableSpace
  签名: : MeasurableSpace (E ->L[𝕜] F)
  定义体: borel _
-/
instance instMeasurableSpace : MeasurableSpace (E ->L[𝕜] F) :=
  borel _

/--
Instance `instBorelSpace` / 实例 `instBorelSpace`

English:
instance instBorelSpace
  signature: : BorelSpace (E ->L[𝕜] F)
  body: ⟨rfl⟩

@[fun_prop]

中文:
实例 instBorelSpace
  签名: : BorelSpace (E ->L[𝕜] F)
  定义体: ⟨rfl⟩

@[fun_prop]
-/
instance instBorelSpace : BorelSpace (E ->L[𝕜] F) :=
  ⟨rfl⟩

@[fun_prop]
/--
theorem `measurable_apply` / 定理 `measurable_apply`

English:
theorem measurable_apply
  given: [MeasurableSpace F] [BorelSpace F] (x : E)
  proof: (apply 𝕜 F x).continuous.measurable

中文:
定理 measurable_apply
  条件: [MeasurableSpace F] [BorelSpace F] (x : E)
  证明: (apply 𝕜 F x).continuous.measurable

Depends on / 依赖: continuous, continuous.measurable, measurable
-/
theorem measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) :
    Measurable fun f : E ->L[𝕜] F => f x :=
  (apply 𝕜 F x).continuous.measurable

/--
theorem `measurable_apply'` / 定理 `measurable_apply'`

English:
theorem measurable_apply'
  statement: [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
  proof: measurable_pi_lambda _ fun f => f.measurable

中文:
定理 measurable_apply'
  结论: [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
  证明: measurable_pi_lambda _ fun f => f.measurable

Depends on / 依赖: f.measurable, measurable, measurable_pi_lambda
-/
theorem measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] : Measurable fun (x : E) (f : E ->L[𝕜] F) => f x :=
  measurable_pi_lambda _ fun f => f.measurable

/--
theorem `measurable_coe` / 定理 `measurable_coe`

English:
theorem measurable_coe
  given: [MeasurableSpace F] [BorelSpace F]
  proof: measurable_pi_lambda _ measurable_apply

中文:
定理 measurable_coe
  条件: [MeasurableSpace F] [BorelSpace F]
  证明: measurable_pi_lambda _ measurable_apply

Depends on / 依赖: measurable_apply, measurable_pi_lambda
-/
theorem measurable_coe [MeasurableSpace F] [BorelSpace F] :
    Measurable fun (f : E ->L[𝕜] F) (x : E) => f x :=
  measurable_pi_lambda _ measurable_apply

end ContinuousLinearMap

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[fun_prop]
/--
theorem `Measurable.apply_continuousLinearMap` / 定理 `Measurable.apply_continuousLinearMap`

English:
theorem Measurable.apply_continuousLinearMap
  given: {φ : α -> F ->L[𝕜] E} (hφ : Measurable φ) (v : F)
  proof: (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ

@[fun_prop]

中文:
定理 Measurable.apply_continuousLinearMap
  条件: {φ : α -> F ->L[𝕜] E} (hφ : Measurable φ) (v : F)
  证明: (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, measurable, measurable.comp
-/
theorem Measurable.apply_continuousLinearMap {φ : α -> F ->L[𝕜] E} (hφ : Measurable φ) (v : F) :
    Measurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ

@[fun_prop]
/--
theorem `AEMeasurable.apply_continuousLinearMap` / 定理 `AEMeasurable.apply_continuousLinearMap`

English:
theorem AEMeasurable.apply_continuousLinearMap
  statement: {φ : α -> F ->L[𝕜] E} {μ : Measure α}
  proof: (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ

中文:
定理 AEMeasurable.apply_continuousLinearMap
  结论: {φ : α -> F ->L[𝕜] E} {μ : Measure α}
  证明: (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, comp_aemeasurable, measurable, measurable.comp_aemeasurable
-/
theorem AEMeasurable.apply_continuousLinearMap {φ : α -> F ->L[𝕜] E} {μ : Measure α}
    (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ

end ContinuousLinearMapNontriviallyNormedField

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]
variable [BorelSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [BorelSpace E]

/--
theorem `measurable_smul_const` / 定理 `measurable_smul_const`

English:
theorem measurable_smul_const
  given: {f : α -> 𝕜} {c : E} (hc : c != 0)
  proof: (isClosedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff

中文:
定理 measurable_smul_const
  条件: {f : α -> 𝕜} {c : E} (hc : c != 0)
  证明: (isClosedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff

Depends on / 依赖: isClosedEmbedding_smul_left, measurableEmbedding, measurableEmbedding.measurable_comp_iff, measurable_comp_iff
-/
theorem measurable_smul_const {f : α -> 𝕜} {c : E} (hc : c != 0) :
    (Measurable fun x => f x • c) ↔ Measurable f :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff

/--
theorem `aemeasurable_smul_const` / 定理 `aemeasurable_smul_const`

English:
theorem aemeasurable_smul_const
  given: {f : α -> 𝕜} {μ : Measure α} {c : E} (hc : c != 0)
  proof: (isClosedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff

中文:
定理 aemeasurable_smul_const
  条件: {f : α -> 𝕜} {μ : Measure α} {c : E} (hc : c != 0)
  证明: (isClosedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff

Depends on / 依赖: aemeasurable_comp_iff, isClosedEmbedding_smul_left, measurableEmbedding, measurableEmbedding.aemeasurable_comp_iff
-/
theorem aemeasurable_smul_const {f : α -> 𝕜} {μ : Measure α} {c : E} (hc : c != 0) :
    AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff

end NormedSpace
