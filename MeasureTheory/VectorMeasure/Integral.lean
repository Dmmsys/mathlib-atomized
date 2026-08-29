/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Yongxi Lin, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.SetToL1
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Integral of vector-valued function against vector measure

We extend the definition of the Bochner integral (of vector-valued function against `ℝ≥0∞`-valued
measure) to vector measures through a bilinear pairing.
Let `E`, `F` be normed vector spaces, and `G` be a Banach space (complete normed vector space).
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] G` and an `F`-valued vector measure `μ`
on a measurable space `X`.
For an integrable function `f : X → E` with respect to the total variation of the vector measure
on `X` informally written `μ ∘ B.flip`, we define the `G`-valued integral, which is informally
written `∫ B (f x) ∂μ x`.

Such integral is defined through the general setting `setToFun` which sends a set function to the
integral of integrable functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The integral against vector measures is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on integrable functions `f` as `setToFun (...) f`.

## Notations

* `∫ᵛ x, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against the `F`-valued
  vector measure `μ` paired through `B`.
* `∫ᵛ x, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is an `F`-valued
  vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.
* `∫ᵛ x in s, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against
  the `F`-valued vector measure `μ` paired through `B`, on the set `s`.
* `∫ᵛ x in s, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is
  an `F`-valued vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x in s, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.

## Note

Let `μ` be a vector measure and `B` be a continuous linear pairing.
We often consider integrable functions with respect to the total variation of
`μ.transpose B` = `μ.mapRange B.flip.toAddMonoidHom B.flip.continuous`, which is the reference
measure for the pairing integral.

When `f` is not integrable with respect to `μ.variation`, the value of
`μ.integral B f` is set to `0`. This is an analogous convention to the Bochner integral. However,
there are cases where a natural definition of the integral as an unconditional sum exists, but `f`
is not integrable in this sense: Let `μ` be the `L∞(ℕ)`-valued measure on `ℕ` defined by extending
`{n} ↦ (0,0,..., 1/(n+1),0,0,...)` and `B` be the trivial coupling (the scalar multiplication by
`ℝ`). The total variation is `∑ n, 1/(n+1) = ∞`, but the sum of `(0,...,0,1/n,0,...)` in `L∞(ℕ)` is
unconditionally convergent.

-/

public section

open Set MeasureTheory VectorMeasure ContinuousLinearMap Filter Topology
open scoped ENNReal NNReal

variable {ι X Y E F G H : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
  [NormedAddCommGroup H] [NormedSpace Real H]

namespace MeasureTheory

section cbmApplyMeasure

/-- The composition of the vector measure with the linear pairing, giving the reference
vector measure. -/
@[expose]
/--
Definition of `VectorMeasure.transpose` / `VectorMeasure.transpose` 的定义

English:
definition VectorMeasure.transpose
  signature: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  body: μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

中文:
定义 VectorMeasure.transpose
  签名: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  定义体: μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

Depends on / 依赖: B.flip.continuous, B.flip.toAddMonoidHom, continuous, mapRange, toAddMonoidHom
-/
noncomputable def VectorMeasure.transpose (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    VectorMeasure X (E ->L[Real] G) := μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

/--
Definition of `cbmApplyMeasure` / `cbmApplyMeasure` 的定义

English:
definition cbmApplyMeasure
  signature: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X)
  body: μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

中文:
定义 cbmApplyMeasure
  签名: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G) (s : Set X)
  定义体: μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

Depends on / 依赖: transpose
-/
noncomputable def cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) :
    E ->L[Real] G where
  toFun x := μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

/--
lemma `transpose_eq_cbmApplyMeasure` / 引理 `transpose_eq_cbmApplyMeasure`

English:
lemma transpose_eq_cbmApplyMeasure
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by rfl

@[simp]

中文:
引理 transpose_eq_cbmApplyMeasure
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by rfl

@[simp]
-/
lemma transpose_eq_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    μ.transpose B = cbmApplyMeasure μ B := by rfl

@[simp]
/--
theorem `cbmApplyMeasure_apply` / 定理 `cbmApplyMeasure_apply`

English:
theorem cbmApplyMeasure_apply
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) (x : E)
  proof: by
  rfl

中文:
定理 cbmApplyMeasure_apply
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G) (s : Set X) (x : E)
  证明: by
  rfl
-/
theorem cbmApplyMeasure_apply (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) (x : E) :
    cbmApplyMeasure μ B s x = B x (μ s) := by
  rfl

/--
theorem `cbmApplyMeasure_union` / 定理 `cbmApplyMeasure_union`

English:
theorem cbmApplyMeasure_union
  statement: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) {s t : Set X}
  proof: by
  ext x
  simp [of_union hdisj hs ht]

中文:
定理 cbmApplyMeasure_union
  结论: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G) {s t : Set X}
  证明: by
  ext x
  simp [of_union hdisj hs ht]

Depends on / 依赖: of_union
-/
theorem cbmApplyMeasure_union (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    cbmApplyMeasure μ B (s union t) = cbmApplyMeasure μ B s + cbmApplyMeasure μ B t := by
  ext x
  simp [of_union hdisj hs ht]

/--
theorem `norm_cbmApplyMeasure_le` / 定理 `norm_cbmApplyMeasure_le`

English:
theorem norm_cbmApplyMeasure_le
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X)
  proof: by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

中文:
定理 norm_cbmApplyMeasure_le
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G) (s : Set X)
  证明: by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

Depends on / 依赖: cbmApplyMeasure_apply, mul_right_comm, opNorm_le_iff
-/
theorem norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) :
    ‖cbmApplyMeasure μ B s‖ <= ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

/--
theorem `dominatedFinMeasAdditive_cbmApplyMeasure` / 定理 `dominatedFinMeasAdditive_cbmApplyMeasure`

English:
theorem dominatedFinMeasAdditive_cbmApplyMeasure
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  apply (norm_cbmApplyMeasure_le _ _ _).trans
  gcongr
  exact norm_measure_le_variation hsf.ne

中文:
定理 dominatedFinMeasAdditive_cbmApplyMeasure
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  apply (norm_cbmApplyMeasure_le _ _ _).trans
  gcongr
  exact norm_measure_le_variation hsf.ne

Depends on / 依赖: cbmApplyMeasure_union, hsf.ne, norm_cbmApplyMeasure_le, norm_measure_le_variation
-/
theorem dominatedFinMeasAdditive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    DominatedFinMeasAdditive μ.variation (μ.transpose B) ‖B‖ := by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  apply (norm_cbmApplyMeasure_le _ _ _).trans
  gcongr
  exact norm_measure_le_variation hsf.ne

/--
theorem `dominatedFinMeasAdditive_transpose_cbmApplyMeasure` / 定理 `dominatedFinMeasAdditive_transpose_cbmApplyMeasure`

English:
theorem dominatedFinMeasAdditive_transpose_cbmApplyMeasure
  proof: by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  simpa using! norm_measure_le_variation hsf.ne

中文:
定理 dominatedFinMeasAdditive_transpose_cbmApplyMeasure
  证明: by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  simpa using! norm_measure_le_variation hsf.ne

Depends on / 依赖: cbmApplyMeasure_union, hsf.ne, norm_measure_le_variation
-/
theorem dominatedFinMeasAdditive_transpose_cbmApplyMeasure
    (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    DominatedFinMeasAdditive (μ.transpose B).variation (μ.transpose B) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf => ?_⟩
  simpa using! norm_measure_le_variation hsf.ne

end cbmApplyMeasure

namespace VectorMeasure

variable (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) {C : E ->L[Real] F ->L[Real] G}
  {f g : X -> E} {φ : X -> Y}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `transpose_zero` / 引理 `transpose_zero`

English:
lemma transpose_zero
  statement: (0 : VectorMeasure X F).transpose B = 0
  proof: by
  simp [transpose]

中文:
引理 transpose_zero
  结论: (0 : VectorMeasure X F).transpose B = 0
  证明: by
  simp [transpose]
-/
@[simp] lemma transpose_zero : (0 : VectorMeasure X F).transpose B = 0 := by
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `transpose_restrict` / 引理 `transpose_restrict`

English:
lemma transpose_restrict
  given: (s : Set X)
  proof: by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs]

中文:
引理 transpose_restrict
  条件: (s : Set X)
  证明: by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs]

Depends on / 依赖: MeasurableSet, VectorMeasure, VectorMeasure.restrict_apply, restrict_apply, restrict_not_measurable, transpose
-/
lemma transpose_restrict (s : Set X) :
    (μ.restrict s).transpose B = (μ.transpose B).restrict s := by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `transpose_map` / 引理 `transpose_map`

English:
lemma transpose_map
  statement: (μ.map φ).transpose B = (μ.transpose B).map φ
  proof: by
  by_cases hφ : Measurable φ; swap
  · simp [map, hφ]
  ext s hs
  simp [transpose, map_apply, hs, hφ]

中文:
引理 transpose_map
  结论: (μ.map φ).transpose B = (μ.transpose B).map φ
  证明: by
  by_cases hφ : Measurable φ; swap
  · simp [map, hφ]
  ext s hs
  simp [transpose, map_apply, hs, hφ]

Depends on / 依赖: Measurable, map_apply, transpose
-/
lemma transpose_map : (μ.map φ).transpose B = (μ.transpose B).map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [map, hφ]
  ext s hs
  simp [transpose, map_apply, hs, hφ]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `transpose_add` / 引理 `transpose_add`

English:
lemma transpose_add
  proof: by
  simp [transpose]

中文:
引理 transpose_add
  证明: by
  simp [transpose]

Depends on / 依赖: transpose
-/
lemma transpose_add :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

/--
lemma `transpose_smul` / 引理 `transpose_smul`

English:
lemma transpose_smul
  given: (c : Real)
  proof: by
  simp [transpose, mapRange_smul]

中文:
引理 transpose_smul
  条件: (c : 实数)
  证明: by
  simp [transpose, mapRange_smul]

Depends on / 依赖: mapRange_smul, transpose
-/
lemma transpose_smul (c : Real) :
    (c • μ).transpose B = c • μ.transpose B := by
  simp [transpose, mapRange_smul]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `transpose_dirac` / 引理 `transpose_dirac`

English:
lemma transpose_dirac
  given: (x : X) (v : F)
  proof: by
  ext s hs : 1
  by_cases hx : x in s <;> simp [transpose, hx, hs]

中文:
引理 transpose_dirac
  条件: (x : X) (v : F)
  证明: by
  ext s hs : 1
  by_cases hx : x in s <;> simp [transpose, hx, hs]

Depends on / 依赖: transpose
-/
lemma transpose_dirac (x : X) (v : F) :
    (dirac x v).transpose B = dirac x (B.flip v) := by
  ext s hs : 1
  by_cases hx : x in s <;> simp [transpose, hx, hs]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `variation_transpose_le` / 引理 `variation_transpose_le`

English:
lemma variation_transpose_le
  proof: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  apply opENorm_le_bound _ (fun x => ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opENorm, le_opENorm, enorm_measure_le_varia

中文:
引理 variation_transpose_le
  证明: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  apply opENorm_le_bound _ (fun x => ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opENorm, le_opENorm, enorm_measure_le_varia

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_coe, Measure, Measure.nnreal_smul_coe_apply, Measure.smul_apply, coe_coe, enorm_eq_nnnorm, enorm_measure_le_variation, flip_apply, le_of_eq, le_opENorm, mapRange_apply, nnreal_smul_coe_apply, opENorm_le_bound, smul_apply, toAddMonoidHom_coe, transpose, variation_le_of_forall_enorm_le
-/
lemma variation_transpose_le :
    (μ.transpose B).variation <= ‖B‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  apply opENorm_le_bound _ (fun x => ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opENorm, le_opENorm, enorm_measure_le_variation, ← enorm_eq_nnnorm]
  exact le_of_eq (by ring)

/--
lemma `absolutelyContinuous_variation_transpose` / 引理 `absolutelyContinuous_variation_transpose`

English:
lemma absolutelyContinuous_variation_transpose
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)

中文:
引理 absolutelyContinuous_variation_transpose
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)

Depends on / 依赖: Measure, Measure.absolutelyContinuous_of_le_smul, absolutelyContinuous_of_le_smul, variation_transpose_le
-/
lemma absolutelyContinuous_variation_transpose (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    (μ.transpose B).variation ≪ μ.variation :=
  Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ.variation] :
  body: isFiniteMeasure_of_le _ (variation_transpose_le μ B)

中文:
实例 [IsFiniteMeasure
  签名: μ.variation] :
  定义体: isFiniteMeasure_of_le _ (variation_transpose_le μ B)

Depends on / 依赖: isFiniteMeasure_of_le, variation_transpose_le
-/
instance [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (μ.transpose B).variation :=
  isFiniteMeasure_of_le _ (variation_transpose_le μ B)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `variation_transpose_eq_smul` / 引理 `variation_transpose_eq_smul`

English:
lemma variation_transpose_eq_smul
  statement: [Nontrivial E] {C : Real>=0}
  proof: by
  apply le_antisymm
  · apply (variation_transpose_le _ _).trans
    gcongr
    apply opNNNorm_le_bound _ _ (fun x => opNNNorm_le_bound _ _ (fun y => by simp [hB]))
  · rcases eq_or_ne C 0 with rfl | hC
    · simp [Measure.zero_le]
    suffices μ.variation <= C⁻¹ • (μ.transpose B).variation by
  

中文:
引理 variation_transpose_eq_smul
  结论: [Nontrivial E] {C : 实数>=0}
  证明: by
  apply le_antisymm
  · apply (variation_transpose_le _ _).trans
    gcongr
    apply opNNNorm_le_bound _ _ (fun x => opNNNorm_le_bound _ _ (fun y => by simp [hB]))
  · rcases eq_or_ne C 0 with rfl | hC
    · simp [Measure.zero_le]
    suffices μ.variation <= C⁻¹ • (μ.transpose B).variation by
  

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_coe, Measure, Measure.zero_le, eq_or_ne, le_antisymm, mapRange_apply, one_smul, opNNNorm_le_bound, smul_smul, toAddMonoidHom_coe, transpose, variation, variation_le_of_forall_enorm_le, variation_transpose_le, zero_le
-/
lemma variation_transpose_eq_smul [Nontrivial E] {C : Real>=0}
    (hB : forall x y, ‖B x y‖₊ = C * ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = C • μ.variation := by
  apply le_antisymm
  · apply (variation_transpose_le _ _).trans
    gcongr
    apply opNNNorm_le_bound _ _ (fun x => opNNNorm_le_bound _ _ (fun y => by simp [hB]))
  · rcases eq_or_ne C 0 with rfl | hC
    · simp [Measure.zero_le]
    suffices μ.variation <= C⁻¹ • (μ.transpose B).variation by
      grw [this, smul_smul, mul_inv_cancel₀ hC, one_smul]
    apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    have : ‖μ s‖ₑ <= C⁻¹ • ‖(μ.transpose B) s‖ₑ := by
      simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe]
      obtain ⟨x, hx⟩ : exists (x : E), x != 0 := exists_ne 0
      have : ‖B.flip (μ s) x‖₊ <= ‖B.flip (μ s)‖₊ * ‖x‖₊ := le_opNNNorm _ _
      simp only [flip_apply, hB] at this
      rw [mul_right_comm]; rw [mul_le_mul_iff_left₀ (by simpa)]; rw [← le_div_iff₀' (by positivity)]; rw [div_eq_inv_mul] at this
      change ENNReal.ofNNReal _ <= ENNReal.ofNNReal _
      gcongr
    grw [this, enorm_measure_le_variation, Measure.smul_apply]

/--
lemma `variation_transpose_eq` / 引理 `variation_transpose_eq`

English:
lemma variation_transpose_eq
  given: [Nontrivial E] (hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊)
  proof: by
  have : μ.variation = (1 : Real>=0) • μ.variation := by simp
  rw [this]
  apply variation_transpose_eq_smul
  simpa using hB

中文:
引理 variation_transpose_eq
  条件: [Nontrivial E] (hB : 对任意 x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊)
  证明: by
  have : μ.variation = (1 : Real>=0) • μ.variation := by simp
  rw [this]
  apply variation_transpose_eq_smul
  simpa using hB

Depends on / 依赖: variation, variation_transpose_eq_smul
-/
lemma variation_transpose_eq [Nontrivial E] (hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = μ.variation := by
  have : μ.variation = (1 : Real>=0) • μ.variation := by simp
  rw [this]
  apply variation_transpose_eq_smul
  simpa using hB

/--
lemma `variation_transpose_lsmul` / 引理 `variation_transpose_lsmul`

English:
lemma variation_transpose_lsmul
  proof: by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

中文:
引理 variation_transpose_lsmul
  证明: by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]
-/
@[simp] lemma variation_transpose_lsmul :
    (μ.transpose (ContinuousLinearMap.lsmul Real Real)).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/--
lemma `variation_transpose_lsmul_flip` / 引理 `variation_transpose_lsmul_flip`

English:
lemma variation_transpose_lsmul_flip
  given: [Nontrivial E] {μ : SignedMeasure X}
  proof: by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

中文:
引理 variation_transpose_lsmul_flip
  条件: [Nontrivial E] {μ : SignedMeasure X}
  证明: by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]
-/
@[simp] lemma variation_transpose_lsmul_flip [Nontrivial E] {μ : SignedMeasure X} :
    (μ.transpose (ContinuousLinearMap.lsmul Real Real (E := E)).flip).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/--
Definition of `Integrable` / `Integrable` 的定义

English:
abbreviation Integrable
  signature: (μ : VectorMeasure X F) (f : X -> E)
  body: MeasureTheory.Integrable f μ.variation

中文:
缩写 Integrable
  签名: (μ : VectorMeasure X F) (f : X -> E)
  定义体: MeasureTheory.Integrable f μ.variation
-/
protected abbrev Integrable (μ : VectorMeasure X F) (f : X -> E) : Prop :=
  MeasureTheory.Integrable f μ.variation

/--
Definition of `IntegrableOn` / `IntegrableOn` 的定义

English:
abbreviation IntegrableOn
  body: (μ.restrict s).Integrable f

中文:
缩写 IntegrableOn
  定义体: (μ.restrict s).Integrable f
-/
protected abbrev IntegrableOn
    (μ : VectorMeasure X F) (f : X -> E) (s : Set X) : Prop :=
  (μ.restrict s).Integrable f

/--
Definition of `integral` / `integral` 的定义

English:
definition integral
  signature: (μ : VectorMeasure X F) (f : X -> E) (B : E ->L[Real] F ->L[Real] G)
  body: setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:65"; "μ:65"]" => integral μ r B

中文:
定义 integral
  签名: (μ : VectorMeasure X F) (f : X -> E) (B : E ->L[实数] F ->L[实数] G)
  定义体: setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:65"; "μ:65"]" => integral μ r B

Depends on / 依赖: dominatedFinMeasAdditive_cbmApplyMeasure, setToFun, transpose, variation
-/
noncomputable def integral (μ : VectorMeasure X F) (f : X -> E) (B : E ->L[Real] F ->L[Real] G) : G :=
  setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:65"; "μ:65"]" => integral μ r B

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral μ r (lsmul Real Real)

/-- The special case of the pairing integral where the pairing is just the flip of scalar
multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂<•"μ:70 => integral μ r (lsmul Real Real).flip

@[inherit_doc integral]
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" =>
  integral (VectorMeasure.restrict μ s) r B

/-- The special case of the pairing integral in a set where the pairing is just the scalar
multiplication by `ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul Real Real)

/-- The special case of the pairing integral in a set where the pairing is just the flip of the
scalar multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂<•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul Real Real).flip

variable {μ ν B}

/--
lemma `integral_eq_setToFun` / 引理 `integral_eq_setToFun`

English:
lemma integral_eq_setToFun
  statement: ∫ᵛ x, f x ∂[B; μ] = setToFun μ.variation (μ.transpose B)
  proof: by rfl

中文:
引理 integral_eq_setToFun
  结论: ∫ᵛ x, f x ∂[B; μ] = setToFun μ.variation (μ.transpose B)
  证明: by rfl
-/
lemma integral_eq_setToFun : ∫ᵛ x, f x ∂[B; μ] = setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f := by rfl

/--
lemma `integral_eq_setToFun_transpose` / 引理 `integral_eq_setToFun_transpose`

English:
lemma integral_eq_setToFun_transpose
  given: (hf : μ.Integrable f)
  proof: setToFun_congr_measure_of_integrable _ (by simp) (variation_transpose_le _ _) _ _ _ hf

中文:
引理 integral_eq_setToFun_transpose
  条件: (hf : μ.整数egrable f)
  证明: setToFun_congr_measure_of_integrable _ (by simp) (variation_transpose_le _ _) _ _ _ hf

Depends on / 依赖: setToFun_congr_measure_of_integrable, variation_transpose_le
-/
lemma integral_eq_setToFun_transpose (hf : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ] = setToFun (μ.transpose B).variation (μ.transpose B)
      (dominatedFinMeasAdditive_transpose_cbmApplyMeasure μ B) f :=
  setToFun_congr_measure_of_integrable _ (by simp) (variation_transpose_le _ _) _ _ _ hf

/--
theorem `integral_of_not_completeSpace` / 定理 `integral_of_not_completeSpace`

English:
theorem integral_of_not_completeSpace
  given: (hG : ¬CompleteSpace G)
  proof: by
  simp [integral, setToFun, hG]

中文:
定理 integral_of_not_completeSpace
  条件: (hG : ¬CompleteSpace G)
  证明: by
  simp [integral, setToFun, hG]

Depends on / 依赖: integral, setToFun
-/
theorem integral_of_not_completeSpace (hG : ¬CompleteSpace G) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun, hG]

variable {f g : X -> E} {μ ν : VectorMeasure X F} {B C : E ->L[Real] F ->L[Real] G}

@[simp]
/--
theorem `transpose_zero_cbm` / 定理 `transpose_zero_cbm`

English:
theorem transpose_zero_cbm
  given: (μ : VectorMeasure X F)
  proof: by
  ext
  simp [transpose]

中文:
定理 transpose_zero_cbm
  条件: (μ : VectorMeasure X F)
  证明: by
  ext
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_zero_cbm (μ : VectorMeasure X F) :
    μ.transpose (0 : E ->L[Real] F ->L[Real] G) = 0 := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_add_vectorMeasure` / 定理 `transpose_add_vectorMeasure`

English:
theorem transpose_add_vectorMeasure
  given: (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  simp [transpose]

中文:
定理 transpose_add_vectorMeasure
  条件: (μ ν : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_add_vectorMeasure (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_add_cbm` / 定理 `transpose_add_cbm`

English:
theorem transpose_add_cbm
  given: (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G)
  proof: by
  ext
  simp [transpose]

@[simp]

中文:
定理 transpose_add_cbm
  条件: (μ : VectorMeasure X F) (B C : E ->L[实数] F ->L[实数] G)
  证明: by
  ext
  simp [transpose]

@[simp]

Depends on / 依赖: transpose
-/
theorem transpose_add_cbm (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G) :
    μ.transpose (B + C) = μ.transpose B + μ.transpose C := by
  ext
  simp [transpose]

@[simp]
/--
theorem `transpose_finsetSum_vectorMeasure` / 定理 `transpose_finsetSum_vectorMeasure`

English:
theorem transpose_finsetSum_vectorMeasure
  statement: (μ : ι -> VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]

中文:
定理 transpose_finsetSum_vectorMeasure
  结论: (μ : ι -> VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_insert, classical, induction_on, insert, sum_insert
-/
theorem transpose_finsetSum_vectorMeasure (μ : ι -> VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
    (s : Finset ι) :
    (∑ i in s, μ i).transpose B = ∑ i in s, (μ i).transpose B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]
/--
theorem `transpose_finsetSum_cbm` / 定理 `transpose_finsetSum_cbm`

English:
theorem transpose_finsetSum_cbm
  given: (μ : VectorMeasure X F) (B : ι -> E ->L[Real] F ->L[Real] G) (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

中文:
定理 transpose_finsetSum_cbm
  条件: (μ : VectorMeasure X F) (B : ι -> E ->L[实数] F ->L[实数] G) (s : Finset ι)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_insert, classical, induction_on, insert, sum_insert
-/
theorem transpose_finsetSum_cbm (μ : VectorMeasure X F) (B : ι -> E ->L[Real] F ->L[Real] G) (s : Finset ι) :
    μ.transpose (∑ i in s, B i) = ∑ i in s, μ.transpose (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_neg_vectorMeasure` / 定理 `transpose_neg_vectorMeasure`

English:
theorem transpose_neg_vectorMeasure
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  ext
  simp [transpose]

中文:
定理 transpose_neg_vectorMeasure
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  ext
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_neg_vectorMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    (-μ).transpose B = - (μ.transpose B) := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_neg_cbm` / 定理 `transpose_neg_cbm`

English:
theorem transpose_neg_cbm
  given: (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  ext
  simp [transpose]

中文:
定理 transpose_neg_cbm
  条件: (μ : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  ext
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_neg_cbm (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    μ.transpose (-B) = - (μ.transpose B) := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_sub_vectorMeasure` / 定理 `transpose_sub_vectorMeasure`

English:
theorem transpose_sub_vectorMeasure
  given: (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
  proof: by
  ext
  simp [transpose]

中文:
定理 transpose_sub_vectorMeasure
  条件: (μ ν : VectorMeasure X F) (B : E ->L[实数] F ->L[实数] G)
  证明: by
  ext
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_sub_vectorMeasure (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) :
    (μ - ν).transpose B = μ.transpose B - ν.transpose B := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transpose_sub_cbm` / 定理 `transpose_sub_cbm`

English:
theorem transpose_sub_cbm
  given: (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G)
  proof: by
  ext
  simp [transpose]

中文:
定理 transpose_sub_cbm
  条件: (μ : VectorMeasure X F) (B C : E ->L[实数] F ->L[实数] G)
  证明: by
  ext
  simp [transpose]

Depends on / 依赖: transpose
-/
theorem transpose_sub_cbm (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G) :
    μ.transpose (B - C) = μ.transpose B - μ.transpose C := by
  ext
  simp [transpose]

section Function

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `integral_undef` / 定理 `integral_undef`

English:
theorem integral_undef
  given: (h : ¬ μ.Integrable f)
  proof: by
  simp [integral, setToFun_undef _ h]

@[simp]

中文:
定理 integral_undef
  条件: (h : ¬ μ.整数egrable f)
  证明: by
  simp [integral, setToFun_undef _ h]

@[simp]

Depends on / 依赖: integral, setToFun_undef
-/
theorem integral_undef (h : ¬ μ.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun_undef _ h]

@[simp]
/--
theorem `integral_zero` / 定理 `integral_zero`

English:
theorem integral_zero
  statement: ∫ᵛ _, 0 ∂[B; μ] = 0
  proof: setToFun_zero _

中文:
定理 integral_zero
  结论: ∫ᵛ _, 0 ∂[B; μ] = 0
  证明: setToFun_zero _

Depends on / 依赖: setToFun_zero
-/
theorem integral_zero : ∫ᵛ _, 0 ∂[B; μ] = 0 :=
  setToFun_zero _

/--
theorem `integral_congr_ae` / 定理 `integral_congr_ae`

English:
theorem integral_congr_ae
  given: (h : f =ᵐ[μ.variation] g)
  proof: setToFun_congr_ae _ h

中文:
定理 integral_congr_ae
  条件: (h : f =ᵐ[μ.variation] g)
  证明: setToFun_congr_ae _ h

Depends on / 依赖: setToFun_congr_ae
-/
theorem integral_congr_ae (h : f =ᵐ[μ.variation] g) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_congr_ae _ h

/--
theorem `integral_eq_zero_of_ae` / 定理 `integral_eq_zero_of_ae`

English:
theorem integral_eq_zero_of_ae
  given: (hf : f =ᵐ[μ.variation] 0)
  proof: by
  simp [integral_congr_ae hf]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
定理 integral_eq_zero_of_ae
  条件: (hf : f =ᵐ[μ.variation] 0)
  证明: by
  simp [integral_congr_ae hf]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: integral_congr_ae
-/
theorem integral_eq_zero_of_ae (hf : f =ᵐ[μ.variation] 0) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral_congr_ae hf]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.add` / 引理 `Integrable.add`

English:
lemma Integrable.add
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: MeasureTheory.Integrable.add hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.add
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: MeasureTheory.Integrable.add hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in
-/
@[to_fun] lemma Integrable.add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    μ.Integrable (f + g) :=
  MeasureTheory.Integrable.add hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.neg` / 引理 `Integrable.neg`

English:
lemma Integrable.neg
  given: (hf : μ.Integrable f)
  proof: MeasureTheory.Integrable.neg hf

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.neg
  条件: (hf : μ.整数egrable f)
  证明: MeasureTheory.Integrable.neg hf

omit [NormedSpace Real E] [NormedSpace Real F] in
-/
@[to_fun] lemma Integrable.neg (hf : μ.Integrable f) :
    μ.Integrable (-f) :=
  MeasureTheory.Integrable.neg hf

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.sub` / 引理 `Integrable.sub`

English:
lemma Integrable.sub
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: MeasureTheory.Integrable.sub hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.sub
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: MeasureTheory.Integrable.sub hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in
-/
@[to_fun] lemma Integrable.sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    μ.Integrable (f - g) :=
  MeasureTheory.Integrable.sub hf hg

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.smul` / 引理 `Integrable.smul`

English:
lemma Integrable.smul
  statement: {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
  proof: MeasureTheory.Integrable.smul c hf

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.smul
  结论: {𝕜 : 类型} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
  证明: MeasureTheory.Integrable.smul c hf

omit [NormedSpace Real E] [NormedSpace Real F] in
-/
@[to_fun] lemma Integrable.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] (c : 𝕜) (hf : μ.Integrable f) :
    μ.Integrable (c • f) :=
  MeasureTheory.Integrable.smul c hf

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
theorem `Integrable.finsetSum` / 定理 `Integrable.finsetSum`

English:
theorem Integrable.finsetSum
  statement: {ι : Type*} (s : Finset ι) {f : ι -> X -> E}
  proof: integrable_finsetSum' s hf

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
定理 Integrable.finsetSum
  结论: {ι : 类型} (s : Finset ι) {f : ι -> X -> E}
  证明: integrable_finsetSum' s hf

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: integrable_finsetSum
-/
theorem Integrable.finsetSum {ι : Type*} (s : Finset ι) {f : ι -> X -> E}
    (hf : forall i in s, μ.Integrable (f i)) : μ.Integrable (∑ i in s, f i) :=
  integrable_finsetSum' s hf

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
theorem `Integrable.fun_finsetSum` / 定理 `Integrable.fun_finsetSum`

English:
theorem Integrable.fun_finsetSum
  statement: {ι : Type*} (s : Finset ι) {f : ι -> X -> E}
  proof: integrable_finsetSum s hf

中文:
定理 Integrable.fun_finsetSum
  结论: {ι : 类型} (s : Finset ι) {f : ι -> X -> E}
  证明: integrable_finsetSum s hf

Depends on / 依赖: integrable_finsetSum
-/
theorem Integrable.fun_finsetSum {ι : Type*} (s : Finset ι) {f : ι -> X -> E}
    (hf : forall i in s, μ.Integrable (f i)) : μ.Integrable (fun x => ∑ i in s, f i x) :=
  integrable_finsetSum s hf

/--
theorem `integral_fun_add` / 定理 `integral_fun_add`

English:
theorem integral_fun_add
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: setToFun_add _ hf hg

中文:
定理 integral_fun_add
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: setToFun_add _ hf hg

Depends on / 依赖: setToFun_add
-/
theorem integral_fun_add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_add _ hf hg

/--
theorem `integral_add` / 定理 `integral_add`

English:
theorem integral_add
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: integral_fun_add hf hg

中文:
定理 integral_add
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: integral_fun_add hf hg

Depends on / 依赖: integral_fun_add
-/
theorem integral_add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := integral_fun_add hf hg

/--
theorem `integral_finsetSum` / 定理 `integral_finsetSum`

English:
theorem integral_finsetSum
  statement: (s : Finset ι) {f : ι -> X -> E}
  proof: setToFun_finsetSum _ s hf

中文:
定理 integral_finsetSum
  结论: (s : Finset ι) {f : ι -> X -> E}
  证明: setToFun_finsetSum _ s hf

Depends on / 依赖: setToFun_finsetSum
-/
theorem integral_finsetSum (s : Finset ι) {f : ι -> X -> E}
    (hf : forall i in s, μ.Integrable (f i)) :
    ∫ᵛ x, ∑ i in s, f i x ∂[B; μ] = ∑ i in s, ∫ᵛ x, f i x ∂[B; μ] :=
  setToFun_finsetSum _ s hf

variable (f μ B) in
@[integral_simps]
/--
theorem `integral_fun_neg` / 定理 `integral_fun_neg`

English:
theorem integral_fun_neg
  given: (f : X -> E)
  proof: setToFun_neg _ f

中文:
定理 integral_fun_neg
  条件: (f : X -> E)
  证明: setToFun_neg _ f

Depends on / 依赖: setToFun_neg
-/
theorem integral_fun_neg (f : X -> E) :
    ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ] :=
  setToFun_neg _ f

variable (f μ B) in
@[integral_simps]
/--
theorem `integral_neg` / 定理 `integral_neg`

English:
theorem integral_neg
  proof: integral_fun_neg μ B f

中文:
定理 integral_neg
  证明: integral_fun_neg μ B f

Depends on / 依赖: integral_fun_neg
-/
theorem integral_neg :
    ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ] := integral_fun_neg μ B f

/--
theorem `integral_fun_sub` / 定理 `integral_fun_sub`

English:
theorem integral_fun_sub
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: setToFun_sub _ hf hg

中文:
定理 integral_fun_sub
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: setToFun_sub _ hf hg

Depends on / 依赖: setToFun_sub
-/
theorem integral_fun_sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_sub _ hf hg

/--
theorem `integral_sub` / 定理 `integral_sub`

English:
theorem integral_sub
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: integral_fun_sub hf hg

中文:
定理 integral_sub
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: integral_fun_sub hf hg

Depends on / 依赖: integral_fun_sub
-/
theorem integral_sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, (f - g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := integral_fun_sub hf hg

variable (f μ B) in
@[integral_simps]
/--
theorem `integral_fun_smul` / 定理 `integral_fun_smul`

English:
theorem integral_fun_smul
  given: (c : Real) (f : X -> E)
  proof: setToFun_smul _ (by simp) c f

中文:
定理 integral_fun_smul
  条件: (c : 实数) (f : X -> E)
  证明: setToFun_smul _ (by simp) c f

Depends on / 依赖: setToFun_smul
-/
theorem integral_fun_smul (c : Real) (f : X -> E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  setToFun_smul _ (by simp) c f

variable (f μ B) in
@[integral_simps]
/--
theorem `integral_smul` / 定理 `integral_smul`

English:
theorem integral_smul
  given: (c : Real)
  proof: integral_fun_smul μ B c f

@[simp]

中文:
定理 integral_smul
  条件: (c : 实数)
  证明: integral_fun_smul μ B c f

@[simp]

Depends on / 依赖: integral_fun_smul
-/
theorem integral_smul (c : Real) :
    ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := integral_fun_smul μ B c f

@[simp]
/--
theorem `integral_const` / 定理 `integral_const`

English:
theorem integral_const
  given: [CompleteSpace G] [IsFiniteMeasure μ.variation] (c : E)
  proof: setToFun_const _ _

中文:
定理 integral_const
  条件: [CompleteSpace G] [IsFiniteMeasure μ.variation] (c : E)
  证明: setToFun_const _ _

Depends on / 依赖: setToFun_const
-/
theorem integral_const [CompleteSpace G] [IsFiniteMeasure μ.variation] (c : E) :
    ∫ᵛ _ : X, c ∂[B; μ] = B c (μ univ) :=
  setToFun_const _ _

end Function

section VectorMeasure

omit [NormedSpace Real E] [NormedSpace Real F] in
/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
@[nolint simpNF, simp]
/--
lemma `Integrable.zero_vectorMeasure` / 引理 `Integrable.zero_vectorMeasure`

English:
lemma Integrable.zero_vectorMeasure
  statement: (0 : VectorMeasure X F).Integrable f
  proof: by
  simp [VectorMeasure.Integrable]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.zero_vectorMeasure
  结论: (0 : VectorMeasure X F).整数egrable f
  证明: by
  simp [VectorMeasure.Integrable]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: Integrable, VectorMeasure, VectorMeasure.Integrable
-/
lemma Integrable.zero_vectorMeasure : (0 : VectorMeasure X F).Integrable f := by
  simp [VectorMeasure.Integrable]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.add_vectorMeasure` / 引理 `Integrable.add_vectorMeasure`

English:
lemma Integrable.add_vectorMeasure
  given: (hμ : μ.Integrable f) (hν : ν.Integrable f)
  proof: by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [variation_add_le]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.add_vectorMeasure
  条件: (hμ : μ.整数egrable f) (hν : ν.整数egrable f)
  证明: by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [variation_add_le]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: Integrable, Integrable.mono_measure, integrable_add_measure, mono_measure, variation_add_le
-/
lemma Integrable.add_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    (μ + ν).Integrable f := by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [variation_add_le]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.neg_vectorMeasure` / 引理 `Integrable.neg_vectorMeasure`

English:
lemma Integrable.neg_vectorMeasure
  given: (hμ : μ.Integrable f)
  proof: Integrable.mono_measure hμ (by simp)

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.neg_vectorMeasure
  条件: (hμ : μ.整数egrable f)
  证明: Integrable.mono_measure hμ (by simp)

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: Integrable, Integrable.mono_measure, mono_measure
-/
lemma Integrable.neg_vectorMeasure (hμ : μ.Integrable f) :
    (-μ).Integrable f :=
  Integrable.mono_measure hμ (by simp)

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.sub_vectorMeasure` / 引理 `Integrable.sub_vectorMeasure`

English:
lemma Integrable.sub_vectorMeasure
  given: (hμ : μ.Integrable f) (hν : ν.Integrable f)
  proof: by
  convert hμ.add_vectorMeasure hν.neg_vectorMeasure using 1
  exact sub_eq_add_neg μ ν

omit [NormedSpace Real E] in

中文:
引理 Integrable.sub_vectorMeasure
  条件: (hμ : μ.整数egrable f) (hν : ν.整数egrable f)
  证明: by
  convert hμ.add_vectorMeasure hν.neg_vectorMeasure using 1
  exact sub_eq_add_neg μ ν

omit [NormedSpace Real E] in

Depends on / 依赖: add_vectorMeasure, convert, neg_vectorMeasure, sub_eq_add_neg
-/
lemma Integrable.sub_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    (μ - ν).Integrable f := by
  convert hμ.add_vectorMeasure hν.neg_vectorMeasure using 1
  exact sub_eq_add_neg μ ν

omit [NormedSpace Real E] in
/--
lemma `Integrable.smul_vectorMeasure` / 引理 `Integrable.smul_vectorMeasure`

English:
lemma Integrable.smul_vectorMeasure
  given: (hμ : μ.Integrable f) (c : Real)
  proof: by
  apply Integrable.mono_measure (Integrable.smul_measure_nnreal hμ (c := ‖c‖₊))
  simp [variation_smul]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 Integrable.smul_vectorMeasure
  条件: (hμ : μ.整数egrable f) (c : 实数)
  证明: by
  apply Integrable.mono_measure (Integrable.smul_measure_nnreal hμ (c := ‖c‖₊))
  simp [variation_smul]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: Integrable, Integrable.mono_measure, Integrable.smul_measure_nnreal, mono_measure, smul_measure_nnreal, variation_smul
-/
lemma Integrable.smul_vectorMeasure (hμ : μ.Integrable f) (c : Real) :
    (c • μ).Integrable f := by
  apply Integrable.mono_measure (Integrable.smul_measure_nnreal hμ (c := ‖c‖₊))
  simp [variation_smul]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.finsetSum_vectorMeasure` / 引理 `Integrable.finsetSum_vectorMeasure`

English:
lemma Integrable.finsetSum_vectorMeasure
  statement: {ι : Type*} {μ : ι -> VectorMeasure X F} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_vectorMeasure (ih h.2)

omit [NormedSpace Real E] [NormedSpace Real

中文:
引理 Integrable.finsetSum_vectorMeasure
  结论: {ι : 类型} {μ : ι -> VectorMeasure X F} {s : Finset ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_vectorMeasure (ih h.2)

omit [NormedSpace Real E] [NormedSpace Real

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_insert, add_vectorMeasure, classical, forall_eq_or_imp, induction_on, insert, mem_insert, not_false_eq_true, sum_insert
-/
lemma Integrable.finsetSum_vectorMeasure {ι : Type*} {μ : ι -> VectorMeasure X F} {s : Finset ι}
    (h : forall i in s, (μ i).Integrable f) :
    (∑ i in s, μ i).Integrable f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_vectorMeasure (ih h.2)

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
lemma `Integrable.restrict` / 引理 `Integrable.restrict`

English:
lemma Integrable.restrict
  given: (hf : μ.Integrable f) {s : Set X}
  proof: by
  by_cases hs : MeasurableSet s
  · simpa [VectorMeasure.Integrable, transpose_restrict, variation_restrict hs] using
      MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp]

中文:
引理 Integrable.restrict
  条件: (hf : μ.整数egrable f) {s : Set X}
  证明: by
  by_cases hs : MeasurableSet s
  · simpa [VectorMeasure.Integrable, transpose_restrict, variation_restrict hs] using
      MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp]
-/
lemma Integrable.restrict (hf : μ.Integrable f) {s : Set X} :
    (μ.restrict s).Integrable f := by
  by_cases hs : MeasurableSet s
  · simpa [VectorMeasure.Integrable, transpose_restrict, variation_restrict hs] using
      MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp]
/--
theorem `integral_zero_vectorMeasure` / 定理 `integral_zero_vectorMeasure`

English:
theorem integral_zero_vectorMeasure
  proof: by simp [integral, FunLike.coe_zero]

中文:
定理 integral_zero_vectorMeasure
  证明: by simp [integral, FunLike.coe_zero]

Depends on / 依赖: FunLike, FunLike.coe_zero, coe_zero, integral
-/
theorem integral_zero_vectorMeasure :
    ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0 := by simp [integral, FunLike.coe_zero]

/--
lemma `integral_of_isEmpty` / 引理 `integral_of_isEmpty`

English:
lemma integral_of_isEmpty
  given: [IsEmpty X]
  statement: ∫ᵛ x, f x ∂[B; μ] = 0
  proof: by simp [eq_zero_of_isEmpty]

@[simp]

中文:
引理 integral_of_isEmpty
  条件: [IsEmpty X]
  结论: ∫ᵛ x, f x ∂[B; μ] = 0
  证明: by simp [eq_zero_of_isEmpty]

@[simp]

Depends on / 依赖: eq_zero_of_isEmpty
-/
lemma integral_of_isEmpty [IsEmpty X] : ∫ᵛ x, f x ∂[B; μ] = 0 := by simp [eq_zero_of_isEmpty]

@[simp]
/--
theorem `integral_smul_vectorMeasure` / 定理 `integral_smul_vectorMeasure`

English:
theorem integral_smul_vectorMeasure
  given: (f : X -> E) (c : Real)
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : (c • μ).variation = ‖c‖₊ • μ.variation := by
    simp [variation_smul]
  simp only [this]
  have : DominatedFinMeasAdditive μ.variation ((c • μ).transpose B) (‖c‖ * ‖B‖) := 

中文:
定理 integral_smul_vectorMeasure
  条件: (f : X -> E) (c : 实数)
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : (c • μ).variation = ‖c‖₊ • μ.variation := by
    simp [variation_smul]
  simp only [this]
  have : DominatedFinMeasAdditive μ.variation ((c • μ).transpose B) (‖c‖ * ‖B‖) := 

Depends on / 依赖: CompleteSpace, DominatedFinMeasAdditive, FunLike, FunLike.coe_smul, coe_smul, dominatedFinMeasAdditive_cbmApplyMeasure, integral, setToFun, setToFun_congr_smul_measure, setToFun_smul_left, simp_rw, transpose, transpose_smul, variation, variation_smul
-/
theorem integral_smul_vectorMeasure (f : X -> E) (c : Real) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : (c • μ).variation = ‖c‖₊ • μ.variation := by
    simp [variation_smul]
  simp only [this]
  have : DominatedFinMeasAdditive μ.variation ((c • μ).transpose B) (‖c‖ * ‖B‖) := by
    simp only [transpose_smul, FunLike.coe_smul]
    exact (dominatedFinMeasAdditive_cbmApplyMeasure μ B).smul c
  rw! [← setToFun_congr_smul_measure' _ this, transpose_smul]
  rfl

@[simp]
/--
theorem `integral_smul_nnreal_vectorMeasure` / 定理 `integral_smul_nnreal_vectorMeasure`

English:
theorem integral_smul_nnreal_vectorMeasure
  given: (f : X -> E) (c : Real>=0)
  proof: integral_smul_vectorMeasure f (c : Real)

中文:
定理 integral_smul_nnreal_vectorMeasure
  条件: (f : X -> E) (c : 实数>=0)
  证明: integral_smul_vectorMeasure f (c : Real)

Depends on / 依赖: integral_smul_vectorMeasure
-/
theorem integral_smul_nnreal_vectorMeasure (f : X -> E) (c : Real>=0) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  integral_smul_vectorMeasure f (c : Real)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `integral_add_vectorMeasure` / 定理 `integral_add_vectorMeasure`

English:
theorem integral_add_vectorMeasure
  given: (hμ : μ.Integrable f) (hν : ν.Integrable f)
  proof: setToFun_add_left'' (by simp [transpose]) hμ hν (by grw [variation_add_le])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

中文:
定理 integral_add_vectorMeasure
  条件: (hμ : μ.整数egrable f) (hν : ν.整数egrable f)
  证明: setToFun_add_left'' (by simp [transpose]) hμ hν (by grw [variation_add_le])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

Depends on / 依赖: norm_nonneg, setToFun_add_left, transpose, variation_add_le
-/
theorem integral_add_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ + ν] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν] :=
  setToFun_add_left'' (by simp [transpose]) hμ hν (by grw [variation_add_le])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

/--
theorem `integral_finsetSum_vectorMeasure` / 定理 `integral_finsetSum_vectorMeasure`

English:
theorem integral_finsetSum_vectorMeasure
  statement: {μ : ι -> VectorMeasure X F}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (Integrable.finsetSum_vectorMeasure hf.2)]; rw [ih

中文:
定理 integral_finsetSum_vectorMeasure
  结论: {μ : ι -> VectorMeasure X F}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (Integrable.finsetSum_vectorMeasure hf.2)]; rw [ih

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_insert, Integrable, Integrable.finsetSum_vectorMeasure, classical, finsetSum_vectorMeasure, forall_eq_or_imp, induction_on, insert, integral_add_vectorMeasure, mem_insert, not_false_eq_true, sum_insert
-/
theorem integral_finsetSum_vectorMeasure {μ : ι -> VectorMeasure X F}
    {s : Finset ι} (hf : forall i in s, (μ i).Integrable f) :
    ∫ᵛ x, f x ∂[B; ∑ i in s, μ i] = ∑ i in s, ∫ᵛ x, f x ∂[B; μ i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (Integrable.finsetSum_vectorMeasure hf.2)]; rw [ih hf.2]

set_option backward.isDefEq.respectTransparency.types false in
@[integral_simps]
/--
theorem `integral_neg_vectorMeasure` / 定理 `integral_neg_vectorMeasure`

English:
theorem integral_neg_vectorMeasure
  proof: by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

中文:
定理 integral_neg_vectorMeasure
  证明: by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

Depends on / 依赖: FunLike, FunLike.coe_neg, coe_neg, integral, setToFun_neg
-/
theorem integral_neg_vectorMeasure :
    ∫ᵛ x, f x ∂[B; -μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

/--
theorem `integral_sub_vectorMeasure` / 定理 `integral_sub_vectorMeasure`

English:
theorem integral_sub_vectorMeasure
  given: (hμ : μ.Integrable f) (hν : ν.Integrable f)
  proof: by
  rw [sub_eq_add_neg]; rw [integral_add_vectorMeasure hμ hν.neg_vectorMeasure]; rw [integral_neg_vectorMeasure]; rw [← sub_eq_add_neg]

中文:
定理 integral_sub_vectorMeasure
  条件: (hμ : μ.整数egrable f) (hν : ν.整数egrable f)
  证明: by
  rw [sub_eq_add_neg]; rw [integral_add_vectorMeasure hμ hν.neg_vectorMeasure]; rw [integral_neg_vectorMeasure]; rw [← sub_eq_add_neg]

Depends on / 依赖: integral_add_vectorMeasure, integral_neg_vectorMeasure, neg_vectorMeasure, sub_eq_add_neg
-/
theorem integral_sub_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ - ν] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[B; ν] := by
  rw [sub_eq_add_neg]; rw [integral_add_vectorMeasure hμ hν.neg_vectorMeasure]; rw [integral_neg_vectorMeasure]; rw [← sub_eq_add_neg]

end VectorMeasure

section cbm

variable (f μ) in
@[simp]
/--
theorem `integral_zero_cbm` / 定理 `integral_zero_cbm`

English:
theorem integral_zero_cbm
  proof: by
  simp [integral, FunLike.coe_zero]

中文:
定理 integral_zero_cbm
  证明: by
  simp [integral, FunLike.coe_zero]

Depends on / 依赖: FunLike, FunLike.coe_zero, coe_zero, integral
-/
theorem integral_zero_cbm :
    ∫ᵛ x, f x ∂[(0 : E ->L[Real] F ->L[Real] G); μ] = 0 := by
  simp [integral, FunLike.coe_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `integral_add_cbm` / 定理 `integral_add_cbm`

English:
theorem integral_add_cbm
  given: (hB : μ.Integrable f)
  proof: by
  refine setToFun_add_left'' (by simp [transpose]) hB hB ?_
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  nth_rw 1 [← add_zero μ.variation]
  gcongr
  exact Measure.zero_le μ.variation

中文:
定理 integral_add_cbm
  条件: (hB : μ.整数egrable f)
  证明: by
  refine setToFun_add_left'' (by simp [transpose]) hB hB ?_
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  nth_rw 1 [← add_zero μ.variation]
  gcongr
  exact Measure.zero_le μ.variation

Depends on / 依赖: Measure, Measure.zero_le, add_zero, norm_nonneg, nth_rw, setToFun_add_left, transpose, variation, zero_le
-/
theorem integral_add_cbm (hB : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B + C; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[C; μ] := by
  refine setToFun_add_left'' (by simp [transpose]) hB hB ?_
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  nth_rw 1 [← add_zero μ.variation]
  gcongr
  exact Measure.zero_le μ.variation

/--
theorem `integral_finsetSum_cbm` / 定理 `integral_finsetSum_cbm`

English:
theorem integral_finsetSum_cbm
  statement: {B : ι -> E ->L[Real] F ->L[Real] G}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    rw [integral_add_cbm hf]; rw [ih]

中文:
定理 integral_finsetSum_cbm
  结论: {B : ι -> E ->L[实数] F ->L[实数] G}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    rw [integral_add_cbm hf]; rw [ih]

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_insert, classical, induction_on, insert, integral_add_cbm, not_false_eq_true, sum_insert
-/
theorem integral_finsetSum_cbm {B : ι -> E ->L[Real] F ->L[Real] G}
    {s : Finset ι} (hf : μ.Integrable f) :
    ∫ᵛ x, f x ∂[∑ i in s, B i; μ] = ∑ i in s, ∫ᵛ x, f x ∂[B i; μ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    rw [integral_add_cbm hf]; rw [ih]

set_option backward.isDefEq.respectTransparency.types false in
@[integral_simps]
/--
theorem `integral_neg_cbm` / 定理 `integral_neg_cbm`

English:
theorem integral_neg_cbm
  proof: by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

中文:
定理 integral_neg_cbm
  证明: by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

Depends on / 依赖: FunLike, FunLike.coe_neg, coe_neg, integral, setToFun_neg
-/
theorem integral_neg_cbm :
    ∫ᵛ x, f x ∂[-B; μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]

/--
theorem `integral_sub_cbm` / 定理 `integral_sub_cbm`

English:
theorem integral_sub_cbm
  given: (hB : μ.Integrable f)
  proof: by
  rw [sub_eq_add_neg]; rw [integral_add_cbm hB]; rw [integral_neg_cbm]; rw [← sub_eq_add_neg]

中文:
定理 integral_sub_cbm
  条件: (hB : μ.整数egrable f)
  证明: by
  rw [sub_eq_add_neg]; rw [integral_add_cbm hB]; rw [integral_neg_cbm]; rw [← sub_eq_add_neg]

Depends on / 依赖: integral_add_cbm, integral_neg_cbm, sub_eq_add_neg
-/
theorem integral_sub_cbm (hB : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B - C; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[C; μ] := by
  rw [sub_eq_add_neg]; rw [integral_add_cbm hB]; rw [integral_neg_cbm]; rw [← sub_eq_add_neg]

end cbm

/--
theorem `Integrable.of_integral_ne_zero` / 定理 `Integrable.of_integral_ne_zero`

English:
theorem Integrable.of_integral_ne_zero
  given: (h : ∫ᵛ a, f a ∂[B; μ] != 0)
  statement: μ.Integrable f
  proof: Not.imp_symm integral_undef h

中文:
定理 Integrable.of_integral_ne_zero
  条件: (h : ∫ᵛ a, f a ∂[B; μ] != 0)
  结论: μ.整数egrable f
  证明: Not.imp_symm integral_undef h
-/
theorem Integrable.of_integral_ne_zero (h : ∫ᵛ a, f a ∂[B; μ] != 0) : μ.Integrable f :=
  Not.imp_symm integral_undef h

/--
theorem `integral_non_aestronglyMeasurable` / 定理 `integral_non_aestronglyMeasurable`

English:
theorem integral_non_aestronglyMeasurable
  statement: {f : X -> E}
  proof: integral_undef not_and_of_not_left _ h

中文:
定理 integral_non_aestronglyMeasurable
  结论: {f : X -> E}
  证明: integral_undef not_and_of_not_left _ h

Depends on / 依赖: integral_undef, not_and_of_not_left
-/
theorem integral_non_aestronglyMeasurable {f : X -> E}
    (h : ¬AEStronglyMeasurable f μ.variation) :
    ∫ᵛ a, f a ∂[B; μ] = 0 :=
integral_undef not_and_of_not_left _ h

/--
lemma `integral_indicator₂` / 引理 `integral_indicator₂`

English:
lemma integral_indicator₂
  given: {β : Type*} (f : β -> X -> E) (s : Set β) (b : β)
  proof: by
  by_cases hb : b in s <;> simp [hb]

@[fun_prop]

中文:
引理 integral_indicator₂
  条件: {β : 类型} (f : β -> X -> E) (s : Set β) (b : β)
  证明: by
  by_cases hb : b in s <;> simp [hb]

@[fun_prop]
-/
lemma integral_indicator₂ {β : Type*} (f : β -> X -> E) (s : Set β) (b : β) :
    ∫ᵛ y, s.indicator (f · y) b ∂[B; μ] = s.indicator (fun x => ∫ᵛ y, f x y ∂[B; μ]) b := by
  by_cases hb : b in s <;> simp [hb]

@[fun_prop]
/--
theorem `continuous_integral` / 定理 `continuous_integral`

English:
theorem continuous_integral
  statement: Continuous fun f : X ->₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ]
  proof: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun _

中文:
定理 continuous_integral
  结论: Continuous fun f : X ->₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ]
  证明: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun _

Depends on / 依赖: continuous_setToFun, integral_eq_setToFun
-/
theorem continuous_integral : Continuous fun f : X ->₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ] := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun _

/--
theorem `norm_integral_le_lintegral_norm` / 定理 `norm_integral_le_lintegral_norm`

English:
theorem norm_integral_le_lintegral_norm
  proof: (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

中文:
定理 norm_integral_le_lintegral_norm
  证明: (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

Depends on / 依赖: norm_setToFun_le_toReal
-/
theorem norm_integral_le_lintegral_norm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ <= ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
  (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

/--
theorem `norm_integral_le_integral_norm` / 定理 `norm_integral_le_integral_norm`

English:
theorem norm_integral_le_integral_norm
  proof: by
  have le_ae : forallᵐ a ∂μ.variation, 0 <= ‖f a‖ :=
    Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ.variation
  · calc ‖∫ᵛ a, f a ∂[B; μ]‖
    _ <= ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
      norm_integral_le_lintegral_norm
    

中文:
定理 norm_integral_le_integral_norm
  证明: by
  have le_ae : forallᵐ a ∂μ.variation, 0 <= ‖f a‖ :=
    Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ.variation
  · calc ‖∫ᵛ a, f a ∂[B; μ]‖
    _ <= ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
      norm_integral_le_lintegral_norm
    

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.ofReal, ENNReal.toReal, Eventually, Eventually.of_forall, h.norm, integral_eq_lintegral_of_nonneg_ae, integral_non_aestronglyMeasurable, le_ae, norm_integral_le_lintegral_norm, norm_nonneg, norm_zero, ofReal, of_forall, toReal, variation
-/
theorem norm_integral_le_integral_norm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ <= ‖B‖ * ∫ a, ‖f a‖ ∂μ.variation := by
  have le_ae : forallᵐ a ∂μ.variation, 0 <= ‖f a‖ :=
    Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ.variation
  · calc ‖∫ᵛ a, f a ∂[B; μ]‖
    _ <= ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
      norm_integral_le_lintegral_norm
    _ = ‖B‖ * ∫ a, ‖f a‖ ∂μ.variation := by
      rw [integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm]
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    positivity

/--
theorem `enorm_integral_le_lintegral_enorm` / 定理 `enorm_integral_le_lintegral_enorm`

English:
theorem enorm_integral_le_lintegral_enorm
  proof: by
  apply (enorm_setToFun_le _ (by simp)).trans
  gcongr
  simp [← coe_nnnorm]

中文:
定理 enorm_integral_le_lintegral_enorm
  证明: by
  apply (enorm_setToFun_le _ (by simp)).trans
  gcongr
  simp [← coe_nnnorm]

Depends on / 依赖: coe_nnnorm, enorm_setToFun_le
-/
theorem enorm_integral_le_lintegral_enorm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ‖B‖ₑ * ∫⁻ a, ‖f a‖ₑ ∂μ.variation := by
  apply (enorm_setToFun_le _ (by simp)).trans
  gcongr
  simp [← coe_nnnorm]

/--
theorem `enorm_integral_le_lintegral_enorm_transpose` / 定理 `enorm_integral_le_lintegral_enorm_transpose`

English:
theorem enorm_integral_le_lintegral_enorm_transpose
  proof: by
  by_cases hf : μ.Integrable f
  · rw [integral_eq_setToFun_transpose hf]
    apply (enorm_setToFun_le _ (by simp)).trans (by simp)
  · simp [integral_undef hf]

中文:
定理 enorm_integral_le_lintegral_enorm_transpose
  证明: by
  by_cases hf : μ.Integrable f
  · rw [integral_eq_setToFun_transpose hf]
    apply (enorm_setToFun_le _ (by simp)).trans (by simp)
  · simp [integral_undef hf]

Depends on / 依赖: Integrable, enorm_setToFun_le, integral_eq_setToFun_transpose, integral_undef
-/
theorem enorm_integral_le_lintegral_enorm_transpose :
    ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂(μ.transpose B).variation := by
  by_cases hf : μ.Integrable f
  · rw [integral_eq_setToFun_transpose hf]
    apply (enorm_setToFun_le _ (by simp)).trans (by simp)
  · simp [integral_undef hf]

/--
theorem `dist_integral_le_lintegral_edist` / 定理 `dist_integral_le_lintegral_edist`

English:
theorem dist_integral_le_lintegral_edist
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

中文:
定理 dist_integral_le_lintegral_edist
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

Depends on / 依赖: dist_eq_norm, edist_eq_enorm_sub, integral_sub, norm_integral_le_lintegral_norm
-/
theorem dist_integral_le_lintegral_edist (hf : μ.Integrable f) (hg : μ.Integrable g) :
    dist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) <=
      ‖B‖ * (∫⁻ a, edist (f a) (g a) ∂μ.variation).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

/--
theorem `edist_integral_le_lintegral_edist` / 定理 `edist_integral_le_lintegral_edist`

English:
theorem edist_integral_le_lintegral_edist
  given: (hf : μ.Integrable f) (hg : μ.Integrable g)
  proof: by
  rw [edist_dist]
  apply ENNReal.ofReal_le_of_le_toReal
  grw [dist_integral_le_lintegral_edist hf hg, ENNReal.toReal_mul, toReal_enorm]

中文:
定理 edist_integral_le_lintegral_edist
  条件: (hf : μ.整数egrable f) (hg : μ.整数egrable g)
  证明: by
  rw [edist_dist]
  apply ENNReal.ofReal_le_of_le_toReal
  grw [dist_integral_le_lintegral_edist hf hg, ENNReal.toReal_mul, toReal_enorm]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_of_le_toReal, ENNReal.toReal_mul, dist_integral_le_lintegral_edist, edist_dist, ofReal_le_of_le_toReal, toReal_enorm, toReal_mul
-/
theorem edist_integral_le_lintegral_edist (hf : μ.Integrable f) (hg : μ.Integrable g) :
    edist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) <=
      ‖B‖ₑ * ∫⁻ a, edist (f a) (g a) ∂μ.variation := by
  rw [edist_dist]
  apply ENNReal.ofReal_le_of_le_toReal
  grw [dist_integral_le_lintegral_edist hf hg, ENNReal.toReal_mul, toReal_enorm]

/--
theorem `frequently_ae_ne_zero_of_integral_ne_zero` / 定理 `frequently_ae_ne_zero_of_integral_ne_zero`

English:
theorem frequently_ae_ne_zero_of_integral_ne_zero
  proof: fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

中文:
定理 frequently_ae_ne_zero_of_integral_ne_zero
  证明: fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

Depends on / 依赖: integral_eq_zero_of_ae, not_not, not_not.mp
-/
theorem frequently_ae_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] != 0) : existsᶠ a in ae μ.variation, f a != 0 :=
  fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

/--
theorem `exists_ne_zero_of_integral_ne_zero` / 定理 `exists_ne_zero_of_integral_ne_zero`

English:
theorem exists_ne_zero_of_integral_ne_zero
  proof: (frequently_ae_ne_zero_of_integral_ne_zero h).exists

中文:
定理 exists_ne_zero_of_integral_ne_zero
  证明: (frequently_ae_ne_zero_of_integral_ne_zero h).exists

Depends on / 依赖: frequently_ae_ne_zero_of_integral_ne_zero
-/
theorem exists_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] != 0) : exists a, f a != 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists

/--
lemma `integral_toSignedMeasure` / 引理 `integral_toSignedMeasure`

English:
lemma integral_toSignedMeasure
  given: {μ : Measure X} [IsFiniteMeasure μ] {f : X -> G}
  proof: by
  rcases subsingleton_or_nontrivial G with h'G | h'G
  · apply Subsingleton.elim
  rw [integral_eq_setToFun]; rw [MeasureTheory.integral_eq_setToFun]
  simp only [Measure.variation_toSignedMeasure]
  apply setToFun_congr_left' _ _ (fun s hs h's => ?_)
  simp only [transpose, ContinuousLinearMap.f

中文:
引理 integral_toSignedMeasure
  条件: {μ : Measure X} [IsFiniteMeasure μ] {f : X -> G}
  证明: by
  rcases subsingleton_or_nontrivial G with h'G | h'G
  · apply Subsingleton.elim
  rw [integral_eq_setToFun]; rw [MeasureTheory.integral_eq_setToFun]
  simp only [Measure.variation_toSignedMeasure]
  apply setToFun_congr_left' _ _ (fun s hs h's => ?_)
  simp only [transpose, ContinuousLinearMap.f
-/
@[simp] lemma integral_toSignedMeasure {μ : Measure X} [IsFiniteMeasure μ] {f : X -> G} :
    ∫ᵛ x, f x ∂<•μ.toSignedMeasure = ∫ x, f x ∂μ := by
  rcases subsingleton_or_nontrivial G with h'G | h'G
  · apply Subsingleton.elim
  rw [integral_eq_setToFun]; rw [MeasureTheory.integral_eq_setToFun]
  simp only [Measure.variation_toSignedMeasure]
  apply setToFun_congr_left' _ _ (fun s hs h's => ?_)
  simp only [transpose, ContinuousLinearMap.flip_flip, mapRange_apply,
    Measure.toSignedMeasure_apply_measurable hs, LinearMap.toAddMonoidHom_coe,
    ContinuousLinearMap.coe_coe, weightedSMul]
  rfl

@[simp]
/--
theorem `integral_dirac'` / 定理 `integral_dirac'`

English:
theorem integral_dirac'
  statement: [MeasurableSpace X] [CompleteSpace G] {a : X} {v : F}
  proof: by
  borelize E
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a 

中文:
定理 integral_dirac'
  结论: [MeasurableSpace X] [CompleteSpace G] {a : X} {v : F}
  证明: by
  borelize E
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a 

Depends on / 依赖: B.flip, IsFiniteMeasure, Measure, Measure.ae_smul_measure, Measure.dirac, VectorMeasure, VectorMeasure.dirac, ae_eq_dirac, ae_smul_measure, borelize, hfm.measurable, infer_instance, integral_congr_ae, measurable, transpose, transpose_dirac, variation, variation_dirac
-/
theorem integral_dirac' [MeasurableSpace X] [CompleteSpace G] {a : X} {v : F}
    (hfm : StronglyMeasurable f) :
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = B (f a) v := by
  borelize E
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMeasure.dirac a v] := by
      apply integral_congr_ae
      simp only [variation_dirac]
      exact Measure.ae_smul_measure (ae_eq_dirac' hfm.measurable) _
    _ = B (f a) v := by simp

@[simp]
/--
theorem `integral_dirac` / 定理 `integral_dirac`

English:
theorem integral_dirac
  statement: [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
  proof: by
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMe

中文:
定理 integral_dirac
  结论: [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
  证明: by
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMe

Depends on / 依赖: B.flip, IsFiniteMeasure, Measure, Measure.ae_smul_measure, Measure.dirac, VectorMeasure, VectorMeasure.dirac, ae_eq_dirac, ae_smul_measure, infer_instance, integral_congr_ae, transpose, transpose_dirac, variation, variation_dirac
-/
theorem integral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
    {a : X} {v : F} :
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = B (f a) v := by
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMeasure.dirac a v] := by
      apply integral_congr_ae
      simp only [variation_dirac]
      exact Measure.ae_smul_measure (ae_eq_dirac f) _
    _ = B (f a) v := by simp

/--
theorem `integral_unique` / 定理 `integral_unique`

English:
theorem integral_unique
  given: [Unique X] [CompleteSpace G]
  proof: calc
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ _, f default ∂[B; μ] := by congr with x; congr; exact Unique.uniq _ x
    _ = B (f default) (μ univ) := by rw [integral_const]

中文:
定理 integral_unique
  条件: [Unique X] [CompleteSpace G]
  证明: calc
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ _, f default ∂[B; μ] := by congr with x; congr; exact Unique.uniq _ x
    _ = B (f default) (μ univ) := by rw [integral_const]

Depends on / 依赖: Unique, Unique.uniq, integral_const
-/
theorem integral_unique [Unique X] [CompleteSpace G] :
    ∫ᵛ x, f x ∂[B; μ] = B (f default) (μ univ) :=
  calc
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ _, f default ∂[B; μ] := by congr with x; congr; exact Unique.uniq _ x
    _ = B (f default) (μ univ) := by rw [integral_const]

/--
theorem `tendsto_integral_of_L1` / 定理 `tendsto_integral_of_L1`

English:
theorem tendsto_integral_of_L1
  statement: {ι} (f : X -> E)
  proof: tendsto_setToFun_of_L1 _ f hfi hFi hF

中文:
定理 tendsto_integral_of_L1
  结论: {ι} (f : X -> E)
  证明: tendsto_setToFun_of_L1 _ f hfi hFi hF

Depends on / 依赖: tendsto_setToFun_of_L1
-/
theorem tendsto_integral_of_L1 {ι} (f : X -> E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X -> E}
    {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) :=
  tendsto_setToFun_of_L1 _ f hfi hFi hF

/--
lemma `tendsto_integral_of_L1'` / 引理 `tendsto_integral_of_L1'`

English:
lemma tendsto_integral_of_L1'
  statement: {ι} (f : X -> E)
  proof: by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

中文:
引理 tendsto_integral_of_L1'
  结论: {ι} (f : X -> E)
  证明: by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

Depends on / 依赖: Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm, simp_rw, sub_apply, tendsto_integral_of_L1
-/
lemma tendsto_integral_of_L1' {ι} (f : X -> E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X -> E}
    {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ.variation) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]

/--
theorem `continuousWithinAt_of_dominated` / 定理 `continuousWithinAt_of_dominated`

English:
theorem continuousWithinAt_of_dominated
  statement: {F : Y -> X -> E} {x₀ : Y} {bound : X -> Real} {s : Set Y}
  proof: continuousWithinAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousWithinAt_of_dominated
  结论: {F : Y -> X -> E} {x₀ : Y} {bound : X -> 实数} {s : Set Y}
  证明: continuousWithinAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousWithinAt_setToFun_of_dominated, hF_meas, h_bound, h_cont
-/
theorem continuousWithinAt_of_dominated {F : Y -> X -> E} {x₀ : Y} {bound : X -> Real} {s : Set Y}
    (hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ.variation, ‖F x a‖ <= bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : forallᵐ a ∂μ.variation, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) s x₀ :=
  continuousWithinAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

/--
theorem `continuousAt_of_dominated` / 定理 `continuousAt_of_dominated`

English:
theorem continuousAt_of_dominated
  statement: {F : Y -> X -> E} {x₀ : Y} {bound : X -> Real}
  proof: continuousAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousAt_of_dominated
  结论: {F : Y -> X -> E} {x₀ : Y} {bound : X -> 实数}
  证明: continuousAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousAt_setToFun_of_dominated, hF_meas, h_bound, h_cont
-/
theorem continuousAt_of_dominated {F : Y -> X -> E} {x₀ : Y} {bound : X -> Real}
    (hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ a ∂μ.variation, ‖F x a‖ <= bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : forallᵐ a ∂μ.variation, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) x₀ :=
  continuousAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

/--
theorem `continuousOn_of_dominated` / 定理 `continuousOn_of_dominated`

English:
theorem continuousOn_of_dominated
  statement: {F : Y -> X -> E} {bound : X -> Real} {s : Set Y}
  proof: continuousOn_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousOn_of_dominated
  结论: {F : Y -> X -> E} {bound : X -> 实数} {s : Set Y}
  证明: continuousOn_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousOn_setToFun_of_dominated, hF_meas, h_bound, h_cont
-/
theorem continuousOn_of_dominated {F : Y -> X -> E} {bound : X -> Real} {s : Set Y}
    (hF_meas : forall x in s, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : forall x in s, forallᵐ a ∂μ.variation, ‖F x a‖ <= bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : forallᵐ a ∂μ.variation, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ᵛ a, F x a ∂[B; μ]) s :=
  continuousOn_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

/--
theorem `continuous_of_dominated` / 定理 `continuous_of_dominated`

English:
theorem continuous_of_dominated
  statement: {F : Y -> X -> E} {bound : X -> Real}
  proof: continuous_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

中文:
定理 continuous_of_dominated
  结论: {F : Y -> X -> E} {bound : X -> 实数}
  证明: continuous_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuous_setToFun_of_dominated, countable_bInter_mem, hF_meas, h_bound, h_cont, preimage_iInter
-/
theorem continuous_of_dominated {F : Y -> X -> E} {bound : X -> Real}
    (hF_meas : forall x, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : forall x, forallᵐ a ∂μ.variation, ‖F x a‖ <= bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : forallᵐ a ∂μ.variation, Continuous fun x => F x a) :
    Continuous fun x => ∫ᵛ a, F x a ∂[B; μ] :=
  continuous_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

/--
theorem `norm_integral_le_of_norm_le_const` / 定理 `norm_integral_le_of_norm_le_const`

English:
theorem norm_integral_le_of_norm_le_const
  statement: [IsFiniteMeasure μ.variation]
  proof: calc
  ‖∫ᵛ x, f x ∂[B; μ]‖
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation).toReal :=
    norm_integral_le_lintegral_norm
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal C ∂μ.variation).toReal := by
    gcongr 1
    apply ENNReal.toReal_mono
    · simp only [lintegral_const, ne_eq]
      finiteness
    · a

中文:
定理 norm_integral_le_of_norm_le_const
  结论: [IsFiniteMeasure μ.variation]
  证明: calc
  ‖∫ᵛ x, f x ∂[B; μ]‖
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation).toReal :=
    norm_integral_le_lintegral_norm
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal C ∂μ.variation).toReal := by
    gcongr 1
    apply ENNReal.toReal_mono
    · simp only [lintegral_const, ne_eq]
      finiteness
    · a

Depends on / 依赖: countable_bInter_mem, mem_map, sInter_eq_biInter
-/
theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ.variation]
    {C : Real} (h : forallᵐ x ∂μ.variation, ‖f x‖ <= C) :
    ‖∫ᵛ x, f x ∂[B; μ]‖ <= C * ‖B‖ * μ.variation.real univ := calc
  ‖∫ᵛ x, f x ∂[B; μ]‖
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation).toReal :=
    norm_integral_le_lintegral_norm
  _ <= ‖B‖ * (∫⁻ a, ENNReal.ofReal C ∂μ.variation).toReal := by
    gcongr 1
    apply ENNReal.toReal_mono
    · simp only [lintegral_const, ne_eq]
      finiteness
    · apply lintegral_mono_ae
      filter_upwards [h] with x hx using ENNReal.ofReal_mono hx
  _ = ‖B‖ * (C * μ.variation.real univ) := by
    by_cases hμ : μ.variation = 0
    · simp [hμ]
    have : (ae μ.variation).NeBot := ae_neBot.mpr hμ
    have hC : 0 <= C := by
      obtain ⟨x, hx⟩ := h.exists
      exact (norm_nonneg _).trans hx
    simp [ENNReal.toReal_ofReal hC, Measure.real]
  _ = C * ‖B‖ * μ.variation.real univ := by ring

/--
theorem `enorm_integral_le_of_enorm_le_const` / 定理 `enorm_integral_le_of_enorm_le_const`

English:
theorem enorm_integral_le_of_enorm_le_const
  proof: by
  apply enorm_integral_le_lintegral_enorm.trans
  rw [mul_comm C]; rw [mul_assoc]
  gcongr
  exact (lintegral_mono_ae h).trans (by simp)

中文:
定理 enorm_integral_le_of_enorm_le_const
  证明: by
  apply enorm_integral_le_lintegral_enorm.trans
  rw [mul_comm C]; rw [mul_assoc]
  gcongr
  exact (lintegral_mono_ae h).trans (by simp)

Depends on / 依赖: enorm_integral_le_lintegral_enorm, enorm_integral_le_lintegral_enorm.trans, lintegral_mono_ae, mul_assoc, mul_comm
-/
theorem enorm_integral_le_of_enorm_le_const
    {C : Real>=0∞} (h : forallᵐ x ∂μ.variation, ‖f x‖ₑ <= C) :
    ‖∫ᵛ x, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ.variation univ := by
  apply enorm_integral_le_lintegral_enorm.trans
  rw [mul_comm C]; rw [mul_assoc]
  gcongr
  exact (lintegral_mono_ae h).trans (by simp)

/--
theorem `nndist_integral_add_vectorMeasure_le_lintegral` / 定理 `nndist_integral_add_vectorMeasure_le_lintegral`

English:
theorem nndist_integral_add_vectorMeasure_le_lintegral
  proof: by
  rw [integral_add_vectorMeasure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm

中文:
定理 nndist_integral_add_vectorMeasure_le_lintegral
  证明: by
  rw [integral_add_vectorMeasure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm

Depends on / 依赖: add_sub_cancel_left, enorm_integral_le_lintegral_enorm, integral_add_vectorMeasure, nndist_comm, nndist_eq_nnnorm
-/
theorem nndist_integral_add_vectorMeasure_le_lintegral
    (h₁ : μ.Integrable f) (h₂ : ν.Integrable f) :
    (nndist (∫ᵛ x, f x ∂[B; μ]) (∫ᵛ x, f x ∂[B; (μ + ν)]) : Real>=0∞) <=
      ‖B‖ₑ * ∫⁻ x, ‖f x‖ₑ ∂ν.variation := by
  rw [integral_add_vectorMeasure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm

variable {β : Type*} [MeasurableSpace β] {φ : X -> β} {a : X} {v : F}

/--
lemma `variation_transpose_map_le` / 引理 `variation_transpose_map_le`

English:
lemma variation_transpose_map_le
  proof: by
  grw [transpose_map, variation_map_le]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
引理 variation_transpose_map_le
  证明: by
  grw [transpose_map, variation_map_le]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: transpose_map, variation_map_le
-/
lemma variation_transpose_map_le :
    ((μ.map φ).transpose B).variation <= Measure.map φ (μ.transpose B).variation := by
  grw [transpose_map, variation_map_le]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
theorem `Integrable.map` / 定理 `Integrable.map`

English:
theorem Integrable.map
  statement: {β : Type*} [MeasurableSpace β] {φ : X -> β}
  proof: by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ]
  simp_rw [VectorMeasure.Integrable] at h ⊢
  apply ((integrable_map_measure hfm hφ.aemeasurable).2 h).mono_measure
  apply variation_map_le

中文:
定理 Integrable.map
  结论: {β : 类型} [MeasurableSpace β] {φ : X -> β}
  证明: by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ]
  simp_rw [VectorMeasure.Integrable] at h ⊢
  apply ((integrable_map_measure hfm hφ.aemeasurable).2 h).mono_measure
  apply variation_map_le

Depends on / 依赖: Integrable, Measurable, VectorMeasure, VectorMeasure.Integrable, VectorMeasure.map, aemeasurable, integrable_map_measure, mono_measure, simp_rw, variation_map_le
-/
theorem Integrable.map {β : Type*} [MeasurableSpace β] {φ : X -> β}
    {f : β -> E} (hfm : AEStronglyMeasurable f (μ.variation.map φ))
    (h : μ.Integrable (f ∘ φ)) : (μ.map φ).Integrable f := by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ]
  simp_rw [VectorMeasure.Integrable] at h ⊢
  apply ((integrable_map_measure hfm hφ.aemeasurable).2 h).mono_measure
  apply variation_map_le

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `integral_map` / 定理 `integral_map`

English:
theorem integral_map
  statement: {β : Type*} [MeasurableSpace β]
  proof: by
  apply setToFun_of_le_map _ _ hfi' hfm hφ variation_map_le
  intro s x hs
  simp [hs, VectorMeasure.map, transpose, hφ]

中文:
定理 integral_map
  结论: {β : 类型} [MeasurableSpace β]
  证明: by
  apply setToFun_of_le_map _ _ hfi' hfm hφ variation_map_le
  intro s x hs
  simp [hs, VectorMeasure.map, transpose, hφ]

Depends on / 依赖: VectorMeasure, VectorMeasure.map, setToFun_of_le_map, transpose, variation_map_le
-/
theorem integral_map {β : Type*} [MeasurableSpace β]
    {φ : X -> β} (hφ : Measurable φ) {f : β -> E}
    (hfm : AEStronglyMeasurable f (μ.variation.map φ))
    (hfi' : μ.Integrable (f ∘ φ)) :
    ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] := by
  apply setToFun_of_le_map _ _ hfi' hfm hφ variation_map_le
  intro s x hs
  simp [hs, VectorMeasure.map, transpose, hφ]

/--
theorem `_root_.MeasurableEmbedding.variation_transpose_map` / 定理 `_root_.MeasurableEmbedding.variation_transpose_map`

English:
theorem _root_.MeasurableEmbedding.variation_transpose_map
  given: (hφ : MeasurableEmbedding φ)
  proof: by
  rw [transpose_map]; rw [hφ.variation_map]

omit [NormedSpace Real E] [NormedSpace Real F] in

中文:
定理 _root_.MeasurableEmbedding.variation_transpose_map
  条件: (hφ : MeasurableEmbedding φ)
  证明: by
  rw [transpose_map]; rw [hφ.variation_map]

omit [NormedSpace Real E] [NormedSpace Real F] in

Depends on / 依赖: transpose_map, variation_map
-/
theorem _root_.MeasurableEmbedding.variation_transpose_map (hφ : MeasurableEmbedding φ) :
    ((μ.map φ).transpose B).variation = (μ.transpose B).variation.map φ := by
  rw [transpose_map]; rw [hφ.variation_map]

omit [NormedSpace Real E] [NormedSpace Real F] in
/--
theorem `_root_.MeasurableEmbedding.integrable_map_vectorMeasure` / 定理 `_root_.MeasurableEmbedding.integrable_map_vectorMeasure`

English:
theorem _root_.MeasurableEmbedding.integrable_map_vectorMeasure
  proof: by
  simp_rw [VectorMeasure.Integrable, ← hφ.integrable_map_iff, hφ.variation_map]

中文:
定理 _root_.MeasurableEmbedding.integrable_map_vectorMeasure
  证明: by
  simp_rw [VectorMeasure.Integrable, ← hφ.integrable_map_iff, hφ.variation_map]

Depends on / 依赖: Integrable, VectorMeasure, VectorMeasure.Integrable, integrable_map_iff, simp_rw, variation_map
-/
theorem _root_.MeasurableEmbedding.integrable_map_vectorMeasure
    (hφ : MeasurableEmbedding φ) {f : β -> E} :
    (μ.map φ).Integrable f ↔ μ.Integrable (f ∘ φ) := by
  simp_rw [VectorMeasure.Integrable, ← hφ.integrable_map_iff, hφ.variation_map]

/--
theorem `_root_.MeasurableEmbedding.integral_map_vectorMeasure` / 定理 `_root_.MeasurableEmbedding.integral_map_vectorMeasure`

English:
theorem _root_.MeasurableEmbedding.integral_map_vectorMeasure
  proof: by
  by_cases hfm : AEStronglyMeasurable f (μ.variation.map φ)
  · by_cases h'fm : μ.Integrable (f ∘ φ)
    · apply integral_map hφ.measurable hfm h'fm
    · rw [integral_undef, integral_undef]
      · exact h'fm
      · rwa [hφ.integrable_map_vectorMeasure]
  · rw [integral_non_aestronglyMeasurable

中文:
定理 _root_.MeasurableEmbedding.integral_map_vectorMeasure
  证明: by
  by_cases hfm : AEStronglyMeasurable f (μ.variation.map φ)
  · by_cases h'fm : μ.Integrable (f ∘ φ)
    · apply integral_map hφ.measurable hfm h'fm
    · rw [integral_undef, integral_undef]
      · exact h'fm
      · rwa [hφ.integrable_map_vectorMeasure]
  · rw [integral_non_aestronglyMeasurable

Depends on / 依赖: AEStronglyMeasurable, Integrable, aestronglyMeasurable_map_iff, integrable_map_vectorMeasure, integral_map, integral_non_aestronglyMeasurable, integral_undef, measurable, variation, variation.map, variation_map
-/
theorem _root_.MeasurableEmbedding.integral_map_vectorMeasure
    (hφ : MeasurableEmbedding φ) {f : β -> E} :
    ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] := by
  by_cases hfm : AEStronglyMeasurable f (μ.variation.map φ)
  · by_cases h'fm : μ.Integrable (f ∘ φ)
    · apply integral_map hφ.measurable hfm h'fm
    · rw [integral_undef, integral_undef]
      · exact h'fm
      · rwa [hφ.integrable_map_vectorMeasure]
  · rw [integral_non_aestronglyMeasurable, integral_non_aestronglyMeasurable]
    · rwa [hφ.aestronglyMeasurable_map_iff] at hfm
    · rwa [hφ.variation_map]

/--
theorem `_root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure` / 定理 `_root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure`

English:
theorem _root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure
  proof: hφ.measurableEmbedding.integral_map_vectorMeasure

中文:
定理 _root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure
  证明: hφ.measurableEmbedding.integral_map_vectorMeasure

Depends on / 依赖: integral_map_vectorMeasure, measurableEmbedding, measurableEmbedding.integral_map_vectorMeasure
-/
theorem _root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure
    [TopologicalSpace X] [BorelSpace X]
    [TopologicalSpace β] [BorelSpace β] (hφ : IsClosedEmbedding φ)
    {f : β -> E} : ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.integral_map_vectorMeasure

/--
theorem `integral_map_equiv` / 定理 `integral_map_equiv`

English:
theorem integral_map_equiv
  given: {β} [MeasurableSpace β] (e : X ≃ᵐ β) (f : β -> E)
  proof: e.measurableEmbedding.integral_map_vectorMeasure

中文:
定理 integral_map_equiv
  条件: {β} [MeasurableSpace β] (e : X ≃ᵐ β) (f : β -> E)
  证明: e.measurableEmbedding.integral_map_vectorMeasure

Depends on / 依赖: e.measurableEmbedding.integral_map_vectorMeasure, integral_map_vectorMeasure, measurableEmbedding
-/
theorem integral_map_equiv {β} [MeasurableSpace β] (e : X ≃ᵐ β) (f : β -> E) :
    ∫ᵛ y, f y ∂[B; μ.map e] = ∫ᵛ x, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.integral_map_vectorMeasure

/--
theorem `tendsto_integral_of_dominated_convergence` / 定理 `tendsto_integral_of_dominated_convergence`

English:
theorem tendsto_integral_of_dominated_convergence
  statement: {F : Nat -> X -> E} {f : X -> E} (bound : X -> Real)
  proof: tendsto_setToFun_of_dominated_convergence _ bound F_measurable bound_integrable h_bound h_lim

中文:
定理 tendsto_integral_of_dominated_convergence
  结论: {F : 自然数 -> X -> E} {f : X -> E} (bound : X -> 实数)
  证明: tendsto_setToFun_of_dominated_convergence _ bound F_measurable bound_integrable h_bound h_lim

Depends on / 依赖: F_measurable, bound_integrable, h_bound, h_lim, tendsto_setToFun_of_dominated_convergence
-/
theorem tendsto_integral_of_dominated_convergence {F : Nat -> X -> E} {f : X -> E} (bound : X -> Real)
    (F_measurable : forall n, AEStronglyMeasurable (F n) μ.variation)
    (bound_integrable : Integrable bound μ.variation)
    (h_bound : forall n, forallᵐ a ∂μ.variation, ‖F n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ.variation, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ᵛ a, F n a ∂[B; μ]) atTop (𝓝 <| ∫ᵛ a, f a ∂[B; μ]) :=
  tendsto_setToFun_of_dominated_convergence _ bound F_measurable bound_integrable h_bound h_lim

/--
theorem `tendsto_integral_filter_of_dominated_convergence` / 定理 `tendsto_integral_filter_of_dominated_convergence`

English:
theorem tendsto_integral_filter_of_dominated_convergence
  statement: {l : Filter ι} [l.IsCountablyGenerated]
  proof: tendsto_setToFun_filter_of_dominated_convergence _ bound hF_meas h_bound bound_integrable h_lim

中文:
定理 tendsto_integral_filter_of_dominated_convergence
  结论: {l : Filter ι} [l.IsCountablyGenerated]
  证明: tendsto_setToFun_filter_of_dominated_convergence _ bound hF_meas h_bound bound_integrable h_lim

Depends on / 依赖: bound_integrable, hF_meas, h_bound, h_lim, tendsto_setToFun_filter_of_dominated_convergence
-/
theorem tendsto_integral_filter_of_dominated_convergence {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι -> X -> E} {f : X -> E} (bound : X -> Real)
    (hF_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : forallᶠ n in l, forallᵐ a ∂μ.variation, ‖F n a‖ <= bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_lim : forallᵐ a ∂μ.variation, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ᵛ a, F n a ∂[B; μ]) l (𝓝 <| ∫ᵛ a, f a ∂[B; μ]) :=
  tendsto_setToFun_filter_of_dominated_convergence _ bound hF_meas h_bound bound_integrable h_lim

/--
theorem `hasSum_integral_of_dominated_convergence` / 定理 `hasSum_integral_of_dominated_convergence`

English:
theorem hasSum_integral_of_dominated_convergence
  statement: [Countable ι] {F : ι -> X -> E} {f : X -> E}
  proof: hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable bound_integrable
    h_lim

中文:
定理 hasSum_integral_of_dominated_convergence
  结论: [Countable ι] {F : ι -> X -> E} {f : X -> E}
  证明: hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable bound_integrable
    h_lim

Depends on / 依赖: bound_integrable, bound_summable, hF_meas, h_bound, h_lim, hasSum_setToFun_of_dominated_convergence
-/
theorem hasSum_integral_of_dominated_convergence [Countable ι] {F : ι -> X -> E} {f : X -> E}
    (bound : ι -> X -> Real) (hF_meas : forall n, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : forall n, forallᵐ a ∂μ.variation, ‖F n a‖ <= bound n a)
    (bound_summable : forallᵐ a ∂μ.variation, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ.variation)
    (h_lim : forallᵐ a ∂μ.variation, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ᵛ a, F n a ∂[B; μ]) (∫ᵛ a, f a ∂[B; μ]) :=
  hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable bound_integrable
    h_lim

/--
theorem `integral_tsum` / 定理 `integral_tsum`

English:
theorem integral_tsum
  statement: [CompleteSpace E] [Countable ι]
  proof: setToFun_tsum _ hf hf'

中文:
定理 integral_tsum
  结论: [CompleteSpace E] [Countable ι]
  证明: setToFun_tsum _ hf hf'

Depends on / 依赖: setToFun_tsum
-/
theorem integral_tsum [CompleteSpace E] [Countable ι]
    {f : ι -> X -> E} (hf : forall i, AEStronglyMeasurable (f i) μ.variation)
    (hf' : ∑' i, ∫⁻ a : X, ‖f i a‖ₑ ∂μ.variation != ∞) :
    ∫ᵛ a, ∑' i, f i a ∂[B; μ] = ∑' i, ∫ᵛ a, f i a ∂[B; μ] :=
  setToFun_tsum _ hf hf'

/--
theorem `tendsto_integral_filter_of_norm_le_const` / 定理 `tendsto_integral_filter_of_norm_le_const`

English:
theorem tendsto_integral_filter_of_norm_le_const
  statement: {l : Filter ι} [l.IsCountablyGenerated]
  proof: tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

中文:
定理 tendsto_integral_filter_of_norm_le_const
  结论: {l : Filter ι} [l.IsCountablyGenerated]
  证明: tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

Depends on / 依赖: h_bound, h_lim, h_meas, tendsto_setToFun_filter_of_norm_le_const
-/
theorem tendsto_integral_filter_of_norm_le_const {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι -> X -> E} [IsFiniteMeasure μ.variation] {f : X -> E}
    (h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : exists C, forallᶠ n in l, forallᵐ a ∂μ.variation, ‖F n a‖ <= C)
    (h_lim : forallᵐ a ∂μ.variation, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ᵛ a, F n a ∂[B; μ]) l (𝓝 (∫ᵛ a, f a ∂[B; μ])) :=
  tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

end VectorMeasure

end MeasureTheory
